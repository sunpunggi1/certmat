"""
CertMat 원클릭 재현 및 SHA-256 무결성 검증 스크립트 (`reproduce_all.py`).

사용법:
  - 빠른 전체 검증 (데이터셋·결과·증명서 SHA-256 + Lean 4 `#print axioms` 51정리 +
    컴파일된 `certmat-check` 바이너리 전체 TSV 전수 검증 + 독립 Fraction 검증 +
    원본 데이터셋 층화 전체벡터/36원소 바인딩 검증 + pytest):
      python reproduce_all.py --verify-only
  - 전체 처음부터 재빌드·재계산 + 보완분석 + 매니페스트 생성 + 검증:
      python reproduce_all.py --full --workers 2
  - 현재 산출물의 Lean 검증 보고서 및 SHA-256 매니페스트 갱신:
      python reproduce_all.py --write-manifest
"""

from __future__ import annotations

import argparse
import csv
import gzip
import json
import re
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List

ROOT_DIR = Path(__file__).resolve().parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from certmat.datasets import DATA_DIR, PINNED_DATASET_SHA256, sha256_file
from certmat.exact_lp import to_fraction
from certmat.lean_bridge import (
    _parse_strict_q,
    build_lean_kernel,
    find_lean_checker_binary,
    verify_lean_axioms,
    verify_tsv_independent,
    verify_tsv_with_lean,
)
from certmat.phase_audit import formula_to_atom_fractions
from certmat.uncertainty import HETERO_CHEM_PROFILE, get_phase_uncertainty

RESULTS_DIR = ROOT_DIR / "results"
LEAN_DIR = ROOT_DIR / "lean"
PAPER_DIR = ROOT_DIR / "paper"
MANIFEST_PATH = RESULTS_DIR / "reproduction_manifest.json"
LEAN_REPORT_PATH = RESULTS_DIR / "lean_verification_report.json"

# Lean 4 커널 금지 우회 키워드 (sorry/axiom/admit + 커널 우회 프리미티브 전수 차단)
_FORBIDDEN_LEAN_RE = re.compile(
    r"\b(sorry|axiom|admit|implemented_by|extern|unsafe|partial|opaque|native_decide|csimp)\b"
)

# fail-closed 완전성 검증용 필수 산출물 목록 (디스크와 매니페스트 동시 삭제 우회 차단)
REQUIRED_SUMMARY_FILES: tuple[str, ...] = (
    "jarvis_elastic_summary.json",
    "jarvis_phase_summary.json",
    "wbm_phase_summary.json",
    "gnome_crossval_summary.json",
    "gnome_r2scan_full_summary.json",
    "gnome_pbe_full_summary.json",
    "supplementary_analysis.json",
    "lean_verification_report.json",
)
REQUIRED_TSV_FILES: tuple[str, ...] = (
    "certs_jarvis_elastic_all.tsv",
    "certs_jarvis_elastic_mandel.tsv",
    "certs_jarvis_phase_sample.tsv",
    "certs_wbm_phase_sample.tsv",
    "certs_gnome_matched_sample.tsv",
    "certs_gnome_matched_r2scan_sample.tsv",
    "certs_gnome_r2scan_sample.tsv",
    "certs_gnome_pbe_sample.tsv",
)
REQUIRED_PAPER_FILES: tuple[str, ...] = (
    "certmat_paper.md",
    "certmat_summary_ko.md",
)


def _strip_lean_comments(text: str) -> str:
    """중첩 블록 주석(`/- ... -/`) 및 줄 주석(`-- ...`)을 문자열 리터럴을 보존하며 제거한다."""
    out: List[str] = []
    i = 0
    n = len(text)
    depth = 0
    in_str = False
    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1
                i += 2
            elif ch == "-" and nxt == "/":
                depth -= 1
                i += 2
            else:
                if ch == "\n":
                    out.append("\n")
                i += 1
            continue
        if in_str:
            out.append(ch)
            if ch == "\\" and i + 1 < n:
                out.append(nxt)
                i += 2
                continue
            if ch == '"':
                in_str = False
            i += 1
            continue
        if ch == '"':
            in_str = True
            out.append(ch)
            i += 1
        elif ch == "/" and nxt == "-":
            depth = 1
            i += 2
        elif ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(ch)
            i += 1
    return "".join(out)


def check_dataset_integrity() -> Dict[str, Any]:
    """소스 고정 SHA-256(`PINNED_DATASET_SHA256`) 및 `data/dataset_manifest.json` 기준으로 필수 4대 원본 공개 데이터셋 무결성을 검증한다."""
    manifest_file = DATA_DIR / "dataset_manifest.json"
    if not manifest_file.exists():
        raise FileNotFoundError(f"데이터셋 매니페스트 없음: {manifest_file}")
    with open(manifest_file, "r", encoding="utf-8") as f:
        manifest = json.load(f)

    report: Dict[str, Any] = {}
    all_ok = True
    # 필수 소스 고정 키(4대 데이터셋) 전체를 강제 순회(fail-closed: 매니페스트 누락 시 즉시 실패)
    all_keys = sorted(set(PINNED_DATASET_SHA256.keys()) | set(manifest.keys()))
    for key in all_keys:
        meta = manifest.get(key)
        pinned = PINNED_DATASET_SHA256.get(key)
        if meta is None or "file" not in meta:
            report[key] = {"exists": False, "in_manifest": False, "sha256_match": False, "pinned_match": False}
            all_ok = False
            continue
        fpath = DATA_DIR / meta["file"]
        if not fpath.exists():
            report[key] = {"exists": False, "in_manifest": True, "sha256_match": False, "pinned_match": False}
            all_ok = False
            continue
        actual = sha256_file(fpath)
        manifest_match = (actual == meta.get("sha256"))
        pinned_match = (pinned is None or actual == pinned)
        match = manifest_match and pinned_match
        if not match:
            all_ok = False
        report[key] = {
            "file": meta["file"],
            "bytes": fpath.stat().st_size,
            "expected_sha256": meta.get("sha256"),
            "pinned_sha256": pinned,
            "actual_sha256": actual,
            "sha256_match": match,
            "pinned_match": pinned_match,
        }
    return {"all_ok": all_ok, "datasets": report}


def check_lean_static_and_axioms(ensure_fresh_build: bool = True) -> Dict[str, Any]:
    """Lean 4 커널 정적 검사(금지 키워드 0건), 빌드 최신성 보장(`lake build`), 및 기계적 `#print axioms` 검증을 수행한다."""
    lean_files = sorted(LEAN_DIR.rglob("*.lean"))
    violations: List[str] = []
    file_hashes: Dict[str, str] = {}
    for lf in lean_files:
        rel = str(lf.relative_to(ROOT_DIR)).replace("\\", "/")
        file_hashes[rel] = sha256_file(lf)
        text = lf.read_text(encoding="utf-8")
        no_comments = _strip_lean_comments(text)
        # 커널 모듈과 Main.lean 모두에 대해 모든 금지 우회 키워드 엄격 검사 (lakefile 제외)
        if lf.name != "lakefile.lean":
            if _FORBIDDEN_LEAN_RE.search(no_comments):
                violations.append(rel)
        else:
            if re.search(r"\b(sorry|axiom|admit|native_decide|implemented_by|extern|unsafe)\b", no_comments):
                violations.append(rel)

    freshness_build: Dict[str, Any] = {"checked": False}
    if ensure_fresh_build:
        # 증분 `lake build` + `lake build certmat-check` 실행으로 현재 `.lean` 소스와 `.olean`/바이너리의 100% 일치를 강제 보장
        freshness_build = build_lean_kernel(LEAN_DIR)
        freshness_build["checked"] = True

    axioms_chk = verify_lean_axioms(LEAN_DIR)
    binary = find_lean_checker_binary(LEAN_DIR)
    olean_path = LEAN_DIR / ".lake" / "build" / "lib" / "CertMat.olean"
    return {
        "n_lean_files": len(lean_files),
        "zero_forbidden_keywords_static": (len(violations) == 0),
        "violations": violations,
        "build_freshness": freshness_build,
        "binary_exists": (binary is not None),
        "binary_path": str(binary) if binary else None,
        "binary_sha256": sha256_file(binary) if binary and binary.exists() else None,
        "olean_sha256": sha256_file(olean_path) if olean_path.exists() else None,
        "axioms_check": axioms_chk,
        "file_sha256": file_hashes,
    }


def verify_all_tsv_certificates(allow_build: bool = False) -> Dict[str, Any]:
    """`results/certs_*.tsv` 전체 증명서를 Lean 4 `certmat-check` 바이너리와 독립 Fraction 검증기로 100% 재검증한다."""
    tsv_files = sorted(RESULTS_DIR.glob("certs_*.tsv"))
    present_names = {p.name for p in tsv_files}
    missing_required = sorted(set(REQUIRED_TSV_FILES) - present_names)
    details: Dict[str, Any] = {}
    total_certs = 0
    total_passed = 0
    total_failed = 0
    lean_total = 0
    lean_passed = 0
    lean_failed = 0
    lean_all_ok = (len(missing_required) == 0)
    lean_ran_all = (len(missing_required) == 0)

    for tsv in tsv_files:
        indep = verify_tsv_independent(tsv)
        lean = verify_tsv_with_lean(tsv, allow_build=allow_build)
        total_certs += indep["total"]
        total_passed += indep["passed"]
        total_failed += indep["failed"]
        if lean.get("lean_built"):
            lean_total += int(lean.get("total", 0))
            lean_passed += int(lean.get("passed", 0))
            lean_failed += int(lean.get("failed", 0))
            if not lean.get("all_passed"):
                lean_all_ok = False
        else:
            lean_ran_all = False
            lean_all_ok = False
        details[tsv.name] = {
            "sha256": sha256_file(tsv),
            "bytes": tsv.stat().st_size,
            "independent_check": indep,
            "lean_binary_check": lean,
        }
    return {
        "n_tsv_files": len(tsv_files),
        "missing_required_tsv_files": missing_required,
        "total_certificates": total_certs,
        "total_passed": total_passed,
        "total_failed": total_failed,
        "independent_all_passed": (len(missing_required) == 0 and total_failed == 0 and total_certs > 0),
        "lean_ran_all": lean_ran_all,
        "lean_total_certificates": lean_total,
        "lean_total_passed": lean_passed,
        "lean_total_failed": lean_failed,
        "lean_all_passed": (len(missing_required) == 0 and lean_all_ok and lean_total == total_certs and lean_total > 0),
        "all_passed": (
            len(missing_required) == 0
            and total_failed == 0
            and total_certs > 0
            and lean_all_ok
            and lean_total == total_certs
        ),
        "files": details,
    }


def _sample_tsv_meta_pairs(tsv_path: Path, max_samples: int = 50) -> List[tuple[Dict[str, Any], List[str]]]:
    """TSV 전체 구간(앞·중간·끝)에서 균등 층화 표본으로 `# META <json>` 과 증명서 라인 쌍을 최대 max_samples개 추출한다."""
    all_pairs: List[tuple[Dict[str, Any], List[str]]] = []
    pending_meta: Dict[str, Any] | None = None
    with open(tsv_path, "r", encoding="utf-8") as fp:
        for raw in fp:
            line = raw.strip()
            if not line:
                continue
            if line.startswith("# META "):
                pending_meta = json.loads(line[7:])
                continue
            if line.startswith("#"):
                continue
            if pending_meta is not None:
                all_pairs.append((pending_meta, line.split("\t")))
                pending_meta = None
    n = len(all_pairs)
    if n <= max_samples:
        return all_pairs
    # 앞·중간·끝을 모두 포함하도록 균등 간격 인덱스 추출
    idxs = sorted({int(round(k * (n - 1) / (max_samples - 1))) for k in range(max_samples)})
    return [all_pairs[i] for i in idxs]


def _verify_phase_cert_full_binding(
    meta: Dict[str, Any],
    parts: List[str],
    row_lookup: Dict[str, tuple[Dict[str, Fraction], Fraction]],
    tag: str,
) -> str | None:
    """단일 상평형 구간 증명서의 후보 ex·cx 및 모든 경쟁상 조성 c_mat·에너지 en·가중치 w/wx 전체를 원본 DB와 대조한다."""
    kind = parts[0]
    m = int(parts[1])
    E = int(parts[2])
    elems = meta.get("elements", [])
    comp_ids = meta.get("competing_ids", [])
    mid = meta["material_id"]
    if len(elems) != E or len(comp_ids) != m or mid not in row_lookup:
        return f"{tag}:{mid}:meta_dim_or_missing"

    if kind == "INTERVAL_STABLE":
        off_cx = 7
    elif kind in ("INTERVAL_UNSTABLE", "INTERVAL_FRAGILE_DESTAB", "INTERVAL_FRAGILE_STAB"):
        off_cx = 6
    else:
        return f"{tag}:{mid}:unexpected_kind_{kind}"

    ex_tsv = _parse_strict_q(parts[3])
    wx_tsv = _parse_strict_q(parts[4])
    cx_tsv = [_parse_strict_q(x) for x in parts[off_cx : off_cx + E]]
    off = off_cx + E
    c_flat = [_parse_strict_q(x) for x in parts[off : off + m * E]]
    off += m * E
    en_tsv = [_parse_strict_q(x) for x in parts[off : off + m]]
    off += m
    w_tsv = [_parse_strict_q(x) for x in parts[off : off + m]]

    cand_comp, cand_e = row_lookup[mid]
    if ex_tsv != cand_e:
        return f"{tag}:{mid}:ex_mismatch"
    expected_cx = [cand_comp.get(el, Fraction(0)) for el in elems]
    if cx_tsv != expected_cx:
        return f"{tag}:{mid}:cx_mismatch"
    expected_wx, _ = get_phase_uncertainty(elems, mode="hetero", profile=HETERO_CHEM_PROFILE)
    if wx_tsv != expected_wx:
        return f"{tag}:{mid}:wx_mismatch"

    for i, cid in enumerate(comp_ids):
        row_tsv = c_flat[i * E : (i + 1) * E]
        if cid.startswith("ELEM_REF_"):
            el_ref = cid[len("ELEM_REF_"):]
            exp_comp = {el_ref: Fraction(1, 1)}
            exp_e = Fraction(0, 1)
        else:
            if cid not in row_lookup:
                return f"{tag}:{mid}:missing_comp_{cid}"
            exp_comp, exp_e = row_lookup[cid]
        exp_row = [exp_comp.get(el, Fraction(0)) for el in elems]
        if row_tsv != exp_row:
            return f"{tag}:{mid}:comp_row_mismatch_{cid}"
        if en_tsv[i] != exp_e:
            return f"{tag}:{mid}:comp_en_mismatch_{cid}"
        exp_wi, _ = get_phase_uncertainty(exp_comp.keys(), mode="hetero", profile=HETERO_CHEM_PROFILE)
        if w_tsv[i] != exp_wi:
            return f"{tag}:{mid}:comp_w_mismatch_{cid}"
    # 비공집합 분해 가능성(ValidDecomp non-emptiness) 확인: 후보에 포함된 모든 원소 e에 대해
    # 순수 원소 기저 벡터 e_k 가 경쟁상 행렬 c_mat 에 존재해야 함
    for k in range(E):
        if cx_tsv[k] > 0:
            unit_vec = [Fraction(1) if j == k else Fraction(0) for j in range(E)]
            if not any(c_flat[i * E : (i + 1) * E] == unit_vec for i in range(m)):
                return f"{tag}:{mid}:missing_elem_vertex_{elems[k]}"
    return None


def verify_certificate_dataset_binding() -> Dict[str, Any]:
    """모든 TSV 증명서의 층화 표본에 대해 후보·경쟁상 전체 조성/에너지/가중치 및 탄성 텐서 36개 원소 전체를 원본 공개 DB와 100% 대조한다."""
    checked = 0
    matched = 0
    mismatches: List[str] = []
    per_file_stats: Dict[str, Dict[str, int]] = {}

    # 1) JARVIS (상평형 + 탄성 primary/mandel 36원소 전수)
    jarvis_tsv_phase = RESULTS_DIR / "certs_jarvis_phase_sample.tsv"
    jarvis_tsv_el = RESULTS_DIR / "certs_jarvis_elastic_all.tsv"
    jarvis_tsv_mandel = RESULTS_DIR / "certs_jarvis_elastic_mandel.tsv"
    jarvis_pairs_p = _sample_tsv_meta_pairs(jarvis_tsv_phase, 40) if jarvis_tsv_phase.exists() else []
    jarvis_pairs_e = _sample_tsv_meta_pairs(jarvis_tsv_el, 200) if jarvis_tsv_el.exists() else []
    jarvis_pairs_m = _sample_tsv_meta_pairs(jarvis_tsv_mandel, 100) if jarvis_tsv_mandel.exists() else []

    needed_jids: set[str] = set()
    for m, _ in jarvis_pairs_p:
        needed_jids.add(m["material_id"])
        for cid in m.get("competing_ids", []):
            if not cid.startswith("ELEM_REF_"):
                needed_jids.add(cid)
    for m, _ in jarvis_pairs_e + jarvis_pairs_m:
        needed_jids.add(m["material_id"])

    if needed_jids:
        with open(DATA_DIR / "jdft_3d.json", "r", encoding="utf-8") as f:
            jraw = {d["jid"]: d for d in json.load(f) if d.get("jid") in needed_jids}
        j_phase_lookup = {
            jid: (formula_to_atom_fractions(d["formula"]), to_fraction(d["formation_energy_peratom"]))
            for jid, d in jraw.items()
            if d.get("formula") and d.get("formation_energy_peratom") not in (None, "na")
        }
        p_ok = 0
        for meta, parts in jarvis_pairs_p:
            checked += 1
            err = _verify_phase_cert_full_binding(meta, parts, j_phase_lookup, "jarvis_phase")
            if err:
                mismatches.append(err)
            else:
                matched += 1
                p_ok += 1
        per_file_stats["certs_jarvis_phase_sample.tsv"] = {"checked": len(jarvis_pairs_p), "matched": p_ok}

        for fname, epairs in (
            ("certs_jarvis_elastic_all.tsv", jarvis_pairs_e),
            ("certs_jarvis_elastic_mandel.tsv", jarvis_pairs_m),
        ):
            e_ok = 0
            for meta, parts in epairs:
                checked += 1
                jid = meta["material_id"]
                d = jraw.get(jid)
                if d is None or not d.get("elastic_tensor"):
                    mismatches.append(f"{fname}:{jid}:missing")
                    continue
                et = d["elastic_tensor"]
                C_raw = [[to_fraction(et[i][j]) for j in range(6)] for i in range(6)]
                C_sym_flat = [(C_raw[i][j] + C_raw[j][i]) / 2 for i in range(6) for j in range(6)]
                kind = parts[0]
                if kind in ("BORN_LDLT", "BORN_NON_PD", "MANDEL_WEYL_FRAGILE"):
                    off = 2
                elif kind == "WEYL_ROBUST":
                    off = 4
                elif kind in ("WEYL_FRAGILE", "MANDEL_WEYL_ROBUST"):
                    off = 3
                else:
                    mismatches.append(f"{fname}:{jid}:unknown_kind_{kind}")
                    continue
                tsv_C = [_parse_strict_q(x) for x in parts[off : off + 36]]
                if tsv_C != C_sym_flat:
                    mismatches.append(f"{fname}:{jid}:C_36_mismatch")
                else:
                    matched += 1
                    e_ok += 1
            per_file_stats[fname] = {"checked": len(epairs), "matched": e_ok}

    # 2) WBM (후보 + 경쟁상 전체)
    wbm_tsv = RESULTS_DIR / "certs_wbm_phase_sample.tsv"
    wbm_pairs = _sample_tsv_meta_pairs(wbm_tsv, 40) if wbm_tsv.exists() else []
    needed_wbm: set[str] = set()
    for m, _ in wbm_pairs:
        needed_wbm.add(m["material_id"])
        for cid in m.get("competing_ids", []):
            if not cid.startswith("ELEM_REF_"):
                needed_wbm.add(cid)
    if needed_wbm:
        wmap: Dict[str, tuple[Dict[str, Fraction], Fraction]] = {}
        with gzip.open(DATA_DIR / "wbm_summary.csv.gz", "rt", encoding="utf-8") as f:
            for r in csv.DictReader(f):
                if r["material_id"] in needed_wbm:
                    wmap[r["material_id"]] = (
                        formula_to_atom_fractions(r["formula"]),
                        to_fraction(r["e_form_per_atom_mp2020_corrected"]),
                    )
        w_ok = 0
        for meta, parts in wbm_pairs:
            checked += 1
            err = _verify_phase_cert_full_binding(meta, parts, wmap, "wbm")
            if err:
                mismatches.append(err)
            else:
                matched += 1
                w_ok += 1
        per_file_stats["certs_wbm_phase_sample.tsv"] = {"checked": len(wbm_pairs), "matched": w_ok}

    # 3) GNoME PBE, r2SCAN, Matched PBE, Matched r2SCAN (후보 + 경쟁상 전체)
    for fname, csv_name in (
        ("certs_gnome_pbe_sample.tsv", "gnome_stable_materials_summary.csv"),
        ("certs_gnome_matched_sample.tsv", "gnome_stable_materials_summary.csv"),
        ("certs_gnome_r2scan_sample.tsv", "gnome_stable_materials_r2scan.csv"),
        ("certs_gnome_matched_r2scan_sample.tsv", "gnome_stable_materials_r2scan.csv"),
    ):
        tsv_g = RESULTS_DIR / fname
        gpairs = _sample_tsv_meta_pairs(tsv_g, 40) if tsv_g.exists() else []
        needed_g: set[str] = set()
        for m, _ in gpairs:
            needed_g.add(m["material_id"])
            for cid in m.get("competing_ids", []):
                if not cid.startswith("ELEM_REF_"):
                    needed_g.add(cid)
        if needed_g:
            gmap: Dict[str, tuple[Dict[str, Fraction], Fraction]] = {}
            with open(DATA_DIR / csv_name, "r", encoding="utf-8") as f:
                for r in csv.DictReader(f):
                    if r["MaterialId"] in needed_g:
                        gmap[r["MaterialId"]] = (
                            formula_to_atom_fractions(r["Composition"]),
                            to_fraction(r["Formation Energy Per Atom"]),
                        )
            g_ok = 0
            for meta, parts in gpairs:
                checked += 1
                err = _verify_phase_cert_full_binding(meta, parts, gmap, fname)
                if err:
                    mismatches.append(err)
                else:
                    matched += 1
                    g_ok += 1
            per_file_stats[fname] = {"checked": len(gpairs), "matched": g_ok}

    return {
        "checked": checked,
        "matched": matched,
        "mismatches": mismatches,
        "per_file": per_file_stats,
        "scope": "stratified_full_vector_and_36_entry_matrix_binding",
        "all_ok": (checked > 0 and len(mismatches) == 0),
    }


def run_pytest_suite() -> Dict[str, Any]:
    """pytest 전체 단위 테스트를 실행한다."""
    res = subprocess.run(
        [sys.executable, "-m", "pytest", "-v"],
        cwd=str(ROOT_DIR),
        capture_output=True,
        text=True,
        timeout=240,
    )
    return {
        "returncode": res.returncode,
        "all_passed": (res.returncode == 0),
        "stdout": res.stdout.strip(),
        "stderr": res.stderr.strip(),
    }


def write_lean_verification_report(
    lean_chk: Dict[str, Any], cert_chk: Dict[str, Any], bind_chk: Dict[str, Any]
) -> Dict[str, Any]:
    """기계 검증된 Lean 4 공리 감사, `certmat-check` TSV 검증, 데이터 바인딩 결과를 JSON 보고서로 저장한다."""
    report = {
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "lean_toolchain": (LEAN_DIR / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_kernel_check": lean_chk,
        "tsv_certificate_verification": {
            "n_tsv_files": cert_chk["n_tsv_files"],
            "lean_total_certificates": cert_chk["lean_total_certificates"],
            "lean_total_passed": cert_chk["lean_total_passed"],
            "lean_total_failed": cert_chk["lean_total_failed"],
            "lean_all_passed": cert_chk["lean_all_passed"],
            "independent_all_passed": cert_chk["independent_all_passed"],
            "per_file": {
                fname: {
                    "sha256": meta["sha256"],
                    "lean_total": meta["lean_binary_check"].get("total"),
                    "lean_passed": meta["lean_binary_check"].get("passed"),
                    "lean_failed": meta["lean_binary_check"].get("failed"),
                    "lean_all_passed": meta["lean_binary_check"].get("all_passed"),
                    "independent_by_kind": meta["independent_check"].get("by_kind"),
                }
                for fname, meta in cert_chk["files"].items()
            },
        },
        "dataset_binding_spot_audit": bind_chk,
    }
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    with open(LEAN_REPORT_PATH, "w", encoding="utf-8") as f:
        json.dump(report, f, indent=2, ensure_ascii=False)
    return report


def _expected_manifest_targets() -> List[Path]:
    """SHA-256 매니페스트에 잠글 전체 필수 산출물·소스·빌드 바이너리 목록을 결정론적으로 반환한다.

    필수 요약 JSON·증명서 TSV·논문·Lean 툴체인/바이너리를 명시적으로 포함하므로,
    디스크와 매니페스트 양쪽에서 파일을 동시에 삭제해도 누락이 즉시 탐지된다(fail-closed).
    """
    seen: set[Path] = set()
    targets: List[Path] = []

    def _add(p: Path) -> None:
        if p not in seen:
            seen.add(p)
            targets.append(p)

    for fname in REQUIRED_SUMMARY_FILES:
        _add(RESULTS_DIR / fname)
    for p in sorted(RESULTS_DIR.glob("*_summary.json")):
        _add(p)
    for fname in REQUIRED_TSV_FILES:
        _add(RESULTS_DIR / fname)
    for p in sorted(RESULTS_DIR.glob("certs_*.tsv")):
        _add(p)
    for p in sorted(LEAN_DIR.rglob("*.lean")):
        _add(p)
    _add(LEAN_DIR / "lean-toolchain")
    for p in sorted((LEAN_DIR / ".lake" / "build" / "lib").rglob("*.olean")):
        _add(p)
    bin_found = False
    for bin_cand in (
        LEAN_DIR / ".lake" / "build" / "bin" / "certmat-check.exe",
        LEAN_DIR / ".lake" / "build" / "bin" / "certmat-check",
    ):
        if bin_cand.exists():
            _add(bin_cand)
            bin_found = True
    if not bin_found:
        _add(LEAN_DIR / ".lake" / "build" / "bin" / ("certmat-check.exe" if sys.platform == "win32" else "certmat-check"))
    for p in sorted((ROOT_DIR / "certmat").glob("*.py")):
        _add(p)
    for p in sorted((ROOT_DIR / "scripts").glob("*.py")):
        _add(p)
    for p in sorted((ROOT_DIR / "tests").glob("*.py")):
        _add(p)
    _add(ROOT_DIR / "reproduce_all.py")
    for fname in REQUIRED_PAPER_FILES:
        _add(PAPER_DIR / fname)
    if PAPER_DIR.exists():
        for p in sorted(PAPER_DIR.glob("*.md")):
            _add(p)
    return targets


def build_artifact_manifest() -> Dict[str, Any]:
    """모든 결과 JSON, 증명서 TSV, Lean 소스/툴체인/전체 `.olean`/바이너리, Python 소스, 논문 문서의 SHA-256 매니페스트를 생성한다."""
    targets = _expected_manifest_targets()

    files_map: Dict[str, Dict[str, Any]] = {}
    for p in targets:
        rel = str(p.relative_to(ROOT_DIR)).replace("\\", "/")
        files_map[rel] = {
            "bytes": p.stat().st_size,
            "sha256": sha256_file(p),
        }

    manifest = {
        "generated_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "n_files": len(files_map),
        "files": files_map,
    }
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    with open(MANIFEST_PATH, "w", encoding="utf-8") as f:
        json.dump(manifest, f, indent=2, ensure_ascii=False)
    return manifest


def verify_artifact_manifest() -> Dict[str, Any]:
    """기존 `reproduction_manifest.json`의 완전성(`n_files`·예상 대상 집합 일치) 및 모든 파일의 SHA-256 일치를 검증한다."""
    if not MANIFEST_PATH.exists():
        return {"exists": False, "all_ok": False, "checked": 0, "mismatches": ["manifest_missing"]}
    with open(MANIFEST_PATH, "r", encoding="utf-8") as f:
        manifest = json.load(f)
    mismatches: List[str] = []
    files_dict = manifest.get("files", {})
    if manifest.get("n_files") != len(files_dict):
        mismatches.append(f"N_FILES_MISMATCH:declared={manifest.get('n_files')},actual={len(files_dict)}")
    expected_rels = {str(p.relative_to(ROOT_DIR)).replace("\\", "/") for p in _expected_manifest_targets()}
    missing_from_manifest = sorted(expected_rels - set(files_dict.keys()))
    for rel in missing_from_manifest:
        mismatches.append(f"UNTRACKED_IN_MANIFEST:{rel}")
    checked = 0
    for rel, meta in files_dict.items():
        p = ROOT_DIR / rel
        checked += 1
        if not p.exists():
            mismatches.append(f"MISSING:{rel}")
            continue
        if sha256_file(p) != meta["sha256"]:
            mismatches.append(f"SHA256_MISMATCH:{rel}")
    return {
        "exists": True,
        "checked": checked,
        "mismatches": mismatches,
        "all_ok": (len(mismatches) == 0 and checked > 0),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="CertMat 원클릭 재현 및 SHA-256 무결성 검증")
    parser.add_argument("--full", action="store_true", help="Lean 빌드 + 전체 5단계 감사 + 보완분석을 처음부터 재실행")
    parser.add_argument("--verify-only", action="store_true", help="재계산 없이 전체 SHA-256·Lean·증명서·바인딩·테스트 검증")
    parser.add_argument("--write-manifest", action="store_true", help="Lean 검증 보고서 및 산출물 SHA-256 매니페스트 생성/갱신")
    parser.add_argument("--workers", type=int, default=2, help="병렬 워커 수 (안전 기본값: 2; 원격 보조 PC 등에서는 명시 상향 가능)")
    args = parser.parse_args()

    t0 = time.time()
    print("=== [1/6] 원본 공개 데이터셋 SHA-256 무결성 검증 ===")
    ds_chk = check_dataset_integrity()
    for k, v in ds_chk["datasets"].items():
        status = "OK" if v.get("sha256_match") else "FAIL"
        print(f"  - {k}: {v.get('file')} [{status}] sha256={str(v.get('actual_sha256',''))[:16]}...")
    if not ds_chk["all_ok"]:
        sys.exit("데이터셋 SHA-256 검증 실패!")

    if args.full:
        print("\n=== [2/6] Lean 4 커널 빌드 + 전체 5단계 공개 DB 감사 + 보완분석 재실행 ===")
        bld = build_lean_kernel(LEAN_DIR)
        if not bld.get("built"):
            sys.exit(f"Lean 4 커널 빌드 실패: {bld}")
        print(f"  Lean 4 빌드 완료: {bld['binary']}")
        rc1 = subprocess.run(
            [sys.executable, "-u", str(ROOT_DIR / "scripts" / "run_full_audit.py"), "--workers", str(args.workers)],
            cwd=str(ROOT_DIR),
        ).returncode
        if rc1 != 0:
            sys.exit(f"전수 감사 실행 실패 (returncode={rc1})")
        rc2 = subprocess.run(
            [
                sys.executable,
                "-u",
                str(ROOT_DIR / "scripts" / "run_supplementary_analysis.py"),
                "--workers",
                str(args.workers),
            ],
            cwd=str(ROOT_DIR),
        ).returncode
        if rc2 != 0:
            sys.exit(f"보완 분석 실행 실패 (returncode={rc2})")
    else:
        print("\n=== [2/6] 저장된 결과/산출물 검증 모드 ===")

    print("\n=== [3/6] Lean 4 커널 정적 검사 및 기계적 #print axioms 검증 ===")
    lean_chk = check_lean_static_and_axioms()
    ax = lean_chk["axioms_check"]
    print(
        f"  Lean 파일={lean_chk['n_lean_files']}, 금지키워드 0건={lean_chk['zero_forbidden_keywords_static']}, "
        f"바이너리={lean_chk['binary_exists']}, "
        f"#print axioms={ax.get('n_theorems_checked', 0)}/{ax.get('n_theorems_expected', 0)} "
        f"(standard_only={ax.get('all_standard_axioms_only')}, zero_sorryAx={ax.get('zero_sorry_ax')})"
    )
    if not lean_chk["zero_forbidden_keywords_static"]:
        sys.exit(f"Lean 커널 금지 키워드 발견: {lean_chk['violations']}")
    if lean_chk["build_freshness"].get("checked") and not lean_chk["build_freshness"].get("built"):
        sys.exit(f"Lean 4 소스-바이너리 최신성 빌드 실패: {lean_chk['build_freshness']}")
    if not ax.get("all_standard_axioms_only"):
        sys.exit(f"Lean 4 #print axioms 기계 검증 실패: {ax}")

    print("\n=== [4/6] 전체 TSV 정확 유리수 증명서 Lean 4 바이너리 + 독립 Fraction 100% 재검증 ===")
    cert_chk = verify_all_tsv_certificates(allow_build=args.full)
    print(
        f"  TSV 파일={cert_chk['n_tsv_files']}개 | "
        f"Lean 4 certmat-check: {cert_chk['lean_total_passed']:,}/{cert_chk['lean_total_certificates']:,} "
        f"(실패={cert_chk['lean_total_failed']}) | "
        f"독립 Fraction 검증기: {cert_chk['total_passed']:,}/{cert_chk['total_certificates']:,} "
        f"(실패={cert_chk['total_failed']})"
    )
    if not cert_chk["all_passed"]:
        sys.exit("TSV 증명서 Lean 4 또는 독립 검증 실패!")

    print("\n=== [5/6] 증명서 `# META` ↔ 원본 공개 데이터셋 바인딩 일치성 감사 ===")
    bind_chk = verify_certificate_dataset_binding()
    print(f"  바인딩 표본 검증: {bind_chk['matched']}/{bind_chk['checked']} 일치 (불일치={len(bind_chk['mismatches'])})")
    if not bind_chk["all_ok"]:
        sys.exit(f"증명서 데이터셋 바인딩 불일치: {bind_chk['mismatches']}")

    if args.full or args.write_manifest:
        write_lean_verification_report(lean_chk, cert_chk, bind_chk)
        mf = build_artifact_manifest()
        print(f"  [매니페스트 갱신] {mf['n_files']}개 파일 SHA-256 잠금 -> {MANIFEST_PATH}")

    print("\n=== [6/6] pytest 전체 단위 테스트 및 매니페스트 최종 검증 ===")
    pt = run_pytest_suite()
    print(pt["stdout"])
    if not pt["all_passed"]:
        sys.exit("pytest 단위 테스트 실패!")

    # 검증 모드(기본 실행 포함) 및 매니페스트 갱신 후에는 항상 fail-closed 매니페스트 검증을 강제한다.
    mf_chk = verify_artifact_manifest()
    print(f"  매니페스트 SHA-256 검증: {mf_chk['checked']}개 파일, 불일치={len(mf_chk['mismatches'])}")
    if not mf_chk["all_ok"]:
        sys.exit(f"매니페스트 SHA-256 불일치: {mf_chk['mismatches']}")

    print(f"\n[CertMat ALL CHECKS PASSED] 총 소요 {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
