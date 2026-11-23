"""
CertMat 대규모 공개 재료 DB 전수 감사 파이프라인.

대상 데이터셋:
  1. jarvis_elastic: NIST JARVIS-DFT 3D 34,323개 6x6 탄성 텐서 전수 감사
     (Voigt/Mandel Weyl 강건성, 구성적 WEYL_FRAGILE 반례, VASP/축치환 대칭성 감사)
  2. jarvis_phase:   NIST JARVIS-DFT 3D 93,902개 상평형 전수 감사 + 공개 ehull 음성대조군 포렌식
     + 정리 2 원소 기준 일관성 포렌식 감사
  3. wbm_phase:      Matbench Discovery WBM 256,963개 상평형 전수 감사 + 동질이상 vs 교차조성 분해
     + MP2020 보정 정리 2 직교 분해
  4. gnome_crossval: DeepMind GNoME PBE-r2SCAN 117,043개 매칭 결정 1:1 동등 비교(Exact LP + Lean 증명서)
     + 2x2 단조성 검증 + 외부 프록시 점수(Proxy) 분리 평가 + 부트스트랩 95% 신뢰구간
  5. gnome_full:     DeepMind GNoME PBE 554,054개 + r2SCAN 139,541개 전수 상평형 감사 + 2x2 단조성 검증

Windows 비파괴적 절전 방지(SetThreadExecutionState) 및 다중 프로세스 병렬 처리를 기본 적용한다.
"""

from __future__ import annotations

import argparse
import csv
import ctypes
import gzip
import json
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np

# 프로젝트 루트를 import 경로에 추가
ROOT_DIR = Path(__file__).resolve().parent.parent
if str(ROOT_DIR) not in sys.path:
    sys.path.insert(0, str(ROOT_DIR))

from certmat.datasets import DATA_DIR, sha256_file
from certmat.elastic_audit import audit_elastic_tensor
from certmat.exact_lp import to_fraction
from certmat.lean_bridge import (
    verify_tsv_independent,
    verify_tsv_with_lean,
    write_certificates_tsv,
)
from certmat.phase_audit import (
    PhaseDiagramIndex,
    PhaseEntry,
    audit_single_phase,
    formula_to_atom_fractions,
    parse_formula_counts,
)
from certmat.uncertainty import (
    HETERO_CHEM_PROFILE,
    classify_chemistry,
    decompose_reference_and_residual_errors,
)

RESULTS_DIR = ROOT_DIR / "results"


# ---------------------------------------------------------------------------
# Windows 비파괴적 절전 방지 래퍼 (비-Windows 환경에서는 안전 무동작)
# ---------------------------------------------------------------------------
def _set_keep_awake(enable: bool) -> None:
    """작업 수명 동안만 Windows 시스템 절전을 방지하고 종료 시 원복한다."""
    if os.name != "nt":
        return
    try:
        flag = 0x80000001 if enable else 0x80000000
        ctypes.windll.kernel32.SetThreadExecutionState(flag)
    except Exception:
        pass


def _set_below_normal_priority() -> None:
    """Windows 환경에서 프로세스 우선순위를 BelowNormal로 낮춰 메인 PC 응답성을 보호한다."""
    if os.name != "nt":
        return
    try:
        handle = ctypes.windll.kernel32.GetCurrentProcess()
        ctypes.windll.kernel32.SetPriorityClass(handle, 0x00004000)
    except Exception:
        pass


# ---------------------------------------------------------------------------
# 다중 프로세스 워커 전역 상태 (Windows spawn 최적화)
# ---------------------------------------------------------------------------
_WORKER_INDEX: Optional[PhaseDiagramIndex] = None
_WORKER_CUSTOM_SIGMA: Optional[Dict[str, Fraction]] = None


def _init_phase_worker(
    pruned_by_elem_set: Dict[frozenset, List[PhaseEntry]],
    custom_sigma: Optional[Dict[str, Fraction]] = None,
) -> None:
    """워커 프로세스마다 경량 가지치기 인덱스만 1회 로드한다."""
    global _WORKER_INDEX, _WORKER_CUSTOM_SIGMA
    _set_below_normal_priority()
    idx = PhaseDiagramIndex.__new__(PhaseDiagramIndex)
    idx.phases = []
    idx.by_elem_set = pruned_by_elem_set
    idx.all_elements = set()
    idx._pruned_by_elem_set = pruned_by_elem_set
    idx.prune_polymorphs = True
    idx.injected_elemental_refs = []
    idx.negative_elemental_phases = []
    _WORKER_INDEX = idx
    _WORKER_CUSTOM_SIGMA = custom_sigma


def _phase_worker_chunk(
    args: Tuple[List[PhaseEntry], set[str]]
) -> List[Tuple[Dict[str, Any], Optional[Dict[str, Any]]]]:
    """후보상 청크에 대해 정확한 유리수 상평형 감사를 수행한다."""
    chunk, cert_ids = args
    assert _WORKER_INDEX is not None
    out: List[Tuple[Dict[str, Any], Optional[Dict[str, Any]]]] = []
    for p in chunk:
        emit = p.material_id in cert_ids
        rec = audit_single_phase(
            p,
            _WORKER_INDEX.get_competing_phases(p),
            custom_class_sigma=_WORKER_CUSTOM_SIGMA,
            use_z3_fallback=True,
            emit_certificate=emit,
        )
        cert = rec.certificate_payload
        summary_row = {
            "id": rec.material_id,
            "formula": rec.formula,
            "chem_class": rec.chem_class,
            "n_elem": rec.n_elements,
            "n_comp": rec.n_competing,
            "margin_mev": rec.nominal_margin_mev,
            "ehull_mev": rec.nominal_ehull_mev,
            "nom_stable": rec.is_nominally_stable,
            "eps_unif_mev": rec.eps_uniform_mev,
            "s10": rec.status_10mev,
            "s25": rec.status_25mev,
            "s50": rec.status_50mev,
            "sigma_x_mev": rec.hetero_sigma_x_mev,
            "h_scale": rec.hetero_critical_scale,
            "s_het": rec.status_hetero,
            "sw": rec.phase_switching,
            "naive_scale": rec.naive_nominal_scale,
            "sw_over_pct": rec.switching_overestimation_pct,
            "crit_flip": rec.critical_robust_to_fragile_flip,
            "same_poly": rec.same_comp_polymorph_decomp,
            "uncompeted": rec.is_uncompeted,
            "exact_bdry": rec.is_exact_boundary,
            "near0_1mev": rec.near_zero_margin_1mev,
            "solver": rec.solver_used,
            "ok": rec.exact_verified,
            "nom_decomp": rec.nominal_decomp_ids if rec.phase_switching else [],
            "adv_decomp": rec.adversarial_decomp_ids if rec.phase_switching else [],
        }
        out.append((summary_row, cert))
    return out


def _elastic_worker_chunk(
    chunk: List[Tuple[str, str, List[List[float]], Optional[int]]]
) -> List[
    Tuple[
        Dict[str, Any],
        Optional[Dict[str, Any]],
        Optional[Dict[str, Any]],
        Optional[Dict[str, Any]],
        Optional[Dict[str, Any]],
    ]
]:
    """6x6 탄성 텐서 청크를 병렬 감사한다 (JARVIS-DFT 3D는 VASP OUTCAR 전단 순서 XY,YZ,ZX 사용)."""
    _set_below_normal_priority()
    out = []
    for jid, formula, tensor, spg in chunk:
        rec = audit_elastic_tensor(
            jid, formula, tensor, spg_number=spg, emit_certificate=True, convention="vasp"
        )
        row = {
            "jid": rec.jid,
            "formula": rec.formula,
            "spg": rec.spg_number,
            "csys": rec.crystal_system,
            "pd": rec.born_pd_exact,
            "lmin_v": rec.lambda_min_voigt_gpa,
            "lmin_m": rec.lambda_min_mandel_gpa,
            "r1": rec.robust_1gpa,
            "r5": rec.robust_5gpa,
            "r10": rec.robust_10gpa,
            "mr1": rec.mandel_robust_1gpa,
            "mr5": rec.mandel_robust_5gpa,
            "mr10": rec.mandel_robust_10gpa,
            "asym": rec.max_asymmetry_gpa,
            "zviol": rec.max_zero_violation_gpa,
            "eviol": rec.max_eq_violation_gpa,
            "vviol": rec.max_voigt_violation_gpa,
            "vviol_std": rec.max_voigt_violation_fixed_std_gpa,
            "setting": rec.matched_setting,
            "crot": rec.cubic_mandel_rot_inv_viol_gpa,
            "ok": rec.exact_verified,
        }
        out.append((
            row,
            rec.certificate_payload,
            rec.fragility_certificate_payload,
            rec.mandel_certificate_payload,
            rec.mandel_fragility_certificate_payload,
        ))
    return out


def _run_parallel_phase_audit(
    phases: Sequence[PhaseEntry],
    label: str,
    workers: int,
    cert_sample_n: int = 5000,
    add_elemental_refs: bool = True,
    custom_sigma: Optional[Dict[str, Fraction]] = None,
    chunk_size: int = 500,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], float, Dict[str, Any]]:
    """대규모 PhaseEntry 목록을 병렬 감사하고 결과 요약행·증명서·인덱스 메타데이터를 반환한다."""
    t0 = time.time()
    idx = PhaseDiagramIndex(phases, add_elemental_refs=add_elemental_refs)
    t_idx = time.time() - t0
    index_meta = {
        "n_elements": len(idx.all_elements),
        "n_injected_zero_elemental_refs": len(idx.injected_elemental_refs),
        "injected_elemental_refs_sample": idx.injected_elemental_refs[:20],
        "n_negative_elemental_phases": len(idx.negative_elemental_phases),
        "negative_elemental_phases_sample": idx.negative_elemental_phases[:10],
    }
    print(
        f"[{label}] 인덱스 구축 완료: {len(phases):,}상 ({t_idx:.2f}s), "
        f"보충 원소참조={len(idx.injected_elemental_refs)}, 워커={workers}"
    )

    n = len(phases)
    if cert_sample_n <= 0:
        cert_ids = set()
    elif cert_sample_n >= n:
        cert_ids = {p.material_id for p in phases}
    else:
        step = max(1, n // cert_sample_n)
        cert_ids = {phases[i].material_id for i in range(0, n, step)[:cert_sample_n]}

    chunks = [
        (list(phases[i : i + chunk_size]), cert_ids)
        for i in range(0, n, chunk_size)
    ]

    rows: List[Dict[str, Any]] = []
    certs: List[Dict[str, Any]] = []
    done = 0
    t_run = time.time()
    with ProcessPoolExecutor(
        max_workers=workers,
        initializer=_init_phase_worker,
        initargs=(idx._pruned_by_elem_set, custom_sigma),
    ) as ex:
        for chunk_res in ex.map(_phase_worker_chunk, chunks):
            for row, cert in chunk_res:
                rows.append(row)
                if cert is not None:
                    certs.append(cert)
            done += len(chunk_res)
            if done % 25000 < chunk_size or done == n:
                elapsed = time.time() - t_run
                rate = done / max(elapsed, 1e-6)
                print(
                    f"  [{label}] {done:,}/{n:,} ({100.0 * done / n:.1f}%) "
                    f"| {rate:.0f} mat/s | 경과 {elapsed:.1f}s",
                    flush=True,
                )

    total_sec = time.time() - t0
    return rows, certs, total_sec, index_meta


def _summarize_phase_rows(
    rows: Sequence[Dict[str, Any]],
    dataset_name: str,
    elapsed_sec: float,
    index_meta: Optional[Dict[str, Any]] = None,
    n_dropped_parse: int = 0,
) -> Dict[str, Any]:
    """상평형 감사 행 목록에서 논문 표·통계용 정확 집계를 산출한다."""
    n = len(rows)
    uncompeted = [r for r in rows if r["uncompeted"]]
    competed = [r for r in rows if not r["uncompeted"]]
    nom_stable = [r for r in competed if r["nom_stable"]]
    nom_unstable = [r for r in competed if not r["nom_stable"]]

    def _count_status(sub: Sequence[Dict[str, Any]], key: str) -> Dict[str, int]:
        c: Dict[str, int] = {}
        for r in sub:
            v = r[key]
            c[v] = c.get(v, 0) + 1
        return c

    sw_stable = [r for r in nom_stable if r["sw"]]
    sw_unstable = [r for r in nom_unstable if r["sw"]]
    sw_stable_over = [r["sw_over_pct"] for r in sw_stable if math.isfinite(r["sw_over_pct"]) and r["sw_over_pct"] > 0]
    sw_critical_flip = [r for r in sw_stable if r["crit_flip"]]

    by_chem: Dict[str, Dict[str, Any]] = {}
    chem_groups: Dict[str, List[Dict[str, Any]]] = {}
    for r in competed:
        chem_groups.setdefault(r["chem_class"], []).append(r)
    for cls, grp in sorted(chem_groups.items()):
        g_stab = [r for r in grp if r["nom_stable"]]
        g_frag25 = sum(1 for r in g_stab if r["s25"] == "Fragile")
        g_frag_het = sum(1 for r in g_stab if r["s_het"] == "Fragile")
        g_sw = sum(1 for r in g_stab if r["sw"])
        by_chem[cls] = {
            "total": len(grp),
            "nom_stable": len(g_stab),
            "nom_stable_fragile_25mev": g_frag25,
            "nom_stable_fragile_25mev_pct": (100.0 * g_frag25 / len(g_stab)) if g_stab else 0.0,
            "nom_stable_fragile_hetero": g_frag_het,
            "nom_stable_fragile_hetero_pct": (100.0 * g_frag_het / len(g_stab)) if g_stab else 0.0,
            "nom_stable_phase_switching": g_sw,
        }

    top_sw = sorted(
        [r for r in sw_stable if math.isfinite(r["sw_over_pct"])],
        key=lambda r: r["sw_over_pct"],
        reverse=True,
    )[:15]
    top_sw_clean = [
        {
            "id": r["id"],
            "formula": r["formula"],
            "chem_class": r["chem_class"],
            "nominal_margin_mev": round(r["margin_mev"], 3),
            "naive_scale": round(r["naive_scale"], 4) if math.isfinite(r["naive_scale"]) else None,
            "true_critical_scale": round(r["h_scale"], 4) if math.isfinite(r["h_scale"]) else None,
            "overestimation_pct": round(r["sw_over_pct"], 2),
            "critical_robust_to_fragile_flip": bool(r["crit_flip"]),
            "nom_decomp": r["nom_decomp"],
            "adv_decomp": r["adv_decomp"],
        }
        for r in top_sw
    ]

    eps_stab = np.array([r["eps_unif_mev"] for r in nom_stable], dtype=np.float64) if nom_stable else np.array([0.0])
    z3_calls = sum(1 for r in competed if "z3" in r["solver"])
    verified_ok = sum(1 for r in competed if r["ok"])
    n_competed = len(competed)

    # 경계 민감도(±1 meV) 및 동질이상 분해 통계
    n_exact_bdry = sum(1 for r in competed if r["exact_bdry"])
    n_near0_1mev = sum(1 for r in competed if r["near0_1mev"])
    n_unstab_same_poly = sum(1 for r in nom_unstable if r["same_poly"])

    return {
        "dataset": dataset_name,
        "elapsed_sec": round(elapsed_sec, 2),
        "n_total": n,
        "n_dropped_parse": n_dropped_parse,
        "n_competed_audited": n_competed,
        "n_uncompeted_elemental": len(uncompeted),
        "n_exact_verified": verified_ok,
        "exact_verified_pct_of_competed": (100.0 * verified_ok / n_competed) if n_competed else 0.0,
        "n_z3_fallback": z3_calls,
        "z3_fallback_pct": (100.0 * z3_calls / n_competed) if n_competed else 0.0,
        "n_nom_stable": len(nom_stable),
        "n_nom_unstable": len(nom_unstable),
        "n_exact_zero_margin_boundary": n_exact_bdry,
        "n_near_zero_margin_lt_1mev": n_near0_1mev,
        "nom_unstable_same_composition_polymorph": n_unstab_same_poly,
        "nom_unstable_cross_composition_decomp": len(nom_unstable) - n_unstab_same_poly,
        "index_metadata": index_meta or {},
        "all_status_10mev": _count_status(competed, "s10"),
        "all_status_25mev": _count_status(competed, "s25"),
        "all_status_50mev": _count_status(competed, "s50"),
        "all_status_hetero": _count_status(competed, "s_het"),
        "nom_stable_status_10mev": _count_status(nom_stable, "s10"),
        "nom_stable_status_25mev": _count_status(nom_stable, "s25"),
        "nom_stable_status_50mev": _count_status(nom_stable, "s50"),
        "nom_stable_status_hetero": _count_status(nom_stable, "s_het"),
        "nom_stable_eps_unif_mev_quantiles": {
            "p10": float(np.percentile(eps_stab, 10)),
            "p25": float(np.percentile(eps_stab, 25)),
            "p50": float(np.percentile(eps_stab, 50)),
            "p75": float(np.percentile(eps_stab, 75)),
            "p90": float(np.percentile(eps_stab, 90)),
        },
        "phase_switching": {
            "nom_stable_count": len(sw_stable),
            "nom_stable_pct": (100.0 * len(sw_stable) / len(nom_stable)) if nom_stable else 0.0,
            "nom_stable_critical_robust_to_fragile_flips": len(sw_critical_flip),
            "nom_stable_overest_median_pct": float(np.median(sw_stable_over)) if sw_stable_over else 0.0,
            "nom_stable_overest_p90_pct": float(np.percentile(sw_stable_over, 90)) if sw_stable_over else 0.0,
            "nom_stable_overest_max_pct": float(np.max(sw_stable_over)) if sw_stable_over else 0.0,
            "nom_unstable_count": len(sw_unstable),
            "nom_unstable_pct": (100.0 * len(sw_unstable) / len(nom_unstable)) if nom_unstable else 0.0,
            "top_stable_examples": top_sw_clean,
        },
        "by_chemistry_class": by_chem,
    }


def _compute_roc_auc(labels: np.ndarray, scores: np.ndarray) -> float:
    """외부 의존성 없이 Mann-Whitney U 통계량으로 정확한 ROC-AUC를 계산한다."""
    labels = np.asarray(labels, dtype=np.int64)
    scores = np.asarray(scores, dtype=np.float64)
    pos = labels == 1
    neg = labels == 0
    n_pos = int(pos.sum())
    n_neg = int(neg.sum())
    if n_pos == 0 or n_neg == 0:
        return float("nan")
    order = np.argsort(scores, kind="mergesort")
    ranks = np.empty(len(scores), dtype=np.float64)
    s_sorted = scores[order]
    i = 0
    n = len(scores)
    while i < n:
        j = i + 1
        while j < n and s_sorted[j] == s_sorted[i]:
            j += 1
        ranks[order[i:j]] = 0.5 * (i + 1 + j)
        i = j
    u = ranks[pos].sum() - n_pos * (n_pos + 1) / 2.0
    return float(u / (n_pos * n_neg))


def _bootstrap_auc_ci(
    labels: np.ndarray, scores: np.ndarray, n_boot: int = 300, seed: int = 2026
) -> Dict[str, float]:
    """층화 없는 표준 부트스트랩으로 ROC-AUC 점추정과 95% 신뢰구간을 계산한다."""
    auc = _compute_roc_auc(labels, scores)
    rng = np.random.default_rng(seed)
    n = len(labels)
    vals = []
    for _ in range(n_boot):
        idx = rng.integers(0, n, size=n)
        a = _compute_roc_auc(labels[idx], scores[idx])
        if math.isfinite(a):
            vals.append(a)
    if not vals:
        return {"auc": round(auc, 4), "ci95_low": float("nan"), "ci95_high": float("nan")}
    arr = np.asarray(vals, dtype=np.float64)
    return {
        "auc": round(auc, 4),
        "ci95_low": round(float(np.percentile(arr, 2.5)), 4),
        "ci95_high": round(float(np.percentile(arr, 97.5)), 4),
    }


def _strat_classification_metrics(
    sub_rows: Sequence[Dict[str, Any]],
    status_key: str,
    positive_status: str,
    negative_status: str,
    flip_fn,
) -> Dict[str, Any]:
    """이진 전복 예측의 기저율(base rate), PPV, NPV, 재현율, 특이도, 상대위험도를 모두 계산한다."""
    low_risk = [r for r in sub_rows if r[status_key] == negative_status]
    high_risk = [r for r in sub_rows if r[status_key] == positive_status]
    n_tot = len(low_risk) + len(high_risk)
    tp = sum(1 for r in high_risk if flip_fn(r))
    fp = len(high_risk) - tp
    fn = sum(1 for r in low_risk if flip_fn(r))
    tn = len(low_risk) - fn
    low_rate = (100.0 * fn / len(low_risk)) if low_risk else 0.0
    high_rate = (100.0 * tp / len(high_risk)) if high_risk else 0.0
    rr = (high_rate / low_rate) if low_rate > 0 else float("inf")
    return {
        "n_evaluated": n_tot,
        "base_rate_flip_pct": round(100.0 * (tp + fn) / max(n_tot, 1), 3),
        "low_risk_count": len(low_risk),
        "low_risk_share_pct": round(100.0 * len(low_risk) / max(n_tot, 1), 3),
        "low_risk_flipped": fn,
        "low_risk_flip_rate_pct": round(low_rate, 3),
        "high_risk_count": len(high_risk),
        "high_risk_share_pct": round(100.0 * len(high_risk) / max(n_tot, 1), 3),
        "high_risk_flipped": tp,
        "high_risk_flip_rate_pct": round(high_rate, 3),
        "ppv_pct": round(100.0 * tp / max(tp + fp, 1), 3),
        "npv_pct": round(100.0 * tn / max(tn + fn, 1), 3),
        "recall_of_flips_pct": round(100.0 * tp / max(tp + fn, 1), 3),
        "specificity_pct": round(100.0 * tn / max(tn + fp, 1), 3),
        "relative_risk_high_vs_low": round(rr, 3) if math.isfinite(rr) else None,
    }


# ---------------------------------------------------------------------------
# Stage 1: NIST JARVIS-DFT 3D 6x6 탄성 텐서 전수 감사
# ---------------------------------------------------------------------------
def run_stage_jarvis_elastic(workers: int) -> Dict[str, Any]:
    print("\n================ [Stage 1] JARVIS-DFT 3D 탄성 텐서 전수 감사 ================")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    with open(DATA_DIR / "jdft_3d.json", "r", encoding="utf-8") as f:
        jdata = json.load(f)

    valid_items: List[Tuple[str, str, List[List[float]], Optional[int]]] = []
    malformed_ids: List[str] = []
    for d in jdata:
        et = d.get("elastic_tensor")
        if not isinstance(et, list) or len(et) == 0:
            continue
        try:
            arr = np.asarray(et, dtype=np.float64)
            if arr.shape == (6, 6) and np.all(np.isfinite(arr)):
                spg_raw = d.get("spg_number")
                spg = int(spg_raw) if isinstance(spg_raw, (int, float)) else (
                    int(spg_raw) if isinstance(spg_raw, str) and spg_raw.isdigit() else None
                )
                valid_items.append((d["jid"], d["formula"], arr.tolist(), spg))
            else:
                malformed_ids.append(d["jid"])
        except Exception:
            malformed_ids.append(d["jid"])

    print(f"유효 6x6 탄성 텐서: {len(valid_items):,}건 (비정상/결측 {len(malformed_ids):,}건)")

    chunk_size = 500
    chunks = [valid_items[i : i + chunk_size] for i in range(0, len(valid_items), chunk_size)]
    rows: List[Dict[str, Any]] = []
    certs_primary: List[Dict[str, Any]] = []
    certs_fragile: List[Dict[str, Any]] = []
    certs_mandel: List[Dict[str, Any]] = []
    certs_mandel_fragile: List[Dict[str, Any]] = []
    with ProcessPoolExecutor(max_workers=workers) as ex:
        for res in ex.map(_elastic_worker_chunk, chunks):
            for r, c_pri, c_frg, c_man, c_mfrg in res:
                rows.append(r)
                if c_pri is not None:
                    certs_primary.append(c_pri)
                if c_frg is not None:
                    certs_fragile.append(c_frg)
                if c_man is not None:
                    certs_mandel.append(c_man)
                if c_mfrg is not None:
                    certs_mandel_fragile.append(c_mfrg)

    # 1) 기본 + 구성적 WEYL_FRAGILE 증명서 직렬화 및 Lean 4 바이너리 + 독립 검증
    tsv_path = RESULTS_DIR / "certs_jarvis_elastic_all.tsv"
    n_written = write_certificates_tsv(certs_primary + certs_fragile, tsv_path)
    indep_chk = verify_tsv_independent(tsv_path)
    lean_chk = verify_tsv_with_lean(tsv_path)

    # 2) 순수 유리수 SO(3)-불변 Mandel/Kelvin 강건 + 구성적 취약 반례 증명서 직렬화 및 Lean 4 + 독립 검증
    tsv_mandel = RESULTS_DIR / "certs_jarvis_elastic_mandel.tsv"
    n_mandel_w = write_certificates_tsv(certs_mandel + certs_mandel_fragile, tsv_mandel)
    mandel_indep = verify_tsv_independent(tsv_mandel)
    mandel_lean = verify_tsv_with_lean(tsv_mandel)

    n = len(rows)
    pd_rows = [r for r in rows if r["pd"]]
    non_pd_rows = [r for r in rows if not r["pd"]]
    r1 = sum(1 for r in rows if r["r1"])
    r5 = sum(1 for r in rows if r["r5"])
    r10 = sum(1 for r in rows if r["r10"])
    mr1 = sum(1 for r in rows if r["mr1"])
    mr5 = sum(1 for r in rows if r["mr5"])
    mr10 = sum(1 for r in rows if r["mr10"])

    # 결정계별 통계 및 채택 설정(matched_setting) 분포 집계
    by_csys: Dict[str, Dict[str, Any]] = {}
    setting_counts_by_csys: Dict[str, Dict[str, int]] = {}
    groups: Dict[str, List[Dict[str, Any]]] = {}
    for r in rows:
        groups.setdefault(r["csys"], []).append(r)
    for csys, grp in sorted(groups.items()):
        g_pd = sum(1 for r in grp if r["pd"])
        g_r1 = sum(1 for r in grp if r["r1"])
        g_r5 = sum(1 for r in grp if r["r5"])
        g_r10 = sum(1 for r in grp if r["r10"])
        g_mr1 = sum(1 for r in grp if r["mr1"])
        g_mr5 = sum(1 for r in grp if r["mr5"])
        g_mr10 = sum(1 for r in grp if r["mr10"])
        sc: Dict[str, int] = {}
        for r in grp:
            sc[r["setting"]] = sc.get(r["setting"], 0) + 1
        setting_counts_by_csys[csys] = sc
        by_csys[csys] = {
            "total": len(grp),
            "born_pd": g_pd,
            "born_non_pd": len(grp) - g_pd,
            "born_non_pd_pct": 100.0 * (len(grp) - g_pd) / len(grp),
            "voigt_robust_1gpa": g_r1,
            "voigt_robust_5gpa": g_r5,
            "voigt_robust_10gpa": g_r10,
            "mandel_robust_1gpa": g_mr1,
            "mandel_robust_5gpa": g_mr5,
            "mandel_robust_10gpa": g_mr10,
            "fragile_1gpa_among_pd": g_pd - g_r1,
            "fragile_5gpa_among_pd": g_pd - g_r5,
            "fragile_10gpa_among_pd": g_pd - g_r10,
            "asym_gt_1gpa": sum(1 for r in grp if r["asym"] > 1.0),
            "zero_viol_gt_1gpa": sum(1 for r in grp if r["zviol"] > 1.0),
            "voigt_viol_gt_1gpa": sum(1 for r in grp if r["vviol"] > 1.0),
            "voigt_viol_gt_5gpa": sum(1 for r in grp if r["vviol"] > 5.0),
            "voigt_fixed_std_gt_1gpa": sum(1 for r in grp if r["vviol_std"] > 1.0),
        }

    cubic_rows = [r for r in rows if r["csys"] == "cubic" and r["crot"] is not None]
    pd_cubic_rows = [r for r in cubic_rows if r["pd"]]
    worst_non_pd = sorted(non_pd_rows, key=lambda r: r["lmin_v"])[:15]
    worst_asym = sorted(rows, key=lambda r: r["asym"], reverse=True)[:10]
    worst_cubic_rot = sorted(cubic_rows, key=lambda r: r["crot"], reverse=True)[:10]

    summary = {
        "stage": "jarvis_elastic",
        "elapsed_sec": round(time.time() - t0, 2),
        "n_valid_6x6": n,
        "n_malformed_skipped": len(malformed_ids),
        "malformed_sample_ids": malformed_ids[:20],
        "n_exact_verified": sum(1 for r in rows if r["ok"]),
        "born_pd_count": len(pd_rows),
        "born_pd_pct": 100.0 * len(pd_rows) / n,
        "born_non_pd_count": len(non_pd_rows),
        "born_non_pd_pct": 100.0 * len(non_pd_rows) / n,
        "weyl_voigt_robust_1gpa": r1,
        "weyl_voigt_robust_1gpa_pct_of_all": 100.0 * r1 / n,
        "weyl_voigt_robust_5gpa": r5,
        "weyl_voigt_robust_5gpa_pct_of_all": 100.0 * r5 / n,
        "weyl_voigt_robust_10gpa": r10,
        "weyl_voigt_robust_10gpa_pct_of_all": 100.0 * r10 / n,
        "fragile_voigt_1gpa_among_pd": len(pd_rows) - r1,
        "fragile_voigt_1gpa_among_pd_pct": 100.0 * (len(pd_rows) - r1) / len(pd_rows),
        "fragile_voigt_5gpa_among_pd": len(pd_rows) - r5,
        "fragile_voigt_5gpa_among_pd_pct": 100.0 * (len(pd_rows) - r5) / len(pd_rows),
        "fragile_voigt_10gpa_among_pd": len(pd_rows) - r10,
        "fragile_voigt_10gpa_among_pd_pct": 100.0 * (len(pd_rows) - r10) / len(pd_rows),
        "weyl_mandel_exact_robust_1gpa": mr1,
        "weyl_mandel_exact_robust_5gpa": mr5,
        "weyl_mandel_exact_robust_10gpa": mr10,
        "fragile_mandel_1gpa_among_pd": len(pd_rows) - mr1,
        "fragile_mandel_5gpa_among_pd": len(pd_rows) - mr5,
        "fragile_mandel_10gpa_among_pd": len(pd_rows) - mr10,
        "fragile_mandel_5gpa_among_pd_pct": 100.0 * (len(pd_rows) - mr5) / len(pd_rows),
        "fragile_mandel_10gpa_among_pd_pct": 100.0 * (len(pd_rows) - mr10) / len(pd_rows),
        "symmetry_violations": {
            "convention": "vasp_outcar_with_axis_permutation_and_rhombohedral_111",
            "matrix_asym_gt_0_1gpa": sum(1 for r in rows if r["asym"] > 0.1),
            "matrix_asym_gt_1gpa": sum(1 for r in rows if r["asym"] > 1.0),
            "matrix_asym_gt_5gpa": sum(1 for r in rows if r["asym"] > 5.0),
            "voigt_zero_gt_1gpa": sum(1 for r in rows if r["zviol"] > 1.0),
            "voigt_zero_gt_5gpa": sum(1 for r in rows if r["zviol"] > 5.0),
            "voigt_any_gt_1gpa": sum(1 for r in rows if r["vviol"] > 1.0),
            "voigt_any_gt_5gpa": sum(1 for r in rows if r["vviol"] > 5.0),
            "voigt_any_gt_10gpa": sum(1 for r in rows if r["vviol"] > 10.0),
            "voigt_fixed_std_gt_1gpa": sum(1 for r in rows if r["vviol_std"] > 1.0),
            "pd_voigt_any_gt_1gpa": sum(1 for r in pd_rows if r["vviol"] > 1.0),
            "pd_voigt_any_gt_1gpa_pct": 100.0 * sum(1 for r in pd_rows if r["vviol"] > 1.0) / len(pd_rows),
            "pd_voigt_any_gt_5gpa": sum(1 for r in pd_rows if r["vviol"] > 5.0),
            "pd_voigt_fixed_std_gt_1gpa": sum(1 for r in pd_rows if r["vviol_std"] > 1.0),
            "pd_matrix_asym_gt_1gpa": sum(1 for r in pd_rows if r["asym"] > 1.0),
            "cubic_total": len(cubic_rows),
            "cubic_mandel_rot_inv_gt_1gpa": sum(1 for r in cubic_rows if r["crot"] > 1.0),
            "cubic_mandel_rot_inv_gt_5gpa": sum(1 for r in cubic_rows if r["crot"] > 5.0),
            "cubic_mandel_rot_inv_gt_10gpa": sum(1 for r in cubic_rows if r["crot"] > 10.0),
            "pd_cubic_total": len(pd_cubic_rows),
            "pd_cubic_mandel_rot_inv_gt_1gpa": sum(1 for r in pd_cubic_rows if r["crot"] > 1.0),
            "pd_cubic_mandel_rot_inv_gt_5gpa": sum(1 for r in pd_cubic_rows if r["crot"] > 5.0),
            "matched_setting_counts_by_csys": setting_counts_by_csys,
        },
        "by_crystal_system": by_csys,
        "worst_non_pd_examples": worst_non_pd,
        "worst_asymmetry_examples": worst_asym,
        "worst_cubic_rot_inv_examples": worst_cubic_rot,
        "certificate_verification": {
            "primary_plus_fragile_tsv": {
                "tsv_file": tsv_path.name,
                "tsv_sha256": sha256_file(tsv_path),
                "written": n_written,
                "n_primary": len(certs_primary),
                "n_weyl_fragile_witnesses": len(certs_fragile),
                "independent_exact_check": indep_chk,
                "lean_binary_check": lean_chk,
            },
            "mandel_weyl_tsv": {
                "tsv_file": tsv_mandel.name,
                "tsv_sha256": sha256_file(tsv_mandel),
                "written": n_mandel_w,
                "n_mandel_robust": len(certs_mandel),
                "n_mandel_fragile_witnesses": len(certs_mandel_fragile),
                "independent_exact_check": mandel_indep,
                "lean_binary_check": mandel_lean,
            },
        },
    }

    out_path = RESULTS_DIR / "jarvis_elastic_summary.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    print(
        f"[Stage 1 완료] PD={len(pd_rows):,}/{n:,} ({summary['born_pd_pct']:.2f}%), "
        f"Voigt 5GPa={r5:,}, Mandel 5GPa={mr5:,}, "
        f"Lean primary+fragile={lean_chk.get('passed')}/{lean_chk.get('total')}, "
        f"Lean mandel={mandel_lean.get('passed')}/{mandel_lean.get('total')}"
    )
    return summary


# ---------------------------------------------------------------------------
# Stage 2: NIST JARVIS-DFT 3D 93,902개 상평형 전수 감사 + 공개 ehull 음성대조 포렌식
# ---------------------------------------------------------------------------
def run_stage_jarvis_phase(workers: int) -> Dict[str, Any]:
    print("\n================ [Stage 2] JARVIS-DFT 3D 상평형 전수 감사 ================")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    with open(DATA_DIR / "jdft_3d.json", "r", encoding="utf-8") as f:
        jdata = json.load(f)

    phases: List[PhaseEntry] = []
    tot_phases: List[PhaseEntry] = []
    elem_o88: Dict[str, float] = {}
    rep_ehull_by_id: Dict[str, float] = {}
    n_dropped = 0
    ref_comps: List[Dict[str, float]] = []
    ref_diffs: List[float] = []
    ref_ids: List[str] = []

    for d in jdata:
        fe = d.get("formation_energy_peratom")
        o88 = d.get("optb88vdw_total_energy")
        eh = d.get("ehull")
        if not isinstance(fe, (int, float)) or not math.isfinite(fe):
            n_dropped += 1
            continue
        try:
            comp = formula_to_atom_fractions(d["formula"])
            cnt = parse_formula_counts(d["formula"])
        except Exception:
            n_dropped += 1
            continue
        eh_f = float(eh) if isinstance(eh, (int, float)) and math.isfinite(eh) else None
        if eh_f is not None:
            rep_ehull_by_id[d["jid"]] = eh_f
        phases.append(PhaseEntry(d["jid"], d["formula"], comp, to_fraction(fe), reported_ehull=eh_f))
        if isinstance(o88, (int, float)) and math.isfinite(o88):
            tot_phases.append(PhaseEntry(d["jid"], d["formula"], comp, to_fraction(o88), reported_ehull=eh_f))
            ref_comps.append({el: float(q) for el, q in comp.items()})
            ref_diffs.append(float(o88) - float(fe))
            ref_ids.append(d["jid"])
            if len(cnt) == 1 and float(next(iter(cnt.values()))) == 1.0:
                el = next(iter(cnt))
                if el not in elem_o88 or o88 < elem_o88[el]:
                    elem_o88[el] = o88

    # 전수 93,902개 상평형 병렬 감사
    rows, certs, elapsed, index_meta = _run_parallel_phase_audit(
        phases, "JARVIS-Phase", workers=workers, cert_sample_n=5000, add_elemental_refs=True
    )
    row_by_id = {r["id"]: r for r in rows}

    # 공개 ehull 이상치 포렌식 + 2종 음성대조군(no /N_fu, random elemental refs) + CertMat 안정상 대조
    bug_div_nfu: List[float] = []
    bug_no_div: List[float] = []
    bug_rand_ref: List[float] = []
    rng = np.random.default_rng(2026)
    elem_vals = list(elem_o88.values())
    rand_elem_o88 = {el: float(rng.choice(elem_vals)) for el in elem_o88}

    # 알고리즘적 대표 사례 선정 (CertMat 명목 안정 다원계 중 공개 ehull > 1.0 eV 이면서 공식 잔차 최소 상위 5건)
    stable_bug_candidates: List[Tuple[float, Dict[str, Any]]] = []
    elem_ehulls: List[float] = []

    for d in jdata:
        o88 = d.get("optb88vdw_total_energy")
        eh = d.get("ehull")
        if not (isinstance(o88, (int, float)) and isinstance(eh, (int, float)) and math.isfinite(o88) and math.isfinite(eh)):
            continue
        try:
            cnt = parse_formula_counts(d["formula"])
        except Exception:
            continue
        n_fu = float(sum(cnt.values()))
        if len(cnt) == 1:
            elem_ehulls.append(float(eh))
        elif n_fu > 1.0 and all(el in elem_o88 for el in cnt):
            e_elem = sum((float(c) / n_fu) * elem_o88[el] for el, c in cnt.items())
            e_rand = sum((float(c) / n_fu) * rand_elem_o88[el] for el, c in cnt.items())
            pred_bug = (o88 / n_fu) - e_elem
            diff_bug = abs(pred_bug - eh)
            bug_div_nfu.append(diff_bug)
            bug_no_div.append(abs((o88 - e_elem) - eh))
            bug_rand_ref.append(abs(((o88 / n_fu) - e_rand) - eh))
            r_aud = row_by_id.get(d["jid"])
            if r_aud and r_aud["nom_stable"] and eh > 1.0 and r_aud["margin_mev"] > 20.0:
                stable_bug_candidates.append((
                    diff_bug,
                    {
                        "jid": d["jid"],
                        "formula": d["formula"],
                        "n_atoms_fu": int(n_fu),
                        "formation_energy_peratom": d.get("formation_energy_peratom"),
                        "optb88vdw_total_energy": o88,
                        "certmat_margin_mev": round(r_aud["margin_mev"], 3),
                        "published_ehull": eh,
                        "predicted_per_atom_div_nfu_ehull": round(pred_bug, 5),
                        "abs_diff_ev": round(diff_bug, 5),
                    },
                ))
    stable_bug_candidates.sort(key=lambda x: (x[0], x[1]["jid"]))
    algo_bug_examples = [x[1] for x in stable_bug_candidates[:8]]

    # CertMat 명목 안정상(25,909개)에서의 공개 ehull 분포
    stable_pub_ehulls = np.array(
        [rep_ehull_by_id[r["id"]] for r in rows if (not r["uncompeted"]) and r["nom_stable"] and r["id"] in rep_ehull_by_id],
        dtype=np.float64,
    )
    all_pub_ehulls = np.array(list(rep_ehull_by_id.values()), dtype=np.float64)
    gt1_pub_ehulls = all_pub_ehulls[all_pub_ehulls > 1.0]

    # 정리 2 원소 기준 일관성 포렌식 감사 (동일 집합 93,902개에서 o88 - fe 직교 분해)
    ref_consistency = decompose_reference_and_residual_errors(ref_comps, ref_diffs)
    ref_eta_mev = np.abs(np.asarray(ref_consistency.pop("residuals_ev"), dtype=np.float64)) * 1000.0
    ref_eta_by_id = {jid: float(eta) for jid, eta in zip(ref_ids, ref_eta_mev)}

    # 동일 모집단(tot_phases에 존재하는 93,902개) + 동일 원소참조 규약(add_elemental_refs=False) 하의
    # 1,000개 표본 총에너지 vs 형성에너지 Hull 여유 일치성 (비혼재 검증)
    common_ids = set(ref_ids)
    fe_common = [p for p in phases if p.material_id in common_ids]
    idx_fe_common = PhaseDiagramIndex(fe_common, add_elemental_refs=False)
    idx_tot_common = PhaseDiagramIndex(tot_phases, add_elemental_refs=False)
    tot_by_id = {p.material_id: p for p in tot_phases}
    thm2_all_diffs: List[float] = []
    thm2_consistent_diffs: List[float] = []
    thm2_mixed_diffs: List[float] = []
    step_t2 = max(1, len(fe_common) // 1000)
    for p in fe_common[::step_t2][:1000]:
        pt = tot_by_id[p.material_id]
        c_fe = idx_fe_common.get_competing_phases(p)
        c_tot = idx_tot_common.get_competing_phases(pt)
        if not c_fe or not c_tot:
            continue
        try:
            r1 = audit_single_phase(p, c_fe, emit_certificate=False)
            r2 = audit_single_phase(pt, c_tot, emit_certificate=False)
        except ValueError:
            continue
        diff = abs(r1.nominal_margin_mev - r2.nominal_margin_mev)
        thm2_all_diffs.append(diff)
        if ref_eta_by_id.get(p.material_id, 0.0) <= 1.0:
            thm2_consistent_diffs.append(diff)
        else:
            thm2_mixed_diffs.append(diff)

    tsv_path = RESULTS_DIR / "certs_jarvis_phase_sample.tsv"
    n_written = write_certificates_tsv(certs, tsv_path)
    indep_chk = verify_tsv_independent(tsv_path)
    lean_chk = verify_tsv_with_lean(tsv_path)

    summary = _summarize_phase_rows(rows, "JARVIS-DFT-3D (93,902)", elapsed, index_meta=index_meta, n_dropped_parse=n_dropped)
    bug_arr = np.array(bug_div_nfu, dtype=np.float64)
    nodiv_arr = np.array(bug_no_div, dtype=np.float64)
    rand_arr = np.array(bug_rand_ref, dtype=np.float64)
    summary["published_ehull_forensic_audit"] = {
        "n_all_finite_published_ehull": int(len(all_pub_ehulls)),
        "all_published_ehull_median_ev": float(np.median(all_pub_ehulls)),
        "published_ehull_gt_0_5ev": int((all_pub_ehulls > 0.5).sum()),
        "published_ehull_gt_1_0ev": int((all_pub_ehulls > 1.0).sum()),
        "gt_1_0ev_subset_median_ev": float(np.median(gt1_pub_ehulls)) if len(gt1_pub_ehulls) else 0.0,
        "elemental_nfu1_count": len(elem_ehulls),
        "elemental_nfu1_median_ehull_ev": float(np.median(elem_ehulls)) if elem_ehulls else 0.0,
        "certmat_nom_stable_published_ehull": {
            "count": int(len(stable_pub_ehulls)),
            "median_ev": float(np.median(stable_pub_ehulls)) if len(stable_pub_ehulls) else 0.0,
            "gt_0_5ev_count": int((stable_pub_ehulls > 0.5).sum()),
            "gt_0_5ev_pct": float(100.0 * (stable_pub_ehulls > 0.5).mean()) if len(stable_pub_ehulls) else 0.0,
            "gt_1_0ev_count": int((stable_pub_ehulls > 1.0).sum()),
            "gt_1_0ev_pct": float(100.0 * (stable_pub_ehulls > 1.0).mean()) if len(stable_pub_ehulls) else 0.0,
        },
        "n_multinary_checked": int(len(bug_arr)),
        "hypothesis_div_nfu_fit": {
            "median_abs_residual_ev": float(np.median(bug_arr)),
            "match_lt_0_01ev_count": int((bug_arr < 0.01).sum()),
            "match_lt_0_01ev_pct": float(100.0 * (bug_arr < 0.01).mean()),
            "match_lt_0_05ev_count": int((bug_arr < 0.05).sum()),
            "match_lt_0_05ev_pct": float(100.0 * (bug_arr < 0.05).mean()),
        },
        "negative_control_no_div_nfu": {
            "median_abs_residual_ev": float(np.median(nodiv_arr)),
            "match_lt_0_01ev_pct": float(100.0 * (nodiv_arr < 0.01).mean()),
            "match_lt_0_05ev_pct": float(100.0 * (nodiv_arr < 0.05).mean()),
        },
        "negative_control_random_elem_refs": {
            "median_abs_residual_ev": float(np.median(rand_arr)),
            "match_lt_0_01ev_pct": float(100.0 * (rand_arr < 0.01).mean()),
            "match_lt_0_05ev_pct": float(100.0 * (rand_arr < 0.05).mean()),
        },
        "algorithmically_selected_stable_examples": algo_bug_examples,
    }
    summary["theorem2_reference_consistency_audit"] = {
        "n_checked_common_pool": int(len(ref_eta_mev)),
        "r2_linear_reference_fit": ref_consistency["variance_explained_by_ref_shift_r2"],
        "condition_number": ref_consistency["condition_number"],
        "residual_mae_mev": ref_consistency["residual_mae_mev"],
        "residual_median_mev": float(np.median(ref_eta_mev)),
        "residual_p95_mev": float(np.percentile(ref_eta_mev, 95)),
        "residual_max_mev": float(np.max(ref_eta_mev)),
        "n_residual_gt_1mev": int((ref_eta_mev > 1.0).sum()),
        "n_residual_gt_10mev": int((ref_eta_mev > 10.0).sum()),
        "n_residual_gt_10mev_pct": float(100.0 * (ref_eta_mev > 10.0).mean()),
        "n_residual_gt_50mev": int((ref_eta_mev > 50.0).sum()),
        "n_residual_gt_50mev_pct": float(100.0 * (ref_eta_mev > 50.0).mean()),
        "unconfounded_1000_sample_margin_diff": {
            "n_checked": len(thm2_all_diffs),
            "median_abs_diff_mev": float(np.median(thm2_all_diffs)) if thm2_all_diffs else 0.0,
            "p95_abs_diff_mev": float(np.percentile(thm2_all_diffs, 95)) if thm2_all_diffs else 0.0,
            "max_abs_diff_mev": float(np.max(thm2_all_diffs)) if thm2_all_diffs else 0.0,
            "consistent_ref_subset_n": len(thm2_consistent_diffs),
            "consistent_ref_median_diff_mev": float(np.median(thm2_consistent_diffs)) if thm2_consistent_diffs else 0.0,
            "mixed_ref_subset_n": len(thm2_mixed_diffs),
            "mixed_ref_median_diff_mev": float(np.median(thm2_mixed_diffs)) if thm2_mixed_diffs else 0.0,
        },
    }
    summary["certificate_verification"] = {
        "tsv_file": tsv_path.name,
        "tsv_sha256": sha256_file(tsv_path),
        "written": n_written,
        "independent_exact_check": indep_chk,
        "lean_binary_check": lean_chk,
    }

    out_path = RESULTS_DIR / "jarvis_phase_summary.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    print(
        f"[Stage 2 완료] n={summary['n_total']:,}, 명목안정={summary['n_nom_stable']:,}, "
        f"Lean TSV={lean_chk.get('passed')}/{lean_chk.get('total')}, "
        f"Ref불일치(>10meV)={summary['theorem2_reference_consistency_audit']['n_residual_gt_10mev']:,}"
    )
    return summary


# ---------------------------------------------------------------------------
# Stage 3: Matbench Discovery WBM 256,963개 전수 감사
# ---------------------------------------------------------------------------
def run_stage_wbm_phase(workers: int) -> Dict[str, Any]:
    print("\n================ [Stage 3] Matbench Discovery WBM 전수 감사 ================")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    phases: List[PhaseEntry] = []
    mp_ehull_map: Dict[str, float] = {}
    uniq_proto_map: Dict[str, bool] = {}
    corr_comps: List[Dict[str, float]] = []
    corr_vals: List[float] = []
    n_dropped = 0

    with gzip.open(DATA_DIR / "wbm_summary.csv.gz", "rt", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            mid = r["material_id"]
            fe_str = r["e_form_per_atom_mp2020_corrected"]
            try:
                fe_f = float(fe_str)
                if not math.isfinite(fe_f):
                    n_dropped += 1
                    continue
                fe_q = to_fraction(fe_str)
                comp = formula_to_atom_fractions(r["formula"])
            except Exception:
                n_dropped += 1
                continue
            eh_mp = float(r["e_above_hull_mp2020_corrected_ppd_mp"]) if r.get("e_above_hull_mp2020_corrected_ppd_mp") else None
            if eh_mp is not None and math.isfinite(eh_mp):
                mp_ehull_map[mid] = eh_mp
            uniq_proto_map[mid] = (r.get("unique_prototype") == "True")
            try:
                ec = float(r["e_correction_per_atom_mp2020"])
                if math.isfinite(ec):
                    corr_comps.append({el: float(q) for el, q in comp.items()})
                    corr_vals.append(ec)
            except Exception:
                pass
            phases.append(PhaseEntry(mid, r["formula"], comp, fe_q, reported_ehull=eh_mp))

    rows, certs, elapsed, index_meta = _run_parallel_phase_audit(
        phases, "WBM-257k", workers=workers, cert_sample_n=5000, add_elemental_refs=True
    )

    mp2020_decomp = decompose_reference_and_residual_errors(corr_comps, corr_vals)
    mp2020_decomp.pop("residuals_ev", None)

    # MP2020 공식 ehull <= 0 (42,688개) 후보군에 대한 WBM 내부 경합 감사 + 동질이상 vs 교차조성 분해
    mp_stable_rows = [r for r in rows if (not r["uncompeted"]) and mp_ehull_map.get(r["id"], 999.0) <= 0.0]
    mp_intra_unstab_rows = [r for r in mp_stable_rows if not r["nom_stable"]]
    mp_intra_unstab_poly = sum(1 for r in mp_intra_unstab_rows if r["same_poly"])
    mp_intra_unstab_cross = len(mp_intra_unstab_rows) - mp_intra_unstab_poly

    mp_stable_uniq = [r for r in mp_stable_rows if uniq_proto_map.get(r["id"], False)]
    mp_uniq_unstab = [r for r in mp_stable_uniq if not r["nom_stable"]]
    mp_uniq_unstab_poly = sum(1 for r in mp_uniq_unstab if r["same_poly"])

    mp_stable_frag25 = sum(1 for r in mp_stable_rows if r["s25"] != "Certified_Robust_Stable")
    mp_stable_frag_het = sum(1 for r in mp_stable_rows if r["s_het"] != "Certified_Robust_Stable")
    uniq_rows = [r for r in rows if uniq_proto_map.get(r["id"], False)]

    tsv_path = RESULTS_DIR / "certs_wbm_phase_sample.tsv"
    n_written = write_certificates_tsv(certs, tsv_path)
    indep_chk = verify_tsv_independent(tsv_path)
    lean_chk = verify_tsv_with_lean(tsv_path)

    summary = _summarize_phase_rows(rows, "Matbench-Discovery-WBM (256,963)", elapsed, index_meta=index_meta, n_dropped_parse=n_dropped)
    summary["unique_prototype_count"] = len(uniq_rows)
    summary["mp2020_reported_stable_subset"] = {
        "n_mp2020_ehull_le_0": len(mp_stable_rows),
        "already_unstable_on_wbm_intracatalog_hull": len(mp_intra_unstab_rows),
        "already_unstable_pct": 100.0 * len(mp_intra_unstab_rows) / len(mp_stable_rows) if mp_stable_rows else 0.0,
        "unstable_by_same_composition_polymorph": mp_intra_unstab_poly,
        "unstable_by_same_composition_polymorph_pct_of_unstable": (
            100.0 * mp_intra_unstab_poly / len(mp_intra_unstab_rows) if mp_intra_unstab_rows else 0.0
        ),
        "unstable_by_cross_composition_decomp": mp_intra_unstab_cross,
        "unstable_by_cross_composition_decomp_pct_of_unstable": (
            100.0 * mp_intra_unstab_cross / len(mp_intra_unstab_rows) if mp_intra_unstab_rows else 0.0
        ),
        "unique_prototype_mp2020_stable_count": len(mp_stable_uniq),
        "unique_prototype_already_unstable": len(mp_uniq_unstab),
        "unique_prototype_already_unstable_pct": (
            100.0 * len(mp_uniq_unstab) / len(mp_stable_uniq) if mp_stable_uniq else 0.0
        ),
        "unique_prototype_unstable_same_polymorph": mp_uniq_unstab_poly,
        "unique_prototype_unstable_cross_composition": len(mp_uniq_unstab) - mp_uniq_unstab_poly,
        "not_robust_25mev_on_wbm_intracatalog": mp_stable_frag25,
        "not_robust_25mev_pct": 100.0 * mp_stable_frag25 / len(mp_stable_rows) if mp_stable_rows else 0.0,
        "not_robust_hetero_on_wbm_intracatalog": mp_stable_frag_het,
        "not_robust_hetero_pct": 100.0 * mp_stable_frag_het / len(mp_stable_rows) if mp_stable_rows else 0.0,
    }
    summary["theorem2_mp2020_correction_decomposition"] = mp2020_decomp
    summary["certificate_verification"] = {
        "tsv_file": tsv_path.name,
        "tsv_sha256": sha256_file(tsv_path),
        "written": n_written,
        "independent_exact_check": indep_chk,
        "lean_binary_check": lean_chk,
    }

    out_path = RESULTS_DIR / "wbm_phase_summary.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    print(
        f"[Stage 3 완료] n={summary['n_total']:,}, 명목안정={summary['n_nom_stable']:,}, "
        f"MP2020안정중 내부불안정={len(mp_intra_unstab_rows):,} "
        f"(동질이상={mp_intra_unstab_poly:,}, 교차조성={mp_intra_unstab_cross:,}), "
        f"Lean TSV={lean_chk.get('passed')}/{lean_chk.get('total')}"
    )
    return summary


# ---------------------------------------------------------------------------
# Stage 4: GNoME PBE vs r2SCAN 117,043개 매칭 실측 교차검증 + 정리 2 실증
# ---------------------------------------------------------------------------
def _parse_opt_float(s: Optional[str]) -> float:
    if not s:
        return float("nan")
    try:
        v = float(s)
        return v if math.isfinite(v) else float("nan")
    except Exception:
        return float("nan")


def run_stage_gnome_crossval(workers: int) -> Dict[str, Any]:
    print("\n================ [Stage 4] GNoME PBE vs r2SCAN 117,043개 실측 교차검증 ================")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    t0 = time.time()
    pbe_map: Dict[str, Dict[str, Any]] = {}
    n_pbe_dropped = 0
    with open(DATA_DIR / "gnome_stable_materials_summary.csv", "r", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            mid = r["MaterialId"]
            fe_str = r["Formation Energy Per Atom"]
            try:
                fe_f = float(fe_str)
                if not math.isfinite(fe_f):
                    n_pbe_dropped += 1
                    continue
                pbe_map[mid] = {
                    "comp_str": r["Composition"],
                    "fe_str": fe_str,
                    "fe_f": fe_f,
                    "de": _parse_opt_float(r.get("Decomposition Energy Per Atom")),
                    "de_all": _parse_opt_float(r.get("Decomposition Energy Per Atom All")),
                    "de_mp": _parse_opt_float(r.get("Decomposition Energy Per Atom MP")),
                    "de_mp_oqmd": _parse_opt_float(r.get("Decomposition Energy Per Atom MP OQMD")),
                }
            except Exception:
                n_pbe_dropped += 1

    matched_pbe_phases: List[PhaseEntry] = []
    matched_r2_phases: List[PhaseEntry] = []
    matched_meta: Dict[str, Dict[str, Any]] = {}
    comps_for_t2: List[Dict[str, float]] = []
    deltas_for_t2: List[float] = []
    n_r2_dropped = 0

    with open(DATA_DIR / "gnome_stable_materials_r2scan.csv", "r", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            mid = r["MaterialId"]
            if mid not in pbe_map:
                continue
            r2_fe_str = r["Formation Energy Per Atom"]
            try:
                r2_fe_f = float(r2_fe_str)
                if not math.isfinite(r2_fe_f):
                    n_r2_dropped += 1
                    continue
                comp = formula_to_atom_fractions(r["Composition"])
                pbe_q = to_fraction(pbe_map[mid]["fe_str"])
                r2_q = to_fraction(r2_fe_str)
            except Exception:
                n_r2_dropped += 1
                continue
            pm = pbe_map[mid]
            matched_pbe_phases.append(PhaseEntry(mid, r["Composition"], comp, pbe_q))
            matched_r2_phases.append(PhaseEntry(mid, r["Composition"], comp, r2_q))
            comps_for_t2.append({el: float(q) for el, q in comp.items()})
            deltas_for_t2.append(r2_fe_f - pm["fe_f"])
            matched_meta[mid] = {
                "formula": r["Composition"],
                "chem_class": classify_chemistry(comp.keys()),
                "pbe_fe": pm["fe_f"],
                "r2_fe": r2_fe_f,
                "pbe_de": pm["de"],
                "pbe_de_all": pm["de_all"],
                "pbe_de_mp": pm["de_mp"],
                "pbe_de_mp_oqmd": pm["de_mp_oqmd"],
                "r2_de": _parse_opt_float(r.get("Decomposition Energy Per Atom")),
                "r2_de_all": _parse_opt_float(r.get("Decomposition Energy Per Atom All")),
                "r2_de_mp": _parse_opt_float(r.get("Decomposition Energy Per Atom MP")),
                "r2_de_mp_oqmd": _parse_opt_float(r.get("Decomposition Energy Per Atom MP OQMD")),
            }

    print(f"매칭 PBE-r2SCAN 결정 수: {len(matched_pbe_phases):,} (파싱 제외 PBE={n_pbe_dropped}, r2SCAN={n_r2_dropped})")

    # 4a) 정리 2 직교 투영 분해 (조건수 및 화학군별 커버리지 포함)
    t2_res = decompose_reference_and_residual_errors(comps_for_t2, deltas_for_t2)
    t2_res.pop("residuals_ev", None)

    # 4b) 동일 117,043개 집합 상의 1:1 동등 비교(Matched Sub-Hull) 정확 유리수 LP + 양쪽 Lean 증명서
    pbe_rows, pbe_certs, t_pbe, pbe_idx_meta = _run_parallel_phase_audit(
        matched_pbe_phases, "GNoME-Matched-PBE-117k", workers=workers, cert_sample_n=5000
    )
    r2_rows, r2_certs, t_r2, r2_idx_meta = _run_parallel_phase_audit(
        matched_r2_phases, "GNoME-Matched-r2SCAN-117k", workers=workers, cert_sample_n=5000
    )
    r2_by_id = {r["id"]: r for r in r2_rows}

    # 4b-1) 2x2 일관성 및 단조성 검증 (CertMat intra-hull vs GNoME `Decomposition Energy Per Atom All`)
    mono_viol_pbe = 0
    max_mono_excess_mev = 0.0
    c2x2_vs_de_all = {"cert_stab_de_all_le0": 0, "cert_stab_de_all_gt0": 0, "cert_unstab_de_all_le0": 0, "cert_unstab_de_all_gt0": 0}
    c2x2_vs_de_ext = {"cert_stab_de_le0": 0, "cert_stab_de_gt0": 0, "cert_unstab_de_le0": 0, "cert_unstab_de_gt0": 0}
    for r in pbe_rows:
        if r["uncompeted"]:
            continue
        meta = matched_meta[r["id"]]
        de_all = meta["pbe_de_all"]
        de_ext = meta["pbe_de"]
        if math.isfinite(de_all):
            excess = r["ehull_mev"] - (de_all * 1000.0)
            if excess > max_mono_excess_mev:
                max_mono_excess_mev = excess
            if excess > 0.5:
                mono_viol_pbe += 1
            k1 = ("cert_stab_" if r["nom_stable"] else "cert_unstab_") + ("de_all_le0" if de_all <= 0.0 else "de_all_gt0")
            c2x2_vs_de_all[k1] += 1
        if math.isfinite(de_ext):
            k2 = ("cert_stab_" if r["nom_stable"] else "cert_unstab_") + ("de_le0" if de_ext <= 0.0 else "de_gt0")
            c2x2_vs_de_ext[k2] += 1

    # 4b-2) Matched 117k Exact Sub-Hull 전복 검증 (실제 Charnes-Cooper 정확 LP 인증 계층!)
    a2a_pbe_stable = [r for r in pbe_rows if (not r["uncompeted"]) and r["nom_stable"]]
    a2a_flips_gt0 = np.array([1 if not r2_by_id[r["id"]]["nom_stable"] else 0 for r in a2a_pbe_stable], dtype=np.int64)
    a2a_flips_gt25 = np.array([1 if r2_by_id[r["id"]]["ehull_mev"] > 25.0 else 0 for r in a2a_pbe_stable], dtype=np.int64)
    a2a_eps_scores = np.array([-r["eps_unif_mev"] for r in a2a_pbe_stable], dtype=np.float64)
    a2a_het_scores = np.array([-r["h_scale"] if math.isfinite(r["h_scale"]) else -1e9 for r in a2a_pbe_stable], dtype=np.float64)

    a2a_validation = {
        "regime": "exact_charnes_cooper_lp_matched_117k_subhull",
        "n_pbe_stable_on_matched_hull": len(a2a_pbe_stable),
        "n_flipped_r2scan_unstable_gt0": int(a2a_flips_gt0.sum()),
        "overall_flip_rate_gt0_pct": round(100.0 * float(a2a_flips_gt0.mean()), 3),
        "n_flipped_r2scan_ehull_gt25mev": int(a2a_flips_gt25.sum()),
        "overall_flip_rate_gt25mev_pct": round(100.0 * float(a2a_flips_gt25.mean()), 3),
        "roc_auc_eps_unif_for_flip_gt0": _bootstrap_auc_ci(a2a_flips_gt0, a2a_eps_scores),
        "roc_auc_hetero_scale_for_flip_gt0": _bootstrap_auc_ci(a2a_flips_gt0, a2a_het_scores),
        "roc_auc_eps_unif_for_flip_gt25": _bootstrap_auc_ci(a2a_flips_gt25, a2a_eps_scores),
        "roc_auc_hetero_scale_for_flip_gt25": _bootstrap_auc_ci(a2a_flips_gt25, a2a_het_scores),
        "flip_gt0_by_10mev": _strat_classification_metrics(
            a2a_pbe_stable, "s10", "Fragile", "Certified_Robust_Stable", lambda r: not r2_by_id[r["id"]]["nom_stable"]
        ),
        "flip_gt0_by_25mev": _strat_classification_metrics(
            a2a_pbe_stable, "s25", "Fragile", "Certified_Robust_Stable", lambda r: not r2_by_id[r["id"]]["nom_stable"]
        ),
        "flip_gt0_by_50mev": _strat_classification_metrics(
            a2a_pbe_stable, "s50", "Fragile", "Certified_Robust_Stable", lambda r: not r2_by_id[r["id"]]["nom_stable"]
        ),
        "flip_gt0_by_hetero": _strat_classification_metrics(
            a2a_pbe_stable, "s_het", "Fragile", "Certified_Robust_Stable", lambda r: not r2_by_id[r["id"]]["nom_stable"]
        ),
        "flip_gt25mev_by_25mev": _strat_classification_metrics(
            a2a_pbe_stable, "s25", "Fragile", "Certified_Robust_Stable", lambda r: r2_by_id[r["id"]]["ehull_mev"] > 25.0
        ),
        "flip_gt25mev_by_hetero": _strat_classification_metrics(
            a2a_pbe_stable, "s_het", "Fragile", "Certified_Robust_Stable", lambda r: r2_by_id[r["id"]]["ehull_mev"] > 25.0
        ),
        "monotonicity_vs_gnome_de_all": {
            "n_violations_gt_0_5mev": mono_viol_pbe,
            "max_excess_ehull_minus_de_all_mev": round(max_mono_excess_mev, 4),
            "contingency_2x2_vs_de_all": c2x2_vs_de_all,
            "contingency_2x2_vs_de_external": c2x2_vs_de_ext,
        },
    }

    sw_pos = [r for r in a2a_pbe_stable if r["sw"]]
    sw_neg = [r for r in a2a_pbe_stable if not r["sw"]]
    sw_pos_flip = sum(1 for r in sw_pos if not r2_by_id[r["id"]]["nom_stable"])
    sw_neg_flip = sum(1 for r in sw_neg if not r2_by_id[r["id"]]["nom_stable"])
    a2a_validation["phase_switching_flip_analysis"] = {
        "switching_count": len(sw_pos),
        "switching_flipped_gt0": sw_pos_flip,
        "switching_flip_rate_pct": round(100.0 * sw_pos_flip / len(sw_pos), 3) if sw_pos else 0.0,
        "non_switching_count": len(sw_neg),
        "non_switching_flipped_gt0": sw_neg_flip,
        "non_switching_flip_rate_pct": round(100.0 * sw_neg_flip / len(sw_neg), 3) if sw_neg else 0.0,
    }

    # 4c) 외부 공개 컬럼(`Decomposition Energy Per Atom` 및 `... MP`, `... MP OQMD`) 기반 프록시 위험도 평가
    # 중요(Codex C1/Claude C4 대응): 외부 경쟁상 목록이 CSV에 없으므로 이질 분모를 `2 * sigma_x`로 근사한
    # 비인증 프록시 점수(`Proxy_Low_Risk` vs `Proxy_High_Risk`)임을 명시하고 Lean 인증 계층과 엄격 분리!
    def _eval_external_column(pbe_col_key: str, r2_col_key: str, col_label: str) -> Dict[str, Any]:
        recs = []
        for mid, meta in matched_meta.items():
            pbe_de = meta[pbe_col_key]
            r2_de = meta[r2_col_key]
            if not (math.isfinite(pbe_de) and math.isfinite(r2_de)) or pbe_de > 0.0:
                continue
            margin_mev = -pbe_de * 1000.0
            eps_unif_mev = 0.5 * margin_mev
            sigma_x_mev = float(getattr(HETERO_CHEM_PROFILE, meta["chem_class"])) * 1000.0
            proxy_het_scale = margin_mev / (2.0 * sigma_x_mev) if sigma_x_mev > 0 else 0.0
            recs.append({
                "id": mid,
                "chem_class": meta["chem_class"],
                "eps_unif_mev": eps_unif_mev,
                "proxy_het_scale": proxy_het_scale,
                "flipped_gt0": (r2_de > 0.0),
                "flipped_gt25": (r2_de > 0.025),
                "p10": "Proxy_Low_Risk" if eps_unif_mev >= 10.0 else "Proxy_High_Risk",
                "p25": "Proxy_Low_Risk" if eps_unif_mev >= 25.0 else "Proxy_High_Risk",
                "p50": "Proxy_Low_Risk" if eps_unif_mev >= 50.0 else "Proxy_High_Risk",
                "p_het": "Proxy_Low_Risk" if proxy_het_scale >= 1.0 else "Proxy_High_Risk",
            })
        y0 = np.array([1 if r["flipped_gt0"] else 0 for r in recs], dtype=np.int64)
        y25 = np.array([1 if r["flipped_gt25"] else 0 for r in recs], dtype=np.int64)
        sc_u = np.array([-r["eps_unif_mev"] for r in recs], dtype=np.float64)
        sc_h = np.array([-r["proxy_het_scale"] for r in recs], dtype=np.float64)

        by_chem: Dict[str, Any] = {}
        cg: Dict[str, List[Dict[str, Any]]] = {}
        for r in recs:
            cg.setdefault(r["chem_class"], []).append(r)
        for cls, grp in sorted(cg.items()):
            f0 = sum(1 for r in grp if r["flipped_gt0"])
            f25 = sum(1 for r in grp if r["flipped_gt25"])
            by_chem[cls] = {
                "n_pbe_stable": len(grp),
                "flipped_gt0": f0,
                "flip_rate_gt0_pct": round(100.0 * f0 / len(grp), 3),
                "flipped_gt25": f25,
                "flip_rate_gt25_pct": round(100.0 * f25 / len(grp), 3),
                "proxy_high_risk_25mev_pct": round(100.0 * sum(1 for r in grp if r["p25"] == "Proxy_High_Risk") / len(grp), 3),
                "proxy_high_risk_hetero_pct": round(100.0 * sum(1 for r in grp if r["p_het"] == "Proxy_High_Risk") / len(grp), 3),
            }
        return {
            "source_column": col_label,
            "is_certified_lp": False,
            "proxy_formula": "margin / (2 * sigma_class(candidate)) — uncertified proxy approximation (external competitors unavailable in CSV)",
            "n_pbe_de_le_0": len(recs),
            "n_flipped_r2scan_gt0": int(y0.sum()),
            "overall_flip_rate_gt0_pct": round(100.0 * float(y0.mean()), 3),
            "n_flipped_r2scan_gt25mev": int(y25.sum()),
            "overall_flip_rate_gt25mev_pct": round(100.0 * float(y25.mean()), 3),
            "roc_auc_uniform_proxy_flip_gt0": _bootstrap_auc_ci(y0, sc_u),
            "roc_auc_hetero_proxy_flip_gt0": _bootstrap_auc_ci(y0, sc_h),
            "roc_auc_uniform_proxy_flip_gt25": _bootstrap_auc_ci(y25, sc_u),
            "roc_auc_hetero_proxy_flip_gt25": _bootstrap_auc_ci(y25, sc_h),
            "flip_gt0_by_uniform_10mev_proxy": _strat_classification_metrics(recs, "p10", "Proxy_High_Risk", "Proxy_Low_Risk", lambda r: r["flipped_gt0"]),
            "flip_gt0_by_uniform_25mev_proxy": _strat_classification_metrics(recs, "p25", "Proxy_High_Risk", "Proxy_Low_Risk", lambda r: r["flipped_gt0"]),
            "flip_gt0_by_uniform_50mev_proxy": _strat_classification_metrics(recs, "p50", "Proxy_High_Risk", "Proxy_Low_Risk", lambda r: r["flipped_gt0"]),
            "flip_gt0_by_hetero_proxy": _strat_classification_metrics(recs, "p_het", "Proxy_High_Risk", "Proxy_Low_Risk", lambda r: r["flipped_gt0"]),
            "flip_gt25mev_by_uniform_25mev_proxy": _strat_classification_metrics(recs, "p25", "Proxy_High_Risk", "Proxy_Low_Risk", lambda r: r["flipped_gt25"]),
            "flip_gt25mev_by_hetero_proxy": _strat_classification_metrics(recs, "p_het", "Proxy_High_Risk", "Proxy_Low_Risk", lambda r: r["flipped_gt25"]),
            "by_chemistry_class": by_chem,
        }

    ext_default = _eval_external_column("pbe_de", "r2_de", "Decomposition Energy Per Atom")
    ext_mp = _eval_external_column("pbe_de_mp", "r2_de_mp", "Decomposition Energy Per Atom MP")
    ext_mpoqmd = _eval_external_column("pbe_de_mp_oqmd", "r2_de_mp_oqmd", "Decomposition Energy Per Atom MP OQMD")

    # 양쪽(PBE 및 r2SCAN) 매칭 TSV 증명서 직렬화 및 Lean 4 + 독립 검증
    tsv_pbe = RESULTS_DIR / "certs_gnome_matched_sample.tsv"
    n_pbe_w = write_certificates_tsv(pbe_certs, tsv_pbe)
    pbe_indep = verify_tsv_independent(tsv_pbe)
    pbe_lean = verify_tsv_with_lean(tsv_pbe)

    tsv_r2 = RESULTS_DIR / "certs_gnome_matched_r2scan_sample.tsv"
    n_r2_w = write_certificates_tsv(r2_certs, tsv_r2)
    r2_indep = verify_tsv_independent(tsv_r2)
    r2_lean = verify_tsv_with_lean(tsv_r2)

    summary = {
        "stage": "gnome_crossval",
        "elapsed_sec": round(time.time() - t0, 2),
        "n_matched_materials": len(matched_pbe_phases),
        "n_dropped_parse": {"pbe": n_pbe_dropped, "r2scan": n_r2_dropped},
        "theorem2_pbe_vs_r2scan_decomposition": t2_res,
        "matched_pbe_intracatalog_summary": _summarize_phase_rows(pbe_rows, "GNoME-Matched-PBE-117k", t_pbe, index_meta=pbe_idx_meta),
        "matched_r2scan_intracatalog_summary": _summarize_phase_rows(r2_rows, "GNoME-Matched-r2SCAN-117k", t_r2, index_meta=r2_idx_meta),
        "matched_117k_exact_hull_validation": a2a_validation,
        "external_proxy_validation_decomp_energy": ext_default,
        "external_proxy_validation_mp": ext_mp,
        "external_proxy_validation_mp_oqmd": ext_mpoqmd,
        "certificate_verification": {
            "matched_pbe": {
                "tsv_file": tsv_pbe.name,
                "tsv_sha256": sha256_file(tsv_pbe),
                "written": n_pbe_w,
                "independent_exact_check": pbe_indep,
                "lean_binary_check": pbe_lean,
            },
            "matched_r2scan": {
                "tsv_file": tsv_r2.name,
                "tsv_sha256": sha256_file(tsv_r2),
                "written": n_r2_w,
                "independent_exact_check": r2_indep,
                "lean_binary_check": r2_lean,
            },
        },
    }

    out_path = RESULTS_DIR / "gnome_crossval_summary.json"
    with open(out_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    print(
        f"[Stage 4 완료] Matched={len(matched_pbe_phases):,}, "
        f"Exact-117k AUC(unif/het)={a2a_validation['roc_auc_eps_unif_for_flip_gt0']['auc']}/{a2a_validation['roc_auc_hetero_scale_for_flip_gt0']['auc']}, "
        f"MonoViol={mono_viol_pbe}, "
        f"Lean PBE={pbe_lean.get('passed')}/{pbe_lean.get('total')}, r2SCAN={r2_lean.get('passed')}/{r2_lean.get('total')}"
    )
    return summary


def run_stage_gnome_pbe_only(workers: int) -> Dict[str, Any]:
    """Stage 5b 단독 실행: GNoME PBE 554,054개 전수 상평형 감사 및 증명서 검증."""
    print("\n================ [Stage 5b] GNoME PBE (554k) 전수 감사 ================")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)
    pbe_phases: List[PhaseEntry] = []
    pbe_cols: Dict[str, Tuple[float, float, float, float]] = {}
    n_pbe_drop = 0
    with open(DATA_DIR / "gnome_stable_materials_summary.csv", "r", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            fe_str = r["Formation Energy Per Atom"]
            try:
                fe_f = float(fe_str)
                if not math.isfinite(fe_f):
                    n_pbe_drop += 1
                    continue
                comp = formula_to_atom_fractions(r["Composition"])
                mid = r["MaterialId"]
                pbe_phases.append(PhaseEntry(mid, r["Composition"], comp, to_fraction(fe_str)))
                pbe_cols[mid] = (
                    _parse_opt_float(r.get("Decomposition Energy Per Atom")),
                    _parse_opt_float(r.get("Decomposition Energy Per Atom All")),
                    _parse_opt_float(r.get("Decomposition Energy Per Atom MP")),
                    _parse_opt_float(r.get("Decomposition Energy Per Atom MP OQMD")),
                )
            except Exception:
                n_pbe_drop += 1

    pbe_rows, pbe_certs, t_pbe, pbe_idx_meta = _run_parallel_phase_audit(
        pbe_phases, "GNoME-PBE-Full-554k", workers=workers, cert_sample_n=5000
    )
    pbe_tsv = RESULTS_DIR / "certs_gnome_pbe_sample.tsv"
    n_pbe_w = write_certificates_tsv(pbe_certs, pbe_tsv)
    pbe_indep = verify_tsv_independent(pbe_tsv)
    pbe_lean = verify_tsv_with_lean(pbe_tsv)

    pbe_summary = _summarize_phase_rows(pbe_rows, "GNoME-PBE-Full (554,054)", t_pbe, index_meta=pbe_idx_meta, n_dropped_parse=n_pbe_drop)

    # 2x2 일관성 및 단조성 검증 (Claude C1 완전 해소):
    # GNoME CSV는 `Decomposition Energy Per Atom All <= 0.001 eV/atom (1 meV)` 인 근접상까지 포함하므로
    # 내부 불안정 137,970건은 전원 1 meV 이내 근접상이며 `ehull_intra <= de_all` 단조성 위반이 0건이어야 함!
    mono_viol = 0
    max_excess_mev = 0.0
    c2x2_de_all = {"cert_stab_de_all_le0": 0, "cert_stab_de_all_gt0": 0, "cert_unstab_de_all_le0": 0, "cert_unstab_de_all_gt0": 0}
    c2x2_de_ext = {"cert_stab_de_le0": 0, "cert_stab_de_gt0": 0, "cert_unstab_de_le0": 0, "cert_unstab_de_gt0": 0}
    unstab_ehulls: List[float] = []
    for r in pbe_rows:
        if r["uncompeted"]:
            continue
        de, de_all, _, _ = pbe_cols[r["id"]]
        if not r["nom_stable"]:
            unstab_ehulls.append(r["ehull_mev"])
        if math.isfinite(de_all):
            excess = r["ehull_mev"] - (de_all * 1000.0)
            if excess > max_excess_mev:
                max_excess_mev = excess
            if excess > 0.5:
                mono_viol += 1
            k1 = ("cert_stab_" if r["nom_stable"] else "cert_unstab_") + ("de_all_le0" if de_all <= 0.0 else "de_all_gt0")
            c2x2_de_all[k1] += 1
        if math.isfinite(de):
            k2 = ("cert_stab_" if r["nom_stable"] else "cert_unstab_") + ("de_le0" if de <= 0.0 else "de_gt0")
            c2x2_de_ext[k2] += 1

    unstab_arr = np.array(unstab_ehulls, dtype=np.float64) if unstab_ehulls else np.array([0.0])
    pbe_summary["monotonicity_and_near_hull_diagnostics"] = {
        "n_violations_ehull_gt_de_all_plus_0_5mev": mono_viol,
        "max_excess_ehull_minus_de_all_mev": round(max_excess_mev, 4),
        "contingency_2x2_vs_de_all": c2x2_de_all,
        "contingency_2x2_vs_de_external": c2x2_de_ext,
        "intracatalog_unstable_ehull_mev_stats": {
            "count": int(len(unstab_ehulls)),
            "median_mev": float(np.median(unstab_arr)),
            "p95_mev": float(np.percentile(unstab_arr, 95)),
            "max_mev": float(np.max(unstab_arr)),
            "le_1mev_pct": float(100.0 * (unstab_arr <= 1.0001).mean()),
        },
    }

    # 외부 GNoME 3개 컬럼(`Decomposition Energy Per Atom`, `... MP`, `... MP OQMD`)별 정확한 프록시 여유 분포
    def _ext_dist(idx_col: int, col_name: str) -> Dict[str, Any]:
        vals = [v[idx_col] for v in pbe_cols.values() if math.isfinite(v[idx_col])]
        margins = np.array([-v * 1000.0 for v in vals if v <= 0.0], dtype=np.float64)
        return {
            "source_column": col_name,
            "n_de_le_0": int(len(margins)),
            "n_de_gt_0": int(sum(1 for v in vals if v > 0.0)),
            "margin_mev_p25": float(np.percentile(margins, 25)) if len(margins) else 0.0,
            "margin_mev_p50": float(np.percentile(margins, 50)) if len(margins) else 0.0,
            "margin_mev_p75": float(np.percentile(margins, 75)) if len(margins) else 0.0,
            "proxy_fragile_10mev_pct": float(100.0 * (margins < 20.0).mean()) if len(margins) else 0.0,
            "proxy_fragile_25mev_pct": float(100.0 * (margins < 50.0).mean()) if len(margins) else 0.0,
            "proxy_fragile_50mev_pct": float(100.0 * (margins < 100.0).mean()) if len(margins) else 0.0,
        }

    pbe_summary["external_decomp_energy_distributions"] = {
        "decomp_energy_per_atom": _ext_dist(0, "Decomposition Energy Per Atom"),
        "decomp_energy_per_atom_mp": _ext_dist(2, "Decomposition Energy Per Atom MP"),
        "decomp_energy_per_atom_mp_oqmd": _ext_dist(3, "Decomposition Energy Per Atom MP OQMD"),
    }
    pbe_summary["certificate_verification"] = {
        "tsv_file": pbe_tsv.name,
        "tsv_sha256": sha256_file(pbe_tsv),
        "written": n_pbe_w,
        "independent_exact_check": pbe_indep,
        "lean_binary_check": pbe_lean,
    }
    with open(RESULTS_DIR / "gnome_pbe_full_summary.json", "w", encoding="utf-8") as f:
        json.dump(pbe_summary, f, indent=2, ensure_ascii=False)

    print(
        f"[Stage 5b 완료] PBE={pbe_summary['n_total']:,} (MonoViol={mono_viol}, "
        f"Lean={pbe_lean.get('passed')}/{pbe_lean.get('total')})"
    )
    return pbe_summary


# ---------------------------------------------------------------------------
# Stage 5: GNoME PBE 554,054개 + r2SCAN 139,541개 전수 상평형 감사
# ---------------------------------------------------------------------------
def run_stage_gnome_full(workers: int) -> Dict[str, Any]:
    print("\n================ [Stage 5] GNoME PBE (554k) + r2SCAN (140k) 전수 감사 ================")
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # 5a. GNoME r2SCAN 전수 (139,541)
    r2_phases: List[PhaseEntry] = []
    r2_de_all_map: Dict[str, float] = {}
    n_r2_drop = 0
    with open(DATA_DIR / "gnome_stable_materials_r2scan.csv", "r", encoding="utf-8") as f:
        for r in csv.DictReader(f):
            fe_str = r["Formation Energy Per Atom"]
            try:
                fe_f = float(fe_str)
                if not math.isfinite(fe_f):
                    n_r2_drop += 1
                    continue
                comp = formula_to_atom_fractions(r["Composition"])
                r2_phases.append(PhaseEntry(r["MaterialId"], r["Composition"], comp, to_fraction(fe_str)))
                de_all = _parse_opt_float(r.get("Decomposition Energy Per Atom All"))
                if math.isfinite(de_all):
                    r2_de_all_map[r["MaterialId"]] = de_all
            except Exception:
                n_r2_drop += 1

    r2_rows, r2_certs, t_r2, r2_idx_meta = _run_parallel_phase_audit(
        r2_phases, "GNoME-r2SCAN-Full-140k", workers=workers, cert_sample_n=5000
    )
    r2_tsv = RESULTS_DIR / "certs_gnome_r2scan_sample.tsv"
    n_r2_w = write_certificates_tsv(r2_certs, r2_tsv)
    r2_indep = verify_tsv_independent(r2_tsv)
    r2_lean = verify_tsv_with_lean(r2_tsv)
    r2_summary = _summarize_phase_rows(r2_rows, "GNoME-r2SCAN-Full (139,541)", t_r2, index_meta=r2_idx_meta, n_dropped_parse=n_r2_drop)
    r2_mono_viol = sum(
        1 for r in r2_rows
        if (not r["uncompeted"]) and r["id"] in r2_de_all_map and (r["ehull_mev"] - r2_de_all_map[r["id"]] * 1000.0) > 0.5
    )
    r2_summary["monotonicity_vs_gnome_de_all_violations_gt_0_5mev"] = r2_mono_viol
    r2_summary["certificate_verification"] = {
        "tsv_file": r2_tsv.name,
        "tsv_sha256": sha256_file(r2_tsv),
        "written": n_r2_w,
        "independent_exact_check": r2_indep,
        "lean_binary_check": r2_lean,
    }
    with open(RESULTS_DIR / "gnome_r2scan_full_summary.json", "w", encoding="utf-8") as f:
        json.dump(r2_summary, f, indent=2, ensure_ascii=False)

    # 5b. GNoME PBE 전수 (554,054)
    pbe_summary = run_stage_gnome_pbe_only(workers)
    print(
        f"[Stage 5 완료] PBE={pbe_summary['n_total']:,}, "
        f"r2SCAN={r2_summary['n_total']:,} (MonoViol={r2_mono_viol}, "
        f"Lean={r2_lean.get('passed')}/{r2_lean.get('total')})"
    )
    return {"gnome_pbe": pbe_summary, "gnome_r2scan": r2_summary}


def main() -> None:
    parser = argparse.ArgumentParser(description="CertMat 대규모 공개 DB 전수 감사 실행기")
    parser.add_argument(
        "--stages",
        nargs="+",
        default=["jarvis_elastic", "jarvis_phase", "wbm_phase", "gnome_crossval", "gnome_full"],
        choices=["jarvis_elastic", "jarvis_phase", "wbm_phase", "gnome_crossval", "gnome_full", "gnome_pbe_only"],
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=2,
        help="병렬 워커 수 (로컬 메인 PC 안전 기본값: 2; 원격 보조 PC 등에서는 최대 8 이하로 명시 지정)",
    )
    args = parser.parse_args()

    _set_below_normal_priority()
    _set_keep_awake(True)
    t_all = time.time()
    try:
        if "jarvis_elastic" in args.stages:
            run_stage_jarvis_elastic(args.workers)
        if "jarvis_phase" in args.stages:
            run_stage_jarvis_phase(args.workers)
        if "wbm_phase" in args.stages:
            run_stage_wbm_phase(args.workers)
        if "gnome_crossval" in args.stages:
            run_stage_gnome_crossval(args.workers)
        if "gnome_full" in args.stages:
            run_stage_gnome_full(args.workers)
        elif "gnome_pbe_only" in args.stages:
            run_stage_gnome_pbe_only(args.workers)
    finally:
        _set_keep_awake(False)

    print(f"\n=== 선택된 모든 감사 단계 완료 (총 소요 {time.time() - t_all:.1f}s) ===")


if __name__ == "__main__":
    main()
