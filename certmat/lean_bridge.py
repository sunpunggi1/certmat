"""
CertMat 증명서 직렬화 및 Lean 4 체커(`certmat-check`) 브리지 모듈.

Python 감사 엔진이 생성한 정확한 유리수 증명서(DUAL_STABLE, PRIMAL_UNSTABLE,
INTERVAL_STABLE, INTERVAL_UNSTABLE, BORN_LDLT, BORN_NON_PD, WEYL_ROBUST)를
`lean/Main.lean` 과 동일한 TSV 프로토콜로 저장하고,
1) 컴파일된 Lean 4 바이너리(`certmat-check`)를 직접 실행해 기계 검증하며,
2) 프로듀서 모듈(`exact_lp`, `elastic_audit`)을 전혀 임포트하지 않는 완전 독립
   순수 `Fraction` 검증기(`verify_tsv_independent`)로 동일 TSV 파일을 재검증하고,
3) `lean.exe --stdin` 의 `#print axioms` 명령으로 모든 핵심 정리의 공리 의존성을
   기계적으로 감사한다(`sorryAx` 및 사용자 정의 공리 0건 확인).
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence

ROOT_DIR = Path(__file__).resolve().parent.parent
LEAN_DIR = ROOT_DIR / "lean"

# Lean 4 `parseStrictInt` / `parseStrictNat` 와 100% 동일한 엄격 ASCII 정규식 ('+5', '1_0', 공백 거부)
_STRICT_INT_RE = re.compile(r"^-?[0-9]+$")
_STRICT_NAT_RE = re.compile(r"^[0-9]+$")

# 기계적으로 공리 의존성을 검증할 CertMat 전체 핵심 정리 목록 (51개)
CORE_LEAN_THEOREMS: List[str] = [
    "CertMat.Q.weighted_cauchy_schwarz",
    "CertMat.farkas_dual_stable_sound",
    "CertMat.farkas_dual_on_hull",
    "CertMat.farkas_primal_unstable_excludes_dual",
    "CertMat.farkas_exact_margin",
    "CertMat.farkas_exact_margin_unique",
    "CertMat.valid_decomp_sum_one",
    "CertMat.ref_error_exact_cancellation",
    "CertMat.ref_error_dual_invariance",
    "CertMat.only_residual_error_flips_stability",
    "CertMat.interval_robust_stable_universal",
    "CertMat.interval_robust_unstable_universal",
    "CertMat.critical_radius_lower_bound",
    "CertMat.critical_radius_lower_bound_nonneg",
    "CertMat.critical_radius_upper_bound_fragile",
    "CertMat.critical_radius_upper_bound_ineq",
    "CertMat.critical_radius_unique",
    "CertMat.interval_fragile_destab_witness",
    "CertMat.interval_fragile_stab_witness",
    "CertMat.born_pd_of_ldlt",
    "CertMat.not_born_pd_of_witness",
    "CertMat.eigenvalue_lower_bound_of_shifted_ldlt",
    "CertMat.weyl_robust_born_pd",
    "CertMat.frobenius_implies_weyl_bound",
    "CertMat.shifted_ldlt_frob_robust_born",
    "CertMat.shifted_ldlt_rayleigh_robust_born",
    "CertMat.weyl_fragile_of_witness",
    "CertMat.weighted_eigenvalue_lower_bound_of_shifted_ldlt",
    "CertMat.weighted_frobenius_implies_weyl_bound",
    "CertMat.weighted_shifted_ldlt_rayleigh_robust_born",
    "CertMat.weighted_shifted_ldlt_frob_robust_born",
    "CertMat.weighted_weyl_fragile_of_witness",
    "CertMat.checkNormalizedComps_sound",
    "CertMat.checkDualStable_sound",
    "CertMat.checkDualStable_on_hull_sound",
    "CertMat.checkPrimalUnstable_sound",
    "CertMat.checkIntervalStable_sound",
    "CertMat.checkIntervalUnstable_sound",
    "CertMat.checkIntervalStableFromNominal_sound",
    "CertMat.checkIntervalUnstableFromNominal_sound",
    "CertMat.checkIntervalFragileDestabFromNominal_sound",
    "CertMat.checkIntervalFragileStabFromNominal_sound",
    "CertMat.checkBornLDLT_sound",
    "CertMat.checkBornNonPD_sound",
    "CertMat.checkWeylRobustBorn_sound",
    "CertMat.checkWeylRobustBorn_rayleigh_sound",
    "CertMat.checkWeylFragile_sound",
    "CertMat.checkMandelWeylRobustBorn_sound",
    "CertMat.checkMandelWeylRobustBorn_frob_sound",
    "CertMat.checkMandelWeylRobustBorn_rayleigh_sound",
    "CertMat.checkMandelWeylFragile_sound",
]

STANDARD_LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def _frac_to_str(q: Fraction) -> str:
    """Lean 4 `certmat-check` 파서가 읽는 `p/q` 또는 `p` 형식 문자열로 직렬화한다."""
    if not isinstance(q, Fraction):
        q = Fraction(q)
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def format_certificate_tsv_line(cert: Dict[str, Any]) -> str:
    """단일 증명서 딕셔너리를 Lean 4 `certmat-check` 호환 탭 구분 문자열로 직렬화한다."""
    kind = cert["kind"]
    f = _frac_to_str
    if kind == "DUAL_STABLE":
        m = int(cert["m"])
        E = int(cert["E"])
        tokens = ["DUAL_STABLE", str(m), str(E), f(cert["ex"]), f(cert["delta"])]
        tokens += [f(x) for x in cert["cx"]]
        tokens += [f(x) for row in cert["c"] for x in row]
        tokens += [f(x) for x in cert["en"]]
        tokens += [f(x) for x in cert["mu"]]
        return "\t".join(tokens)
    if kind == "PRIMAL_UNSTABLE":
        m = int(cert["m"])
        E = int(cert["E"])
        tokens = ["PRIMAL_UNSTABLE", str(m), str(E), f(cert["ex"])]
        tokens += [f(x) for x in cert["cx"]]
        tokens += [f(x) for row in cert["c"] for x in row]
        tokens += [f(x) for x in cert["en"]]
        tokens += [f(x) for x in cert["lam"]]
        return "\t".join(tokens)
    if kind == "INTERVAL_STABLE":
        m = int(cert["m"])
        E = int(cert["E"])
        tokens = [
            "INTERVAL_STABLE", str(m), str(E),
            f(cert["ex"]), f(cert["wx"]), f(cert["eps"]), f(cert["delta"]),
        ]
        tokens += [f(x) for x in cert["cx"]]
        tokens += [f(x) for row in cert["c"] for x in row]
        tokens += [f(x) for x in cert["en"]]
        tokens += [f(x) for x in cert["w"]]
        tokens += [f(x) for x in cert["mu"]]
        return "\t".join(tokens)
    if kind in ("INTERVAL_UNSTABLE", "INTERVAL_FRAGILE_DESTAB"):
        m = int(cert["m"])
        E = int(cert["E"])
        tokens = [
            kind, str(m), str(E),
            f(cert["ex"]), f(cert["wx"]), f(cert["eps"]),
        ]
        tokens += [f(x) for x in cert["cx"]]
        tokens += [f(x) for row in cert["c"] for x in row]
        tokens += [f(x) for x in cert["en"]]
        tokens += [f(x) for x in cert["w"]]
        tokens += [f(x) for x in cert["lam"]]
        return "\t".join(tokens)
    if kind == "INTERVAL_FRAGILE_STAB":
        m = int(cert["m"])
        E = int(cert["E"])
        tokens = [
            "INTERVAL_FRAGILE_STAB", str(m), str(E),
            f(cert["ex"]), f(cert["wx"]), f(cert["eps"]),
        ]
        tokens += [f(x) for x in cert["cx"]]
        tokens += [f(x) for row in cert["c"] for x in row]
        tokens += [f(x) for x in cert["en"]]
        tokens += [f(x) for x in cert["w"]]
        tokens += [f(x) for x in cert["mu"]]
        return "\t".join(tokens)
    if kind == "BORN_LDLT":
        n = int(cert["n"])
        tokens = ["BORN_LDLT", str(n)]
        tokens += [f(x) for row in cert["C"] for x in row]
        tokens += [f(x) for row in cert["L"] for x in row]
        tokens += [f(x) for x in cert["d"]]
        return "\t".join(tokens)
    if kind == "BORN_NON_PD":
        n = int(cert["n"])
        tokens = ["BORN_NON_PD", str(n)]
        tokens += [f(x) for row in cert["C"] for x in row]
        tokens += [f(x) for x in cert["v"]]
        return "\t".join(tokens)
    if kind == "WEYL_ROBUST":
        n = int(cert["n"])
        tokens = ["WEYL_ROBUST", str(n), f(cert["lam0"]), f(cert["delta"])]
        tokens += [f(x) for row in cert["C"] for x in row]
        tokens += [f(x) for row in cert["L"] for x in row]
        tokens += [f(x) for x in cert["d"]]
        return "\t".join(tokens)
    if kind == "WEYL_FRAGILE":
        n = int(cert["n"])
        tokens = ["WEYL_FRAGILE", str(n), f(cert["delta"])]
        tokens += [f(x) for row in cert["C"] for x in row]
        tokens += [f(x) for x in cert["v"]]
        return "\t".join(tokens)
    if kind == "MANDEL_WEYL_ROBUST":
        tokens = ["MANDEL_WEYL_ROBUST", f(cert["lam0"]), f(cert["delta"])]
        tokens += [f(x) for row in cert["C"] for x in row]
        tokens += [f(x) for row in cert["L"] for x in row]
        tokens += [f(x) for x in cert["d"]]
        return "\t".join(tokens)
    if kind == "MANDEL_WEYL_FRAGILE":
        tokens = ["MANDEL_WEYL_FRAGILE", f(cert["delta"])]
        tokens += [f(x) for row in cert["C"] for x in row]
        tokens += [f(x) for x in cert["v"]]
        return "\t".join(tokens)
    raise ValueError(f"지원하지 않는 증명서 종류: {kind}")


def write_certificates_tsv(certs: Iterable[Dict[str, Any]], out_path: Path) -> int:
    """증명서 목록을 TSV 파일로 기록한다(메타데이터가 있으면 직전 줄에 `# META <json>` 데이터 바인딩 주석 기록)."""
    out_path.parent.mkdir(parents=True, exist_ok=True)
    count = 0
    with open(out_path, "w", encoding="utf-8", newline="\n") as fp:
        fp.write("# CertMat Exact Rational Certificates (Lean 4 certmat-check TSV format)\n")
        for cert in certs:
            if cert is None:
                continue
            meta = cert.get("meta")
            if meta is not None:
                fp.write("# META " + json.dumps(meta, ensure_ascii=False, separators=(",", ":")) + "\n")
            fp.write(format_certificate_tsv_line(cert) + "\n")
            count += 1
    return count


# ---------------------------------------------------------------------------
# 프로듀서 모듈과 완전히 분리된 독립 순수 Fraction 파서·검증기
# ---------------------------------------------------------------------------
def _parse_strict_nat(tok: str) -> int:
    if not _STRICT_NAT_RE.match(tok):
        raise ValueError(f"엄격 자연수 형식 위반: {tok!r}")
    return int(tok)


def _parse_strict_q(tok: str) -> Fraction:
    # Lean 4 `parseQ` 와 동일하게 토큰 내부 공백·'+'·'_' 를 모두 엄격 거부
    if "/" in tok:
        parts = tok.split("/")
        if len(parts) != 2:
            raise ValueError(f"유리수 형식 위반: {tok!r}")
        p_str, q_str = parts
        if not _STRICT_INT_RE.match(p_str) or not _STRICT_NAT_RE.match(q_str):
            raise ValueError(f"유리수 정수부/분모부 형식 위반: {tok!r}")
        den = int(q_str)
        if den <= 0:
            raise ValueError(f"분모가 양수가 아닙니다: {tok!r}")
        return Fraction(int(p_str), den)
    if not _STRICT_INT_RE.match(tok):
        raise ValueError(f"정수 형식 위반: {tok!r}")
    return Fraction(int(tok), 1)


def _indep_check_normalized_comps(
    c_mat: Sequence[Sequence[Fraction]], cx: Sequence[Fraction]
) -> bool:
    m = len(c_mat)
    E = len(cx)
    if m <= 0 or E <= 0:
        return False
    if any(x < 0 for x in cx) or sum(cx, Fraction(0)) != 1:
        return False
    for row in c_mat:
        if len(row) != E or any(x < 0 for x in row) or sum(row, Fraction(0)) != 1:
            return False
    return True


def _indep_check_dual_stable(
    c_mat: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    en: Sequence[Fraction],
    ex: Fraction,
    delta: Fraction,
    mu: Sequence[Fraction],
) -> bool:
    if delta < 0:
        return False
    E = len(cx)
    for i, row in enumerate(c_mat):
        dot_val = sum((mu[e] * row[e] for e in range(E)), Fraction(0))
        if dot_val > en[i]:
            return False
    cand_dot = sum((mu[e] * cx[e] for e in range(E)), Fraction(0))
    return (ex + delta) <= cand_dot


def _indep_check_primal_unstable(
    c_mat: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    en: Sequence[Fraction],
    ex: Fraction,
    lam: Sequence[Fraction],
) -> bool:
    m = len(c_mat)
    E = len(cx)
    if any(li < 0 for li in lam):
        return False
    for e in range(E):
        if sum((lam[i] * c_mat[i][e] for i in range(m)), Fraction(0)) != cx[e]:
            return False
    decomp_e = sum((lam[i] * en[i] for i in range(m)), Fraction(0))
    return decomp_e < ex


def _indep_check_born_ldlt(
    C: Sequence[Sequence[Fraction]],
    L: Sequence[Sequence[Fraction]],
    d: Sequence[Fraction],
) -> bool:
    n = len(C)
    if n <= 0 or len(L) != n or len(d) != n:
        return False
    for i in range(n):
        if L[i][i] != 1 or d[i] <= 0:
            return False
        for j in range(i + 1, n):
            if L[i][j] != 0:
                return False
    for i in range(n):
        for j in range(n):
            recon = sum((L[i][k] * d[k] * L[j][k] for k in range(n)), Fraction(0))
            if recon != C[i][j]:
                return False
    return True


def _indep_check_born_non_pd(
    C: Sequence[Sequence[Fraction]], v: Sequence[Fraction]
) -> bool:
    n = len(C)
    if n <= 0 or len(v) != n or not any(x != 0 for x in v):
        return False
    qval = sum((v[i] * C[i][j] * v[j] for i in range(n) for j in range(n)), Fraction(0))
    return qval <= 0


def verify_tsv_independent(tsv_path: Path) -> Dict[str, Any]:
    """TSV 증명서 파일을 프로듀서 코드 없이 처음부터 파싱해 `CertMat.Checker` 명세대로 독립 검증한다."""
    total = 0
    passed = 0
    failed = 0
    by_kind: Dict[str, int] = {}

    with open(tsv_path, "r", encoding="utf-8") as fp:
        for raw in fp:
            line = raw.strip()
            if not line or line.startswith("#"):
                continue
            total += 1
            parts = line.split("\t")
            kind = parts[0]
            by_kind[kind] = by_kind.get(kind, 0) + 1
            ok = False
            try:
                if len(parts) < 2:
                    raise ValueError("too few fields")
                if kind == "DUAL_STABLE":
                    m, E = _parse_strict_nat(parts[1]), _parse_strict_nat(parts[2])
                    if m == 0 or E == 0:
                        raise ValueError("vacuous dimensions")
                    expected = 5 + E + m * E + m + E
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    ex, delta = _parse_strict_q(parts[3]), _parse_strict_q(parts[4])
                    off = 5
                    cx = [_parse_strict_q(x) for x in parts[off : off + E]]; off += E
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + m * E]]; off += m * E
                    c_mat = [c_flat[i * E : (i + 1) * E] for i in range(m)]
                    en = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    mu = [_parse_strict_q(x) for x in parts[off : off + E]]
                    ok = _indep_check_normalized_comps(c_mat, cx) and _indep_check_dual_stable(
                        c_mat, cx, en, ex, delta, mu
                    )
                elif kind == "PRIMAL_UNSTABLE":
                    m, E = _parse_strict_nat(parts[1]), _parse_strict_nat(parts[2])
                    if m == 0 or E == 0:
                        raise ValueError("vacuous dimensions")
                    expected = 4 + E + m * E + m + m
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    ex = _parse_strict_q(parts[3])
                    off = 4
                    cx = [_parse_strict_q(x) for x in parts[off : off + E]]; off += E
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + m * E]]; off += m * E
                    c_mat = [c_flat[i * E : (i + 1) * E] for i in range(m)]
                    en = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    lam = [_parse_strict_q(x) for x in parts[off : off + m]]
                    ok = _indep_check_normalized_comps(c_mat, cx) and _indep_check_primal_unstable(
                        c_mat, cx, en, ex, lam
                    )
                elif kind == "INTERVAL_STABLE":
                    m, E = _parse_strict_nat(parts[1]), _parse_strict_nat(parts[2])
                    if m == 0 or E == 0:
                        raise ValueError("vacuous dimensions")
                    expected = 7 + E + m * E + m + m + E
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    ex = _parse_strict_q(parts[3])
                    wx = _parse_strict_q(parts[4])
                    eps = _parse_strict_q(parts[5])
                    delta = _parse_strict_q(parts[6])
                    off = 7
                    cx = [_parse_strict_q(x) for x in parts[off : off + E]]; off += E
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + m * E]]; off += m * E
                    c_mat = [c_flat[i * E : (i + 1) * E] for i in range(m)]
                    en = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    w = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    mu = [_parse_strict_q(x) for x in parts[off : off + E]]
                    if eps >= 0 and wx >= 0 and all(wi >= 0 for wi in w):
                        L_box = [en[i] - eps * w[i] for i in range(m)]
                        Ux = ex + eps * wx
                        ok = _indep_check_normalized_comps(c_mat, cx) and _indep_check_dual_stable(
                            c_mat, cx, L_box, Ux, delta, mu
                        )
                elif kind in ("INTERVAL_UNSTABLE", "INTERVAL_FRAGILE_DESTAB"):
                    m, E = _parse_strict_nat(parts[1]), _parse_strict_nat(parts[2])
                    if m == 0 or E == 0:
                        raise ValueError("vacuous dimensions")
                    expected = 6 + E + m * E + m + m + m
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    ex = _parse_strict_q(parts[3])
                    wx = _parse_strict_q(parts[4])
                    eps = _parse_strict_q(parts[5])
                    off = 6
                    cx = [_parse_strict_q(x) for x in parts[off : off + E]]; off += E
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + m * E]]; off += m * E
                    c_mat = [c_flat[i * E : (i + 1) * E] for i in range(m)]
                    en = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    w = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    lam = [_parse_strict_q(x) for x in parts[off : off + m]]
                    if eps >= 0 and wx >= 0 and all(wi >= 0 for wi in w):
                        if kind == "INTERVAL_UNSTABLE":
                            box_e = [en[i] + eps * w[i] for i in range(m)]
                            box_x = ex - eps * wx
                        else:
                            box_e = [en[i] - eps * w[i] for i in range(m)]
                            box_x = ex + eps * wx
                        ok = _indep_check_normalized_comps(c_mat, cx) and _indep_check_primal_unstable(
                            c_mat, cx, box_e, box_x, lam
                        )
                elif kind == "INTERVAL_FRAGILE_STAB":
                    m, E = _parse_strict_nat(parts[1]), _parse_strict_nat(parts[2])
                    if m == 0 or E == 0:
                        raise ValueError("vacuous dimensions")
                    expected = 6 + E + m * E + m + m + E
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    ex = _parse_strict_q(parts[3])
                    wx = _parse_strict_q(parts[4])
                    eps = _parse_strict_q(parts[5])
                    off = 6
                    cx = [_parse_strict_q(x) for x in parts[off : off + E]]; off += E
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + m * E]]; off += m * E
                    c_mat = [c_flat[i * E : (i + 1) * E] for i in range(m)]
                    en = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    w = [_parse_strict_q(x) for x in parts[off : off + m]]; off += m
                    mu = [_parse_strict_q(x) for x in parts[off : off + E]]
                    if eps >= 0 and wx >= 0 and all(wi >= 0 for wi in w):
                        U_box = [en[i] + eps * w[i] for i in range(m)]
                        Lx = ex - eps * wx
                        ok = _indep_check_normalized_comps(c_mat, cx) and _indep_check_dual_stable(
                            c_mat, cx, U_box, Lx, Fraction(0), mu
                        )
                elif kind == "BORN_LDLT":
                    n = _parse_strict_nat(parts[1])
                    if n == 0:
                        raise ValueError("vacuous dimension")
                    expected = 2 + n * n + n * n + n
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    off = 2
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + n * n]]; off += n * n
                    l_flat = [_parse_strict_q(x) for x in parts[off : off + n * n]]; off += n * n
                    d = [_parse_strict_q(x) for x in parts[off : off + n]]
                    C = [c_flat[i * n : (i + 1) * n] for i in range(n)]
                    L = [l_flat[i * n : (i + 1) * n] for i in range(n)]
                    ok = _indep_check_born_ldlt(C, L, d)
                elif kind == "BORN_NON_PD":
                    n = _parse_strict_nat(parts[1])
                    if n == 0:
                        raise ValueError("vacuous dimension")
                    expected = 2 + n * n + n
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    off = 2
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + n * n]]; off += n * n
                    v = [_parse_strict_q(x) for x in parts[off : off + n]]
                    C = [c_flat[i * n : (i + 1) * n] for i in range(n)]
                    ok = _indep_check_born_non_pd(C, v)
                elif kind == "WEYL_ROBUST":
                    n = _parse_strict_nat(parts[1])
                    if n == 0:
                        raise ValueError("vacuous dimension")
                    expected = 4 + n * n + n * n + n
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    lam0, delta = _parse_strict_q(parts[2]), _parse_strict_q(parts[3])
                    off = 4
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + n * n]]; off += n * n
                    l_flat = [_parse_strict_q(x) for x in parts[off : off + n * n]]; off += n * n
                    d = [_parse_strict_q(x) for x in parts[off : off + n]]
                    C = [c_flat[i * n : (i + 1) * n] for i in range(n)]
                    L = [l_flat[i * n : (i + 1) * n] for i in range(n)]
                    C_shift = [
                        [C[i][j] - lam0 if i == j else C[i][j] for j in range(n)]
                        for i in range(n)
                    ]
                    ok = _indep_check_born_ldlt(C_shift, L, d) and (0 <= delta <= lam0)
                elif kind == "WEYL_FRAGILE":
                    n = _parse_strict_nat(parts[1])
                    if n == 0:
                        raise ValueError("vacuous dimension")
                    expected = 3 + n * n + n
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    delta = _parse_strict_q(parts[2])
                    off = 3
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + n * n]]; off += n * n
                    v = [_parse_strict_q(x) for x in parts[off : off + n]]
                    C = [c_flat[i * n : (i + 1) * n] for i in range(n)]
                    if delta >= 0 and any(x != 0 for x in v):
                        ns = sum((x * x for x in v), Fraction(0))
                        qval = sum((v[i] * C[i][j] * v[j] for i in range(n) for j in range(n)), Fraction(0))
                        ok = qval <= delta * ns
                elif kind == "MANDEL_WEYL_ROBUST":
                    expected = 3 + 36 + 36 + 6
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    lam0, delta = _parse_strict_q(parts[1]), _parse_strict_q(parts[2])
                    off = 3
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + 36]]; off += 36
                    l_flat = [_parse_strict_q(x) for x in parts[off : off + 36]]; off += 36
                    d = [_parse_strict_q(x) for x in parts[off : off + 6]]
                    C = [c_flat[i * 6 : (i + 1) * 6] for i in range(6)]
                    L = [l_flat[i * 6 : (i + 1) * 6] for i in range(6)]
                    mweights = [Fraction(1), Fraction(1), Fraction(1), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)]
                    C_shift = [
                        [C[i][j] - lam0 * mweights[i] if i == j else C[i][j] for j in range(6)]
                        for i in range(6)
                    ]
                    ok = _indep_check_born_ldlt(C_shift, L, d) and (0 <= delta <= lam0)
                elif kind == "MANDEL_WEYL_FRAGILE":
                    expected = 2 + 36 + 6
                    if len(parts) != expected:
                        raise ValueError("token count mismatch")
                    delta = _parse_strict_q(parts[1])
                    off = 2
                    c_flat = [_parse_strict_q(x) for x in parts[off : off + 36]]; off += 36
                    v = [_parse_strict_q(x) for x in parts[off : off + 6]]
                    C = [c_flat[i * 6 : (i + 1) * 6] for i in range(6)]
                    if delta >= 0 and any(x != 0 for x in v):
                        mweights = [Fraction(1), Fraction(1), Fraction(1), Fraction(1, 2), Fraction(1, 2), Fraction(1, 2)]
                        wns = sum((mweights[i] * v[i] * v[i] for i in range(6)), Fraction(0))
                        qval = sum((v[i] * C[i][j] * v[j] for i in range(6) for j in range(6)), Fraction(0))
                        ok = qval <= delta * wns
            except Exception:
                ok = False
            if ok:
                passed += 1
            else:
                failed += 1

    return {
        "tsv_path": str(tsv_path),
        "total": total,
        "passed": passed,
        "failed": failed,
        "by_kind": by_kind,
        "all_passed": (failed == 0 and total > 0),
    }


# ---------------------------------------------------------------------------
# Lean 4 툴체인·바이너리 탐색, 실행 검증 및 #print axioms 감사
# ---------------------------------------------------------------------------
def build_lean_kernel(lean_dir: Path = LEAN_DIR) -> Dict[str, Any]:
    """`lake build` 및 `lake build certmat-check` 를 실행해 Lean 4 커널(`.olean`)과 체커 바이너리를 빌드한다."""
    tbin = find_lean_toolchain_bin()
    if tbin is None:
        return {"lean_available": False, "built": False, "error": "lean/lake toolchain not found"}
    lake_exe = tbin / ("lake.exe" if os.name == "nt" else "lake")
    env = dict(os.environ)
    env["PATH"] = str(tbin) + os.pathsep + env.get("PATH", "")
    try:
        res1 = subprocess.run(
            [str(lake_exe), "build"],
            cwd=str(lean_dir),
            capture_output=True,
            text=True,
            env=env,
            timeout=300,
        )
        if res1.returncode != 0:
            return {"lean_available": True, "built": False, "error": res1.stderr[-1000:]}
        res2 = subprocess.run(
            [str(lake_exe), "build", "certmat-check"],
            cwd=str(lean_dir),
            capture_output=True,
            text=True,
            env=env,
            timeout=300,
        )
        if res2.returncode != 0:
            return {"lean_available": True, "built": False, "error": res2.stderr[-1000:]}
    except subprocess.TimeoutExpired:
        return {"lean_available": True, "built": False, "error": "lake build timed out"}
    exe = find_lean_checker_binary(lean_dir)
    return {
        "lean_available": True,
        "built": (exe is not None),
        "binary": str(exe) if exe else None,
    }


def find_lean_toolchain_bin() -> Optional[Path]:
    """PATH 또는 프로젝트 내장 `.tools/lean-*/bin` 에서 Lean 4 툴체인 경로를 탐색한다."""
    lake_in_path = shutil.which("lake")
    if lake_in_path:
        return Path(lake_in_path).resolve().parent
    tools_dir = ROOT_DIR / ".tools"
    if tools_dir.exists():
        for cand in sorted(tools_dir.glob("lean-*/bin"), reverse=True):
            if (cand / "lean.exe").exists() or (cand / "lean").exists():
                return cand
    return None


def find_lean_checker_binary(lean_dir: Path = LEAN_DIR) -> Optional[Path]:
    """컴파일된 Lean 4 `certmat-check` 실행 파일을 탐색한다."""
    candidates = [
        lean_dir / ".lake" / "build" / "bin" / "certmat-check.exe",
        lean_dir / ".lake" / "build" / "bin" / "certmat-check",
    ]
    for p in candidates:
        if p.exists():
            return p
    return None


def verify_lean_axioms(lean_dir: Path = LEAN_DIR) -> Dict[str, Any]:
    """컴파일된 Lean 4 커널(`.olean`)에 `#print axioms` 를 실행해 `sorryAx`·사용자 정의 공리 0건을 기계 검증한다."""
    tbin = find_lean_toolchain_bin()
    if tbin is None:
        return {"lean_available": False, "all_standard_axioms_only": False, "reason": "lean binary not found"}
    lean_exe = tbin / ("lean.exe" if os.name == "nt" else "lean")
    lib_dir = lean_dir / ".lake" / "build" / "lib"
    if not (lib_dir / "CertMat.olean").exists():
        return {"lean_available": True, "all_standard_axioms_only": False, "reason": "CertMat.olean not built"}

    script = "import CertMat\n" + "\n".join(f"#print axioms {thm}" for thm in CORE_LEAN_THEOREMS) + "\n"
    env = dict(os.environ)
    env["LEAN_PATH"] = str(lib_dir)
    env["PATH"] = str(tbin) + os.pathsep + env.get("PATH", "")

    try:
        res = subprocess.run(
            [str(lean_exe), "--stdin"],
            input=script,
            capture_output=True,
            text=True,
            env=env,
            timeout=120,
        )
    except subprocess.TimeoutExpired:
        return {"lean_available": True, "all_standard_axioms_only": False, "error": "lean #print axioms timed out"}

    theorems: Dict[str, List[str]] = {}
    non_standard: Dict[str, List[str]] = {}
    for line in res.stdout.splitlines():
        m = re.match(r"^'([^']+)' depends on axioms: \[([^\]]*)\]$", line.strip())
        if m:
            thm = m.group(1)
            axs = [a.strip() for a in m.group(2).split(",") if a.strip()]
            theorems[thm] = axs
            bad = [a for a in axs if a not in STANDARD_LEAN_AXIOMS]
            if bad:
                non_standard[thm] = bad
        else:
            m0 = re.match(r"^'([^']+)' does not depend on any axioms$", line.strip())
            if m0:
                theorems[m0.group(1)] = []

    missing = [t for t in CORE_LEAN_THEOREMS if t not in theorems]
    return {
        "lean_available": True,
        "returncode": res.returncode,
        "n_theorems_checked": len(theorems),
        "n_theorems_expected": len(CORE_LEAN_THEOREMS),
        "missing_theorems": missing,
        "non_standard_axioms": non_standard,
        "zero_sorry_ax": all("sorryAx" not in axs for axs in theorems.values()),
        "all_standard_axioms_only": (
            res.returncode == 0 and len(missing) == 0 and len(non_standard) == 0
        ),
        "theorems": theorems,
    }


def verify_tsv_with_lean(
    tsv_path: Path, lean_dir: Path = LEAN_DIR, allow_build: bool = False
) -> Dict[str, Any]:
    """컴파일된 Lean 4 `certmat-check` 바이너리로 TSV 증명서를 기계 검증한다."""
    exe = find_lean_checker_binary(lean_dir)
    if exe is None and allow_build:
        tbin = find_lean_toolchain_bin()
        if tbin is not None:
            lake_exe = tbin / ("lake.exe" if os.name == "nt" else "lake")
            env = dict(os.environ)
            env["PATH"] = str(tbin) + os.pathsep + env.get("PATH", "")
            try:
                build = subprocess.run(
                    [str(lake_exe), "build", "certmat-check"],
                    cwd=str(lean_dir),
                    capture_output=True,
                    text=True,
                    env=env,
                    timeout=300,
                )
            except subprocess.TimeoutExpired:
                return {"lean_available": True, "lean_built": False, "all_passed": False, "error": "lake build timed out"}
            if build.returncode == 0:
                exe = find_lean_checker_binary(lean_dir)
            else:
                return {
                    "lean_available": True,
                    "lean_built": False,
                    "all_passed": False,
                    "error": build.stderr[-1000:],
                }

    if exe is None:
        return {
            "lean_available": False,
            "lean_built": False,
            "all_passed": False,
            "reason": "Lean 4 certmat-check binary not found",
        }

    try:
        res = subprocess.run(
            [str(exe), str(tsv_path)],
            capture_output=True,
            text=True,
            timeout=300,
        )
    except subprocess.TimeoutExpired:
        return {
            "lean_available": True,
            "lean_built": True,
            "all_passed": False,
            "error": "certmat-check execution timed out",
        }

    total, passed, failed = 0, 0, 0
    m = re.search(r"total=(\d+)\s+passed=(\d+)\s+failed=(\d+)", res.stdout)
    if m:
        total, passed, failed = int(m.group(1)), int(m.group(2)), int(m.group(3))

    return {
        "lean_available": True,
        "lean_built": True,
        "binary": str(exe),
        "returncode": res.returncode,
        "total": total,
        "passed": passed,
        "failed": failed,
        "stdout": res.stdout.strip(),
        "stderr": res.stderr.strip(),
        "all_passed": (res.returncode == 0 and failed == 0 and total > 0 and passed == total),
    }
