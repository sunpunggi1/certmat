"""
CertMat 6x6 탄성 텐서 Born 안정성 및 결정계 대칭성 정확 감사 엔진.

핵심 기능:
1. 정확한 유리수 LDL^T 분해 (정리 4a):
   C_sym = L · diag(d) · L^T (d_k > 0) 를 순수 Fraction 연산으로 분해 및 재조립 검증.
2. 정확한 유리수 비양정치 반례 벡터 v 합성 (정리 4b):
   LDL^T 가 비양수 피벗 d_k ≤ 0 에서 실패하면 L^T u = e_k 역치환으로
   정확한 비영 유리수 반례 벡터 v ∈ Q^6 (v^T C v ≤ 0) 를 100% 결정적으로 합성.
3. 이동 LDL^T 기반 Weyl 섭동 강건 Born 안정성 감사 (정리 4c):
   응력/탄성 텐서 오차 δ ∈ {1, 5, 10} GPa 하에서 C - δ I 의 정확한 유리수 LDL^T 존재 여부를
   인증하여 취약 결정(Mechanically Fragile Crystals)을 검출.
   (Voigt 6x6 및 SO(3)-회전불변 Mandel/Kelvin 6x6 고유값 하한을 모두 산출)
4. 결정계 대칭성 위반 감사:
   - 행렬 대칭성 위반 ‖C - C^T‖_∞ (좌표계 무관)
   - 공간군(spg_number) 기반 표준 Voigt 0-성분 및 등식 제약 위반 (cubic, hexagonal, tetragonal,
     trigonal, orthorhombic, monoclinic b/c-unique)
   - 입방정(cubic)의 SO(3)-회전불변 Mandel 고유값 축퇴(1, 2, 3중 축퇴) 위반 검사
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

from certmat.exact_lp import to_fraction


def exact_ldlt_or_counterexample(
    C: Sequence[Sequence[Fraction]],
) -> Tuple[bool, Optional[List[List[Fraction]]], Optional[List[Fraction]], Optional[List[Fraction]]]:
    """대칭 행렬 C ∈ Q^{n×n} (n ≥ 1) 에 대해:
    - 엄격 양정치이면 (True, L, d, None) 반환 (C = L diag(d) L^T, ∀k d_k > 0 정확 성립)
    - 비양정치이면 (False, None, None, v) 반환 (v ≠ 0, v^T C v ≤ 0 정확 성립)
    """
    n = len(C)
    if n == 0 or any(len(row) != n for row in C):
        raise ValueError(f"비어 있거나 정방 행렬이 아닙니다: n={n}")
    for i in range(n):
        for j in range(i + 1, n):
            if C[i][j] != C[j][i]:
                raise ValueError(f"비대칭 행렬이 입력되었습니다 ({i},{j}): {C[i][j]} != {C[j][i]}")
    L = [[Fraction(1) if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    d = [Fraction(0) for _ in range(n)]

    for k in range(n):
        # d_k = C_kk - ∑_{j < k} L_kj^2 d_j
        dk = C[k][k] - sum(L[k][j] * L[k][j] * d[j] for j in range(k))
        if dk <= 0:
            # 비양정치 반례 벡터 v 구성: 상삼각 L_{0..k}^T u = e_k 역치환
            v = [Fraction(0) for _ in range(n)]
            v[k] = Fraction(1)
            for i in range(k - 1, -1, -1):
                v[i] = -sum(L[j][i] * v[j] for j in range(i + 1, k + 1))
            # 엄격 검증: v^T C v == dk ≤ 0 (-O 최적화에서도 생략되지 않도록 명시적 예외 사용)
            qval = quad_form_exact(C, v)
            if qval != dk or qval > 0:
                raise RuntimeError(f"LDL^T 반례 검증 불일치: {qval} vs {dk}")
            return False, None, None, v

        d[k] = dk
        for i in range(k + 1, n):
            s = C[i][k] - sum(L[i][j] * d[j] * L[k][j] for j in range(k))
            L[i][k] = s / dk

    # 정확 재조립 검증: ∀ i, j, C_ij == ∑_k L_ik d_k L_jk
    for i in range(n):
        for j in range(n):
            recon = sum(L[i][k] * d[k] * L[j][k] for k in range(n))
            if recon != C[i][j]:
                raise RuntimeError(f"LDL^T 정확 재조립 실패 ({i},{j}): {recon} != {C[i][j]}")
    return True, L, d, None


def quad_form_exact(C: Sequence[Sequence[Fraction]], v: Sequence[Fraction]) -> Fraction:
    """정확한 유리수 이차 형식 v^T C v 계산."""
    n = len(v)
    return sum(v[i] * C[i][j] * v[j] for i in range(n) for j in range(n))


MANDEL_WEIGHTS: Tuple[Fraction, ...] = (
    Fraction(1, 1), Fraction(1, 1), Fraction(1, 1),
    Fraction(1, 2), Fraction(1, 2), Fraction(1, 2),
)


def shift_matrix_exact(C: Sequence[Sequence[Fraction]], lam0: Fraction) -> List[List[Fraction]]:
    """이동 행렬 C - lam0 * I 계산."""
    n = len(C)
    return [
        [C[i][j] - lam0 if i == j else C[i][j] for j in range(n)]
        for i in range(n)
    ]


def weighted_shift_matrix_exact(
    C: Sequence[Sequence[Fraction]],
    lam0: Fraction,
    weights: Sequence[Fraction] = MANDEL_WEIGHTS,
) -> List[List[Fraction]]:
    """대각 가중 이동 행렬 C - lam0 * diag(weights) 계산.

    weights = (1, 1, 1, 1/2, 1/2, 1/2) 일 때 Sylvester 관성 법칙에 의해
    C_Mandel - lam0 * I ≻ 0  ⟺  C_Voigt - lam0 * diag(1,1,1,1/2,1/2,1/2) ≻ 0 이
    무리수 √2 없이 100% 정확한 유리수 산술로 성립한다.
    """
    n = len(C)
    return [
        [C[i][j] - lam0 * weights[i] if i == j else C[i][j] for j in range(n)]
        for i in range(n)
    ]


def verify_weyl_fragile_certificate(
    C: Sequence[Sequence[Fraction]], delta: Fraction, v: Sequence[Fraction]
) -> bool:
    """Lean 4 `checkWeylFragile` 와 동일한 정확한 유리수 Weyl 취약성 반례 검증기."""
    if delta < 0 or not any(x != 0 for x in v):
        return False
    ns = sum(x * x for x in v)
    return quad_form_exact(C, v) <= delta * ns


def verify_mandel_weyl_fragile_certificate(
    C: Sequence[Sequence[Fraction]],
    delta: Fraction,
    v: Sequence[Fraction],
    weights: Sequence[Fraction] = MANDEL_WEIGHTS,
) -> bool:
    """Lean 4 `checkMandelWeylFragile` 와 동일한 순수 유리수 SO(3)-불변 Mandel 취약성 반례 검증기."""
    if len(C) != 6 or len(v) != 6 or delta < 0 or not any(x != 0 for x in v):
        return False
    wns = sum((weights[i] * v[i] * v[i] for i in range(6)), Fraction(0))
    return quad_form_exact(C, v) <= delta * wns


def verify_ldlt_certificate(
    C: Sequence[Sequence[Fraction]],
    L: Sequence[Sequence[Fraction]],
    d: Sequence[Fraction],
) -> bool:
    """Lean 4 `checkBornLDLT` 와 동일한 정확한 유리수 LDL^T 검증기."""
    n = len(C)
    if len(L) != n or len(d) != n:
        return False
    for i in range(n):
        if L[i][i] != 1:
            return False
        for j in range(i + 1, n):
            if L[i][j] != 0:
                return False
        if d[i] <= 0:
            return False
    for i in range(n):
        for j in range(n):
            if C[i][j] != sum(L[i][k] * d[k] * L[j][k] for k in range(n)):
                return False
    return True


def verify_non_pd_certificate(
    C: Sequence[Sequence[Fraction]], v: Sequence[Fraction]
) -> bool:
    """Lean 4 `checkBornNonPD` 와 동일한 정확한 유리수 비양정치 반례 검증기."""
    if not any(x != 0 for x in v):
        return False
    return quad_form_exact(C, v) <= 0


def crystal_system_from_spg(spg_number: Optional[int]) -> str:
    """국제 공간군 번호(1-230)로부터 결정계(Laue 대칭군 포함)를 판별한다."""
    if spg_number is None or spg_number < 1 or spg_number > 230:
        return "unknown"
    if spg_number <= 2:
        return "triclinic"
    if spg_number <= 15:
        return "monoclinic"
    if spg_number <= 74:
        return "orthorhombic"
    if spg_number <= 88:
        return "tetragonal_low"
    if spg_number <= 142:
        return "tetragonal_high"
    if spg_number <= 148:
        return "trigonal_low"
    if spg_number <= 167:
        return "trigonal_high"
    if spg_number <= 194:
        return "hexagonal"
    return "cubic"


def _upper_pairs_not_in(allowed: set[Tuple[int, int]]) -> List[Tuple[int, int]]:
    """0-기반 상삼각 (i <= j) 중 허용 집합에 없는 0-성분 쌍 목록을 반환한다."""
    zeros = []
    for i in range(6):
        for j in range(i, 6):
            if (i, j) not in allowed:
                zeros.append((i, j))
    return zeros


# IEEE 표준 Voigt 0-기반 인덱스 (0=11, 1=22, 2=33, 3=44(yz), 4=55(xz), 5=66(xy))
_DIAG_AND_UL = {(0, 0), (1, 1), (2, 2), (0, 1), (0, 2), (1, 2), (3, 3), (4, 4), (5, 5)}

_ALLOWED_NONZERO = {
    "cubic": _DIAG_AND_UL,
    "hexagonal": _DIAG_AND_UL,
    "tetragonal_high": _DIAG_AND_UL,
    "tetragonal_low": _DIAG_AND_UL | {(0, 5), (1, 5)},
    # 삼방정계(고대칭 32, 3m, -3m): 2회 대칭축이 x축(C14!=0) 또는 y축(C15!=0)인 두 표준 설정 모두 허용
    "trigonal_high_x": _DIAG_AND_UL | {(0, 3), (1, 3), (4, 5)},
    "trigonal_high_y": _DIAG_AND_UL | {(0, 4), (1, 4), (3, 5)},
    "trigonal_low": _DIAG_AND_UL | {(0, 3), (1, 3), (4, 5), (0, 4), (1, 4), (3, 5)},
    "orthorhombic": _DIAG_AND_UL,
    # 단사정계는 a-고유축(JARVIS 표준 포함), b-고유축, c-고유축 세 표준 설정 모두 허용하고 최소 위반 채택
    "monoclinic_a": _DIAG_AND_UL | {(0, 3), (1, 3), (2, 3), (4, 5)},
    "monoclinic_b": _DIAG_AND_UL | {(0, 4), (1, 4), (2, 4), (3, 5)},
    "monoclinic_c": _DIAG_AND_UL | {(0, 5), (1, 5), (2, 5), (3, 4)},
}

# VASP OUTCAR 전단 성분 순서 (XX, YY, ZZ, XY, YZ, ZX) -> IEEE Voigt 순서 (XX, YY, ZZ, YZ, ZX, XY) 치환
_VASP_TO_IEEE_PERM = [0, 1, 2, 4, 5, 3]


def _eval_ieee_voigt_violations(C: np.ndarray, csys: str) -> Tuple[float, float]:
    """이미 IEEE Voigt 순서 (XX, YY, ZZ, YZ, ZX, XY)로 정렬된 대칭 행렬 C의 0-성분·등식 위반을 계산한다."""
    def _eval_zero(key: str) -> float:
        zs = _upper_pairs_not_in(_ALLOWED_NONZERO[key])
        return max((abs(float(C[i, j])) for i, j in zs), default=0.0)

    if csys == "cubic":
        max_zero_viol = _eval_zero("cubic")
        eqs = [
            abs(C[0, 0] - C[1, 1]), abs(C[0, 0] - C[2, 2]), abs(C[1, 1] - C[2, 2]),
            abs(C[0, 1] - C[0, 2]), abs(C[0, 1] - C[1, 2]), abs(C[0, 2] - C[1, 2]),
            abs(C[3, 3] - C[4, 4]), abs(C[3, 3] - C[5, 5]), abs(C[4, 4] - C[5, 5]),
        ]
        return max_zero_viol, float(max(eqs))
    if csys == "hexagonal":
        max_zero_viol = _eval_zero("hexagonal")
        eqs = [
            abs(C[0, 0] - C[1, 1]),
            abs(C[0, 2] - C[1, 2]),
            abs(C[3, 3] - C[4, 4]),
            abs(C[5, 5] - 0.5 * (C[0, 0] - C[0, 1])),
        ]
        return max_zero_viol, float(max(eqs))
    if csys == "tetragonal_high":
        max_zero_viol = _eval_zero("tetragonal_high")
        eqs = [abs(C[0, 0] - C[1, 1]), abs(C[0, 2] - C[1, 2]), abs(C[3, 3] - C[4, 4])]
        return max_zero_viol, float(max(eqs))
    if csys == "tetragonal_low":
        max_zero_viol = _eval_zero("tetragonal_low")
        eqs = [
            abs(C[0, 0] - C[1, 1]),
            abs(C[0, 2] - C[1, 2]),
            abs(C[3, 3] - C[4, 4]),
            abs(C[0, 5] + C[1, 5]),
        ]
        return max_zero_viol, float(max(eqs))
    if csys == "trigonal_high":
        z_x = _eval_zero("trigonal_high_x")
        eq_x = float(max([
            abs(C[0, 0] - C[1, 1]),
            abs(C[0, 2] - C[1, 2]),
            abs(C[3, 3] - C[4, 4]),
            abs(C[5, 5] - 0.5 * (C[0, 0] - C[0, 1])),
            abs(C[0, 3] + C[1, 3]),
            abs(C[0, 3] - C[4, 5]),
        ]))
        z_y = _eval_zero("trigonal_high_y")
        eq_y = float(max([
            abs(C[0, 0] - C[1, 1]),
            abs(C[0, 2] - C[1, 2]),
            abs(C[3, 3] - C[4, 4]),
            abs(C[5, 5] - 0.5 * (C[0, 0] - C[0, 1])),
            abs(C[0, 4] + C[1, 4]),
            abs(C[0, 4] + C[3, 5]),
        ]))
        return (z_x, eq_x) if max(z_x, eq_x) <= max(z_y, eq_y) else (z_y, eq_y)
    if csys == "trigonal_low":
        max_zero_viol = _eval_zero("trigonal_low")
        eqs = [
            abs(C[0, 0] - C[1, 1]),
            abs(C[0, 2] - C[1, 2]),
            abs(C[3, 3] - C[4, 4]),
            abs(C[5, 5] - 0.5 * (C[0, 0] - C[0, 1])),
            abs(C[0, 3] + C[1, 3]),
            abs(C[0, 3] - C[4, 5]),
            abs(C[0, 4] + C[1, 4]),
            abs(C[0, 4] + C[3, 5]),
        ]
        return max_zero_viol, float(max(eqs))
    if csys == "orthorhombic":
        return _eval_zero("orthorhombic"), 0.0
    if csys == "monoclinic":
        return min(
            _eval_zero("monoclinic_a"),
            _eval_zero("monoclinic_b"),
            _eval_zero("monoclinic_c"),
        ), 0.0
    return 0.0, 0.0


def _build_voigt_rotation_matrix(R: np.ndarray) -> np.ndarray:
    """3x3 직교 회전 행렬 R 에 대응하는 6x6 IEEE Voigt 응력/강성 변환 행렬 M (C' = M C M^T) 을 생성한다."""
    voigt = [(0, 0), (1, 1), (2, 2), (1, 2), (0, 2), (0, 1)]
    M = np.zeros((6, 6), dtype=np.float64)
    for a, (i, j) in enumerate(voigt):
        for b, (p, q) in enumerate(voigt):
            if p == q:
                M[a, b] = R[i, p] * R[j, p]
            else:
                M[a, b] = R[i, p] * R[j, q] + R[i, q] * R[j, p]
    return M


# 단축 결정계(정방·육방·삼방정계)의 주축 순환 치환 (c||z, c||x, c||y) 및 삼방정계 능면체 [111] 회전 행렬
_M_AXIS_Z = np.eye(6, dtype=np.float64)
_M_AXIS_X = _build_voigt_rotation_matrix(np.array([[0.0, 1.0, 0.0], [0.0, 0.0, 1.0], [1.0, 0.0, 0.0]]))
_M_AXIS_Y = _build_voigt_rotation_matrix(np.array([[0.0, 0.0, 1.0], [1.0, 0.0, 0.0], [0.0, 1.0, 0.0]]))
_E3_RHOM = np.array([1.0, 1.0, 1.0], dtype=np.float64) / np.sqrt(3.0)
_E1_RHOM = np.array([1.0, -1.0, 0.0], dtype=np.float64) / np.sqrt(2.0)
_E2_RHOM = np.cross(_E3_RHOM, _E1_RHOM)
_M_RHOM_111 = _build_voigt_rotation_matrix(np.vstack([_E1_RHOM, _E2_RHOM, _E3_RHOM]))


def _eval_ieee_voigt_with_setting(C: np.ndarray, csys: str) -> Tuple[float, float, float, float, str]:
    """IEEE Voigt 대칭 행렬 C 의 (1) 표준 z-축 기준 위반과 (2) 표준 축 치환/설정 허용 최소 위반 및 채택 설정명을 반환한다.

    반환값: (best_zero, best_eq, std_z_zero, std_z_eq, matched_setting)
    """
    std_z, std_e = _eval_ieee_voigt_violations(C, csys)
    if csys == "monoclinic":
        opts = [
            ("monoclinic_a", max((abs(float(C[i, j])) for i, j in _upper_pairs_not_in(_ALLOWED_NONZERO["monoclinic_a"])), default=0.0)),
            ("monoclinic_b", max((abs(float(C[i, j])) for i, j in _upper_pairs_not_in(_ALLOWED_NONZERO["monoclinic_b"])), default=0.0)),
            ("monoclinic_c", max((abs(float(C[i, j])) for i, j in _upper_pairs_not_in(_ALLOWED_NONZERO["monoclinic_c"])), default=0.0)),
        ]
        best_name, best_z = min(opts, key=lambda x: x[1])
        return best_z, 0.0, opts[1][1], 0.0, best_name

    if csys in ("tetragonal_high", "tetragonal_low", "hexagonal", "trigonal_high", "trigonal_low"):
        candidates: List[Tuple[str, float, float]] = [("c_axis_z", std_z, std_e)]
        for label, M in (("c_axis_x", _M_AXIS_X), ("c_axis_y", _M_AXIS_Y)):
            Cr = M @ C @ M.T
            zr, er = _eval_ieee_voigt_violations(Cr, csys)
            candidates.append((label, zr, er))
        if csys in ("trigonal_high", "trigonal_low"):
            Cr = _M_RHOM_111 @ C @ _M_RHOM_111.T
            zr, er = _eval_ieee_voigt_violations(Cr, csys)
            candidates.append(("rhombohedral_111", zr, er))
        best_label, bz, be = min(candidates, key=lambda x: max(x[1], x[2]))
        return bz, be, std_z, std_e, best_label

    return std_z, std_e, std_z, std_e, "standard"


def compute_voigt_symmetry_violations(
    C_raw: np.ndarray, spg_number: Optional[int], convention: str = "ieee"
) -> Dict[str, object]:
    """Voigt 탄성 텐서의 행렬 대칭 위반, 결정계 0-성분/등식 위반(표준축 및 축치환 기준),
    및 입방정 SO(3)-회전불변 Mandel 고유값 축퇴 필요조건 위반을 계산한다.

    주의: 결정계 템플릿 검사는 결정 축 정렬(coordinate frame)에 의존하므로 단축계(정방·육방·삼방)의
    순환 축 치환(c||z, c||x, c||y)과 삼방정 능면체 [111], 단사정계 a/b/c 고유축 설정을 모두 평가하고
    실제 채택된 설정명(`matched_setting`)과 고정 표준축 위반(`max_voigt_violation_fixed_std_gpa`)을 함께 기록한다.
    """
    max_asym = float(np.max(np.abs(C_raw - C_raw.T)))
    C = 0.5 * (C_raw + C_raw.T)
    csys = crystal_system_from_spg(spg_number)

    if convention == "ieee":
        max_zero_viol, max_eq_viol, std_z, std_e, setting = _eval_ieee_voigt_with_setting(C, csys)
        used_conv = "ieee"
    elif convention == "vasp":
        C_ieee = C[np.ix_(_VASP_TO_IEEE_PERM, _VASP_TO_IEEE_PERM)]
        max_zero_viol, max_eq_viol, std_z, std_e, setting = _eval_ieee_voigt_with_setting(C_ieee, csys)
        used_conv = "vasp"
    elif convention == "auto":
        z1, e1, sz1, se1, st1 = _eval_ieee_voigt_with_setting(C, csys)
        C_ieee = C[np.ix_(_VASP_TO_IEEE_PERM, _VASP_TO_IEEE_PERM)]
        z2, e2, sz2, se2, st2 = _eval_ieee_voigt_with_setting(C_ieee, csys)
        if max(z1, e1) <= max(z2, e2):
            max_zero_viol, max_eq_viol, std_z, std_e, setting, used_conv = z1, e1, sz1, se1, st1, "ieee"
        else:
            max_zero_viol, max_eq_viol, std_z, std_e, setting, used_conv = z2, e2, sz2, se2, st2, "vasp"
    else:
        raise ValueError(f"알 수 없는 탄성 텐서 순서 규약: {convention}")

    # SO(3)-회전불변 Mandel/Kelvin 텐서 고유값 계산: C_Mandel = D C D, D = diag(1,1,1,sqrt(2),sqrt(2),sqrt(2))
    D = np.diag([1.0, 1.0, 1.0, np.sqrt(2.0), np.sqrt(2.0), np.sqrt(2.0)])
    C_mandel = D @ C @ D
    eigs_voigt = np.linalg.eigvalsh(C)
    eigs_mandel = np.linalg.eigvalsh(C_mandel)

    # 입방정 SO(3)-불변 축퇴 필요조건 검사: Mandel 고유값은 회전과 무관하게 (1, 2, 3) 다중도를 가져야 함
    cubic_rot_inv_viol = None
    if csys == "cubic":
        ev = sorted(float(x) for x in eigs_mandel)
        splits = [
            ((0, 1), (1, 3), (3, 6)),
            ((0, 1), (1, 4), (4, 6)),
            ((0, 2), (2, 3), (3, 6)),
            ((0, 2), (2, 5), (5, 6)),
            ((0, 3), (3, 4), (4, 6)),
            ((0, 3), (3, 5), (5, 6)),
        ]
        best_spread = float("inf")
        for g1, g2, g3 in splits:
            s = max(
                ev[g1[1] - 1] - ev[g1[0]],
                ev[g2[1] - 1] - ev[g2[0]],
                ev[g3[1] - 1] - ev[g3[0]],
            )
            if s < best_spread:
                best_spread = s
        cubic_rot_inv_viol = float(best_spread)

    return {
        "crystal_system": csys,
        "convention_used": used_conv,
        "matched_setting": setting,
        "max_asymmetry_gpa": max_asym,
        "max_zero_violation_gpa": max_zero_viol,
        "max_eq_violation_gpa": max_eq_viol,
        "max_voigt_violation_gpa": max(max_asym, max_zero_viol, max_eq_viol),
        "max_voigt_violation_fixed_std_gpa": max(max_asym, std_z, std_e),
        "cubic_mandel_rot_inv_viol_gpa": cubic_rot_inv_viol,
        "lambda_min_voigt_gpa": float(eigs_voigt[0]),
        "lambda_min_mandel_gpa": float(eigs_mandel[0]),
    }


@dataclass
class ElasticAuditRecord:
    """단일 결정의 대칭화 6x6 탄성 텐서 C_sym Born 안정성·Weyl 강건성·대칭성 감사 결과."""
    jid: str
    formula: str
    spg_number: Optional[int]
    crystal_system: str
    # Born 안정성 정확 인증 결과 (C_sym = (C + C^T)/2 기준)
    born_pd_exact: bool
    lambda_min_voigt_gpa: float
    lambda_min_mandel_gpa: float
    # 이동 LDL^T Voigt Weyl 강건 Born 인증 (δ = 1, 5, 10 GPa)
    robust_1gpa: bool
    robust_5gpa: bool
    robust_10gpa: bool
    # 순수 유리수 SO(3)-불변 Mandel/Kelvin Weyl 강건 Born 인증 (δ = 1, 5, 10 GPa)
    mandel_robust_1gpa: bool
    mandel_robust_5gpa: bool
    mandel_robust_10gpa: bool
    # 결정계 대칭 위반 및 채택 설정
    max_asymmetry_gpa: float
    max_zero_violation_gpa: float
    max_eq_violation_gpa: float
    max_voigt_violation_gpa: float
    max_voigt_violation_fixed_std_gpa: float
    matched_setting: str
    cubic_mandel_rot_inv_viol_gpa: Optional[float]
    # 증명서 검증 상태
    exact_verified: bool
    certificate_payload: Optional[Dict[str, object]] = None
    fragility_certificate_payload: Optional[Dict[str, object]] = None
    mandel_certificate_payload: Optional[Dict[str, object]] = None
    mandel_fragility_certificate_payload: Optional[Dict[str, object]] = None


def audit_elastic_tensor(
    jid: str,
    formula: str,
    C_raw_input: Sequence[Sequence[float]],
    spg_number: Optional[int] = None,
    emit_certificate: bool = False,
    convention: str = "ieee",
) -> ElasticAuditRecord:
    """6x6 Voigt 탄성 텐서의 대칭화 행렬 C_sym 에 대해 정확한 유리수 LDL^T, 반례 벡터,
    Voigt/Mandel Weyl 강건성(1/5/10 GPa), 구성적 Weyl 취약성 반례, 대칭 위반을 감사한다.
    """
    C_np = np.asarray(C_raw_input, dtype=np.float64)
    if C_np.shape != (6, 6) or not np.all(np.isfinite(C_np)):
        raise ValueError(f"유효하지 않은 6x6 탄성 텐서 ({jid}): shape={C_np.shape}")

    sym_info = compute_voigt_symmetry_violations(C_np, spg_number, convention=convention)

    # 정확한 유리수 대칭 텐서 C_sym = (C + C^T) / 2 생성 (원본 비대칭량은 max_asymmetry_gpa로 별도 기록)
    C_exact_raw = [[to_fraction(C_raw_input[i][j]) for j in range(6)] for i in range(6)]
    C_sym = [
        [(C_exact_raw[i][j] + C_exact_raw[j][i]) / 2 for j in range(6)]
        for i in range(6)
    ]

    # 1) 명목 Born 양정치성 (δ = 0) 정확 유리수 LDL^T 또는 반례 벡터 v 합성
    is_pd, L0, d0, v_bad = exact_ldlt_or_counterexample(C_sym)
    if is_pd:
        if L0 is None or d0 is None:
            raise RuntimeError("Born PD 결과에 L/d 인자가 누락되었습니다.")
        ok0 = verify_ldlt_certificate(C_sym, L0, d0)
    else:
        if v_bad is None:
            raise RuntimeError("Born Non-PD 결과에 반례 벡터 v가 누락되었습니다.")
        ok0 = verify_non_pd_certificate(C_sym, v_bad)
    if not ok0:
        raise RuntimeError(f"탄성 텐서 {jid} 명목 Born 증명서 검증 실패")

    # 2) Voigt 이동 LDL^T 기반 Weyl 강건 Born 인증 및 구성적 취약성 반례 벡터 (δ = 1, 5, 10 GPa)
    r1, r5, r10 = False, False, False
    best_weyl_cert = None
    first_fragile_cert = None
    if is_pd:
        for delta_int in (1, 5, 10):
            delta_q = Fraction(delta_int, 1)
            C_shift = shift_matrix_exact(C_sym, delta_q)
            ok_d, Ld, dd, v_frag = exact_ldlt_or_counterexample(C_shift)
            if ok_d:
                if Ld is None or dd is None or not verify_ldlt_certificate(C_shift, Ld, dd):
                    raise RuntimeError(f"Weyl 이동 LDL^T 검증 실패 (delta={delta_int} GPa)")
                if delta_int == 1:
                    r1 = True
                elif delta_int == 5:
                    r5 = True
                elif delta_int == 10:
                    r10 = True
                best_weyl_cert = (delta_q, Ld, dd)
            else:
                if v_frag is None or not verify_weyl_fragile_certificate(C_sym, delta_q, v_frag):
                    raise RuntimeError(f"Weyl 취약성 반례 벡터 검증 실패 (delta={delta_int} GPa)")
                first_fragile_cert = (delta_q, v_frag)
                # 단조성: δ1 에서 실패하면 더 큰 δ에서도 반드시 실패
                break

    # 3) 순수 유리수 SO(3)-불변 Mandel/Kelvin Weyl 강건 Born 인증 및 구성적 취약성 반례 벡터
    mr1, mr5, mr10 = False, False, False
    best_mandel_cert = None
    first_mandel_fragile_cert = None
    if is_pd:
        for delta_int in (1, 5, 10):
            delta_q = Fraction(delta_int, 1)
            C_mshift = weighted_shift_matrix_exact(C_sym, delta_q, MANDEL_WEIGHTS)
            ok_m, Lm, dm, v_mfrag = exact_ldlt_or_counterexample(C_mshift)
            if ok_m:
                if Lm is None or dm is None or not verify_ldlt_certificate(C_mshift, Lm, dm):
                    raise RuntimeError(f"Mandel 이동 LDL^T 검증 실패 (delta={delta_int} GPa)")
                if delta_int == 1:
                    mr1 = True
                elif delta_int == 5:
                    mr5 = True
                elif delta_int == 10:
                    mr10 = True
                best_mandel_cert = (delta_q, Lm, dm)
            else:
                if v_mfrag is None or not verify_mandel_weyl_fragile_certificate(C_sym, delta_q, v_mfrag):
                    raise RuntimeError(f"Mandel Weyl 취약성 반례 벡터 검증 실패 (delta={delta_int} GPa)")
                first_mandel_fragile_cert = (delta_q, v_mfrag)
                break

    cert_payload: Optional[Dict[str, object]] = None
    frag_payload: Optional[Dict[str, object]] = None
    mandel_payload: Optional[Dict[str, object]] = None
    mandel_frag_payload: Optional[Dict[str, object]] = None
    if emit_certificate:
        base_meta = {
            "material_id": jid,
            "formula": formula,
            "spg_number": spg_number,
            "crystal_system": str(sym_info["crystal_system"]),
            "symmetrized_matrix": True,
            "max_asymmetry_gpa": float(sym_info["max_asymmetry_gpa"]),
        }
        if not is_pd:
            cert_payload = {
                "kind": "BORN_NON_PD",
                "n": 6,
                "C": C_sym,
                "v": v_bad,
                "meta": base_meta,
            }
        elif best_weyl_cert is not None:
            dq, Ld, dd = best_weyl_cert
            cert_payload = {
                "kind": "WEYL_ROBUST",
                "n": 6,
                "lam0": dq,
                "delta": dq,
                "C": C_sym,
                "L": Ld,
                "d": dd,
                "meta": base_meta,
            }
        else:
            cert_payload = {
                "kind": "BORN_LDLT",
                "n": 6,
                "C": C_sym,
                "L": L0,
                "d": d0,
                "meta": base_meta,
            }
        if first_fragile_cert is not None:
            fq, vf = first_fragile_cert
            frag_payload = {
                "kind": "WEYL_FRAGILE",
                "n": 6,
                "delta": fq,
                "C": C_sym,
                "v": vf,
                "meta": {**base_meta, "fragile_threshold_gpa": int(fq)},
            }
        if best_mandel_cert is not None:
            mq, Lm, dm = best_mandel_cert
            mandel_payload = {
                "kind": "MANDEL_WEYL_ROBUST",
                "lam0": mq,
                "delta": mq,
                "C": C_sym,
                "L": Lm,
                "d": dm,
                "meta": {**base_meta, "mandel_threshold_gpa": int(mq)},
            }
        if first_mandel_fragile_cert is not None:
            mfq, vmf = first_mandel_fragile_cert
            mandel_frag_payload = {
                "kind": "MANDEL_WEYL_FRAGILE",
                "delta": mfq,
                "C": C_sym,
                "v": vmf,
                "meta": {**base_meta, "mandel_fragile_threshold_gpa": int(mfq)},
            }

    return ElasticAuditRecord(
        jid=jid,
        formula=formula,
        spg_number=spg_number,
        crystal_system=str(sym_info["crystal_system"]),
        born_pd_exact=is_pd,
        lambda_min_voigt_gpa=float(sym_info["lambda_min_voigt_gpa"]),
        lambda_min_mandel_gpa=float(sym_info["lambda_min_mandel_gpa"]),
        robust_1gpa=r1,
        robust_5gpa=r5,
        robust_10gpa=r10,
        mandel_robust_1gpa=mr1,
        mandel_robust_5gpa=mr5,
        mandel_robust_10gpa=mr10,
        max_asymmetry_gpa=float(sym_info["max_asymmetry_gpa"]),
        max_zero_violation_gpa=float(sym_info["max_zero_violation_gpa"]),
        max_eq_violation_gpa=float(sym_info["max_eq_violation_gpa"]),
        max_voigt_violation_gpa=float(sym_info["max_voigt_violation_gpa"]),
        max_voigt_violation_fixed_std_gpa=float(sym_info["max_voigt_violation_fixed_std_gpa"]),
        matched_setting=str(sym_info["matched_setting"]),
        cubic_mandel_rot_inv_viol_gpa=sym_info["cubic_mandel_rot_inv_viol_gpa"],
        exact_verified=ok0,
        certificate_payload=cert_payload,
        fragility_certificate_payload=frag_payload,
        mandel_certificate_payload=mandel_payload,
        mandel_fragility_certificate_payload=mandel_frag_payload,
    )
