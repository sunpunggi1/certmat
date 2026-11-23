"""
CertMat 불확실성 모델(균일 오차 및 화학종·보정별 이질적 잔차 오차 모델)과
정리 2 기반 원소 기준 상태 상관 오차(δμ_e) 분리·회귀 모듈.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Mapping, Optional, Sequence, Set, Tuple

import numpy as np

# Materials Project MP2020 GGA+U 적용 대표 전이금속 원소군
GGA_U_TRANSITION_METALS: Set[str] = {"V", "Cr", "Mn", "Fe", "Co", "Ni", "Mo", "W"}

# 음이온 및 강한 공유/이온 결합 주족 원소군
OXYGEN_FLUORINE: Set[str] = {"O", "F"}
CHALCOGENS: Set[str] = {"S", "Se", "Te"}
PNICTOGENS: Set[str] = {"N", "P", "As", "Sb"}
HALOGENS: Set[str] = {"F", "Cl", "Br", "I"}

# f-블록 (란탄족·악티늄족: 강한 4f/5f 자기상호작용 잔차 오차)
F_BLOCK_ELEMENTS: Set[str] = {
    "La", "Ce", "Pr", "Nd", "Pm", "Sm", "Eu", "Gd", "Tb", "Dy", "Ho", "Er", "Tm", "Yb", "Lu",
    "Ac", "Th", "Pa", "U", "Np", "Pu", "Am", "Cm", "Bk", "Cf", "Es", "Fm", "Md", "No", "Lr",
}


@dataclass(frozen=True)
class UncertaintyProfile:
    """화학종·보정별 이질적 불확실성 반폭(eV/atom, 정확한 유리수) 프로파일."""
    name: str
    description: str
    # 기본 반폭 (eV/atom)
    elemental_ref: Fraction = Fraction(10, 1000)       # 10 meV/atom: 원소 기준 잔차
    intermetallic: Fraction = Fraction(15, 1000)       # 15 meV/atom: sp/d-비자성 금속간화합물
    chalcogenide_pnictide: Fraction = Fraction(25, 1000)  # 25 meV/atom: 황화물·질화물·인화물
    halide_oxide_main: Fraction = Fraction(30, 1000)   # 30 meV/atom: 주족 산화물·할로겐화물
    tm_non_oxide: Fraction = Fraction(35, 1000)        # 35 meV/atom: GGA+U 대상 3d/5d 비산화물(자성 잔차)
    f_block_non_oxide: Fraction = Fraction(45, 1000)   # 45 meV/atom: f-블록 비산화물
    ggau_oxide_fluoride: Fraction = Fraction(50, 1000) # 50 meV/atom: GGA+U 전이금속 산화물/불화물(MP2020 혼합 보정)
    f_block_oxide_fluoride: Fraction = Fraction(55, 1000)  # 55 meV/atom: f-블록 산화물/불화물


# 문헌 동기화(a priori) 화학군별 이질적 잔차 불확실성 스트레스 테스트 프로파일
# 주의: 이 반폭(10-55 meV/atom)은 절대적 물리 상한이 아니라, MP2020 GGA/GGA+U·음이온·f-블록
# 오차 계층 구조에 기반한 조건부 감사 가정(conditional error-box hypothesis)이며,
# 실제 GNoME PBE-r2SCAN 잔차 커버리지 및 OOS 실측 보정은 별도 검증한다.
# 또한 JARVIS-DFT 3D는 OptB88vdW(+U 미적용)이므로 균일 오차 및 화학군별 스트레스 테스트를 병행 보고한다.
HETERO_CHEM_PROFILE = UncertaintyProfile(
    name="hetero_chem",
    description="화학군별 이질적 잔차 불확실성 스트레스 테스트 프로파일 (10-55 meV/atom; 조건부 오차 구간 가정)",
)

# 원소 기준 잔차를 0으로 두는 절제(ablation) 프로파일
HETERO_CHEM_ZERO_ELEM_PROFILE = UncertaintyProfile(
    name="hetero_chem_zero_elem",
    description="원소 기준 잔차=0으로 둔 이질적 불확실성 절제 모델 (0-55 meV/atom)",
    elemental_ref=Fraction(0, 1),
)


def classify_chemistry(elements: Iterable[str]) -> str:
    """조성 내 원소 집합에 따라 물리적 오차 화학군을 분류한다."""
    elems = set(elements)
    if len(elems) <= 1:
        return "elemental_ref"
    has_of = bool(elems & OXYGEN_FLUORINE)
    has_fblock = bool(elems & F_BLOCK_ELEMENTS)
    has_ggau_tm = bool(elems & GGA_U_TRANSITION_METALS)
    has_hal_ox = bool(elems & (HALOGENS | {"O"}))
    has_chal_pnic = bool(elems & (CHALCOGENS | PNICTOGENS))

    if has_fblock and has_of:
        return "f_block_oxide_fluoride"
    if has_ggau_tm and has_of:
        return "ggau_oxide_fluoride"
    if has_fblock:
        return "f_block_non_oxide"
    if has_ggau_tm:
        return "tm_non_oxide"
    if has_hal_ox:
        return "halide_oxide_main"
    if has_chal_pnic:
        return "chalcogenide_pnictide"
    return "intermetallic"


def get_phase_uncertainty(
    elements: Iterable[str],
    mode: str = "uniform",
    uniform_ev: Fraction = Fraction(25, 1000),
    profile: UncertaintyProfile = HETERO_CHEM_PROFILE,
    custom_class_sigma: Optional[Mapping[str, Fraction]] = None,
) -> Tuple[Fraction, str]:
    """특정 상의 불확실성 반폭(eV/atom, 정확한 유리수)과 화학군 라벨을 반환한다."""
    chem_class = classify_chemistry(elements)
    if mode == "uniform":
        return uniform_ev, chem_class
    if mode == "hetero":
        if custom_class_sigma is not None and chem_class in custom_class_sigma:
            return custom_class_sigma[chem_class], chem_class
        return getattr(profile, chem_class), chem_class
    raise ValueError(f"알 수 없는 불확실성 모드: {mode}")


def decompose_reference_and_residual_errors(
    compositions: Sequence[Mapping[str, float]],
    delta_energies: Sequence[float],
) -> Dict[str, object]:
    """정리 2 실증 분석: 두 DFT 범함수(예: PBE vs r2SCAN) 간 에너지 차이 ΔE_i 를
    상관 원소 기준 오차(∑ c_ie δμ_e)와 비상관 잔차 오차(η_i)로 최소제곱 직교 분해한다.

    ΔE_i = ∑_e c_ie δμ_e + η_i
    정리 2에 의해 첫 번째 항은 조성 보존 분해에서 완벽히 상쇄되며,
    두 번째 항 η_i 만이 상 안정성 전복을 유발한다.
    """
    all_elems = sorted({e for comp in compositions for e in comp.keys()})
    elem_idx = {e: k for k, e in enumerate(all_elems)}
    n = len(compositions)
    E = len(all_elems)

    C = np.zeros((n, E), dtype=np.float64)
    for i, comp in enumerate(compositions):
        for el, frac in comp.items():
            C[i, elem_idx[el]] = frac
    y = np.asarray(delta_energies, dtype=np.float64)

    # 최소제곱 회귀: C @ dmu ≈ y (직교 투영 및 특이값 조건수 계산)
    dmu, _, rank, singular_vals = np.linalg.lstsq(C, y, rcond=None)
    pos_sv = singular_vals[singular_vals > 0]
    cond_num = float(pos_sv[0] / pos_sv[-1]) if len(pos_sv) >= 2 else (1.0 if len(pos_sv) == 1 else float("inf"))
    correlated = C @ dmu
    residual = y - correlated

    raw_mae = float(np.mean(np.abs(y)))
    raw_rmse = float(np.sqrt(np.mean(y ** 2)))
    res_mae = float(np.mean(np.abs(residual)))
    res_rmse = float(np.sqrt(np.mean(residual ** 2)))
    var_total = float(np.var(y))
    var_res = float(np.var(residual))
    r2_correlated = 1.0 - (var_res / var_total) if var_total > 0 else 0.0

    # 화학군별 잔차 오차 통계(MAE, 75/90/95 백분위 및 문헌 프로파일 커버리지)
    class_residuals: Dict[str, List[float]] = {}
    for comp, eta in zip(compositions, residual):
        cls = classify_chemistry(comp.keys())
        class_residuals.setdefault(cls, []).append(abs(float(eta)))

    class_stats = {}
    for cls, vals in sorted(class_residuals.items()):
        arr = np.asarray(vals, dtype=np.float64)
        prof_w = float(getattr(HETERO_CHEM_PROFILE, cls, Fraction(25, 1000)))
        class_stats[cls] = {
            "count": int(len(arr)),
            "mae_mev": float(np.mean(arr) * 1000.0),
            "median_mev": float(np.median(arr) * 1000.0),
            "p75_mev": float(np.percentile(arr, 75) * 1000.0),
            "p90_mev": float(np.percentile(arr, 90) * 1000.0),
            "p95_mev": float(np.percentile(arr, 95) * 1000.0),
            "hetero_profile_width_mev": round(prof_w * 1000.0, 2),
            "empirical_coverage_at_profile_pct": round(float(100.0 * np.mean(arr <= prof_w)), 2),
            "empirical_coverage_at_25mev_pct": round(float(100.0 * np.mean(arr <= 0.025)), 2),
        }

    return {
        "n_materials": n,
        "n_elements": E,
        "matrix_rank": int(rank),
        "condition_number": cond_num,
        "raw_mae_mev": raw_mae * 1000.0,
        "raw_rmse_mev": raw_rmse * 1000.0,
        "residual_mae_mev": res_mae * 1000.0,
        "residual_rmse_mev": res_rmse * 1000.0,
        "variance_explained_by_ref_shift_r2": r2_correlated,
        "mae_reduction_pct": (1.0 - res_mae / raw_mae) * 100.0 if raw_mae > 0 else 0.0,
        "elemental_shifts_ev": {el: float(dmu[k]) for k, el in enumerate(all_elems)},
        "class_residual_stats": class_stats,
        "residuals_ev": residual.tolist(),
    }
