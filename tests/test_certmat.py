"""
CertMat 핵심 수학·물리·형식검증 엔진 전수 단위 및 차분(Differential) 테스트.

테스트 범위:
1. 정확한 유리수 LP & Z3 폴백 (강쌍대성, 퇴화, 동률, 원시·쌍대 상호 배타성, 정확한 10진 문자열 파싱)
2. 정리 2: 원소 기준 상태 상관 오차(∑ c_ie δμ_e)의 조성 보존 분해 시 완전 상쇄 검증
3. 정리 3: 이질적 구간 불확실성 하의 임계 전복 반경 ε*(x), Phase Switching, 부분/전체 0-가중치·무한 반경·경계값(scale=1),
   음수 가중치 거부, 무작위 화학계 동질이상 가지치기 무손실 동치 검증
4. 정리 4: 6x6 탄성 텐서 정확한 유리수 LDL^T, 비양정치 반례 벡터, Voigt/Mandel Weyl 강건성,
   구성적 WEYL_FRAGILE 및 MANDEL_WEYL_FRAGILE 랭크-1 섭동 반례, VASP/IEEE/축치환/능면체 결정계 대칭성 검증
5. Lean 4 커널 기계 검증: `#print axioms` 51정리 표준 공리 전용(sorryAx 0건), 금지 우회 키워드 0건,
   컴파일된 `certmat-check` 바이너리 vs 독립 Fraction 검증기 12종 전체 차분 파싱·변조 거부 동치 테스트
6. 원클릭 재현(`reproduce_all.py`) fail-closed 무결성 및 논문-JSON 수치 자동 정합성 검증
"""

from __future__ import annotations

import math
import random
import re
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest

from certmat.elastic_audit import (
    MANDEL_WEIGHTS,
    audit_elastic_tensor,
    compute_voigt_symmetry_violations,
    exact_ldlt_or_counterexample,
    quad_form_exact,
    verify_ldlt_certificate,
    verify_mandel_weyl_fragile_certificate,
    verify_non_pd_certificate,
    verify_weyl_fragile_certificate,
    weighted_shift_matrix_exact,
)
from certmat.exact_lp import (
    _z3_solve_charnes_cooper,
    solve_critical_radius_exact,
    solve_hull_primal_dual_exact,
    to_fraction,
    verify_dual_stable,
    verify_primal_unstable,
)
from certmat.lean_bridge import (
    find_lean_checker_binary,
    verify_lean_axioms,
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
    HETERO_CHEM_ZERO_ELEM_PROFILE,
    classify_chemistry,
    decompose_reference_and_residual_errors,
)


def test_formula_parser_and_exact_decimal_parsing():
    """괄호·공백·소수 화학식 파싱 및 손실 없는 정확한 10진 유리수 변환 검증."""
    c1 = formula_to_atom_fractions("Cs(ZrS2)3")
    assert c1 == {"Cs": Fraction(1, 10), "S": Fraction(6, 10), "Zr": Fraction(3, 10)}
    assert sum(c1.values()) == 1

    c2 = formula_to_atom_fractions("Ac6 U2")
    assert c2 == {"Ac": Fraction(3, 4), "U": Fraction(1, 4)}

    c3 = parse_formula_counts("Li0.5Fe0.5PO4")
    assert c3["Li"] == Fraction(1, 2)
    assert c3["O"] == Fraction(4, 1)

    # 손실 없는 고정밀 10진 문자열 파싱 (분모 10^15 절단 없음)
    q_hi = to_fraction("-1.234567890123456")
    assert q_hi == Fraction(-1234567890123456, 10**15)
    assert to_fraction(0.1) == Fraction(1, 10)

    with pytest.raises(ValueError):
        formula_to_atom_fractions("")
    with pytest.raises(ValueError):
        formula_to_atom_fractions("Li2(O3")
    with pytest.raises(ValueError):
        parse_formula_counts("Li.")
    with pytest.raises(ValueError):
        parse_formula_counts("Li0")
    with pytest.raises(ValueError):
        to_fraction(float("nan"))


def test_classify_chemistry_hierarchy():
    """화학군 분류 우선순위(f-블록 산화물 > GGA+U 산화물 > f-블록 > GGA+U > 주족 산화물 > 칼코겐/프닉토겐 > 금속간) 검증."""
    assert classify_chemistry(["Fe"]) == "elemental_ref"
    assert classify_chemistry(["Gd", "O", "Fe"]) == "f_block_oxide_fluoride"
    assert classify_chemistry(["Fe", "O", "Li"]) == "ggau_oxide_fluoride"
    assert classify_chemistry(["Gd", "Co"]) == "f_block_non_oxide"
    assert classify_chemistry(["Fe", "S"]) == "tm_non_oxide"
    assert classify_chemistry(["Li", "O"]) == "halide_oxide_main"
    assert classify_chemistry(["Ga", "As"]) == "chalcogenide_pnictide"
    assert classify_chemistry(["Al", "Cu", "Mg"]) == "intermetallic"


def test_theorem1_farkas_primal_dual_exact():
    """정리 1: 원시 불안정/쌍대 안정 증명서 및 강쌍대성 정확 일치 검증."""
    comp = [
        [Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(1)],
    ]
    energies = [Fraction(0), Fraction(0)]
    cx = [Fraction(1, 2), Fraction(1, 2)]

    res_s = solve_hull_primal_dual_exact(comp, cx, energies, Fraction(-1, 2))
    assert res_s.exact_verified
    assert res_s.hull_energy == Fraction(0)
    assert res_s.stability_margin == Fraction(1, 2)
    assert verify_dual_stable(comp, cx, energies, Fraction(-1, 2), res_s.mu, Fraction(1, 2))

    res_u = solve_hull_primal_dual_exact(comp, cx, energies, Fraction(1, 5))
    assert res_u.exact_verified
    assert res_u.stability_margin == Fraction(-1, 5)
    assert verify_primal_unstable(comp, cx, energies, Fraction(1, 5), res_u.lam)
    assert not verify_dual_stable(comp, cx, energies, Fraction(1, 5), res_u.mu, Fraction(0))


def test_theorem1_degenerate_z3_fallback():
    """퇴화/동률 경쟁상에서도 HiGHS + Z3 폴백이 100% 정확한 유리수 증명서를 산출한다."""
    comp = [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(0), Fraction(1)],
        [Fraction(1, 2), Fraction(1, 2), Fraction(0)],
        [Fraction(1, 2), Fraction(1, 2), Fraction(0)],
    ]
    energies = [Fraction(0), Fraction(0), Fraction(0), Fraction(-3, 10), Fraction(-3, 10)]
    cx = [Fraction(1, 2), Fraction(1, 2), Fraction(0)]
    ex = Fraction(-4, 10)

    res = solve_hull_primal_dual_exact(comp, cx, energies, ex, use_z3_fallback=True)
    assert res.exact_verified
    assert res.hull_energy == Fraction(-3, 10)
    assert res.stability_margin == Fraction(1, 10)
    assert verify_dual_stable(comp, cx, energies, ex, res.mu, Fraction(1, 10))


def test_theorem2_reference_error_exact_cancellation():
    """정리 2: 임의로 큰 원소 기준 오차 δμ 가 가해져도 상평형 여유와 ε*(x) 가 항등 불변임을 검증."""
    comp = [
        [Fraction(1), Fraction(0), Fraction(0)],
        [Fraction(0), Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(0), Fraction(1)],
        [Fraction(1, 2), Fraction(1, 2), Fraction(0)],
        [Fraction(0), Fraction(1, 2), Fraction(1, 2)],
    ]
    en_base = [Fraction(0), Fraction(0), Fraction(0), Fraction(-1, 5), Fraction(-3, 10)]
    cx = [Fraction(1, 3), Fraction(1, 3), Fraction(1, 3)]
    ex_base = Fraction(-1, 2)

    dmu = [Fraction(35, 2), Fraction(-169, 4), Fraction(73, 8)]
    en_shift = [en_base[i] + sum(comp[i][e] * dmu[e] for e in range(3)) for i in range(5)]
    ex_shift = ex_base + sum(cx[e] * dmu[e] for e in range(3))

    r0 = solve_hull_primal_dual_exact(comp, cx, en_base, ex_base)
    r1 = solve_hull_primal_dual_exact(comp, cx, en_shift, ex_shift)
    assert r0.stability_margin == r1.stability_margin
    mu_shifted = [r0.mu[e] + dmu[e] for e in range(3)]
    assert verify_dual_stable(comp, cx, en_shift, ex_shift, mu_shifted, r0.stability_margin)

    # 최소제곱 회귀 분해기 테스트 (정확한 Fraction 기반 델타 생성 + 조건수 확인)
    comps_exact = [
        {"A": Fraction(1)}, {"B": Fraction(1)}, {"C": Fraction(1)},
        {"A": Fraction(1, 2), "B": Fraction(1, 2)},
        {"B": Fraction(1, 2), "C": Fraction(1, 2)},
        {"A": Fraction(1, 3), "B": Fraction(1, 3), "C": Fraction(1, 3)},
    ]
    comps_float = [{k: float(v) for k, v in c.items()} for c in comps_exact]
    deltas = [
        float(sum(c.get(el, Fraction(0)) * dmu[k] for k, el in enumerate(["A", "B", "C"])))
        for c in comps_exact
    ]
    dec = decompose_reference_and_residual_errors(comps_float, deltas)
    # np.linalg.lstsq(float64) 는 ~42 eV 스케일에서 기계 엡실론(~1e-14 eV = 1e-11 meV) 수준의 부동소수점 반올림을 남김
    assert dec["residual_mae_mev"] < 1e-10
    assert dec["variance_explained_by_ref_shift_r2"] > 0.999999999
    assert math.isfinite(dec["condition_number"]) and dec["condition_number"] > 0


def test_theorem3_phase_switching_and_exact_radius():
    """정리 3: 이질적 불확실성 하 Phase Switching 해석 반례 및 임계 반경 검증."""
    comp = [
        [Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(1)],
        [Fraction(1, 2), Fraction(1, 2)],
        [Fraction(2, 5), Fraction(3, 5)],
    ]
    cx = [Fraction(1, 2), Fraction(1, 2)]
    energies = [Fraction(0), Fraction(0), Fraction(-96, 100), Fraction(-114, 100)]
    ex = Fraction(-1, 1)
    weights = [Fraction(1, 100), Fraction(1, 100), Fraction(2, 100), Fraction(12, 100)]
    wx = Fraction(2, 100)

    nom = solve_hull_primal_dual_exact(comp, cx, energies, ex)
    assert nom.lam[2] == 1
    assert nom.stability_margin == Fraction(4, 100)

    rad = solve_critical_radius_exact(comp, cx, energies, ex, weights, wx)
    assert rad.exact_verified and (not rad.is_infinite)
    assert rad.is_nominally_stable
    assert rad.lam_adv[0] == Fraction(1, 6)
    assert rad.lam_adv[3] == Fraction(5, 6)
    assert rad.lam_adv[2] == 0
    expected_scale = Fraction(5, 100) / (Fraction(2, 100) + Fraction(1, 600) + Fraction(10, 100))
    assert rad.critical_radius == expected_scale
    assert rad.critical_radius < Fraction(1, 2)

    L_box = [energies[i] - weights[i] for i in range(4)]
    Ux = ex + wx
    assert verify_primal_unstable(comp, cx, L_box, Ux, rad.lam_adv)


def test_theorem3_zero_partial_weights_negative_rejection_and_exact_boundary():
    """부분/전체 0-가중치, 무한 반경, 음수 가중치 거부, 정확 경계(scale == 1) 회귀 테스트."""
    comp = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)], [Fraction(1, 2), Fraction(1, 2)]]
    cx = [Fraction(1, 2), Fraction(1, 2)]

    # 1) 음수 가중치 엄격 거부
    with pytest.raises(ValueError):
        solve_critical_radius_exact(
            comp, cx, [Fraction(0), Fraction(0), Fraction(-1, 2)], Fraction(-1),
            [Fraction(1, 100), Fraction(-1, 100), Fraction(1, 100)], Fraction(1, 100),
        )

    # 2) 전체 0-가중치 -> 유한 sentinel(10^9) 대신 명시적 is_infinite=True 반환
    r_inf_stab = solve_critical_radius_exact(
        comp, cx, [Fraction(0), Fraction(0), Fraction(-1, 2)], Fraction(-1),
        [Fraction(0), Fraction(0), Fraction(0)], Fraction(0),
    )
    assert r_inf_stab.is_infinite and r_inf_stab.infinite_sign == 1 and r_inf_stab.critical_radius is None

    # 3) 부분 0-가중치: 0-가중치 경쟁상(comp[0]+comp[1])만으로 엄격 불안정 -> r* = -∞
    r_part_inf = solve_critical_radius_exact(
        comp, cx, [Fraction(0), Fraction(0), Fraction(1, 10)], Fraction(1, 2),
        [Fraction(0), Fraction(0), Fraction(5, 100)], Fraction(0),
    )
    assert r_part_inf.is_infinite and r_part_inf.infinite_sign == -1 and (not r_part_inf.is_nominally_stable)

    # 4) 부분 0-가중치: 0-가중치 경로(comp[0]+comp[1])는 명목 안정(+1.0), 양의 가중치 경쟁상(comp[2], w=0.1)은 여유 0.2 -> 유한 반경 2.0!
    r_part_fin = solve_critical_radius_exact(
        comp, cx, [Fraction(0), Fraction(0), Fraction(-8, 10)], Fraction(-1),
        [Fraction(0), Fraction(0), Fraction(1, 10)], Fraction(0),
    )
    assert (not r_part_fin.is_infinite) and r_part_fin.critical_radius == Fraction(2, 1)

    # 4b) Codex #2 반례: 0-가중치 동률(margin=0) + 양의 가중치 경쟁상(E=1, w=1) -> 진정한 전복 반경은 0이 아니라 1!
    r_codex_p1 = solve_critical_radius_exact(
        [[Fraction(1)], [Fraction(1)]], [Fraction(1)],
        [Fraction(0), Fraction(1)], Fraction(0),
        [Fraction(0), Fraction(1)], Fraction(0),
    )
    assert r_codex_p1.exact_verified and (not r_codex_p1.is_infinite)
    assert r_codex_p1.critical_radius == Fraction(1, 1)

    # 4c) Claude P1 반례: 0-가중치 2원계 동률(margin=0) + 양의 가중치 2원상(E=1/10, w=1) -> 진정한 전복 반경은 1/10!
    r_claude_p1 = solve_critical_radius_exact(
        [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)], [Fraction(1, 2), Fraction(1, 2)]],
        [Fraction(1, 2), Fraction(1, 2)],
        [Fraction(0), Fraction(0), Fraction(1, 10)], Fraction(0),
        [Fraction(0), Fraction(0), Fraction(1)], Fraction(0),
    )
    assert r_claude_p1.exact_verified and (not r_claude_p1.is_infinite)
    assert r_claude_p1.critical_radius == Fraction(1, 10)

    # 4d) Claude P2: 전체 0-가중치 + margin=0 -> 비엄격 안정(≤) 규약 하에서 영구 안정(+∞)
    r_all_zero_tie = solve_critical_radius_exact(
        comp, cx, [Fraction(0), Fraction(0), Fraction(0)], Fraction(0),
        [Fraction(0), Fraction(0), Fraction(0)], Fraction(0),
    )
    assert r_all_zero_tie.is_infinite and r_all_zero_tie.infinite_sign == 1

    # 4e) 부분 0-가중치이나 양의 가중치 경쟁상이 도달 불가능한 경우 -> 영구 안정(+∞)
    r_no_pos_reach = solve_critical_radius_exact(
        [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]],
        [Fraction(1), Fraction(0)],
        [Fraction(0), Fraction(0)], Fraction(0),
        [Fraction(0), Fraction(1)], Fraction(0),
    )
    assert r_no_pos_reach.is_infinite and r_no_pos_reach.infinite_sign == 1

    # 4f) Z3 Charnes-Cooper 직접 경로 vs 전수 꼭짓점(brute-force) 완전 일치 검증
    c_bf = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)], [Fraction(1, 2), Fraction(1, 2)], [Fraction(2, 5), Fraction(3, 5)]]
    cx_bf = [Fraction(1, 2), Fraction(1, 2)]
    e_bf = [Fraction(0), Fraction(0), Fraction(-96, 100), Fraction(-114, 100)]
    w_bf = [Fraction(1, 100), Fraction(1, 100), Fraction(2, 100), Fraction(12, 100)]
    r_z3 = _z3_solve_charnes_cooper(c_bf, cx_bf, e_bf, Fraction(-1), w_bf, Fraction(2, 100))
    # 2원계 4경쟁상의 모든 유효 꼭짓점 분해 비율 직접 열거: {0,1}, {2}, {0,3}, {2,3} 등
    brute_ratios = [
        (Fraction(0) - Fraction(-1)) / (Fraction(2, 100) + Fraction(1, 100)),
        (Fraction(-96, 100) - Fraction(-1)) / (Fraction(2, 100) + Fraction(2, 100)),
        (Fraction(1, 6) * Fraction(0) + Fraction(5, 6) * Fraction(-114, 100) - Fraction(-1))
        / (Fraction(2, 100) + Fraction(1, 6) * Fraction(1, 100) + Fraction(5, 6) * Fraction(12, 100)),
    ]
    assert r_z3.exact_verified and r_z3.critical_radius == min(brute_ratios)

    # 4g) 음수 여유 delta < 0 은 verify_dual_stable 에서 엄격 거부, 비정규화 조성은 solve_hull_primal_dual_exact 에서 거부
    assert not verify_dual_stable([[Fraction(1)]], [Fraction(1)], [Fraction(0)], Fraction(1), [Fraction(0)], Fraction(-1))
    with pytest.raises(ValueError):
        solve_hull_primal_dual_exact([[Fraction(1), Fraction(1)]], [Fraction(1), Fraction(1)], [Fraction(0)], Fraction(0))

    # 4h) 부분 0-가중치 도달 불가능 양의 가중치 경쟁상 -> +∞ 및 1x 박스 INTERVAL_STABLE 증명서 정상 발급
    cand_inf = PhaseEntry("X_inf", "LiFeO2", {"Li": Fraction(1, 4), "Fe": Fraction(1, 4), "O": Fraction(1, 2)}, Fraction(0))
    c_inf_0 = PhaseEntry("P0_inf", "LiFeO2", {"Li": Fraction(1, 4), "Fe": Fraction(1, 4), "O": Fraction(1, 2)}, Fraction(1))
    c_inf_1 = PhaseEntry("P1_inf", "LiO", {"Li": Fraction(1, 2), "O": Fraction(1, 2)}, Fraction(-10))
    sig_inf = {"ggau_oxide_fluoride": Fraction(0), "halide_oxide_main": Fraction(100)}
    rec_inf = audit_single_phase(cand_inf, [c_inf_0, c_inf_1], custom_class_sigma=sig_inf, emit_certificate=True)
    assert rec_inf.status_hetero == "Certified_Robust_Stable"
    assert math.isinf(rec_inf.hetero_critical_scale)
    assert rec_inf.certificate_payload is not None and rec_inf.certificate_payload["kind"] == "INTERVAL_STABLE"

    # 4i) 0-가중치 명목 동률(margin=0, denom=0 -> naive=+∞) + 양의 가중치 유한 반경 경쟁상 -> Phase Switching & 치명적 역전 검출
    cand_tie = PhaseEntry("X_tie", "LiFeO2", {"Li": Fraction(1, 4), "Fe": Fraction(1, 4), "O": Fraction(1, 2)}, Fraction(0))
    c_tie = [
        PhaseEntry("E_Li", "Li", {"Li": Fraction(1)}, Fraction(0)),
        PhaseEntry("E_Fe", "Fe", {"Fe": Fraction(1)}, Fraction(0)),
        PhaseEntry("E_O", "O", {"O": Fraction(1)}, Fraction(0)),
        PhaseEntry("P_LiO", "LiO", {"Li": Fraction(1, 2), "O": Fraction(1, 2)}, Fraction(1, 2)),
    ]
    sig_tie = {"ggau_oxide_fluoride": Fraction(0), "elemental_ref": Fraction(0), "halide_oxide_main": Fraction(1)}
    rec_tie = audit_single_phase(cand_tie, c_tie, custom_class_sigma=sig_tie, emit_certificate=True)
    assert rec_tie.is_nominally_stable and rec_tie.nominal_margin_mev == 0.0
    assert math.isinf(rec_tie.naive_nominal_scale)
    assert rec_tie.hetero_critical_scale == pytest.approx(0.5)
    assert rec_tie.phase_switching and rec_tie.critical_robust_to_fragile_flip
    assert rec_tie.status_hetero == "Fragile"
    assert rec_tie.certificate_payload["kind"] == "INTERVAL_FRAGILE_DESTAB"

    # 5) 정확 경계(crit_scale == 1): 명목 안정이면 Certified_Robust_Stable, 명목 불안정이면 Fragile (비대칭 규약 검증)
    p_elem_a = PhaseEntry("A", "Li", {"Li": Fraction(1)}, Fraction(0))
    p_elem_b = PhaseEntry("B", "O", {"O": Fraction(1)}, Fraction(0))
    # LiO 는 halide_oxide_main (w=30 meV), 동질이상 LiO_comp 도 w=30 meV -> 분모 60 meV
    p_stab_bdry = PhaseEntry("LiO_s", "LiO", {"Li": Fraction(1, 2), "O": Fraction(1, 2)}, Fraction(-1060, 1000))
    p_comp_s = PhaseEntry("LiO_c", "LiO", {"Li": Fraction(1, 2), "O": Fraction(1, 2)}, Fraction(-1000, 1000))
    rec_sb = audit_single_phase(p_stab_bdry, [p_elem_a, p_elem_b, p_comp_s], emit_certificate=True)
    assert rec_sb.hetero_critical_scale == 1.0
    assert rec_sb.status_hetero == "Certified_Robust_Stable"
    assert rec_sb.certificate_payload["kind"] == "INTERVAL_STABLE"

    p_unstab_bdry = PhaseEntry("LiO_u", "LiO", {"Li": Fraction(1, 2), "O": Fraction(1, 2)}, Fraction(-940, 1000))
    rec_ub = audit_single_phase(p_unstab_bdry, [p_elem_a, p_elem_b, p_comp_s], emit_certificate=True)
    assert rec_ub.hetero_critical_scale == 1.0
    assert rec_ub.status_hetero == "Fragile"
    assert rec_ub.certificate_payload["kind"] == "INTERVAL_FRAGILE_STAB"


def test_polymorph_pruning_exact_equivalence_property():
    """무작위 다원계+동질이상 40개 시나리오에서 가지치기(prune=True) vs 전체(prune=False) 100% 동치 검증."""
    rng = random.Random(2026)
    elems = ["Li", "Fe", "O"]
    for trial in range(40):
        phases = [
            PhaseEntry("E_Li", "Li", {"Li": Fraction(1)}, Fraction(0)),
            PhaseEntry("E_Fe", "Fe", {"Fe": Fraction(1)}, Fraction(0)),
            PhaseEntry("E_O", "O", {"O": Fraction(1)}, Fraction(0)),
        ]
        # 5개 조성 각각에 3-4개 동질이상 생성
        stoichs = [
            ("LiO", {"Li": Fraction(1, 2), "O": Fraction(1, 2)}),
            ("FeO", {"Fe": Fraction(1, 2), "O": Fraction(1, 2)}),
            ("LiFeO2", {"Li": Fraction(1, 4), "Fe": Fraction(1, 4), "O": Fraction(1, 2)}),
            ("Li2FeO3", {"Li": Fraction(1, 3), "Fe": Fraction(1, 6), "O": Fraction(1, 2)}),
            ("LiFe", {"Li": Fraction(1, 2), "Fe": Fraction(1, 2)}),
        ]
        for s_idx, (form, comp) in enumerate(stoichs):
            for p_idx in range(4):
                e_val = Fraction(rng.randint(-3000, -100), 1000)
                phases.append(PhaseEntry(f"P_{trial}_{s_idx}_{p_idx}", form, comp, e_val))

        idx_pruned = PhaseDiagramIndex(phases, add_elemental_refs=True, prune_polymorphs=True)
        idx_full = PhaseDiagramIndex(phases, add_elemental_refs=True, prune_polymorphs=False)

        for cand in phases[3:10]:
            r_p = audit_single_phase(cand, idx_pruned.get_competing_phases(cand), emit_certificate=False)
            r_f = audit_single_phase(cand, idx_full.get_competing_phases(cand), emit_certificate=False)
            assert pytest.approx(r_p.nominal_margin_mev, abs=1e-9) == r_f.nominal_margin_mev
            assert pytest.approx(r_p.hetero_critical_scale, abs=1e-9) == r_f.hetero_critical_scale
            assert r_p.status_hetero == r_f.status_hetero
            assert r_p.status_25mev == r_f.status_25mev


def test_phase_diagram_index_duplicate_id_and_uncompeted_elemental():
    """중복 material_id 거부 및 경쟁상 없는 단원소상의 명시적 Uncompeted_Elemental 분류 검증."""
    p1 = PhaseEntry("DUP", "Li", {"Li": Fraction(1)}, Fraction(0))
    p2 = PhaseEntry("DUP", "Li", {"Li": Fraction(1)}, Fraction(1, 10))
    with pytest.raises(ValueError):
        PhaseDiagramIndex([p1, p2])

    idx_solo = PhaseDiagramIndex([p1], add_elemental_refs=True)
    rec = audit_single_phase(p1, idx_solo.get_competing_phases(p1), emit_certificate=True)
    assert rec.is_uncompeted
    assert rec.status_hetero == "Uncompeted_Elemental"
    assert not rec.exact_verified
    assert rec.certificate_payload is None


def test_phase_diagram_index_and_interval_certificates():
    """PhaseDiagramIndex 4종 결과(INTERVAL_STABLE/UNSTABLE/FRAGILE_DESTAB/FRAGILE_STAB) 증명서 발급 검증."""
    phases = [
        PhaseEntry("A", "Li", formula_to_atom_fractions("Li"), Fraction(0)),
        PhaseEntry("B", "O", formula_to_atom_fractions("O"), Fraction(0)),
        PhaseEntry("Li2O_low", "Li2O", formula_to_atom_fractions("Li2O"), Fraction(-200, 100)),
        PhaseEntry("Li2O_high", "Li2O", formula_to_atom_fractions("Li2O"), Fraction(-180, 100)),
        PhaseEntry("Li2O_frag_u", "Li2O", formula_to_atom_fractions("Li2O"), Fraction(-199, 100)),
        PhaseEntry("LiO_unstab", "LiO", formula_to_atom_fractions("LiO"), Fraction(-110, 100)),
        PhaseEntry("LiO2_frag_s", "LiO2", formula_to_atom_fractions("LiO2"), Fraction(-68, 100)),
    ]
    idx = PhaseDiagramIndex(phases, add_elemental_refs=True)

    # 1) Robust Stable -> INTERVAL_STABLE (margin=10 meV -> wait: Li2O_frag_u is -1.99 so margin=10 meV -> Fragile!)
    # Check Li2O_low vs Li2O_frag_u: margin = 10 meV < 60 meV -> INTERVAL_FRAGILE_DESTAB!
    r_fd = audit_single_phase(phases[2], idx.get_competing_phases(phases[2]), emit_certificate=True)
    assert r_fd.status_hetero == "Fragile" and r_fd.is_nominally_stable
    assert r_fd.certificate_payload["kind"] == "INTERVAL_FRAGILE_DESTAB"

    # 2) Robust Unstable (LiO_unstab, ehull = 400 meV >> 60 meV) -> INTERVAL_UNSTABLE
    r_iu = audit_single_phase(phases[5], idx.get_competing_phases(phases[5]), emit_certificate=True)
    assert r_iu.status_hetero == "Certified_Robust_Unstable"
    assert r_iu.certificate_payload["kind"] == "INTERVAL_UNSTABLE"

    # 3) Nominally Unstable Fragile (Li2O_frag_u, ehull = 10 meV < 60 meV) -> INTERVAL_FRAGILE_STAB
    r_fs = audit_single_phase(phases[4], idx.get_competing_phases(phases[4]), emit_certificate=True)
    assert r_fs.status_hetero == "Fragile" and (not r_fs.is_nominally_stable)
    assert r_fs.certificate_payload["kind"] == "INTERVAL_FRAGILE_STAB"

    # 4) Robust Stable (remove Li2O_frag_u so Li2O_low has margin = 200 meV >> 60 meV) -> INTERVAL_STABLE
    idx2 = PhaseDiagramIndex([phases[0], phases[1], phases[2], phases[3]], add_elemental_refs=True)
    r_is = audit_single_phase(phases[2], idx2.get_competing_phases(phases[2]), emit_certificate=True)
    assert r_is.status_hetero == "Certified_Robust_Stable"
    assert r_is.certificate_payload["kind"] == "INTERVAL_STABLE"


def test_theorem4_born_ldlt_mandel_weyl_fragile_and_symmetry():
    """정리 4: Born PD/Non-PD, Voigt & Mandel 순수 유리수 Weyl 강건성, 구성적 WEYL_FRAGILE 반례,
    축치환(c||x) 정방정 대칭성 검증.
    """
    C_diam = np.array([
        [1000, 120, 120, 0, 0, 0],
        [120, 1000, 120, 0, 0, 0],
        [120, 120, 1000, 0, 0, 0],
        [0, 0, 0, 550, 0, 0],
        [0, 0, 0, 0, 550, 0],
        [0, 0, 0, 0, 0, 550],
    ], dtype=float)
    r_d = audit_elastic_tensor("DIAM", "C", C_diam, spg_number=227, emit_certificate=True)
    assert r_d.exact_verified and r_d.born_pd_exact
    assert r_d.robust_10gpa and r_d.mandel_robust_10gpa
    assert r_d.certificate_payload["kind"] == "WEYL_ROBUST"
    assert r_d.fragility_certificate_payload is None
    assert r_d.mandel_certificate_payload["kind"] == "MANDEL_WEYL_ROBUST"

    # 연성 입방정: C11=40, C12=37, C44=3 -> Voigt λ_min=3 (5 GPa 취약), Mandel λ_min=min(3, 6)=3 (5 GPa 취약)
    # 전단 연성 입방정: C11=100, C12=40, C44=4 -> Voigt λ_min=4 (<5 취약), Mandel λ_min=8 (>5 강건!)
    C_shear_soft = np.array([
        [100, 40, 40, 0, 0, 0],
        [40, 100, 40, 0, 0, 0],
        [40, 40, 100, 0, 0, 0],
        [0, 0, 0, 4, 0, 0],
        [0, 0, 0, 0, 4, 0],
        [0, 0, 0, 0, 0, 4],
    ], dtype=float)
    r_ss = audit_elastic_tensor("SHSOFT", "Na", C_shear_soft, spg_number=229, emit_certificate=True)
    assert r_ss.born_pd_exact
    assert r_ss.robust_1gpa and (not r_ss.robust_5gpa)
    assert r_ss.mandel_robust_1gpa and r_ss.mandel_robust_5gpa and (not r_ss.mandel_robust_10gpa)
    # 구성적 WEYL_FRAGILE (delta=5 GPa) 및 MANDEL_WEYL_FRAGILE (delta=10 GPa) 반례 검증
    assert r_ss.fragility_certificate_payload is not None
    assert r_ss.fragility_certificate_payload["kind"] == "WEYL_FRAGILE"
    assert r_ss.fragility_certificate_payload["delta"] == Fraction(5, 1)
    assert verify_weyl_fragile_certificate(
        r_ss.fragility_certificate_payload["C"],
        r_ss.fragility_certificate_payload["delta"],
        r_ss.fragility_certificate_payload["v"],
    )
    assert r_ss.mandel_fragility_certificate_payload is not None
    assert r_ss.mandel_fragility_certificate_payload["kind"] == "MANDEL_WEYL_FRAGILE"
    assert r_ss.mandel_fragility_certificate_payload["delta"] == Fraction(10, 1)
    assert verify_mandel_weyl_fragile_certificate(
        r_ss.mandel_fragility_certificate_payload["C"],
        r_ss.mandel_fragility_certificate_payload["delta"],
        r_ss.mandel_fragility_certificate_payload["v"],
    )

    # 빈 행렬 및 비대칭 행렬은 exact_ldlt_or_counterexample 에서 엄격 거부
    with pytest.raises(ValueError):
        exact_ldlt_or_counterexample([])
    with pytest.raises(ValueError):
        exact_ldlt_or_counterexample([[Fraction(-1), Fraction(10)], [Fraction(0), Fraction(1)]])

    # Born 불안정 결정 (C11=40, C12=45)
    C_bad = np.array([
        [40, 45, 45, 0, 0, 0],
        [45, 40, 45, 0, 0, 0],
        [45, 45, 40, 0, 0, 0],
        [0, 0, 0, 10, 0, 0],
        [0, 0, 0, 0, 10, 0],
        [0, 0, 0, 0, 0, 10],
    ], dtype=float)
    r_b = audit_elastic_tensor("BAD", "X", C_bad, spg_number=225, emit_certificate=True)
    assert r_b.exact_verified and (not r_b.born_pd_exact)
    assert r_b.certificate_payload["kind"] == "BORN_NON_PD"
    assert quad_form_exact(r_b.certificate_payload["C"], r_b.certificate_payload["v"]) < 0

    # 주축이 x축(c||x)인 정방정 텐서 (JVASP-85840 CuF2 형상) 축치환 대칭성 통과 확인
    C_tet_x = np.array([
        [181.4, 104.4, 104.4,  0.0,  0.0,  0.0],
        [104.4, 125.7, 100.6,  0.0,  0.0,  0.0],
        [104.4, 100.6, 125.7,  0.0,  0.0,  0.0],
        [  0.0,   0.0,   0.0, 16.0,  0.0,  0.0],
        [  0.0,   0.0,   0.0,  0.0, 72.4,  0.0],
        [  0.0,   0.0,   0.0,  0.0,  0.0, 16.0],
    ], dtype=float)
    sym_tx = compute_voigt_symmetry_violations(C_tet_x, spg_number=136, convention="vasp")
    assert sym_tx["matched_setting"] == "c_axis_x"
    assert sym_tx["max_voigt_violation_gpa"] < 1e-9
    assert sym_tx["max_voigt_violation_fixed_std_gpa"] > 50.0


def test_vasp_vs_ieee_elastic_symmetry_convention():
    """JARVIS/VASP OUTCAR 전단 순서 (XY, YZ, ZX) vs IEEE Voigt (YZ, ZX, XY) 대칭성 판정 검증."""
    C_vasp = np.array([
        [234.0, 135.4,  70.8,  0.0,  19.9,  0.0],
        [135.4, 234.0,  70.8,  0.0, -19.9,  0.0],
        [ 70.8,  70.8, 197.7,  0.0,   0.0,  0.0],
        [  0.0,   0.0,   0.0, 49.3,   0.0, 19.9],
        [ 19.9, -19.9,   0.0,  0.0,  47.4,  0.0],
        [  0.0,   0.0,   0.0, 19.9,   0.0, 47.4],
    ], dtype=float)
    assert compute_voigt_symmetry_violations(C_vasp, spg_number=166, convention="vasp")["max_voigt_violation_gpa"] < 1e-9
    assert compute_voigt_symmetry_violations(C_vasp, spg_number=166, convention="auto")["max_voigt_violation_gpa"] < 1e-9
    assert compute_voigt_symmetry_violations(C_vasp, spg_number=166, convention="ieee")["max_voigt_violation_gpa"] > 19.0


def test_lean_binary_and_independent_verifier_differential_parity(tmp_path: Path):
    """컴파일된 Lean 4 `certmat-check` 바이너리와 독립 Python 검증기가
    12종 유효 증명서 + 30종 적대적 변조/파싱 엣지케이스에서 100% 동일한 판정을 내리는지 차분 검증한다.
    """
    exe = find_lean_checker_binary()
    assert exe is not None and exe.exists(), "Lean 4 certmat-check 바이너리가 빌드되어 있어야 합니다."

    # 1) 12종 전체 유효 증명서 생성
    comp = [[Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)]]
    cx = [Fraction(1, 2), Fraction(1, 2)]
    valid_certs = [
        # DUAL_STABLE
        {"kind": "DUAL_STABLE", "m": 2, "E": 2, "ex": Fraction(-1, 2), "delta": Fraction(1, 2),
         "cx": cx, "c": comp, "en": [Fraction(0), Fraction(0)], "mu": [Fraction(0), Fraction(0)]},
        # PRIMAL_UNSTABLE
        {"kind": "PRIMAL_UNSTABLE", "m": 2, "E": 2, "ex": Fraction(1, 5),
         "cx": cx, "c": comp, "en": [Fraction(0), Fraction(0)], "lam": [Fraction(1, 2), Fraction(1, 2)]},
        # INTERVAL_STABLE
        {"kind": "INTERVAL_STABLE", "m": 2, "E": 2, "ex": Fraction(-1, 2), "wx": Fraction(1, 10),
         "eps": Fraction(1), "delta": Fraction(0), "cx": cx, "c": comp,
         "en": [Fraction(0), Fraction(0)], "w": [Fraction(1, 10), Fraction(1, 10)],
         "mu": [Fraction(-1, 10), Fraction(-1, 10)]},
        # INTERVAL_UNSTABLE
        {"kind": "INTERVAL_UNSTABLE", "m": 2, "E": 2, "ex": Fraction(1, 2), "wx": Fraction(1, 10),
         "eps": Fraction(1), "cx": cx, "c": comp,
         "en": [Fraction(0), Fraction(0)], "w": [Fraction(1, 10), Fraction(1, 10)],
         "lam": [Fraction(1, 2), Fraction(1, 2)]},
        # INTERVAL_FRAGILE_DESTAB
        {"kind": "INTERVAL_FRAGILE_DESTAB", "m": 2, "E": 2, "ex": Fraction(-1, 20), "wx": Fraction(1, 10),
         "eps": Fraction(1), "cx": cx, "c": comp,
         "en": [Fraction(0), Fraction(0)], "w": [Fraction(1, 10), Fraction(1, 10)],
         "lam": [Fraction(1, 2), Fraction(1, 2)]},
        # INTERVAL_FRAGILE_STAB
        {"kind": "INTERVAL_FRAGILE_STAB", "m": 2, "E": 2, "ex": Fraction(1, 20), "wx": Fraction(1, 10),
         "eps": Fraction(1), "cx": cx, "c": comp,
         "en": [Fraction(0), Fraction(0)], "w": [Fraction(1, 10), Fraction(1, 10)],
         "mu": [Fraction(1, 10), Fraction(1, 10)]},
    ]
    # BORN_LDLT, BORN_NON_PD, WEYL_ROBUST, WEYL_FRAGILE, MANDEL_WEYL_ROBUST, MANDEL_WEYL_FRAGILE
    C_soft = np.diag([100.0, 100.0, 100.0, 4.0, 4.0, 4.0])
    C_tiny = np.diag([0.5, 100.0, 100.0, 50.0, 50.0, 50.0])
    C_bad = np.diag([100.0, -5.0, 100.0, 50.0, 50.0, 50.0])
    rs = audit_elastic_tensor("S", "X", C_soft, spg_number=227, emit_certificate=True)
    rt = audit_elastic_tensor("T", "X", C_tiny, spg_number=227, emit_certificate=True)
    rb = audit_elastic_tensor("B", "X", C_bad, spg_number=227, emit_certificate=True)
    valid_certs.extend([
        rt.certificate_payload,               # BORN_LDLT
        rb.certificate_payload,               # BORN_NON_PD
        rs.certificate_payload,               # WEYL_ROBUST (1 GPa)
        rs.fragility_certificate_payload,     # WEYL_FRAGILE (5 GPa)
        rs.mandel_certificate_payload,        # MANDEL_WEYL_ROBUST (5 GPa)
        rs.mandel_fragility_certificate_payload,  # MANDEL_WEYL_FRAGILE (10 GPa)
    ])
    assert {c["kind"] for c in valid_certs} == {
        "DUAL_STABLE", "PRIMAL_UNSTABLE", "INTERVAL_STABLE", "INTERVAL_UNSTABLE",
        "INTERVAL_FRAGILE_DESTAB", "INTERVAL_FRAGILE_STAB",
        "BORN_LDLT", "BORN_NON_PD", "WEYL_ROBUST", "WEYL_FRAGILE",
        "MANDEL_WEYL_ROBUST", "MANDEL_WEYL_FRAGILE",
    }

    tsv_ok = tmp_path / "all_12_valid.tsv"
    write_certificates_tsv(valid_certs, tsv_ok)
    res_py = verify_tsv_independent(tsv_ok)
    res_lean = verify_tsv_with_lean(tsv_ok)
    assert res_py["all_passed"] and res_py["passed"] == 12 and res_py["failed"] == 0
    assert res_lean["all_passed"] and res_lean["passed"] == 12 and res_lean["failed"] == 0

    # 2) 적대적 변조·파싱 경계 + 12종 전체 의미적 거짓(semantically false) 증명서 — Lean과 Python이 매 케이스 동일 거부!
    valid_line_0 = tsv_ok.read_text(encoding="utf-8").splitlines()[1]
    eye6 = "\t".join("1" if i == j else "0" for i in range(6) for j in range(6))
    diag10_6 = "\t".join("10" if i == j else "0" for i in range(6) for j in range(6))
    bad_cases = [
        # 파싱/구문 위반
        ("plus_sign_nat", "DUAL_STABLE\t+2\t2\t-1/2\t1/2\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("plus_sign_q", "DUAL_STABLE\t2\t2\t+1/2\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("underscore_num", "DUAL_STABLE\t2\t2\t-1_0\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("zero_denom", "DUAL_STABLE\t2\t2\t-1/0\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("space_inside_token", "DUAL_STABLE\t2\t2\t -1/2\t1/2\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("vacuous_m0", "DUAL_STABLE\t0\t2\t0\t0\t1/2\t1/2\t0\t0"),
        ("unnormalized_cx", "DUAL_STABLE\t2\t2\t-1/2\t0\t1/2\t1/3\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("neg_weight_interval", "INTERVAL_STABLE\t2\t2\t-1/2\t-1/10\t1\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/10\t1/10\t0\t0"),
        ("neg_eps_interval", "INTERVAL_STABLE\t2\t2\t-1/2\t1/10\t-1\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/10\t1/10\t0\t0"),
        ("trailing_token", valid_line_0 + "\t999"),
        ("truncated_line", "INTERVAL_STABLE\t2\t2\t0"),
        ("zero_witness_nonpd", "BORN_NON_PD\t2\t1\t0\t0\t-1\t0\t0"),
        ("zero_witness_weyl_frag", "WEYL_FRAGILE\t2\t5\t1\t0\t0\t1\t0\t0"),
        ("zero_witness_mandel_frag", f"MANDEL_WEYL_FRAGILE\t5\t{eye6}\t0\t0\t0\t0\t0\t0"),
        ("neg_delta_mandel_frag", f"MANDEL_WEYL_FRAGILE\t-1\t{eye6}\t1\t0\t0\t0\t0\t0"),
        # 음수 delta 차단 (Codex #1, Claude L1 회귀)
        ("neg_delta_dual_stable", "DUAL_STABLE\t1\t1\t1\t-1\t1\t1\t0\t0"),
        ("neg_delta_dual_stable_2d", "DUAL_STABLE\t2\t2\t5\t-5\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("neg_delta_interval_stable", "INTERVAL_STABLE\t1\t1\t1\t0\t0\t-1\t1\t1\t0\t0\t0"),
        # 12종 전체 의미적 거짓(well-formed but mathematically false) 증명서 거부
        ("false_dual_stable", "DUAL_STABLE\t2\t2\t1/2\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t0\t0"),
        ("false_primal_unstable", "PRIMAL_UNSTABLE\t2\t2\t-1/2\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/2\t1/2"),
        ("false_interval_stable", "INTERVAL_STABLE\t2\t2\t-1/20\t1/10\t1\t0\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/10\t1/10\t-1/10\t-1/10"),
        ("false_interval_unstable", "INTERVAL_UNSTABLE\t2\t2\t1/20\t1/10\t1\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/10\t1/10\t1/2\t1/2"),
        ("false_interval_frag_destab", "INTERVAL_FRAGILE_DESTAB\t2\t2\t-1/2\t1/10\t1\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/10\t1/10\t1/2\t1/2"),
        ("false_interval_frag_stab", "INTERVAL_FRAGILE_STAB\t2\t2\t1/2\t1/10\t1\t1/2\t1/2\t1\t0\t0\t1\t0\t0\t1/10\t1/10\t1/10\t1/10"),
        ("false_born_ldlt_neg_d", "BORN_LDLT\t2\t1\t0\t0\t-1\t1\t0\t0\t1\t1\t-1"),
        ("false_born_non_pd_pos_q", "BORN_NON_PD\t2\t2\t0\t0\t2\t1\t0"),
        ("false_weyl_robust_delta_gt_lam0", "WEYL_ROBUST\t2\t1\t2\t5\t0\t0\t5\t1\t0\t0\t1\t4\t4"),
        ("false_weyl_frag_margin", "WEYL_FRAGILE\t2\t1\t10\t0\t0\t10\t1\t0"),
        ("false_mandel_weyl_robust", f"MANDEL_WEYL_ROBUST\t1\t2\t{eye6}\t{eye6}\t1\t1\t1\t1\t1\t1"),
        ("false_mandel_weyl_frag_margin", f"MANDEL_WEYL_FRAGILE\t10\t{diag10_6}\t0\t0\t0\t1\t0\t0"),
    ]
    for name, bad_line in bad_cases:
        p = tmp_path / f"bad_{name}.tsv"
        p.write_text(bad_line + "\n", encoding="utf-8")
        py_r = verify_tsv_independent(p)
        ln_r = verify_tsv_with_lean(p)
        assert (not py_r["all_passed"]) and py_r["failed"] == 1, f"Python이 {name} 을 거부하지 못함"
        assert (not ln_r["all_passed"]) and ln_r["failed"] == 1, f"Lean이 {name} 을 거부하지 못함"


def test_lean_kernel_axioms_and_zero_forbidden_keywords():
    """Lean 4 커널 및 Main.lean 정적 금지 키워드 0건 및 51개 핵심 정리 `#print axioms` 표준 공리 전용 기계 검증."""
    import reproduce_all as ra

    lean_root = Path(__file__).resolve().parent.parent / "lean"
    lean_files = list(lean_root.rglob("*.lean"))
    assert len(lean_files) >= 8
    strict_re = re.compile(
        r"\b(sorry|axiom|admit|implemented_by|extern|unsafe|partial|opaque|native_decide|csimp)\b"
    )
    for lf in lean_files:
        text = lf.read_text(encoding="utf-8")
        no_comments = ra._strip_lean_comments(text)
        if lf.name != "lakefile.lean":
            assert not strict_re.search(no_comments), f"커널/CLI 금지 키워드 발견: {lf}"
        else:
            assert not re.search(r"\b(sorry|axiom|admit|native_decide|implemented_by|extern|unsafe)\b", no_comments), f"금지 키워드 발견: {lf}"

    # 중첩 블록 주석 제거 단위 검증
    assert ra._strip_lean_comments("def x /- outer /- inner -/ still comment -/ := 1 -- tail").strip() == "def x  := 1"

    ax = verify_lean_axioms(lean_root)
    assert ax["lean_available"]
    assert ax["all_standard_axioms_only"]
    assert ax["zero_sorry_ax"]
    assert ax["n_theorems_checked"] == ax["n_theorems_expected"] == 51
    assert ax["missing_theorems"] == []
    assert ax["non_standard_axioms"] == {}


def test_reproduce_all_fail_closed_and_paper_consistency(tmp_path: Path, monkeypatch):
    """reproduce_all.py 의 fail-closed 필수 산출물 검사 및 논문 문서 무결성(물결표 0건·주요 수치 정합성)을 검증한다."""
    import json
    import reproduce_all as ra

    # 1) 디스크와 매니페스트에서 필수 요약 JSON을 동시에 삭제해도 fail-closed 거부됨을 검증
    fake_res = tmp_path / "results"
    fake_res.mkdir()
    (tmp_path / "lean").mkdir()
    (tmp_path / "paper").mkdir()
    (tmp_path / "certmat").mkdir()
    (tmp_path / "scripts").mkdir()
    (tmp_path / "tests").mkdir()
    fake_mf = fake_res / "reproduction_manifest.json"
    fake_mf.write_text(json.dumps({"generated_at_utc": "2026-01-01T00:00:00Z", "n_files": 0, "files": {}}), encoding="utf-8")
    monkeypatch.setattr(ra, "ROOT_DIR", tmp_path)
    monkeypatch.setattr(ra, "RESULTS_DIR", fake_res)
    monkeypatch.setattr(ra, "LEAN_DIR", tmp_path / "lean")
    monkeypatch.setattr(ra, "PAPER_DIR", tmp_path / "paper")
    monkeypatch.setattr(ra, "MANIFEST_PATH", fake_mf)
    mf_chk = ra.verify_artifact_manifest()
    assert not mf_chk["all_ok"]
    assert any("UNTRACKED_IN_MANIFEST:" in m for m in mf_chk["mismatches"])
    tsv_chk = ra.verify_all_tsv_certificates(allow_build=False)
    assert not tsv_chk["all_passed"]
    assert len(tsv_chk["missing_required_tsv_files"]) == len(ra.REQUIRED_TSV_FILES)

    # 2) 논문 및 한국어 요약 문서의 범위 표기 물결표(~) 0건 및 JSON 핵심 수치 정합성 확인
    root = Path(__file__).resolve().parent.parent
    en_text = (root / "paper" / "certmat_paper.md").read_text(encoding="utf-8")
    ko_text = (root / "paper" / "certmat_summary_ko.md").read_text(encoding="utf-8")
    assert "~" not in en_text, "영문 논문에 금지된 물결표(~)가 포함되어 있습니다."
    assert "~" not in ko_text, "한국어 요약서에 금지된 물결표(~)가 포함되어 있습니다."

    res_dir = root / "results"
    if (res_dir / "lean_verification_report.json").exists():
        lr = json.loads((res_dir / "lean_verification_report.json").read_text(encoding="utf-8"))
        je = json.loads((res_dir / "jarvis_elastic_summary.json").read_text(encoding="utf-8"))
        jp = json.loads((res_dir / "jarvis_phase_summary.json").read_text(encoding="utf-8"))
        wp = json.loads((res_dir / "wbm_phase_summary.json").read_text(encoding="utf-8"))
        gp = json.loads((res_dir / "gnome_pbe_full_summary.json").read_text(encoding="utf-8"))
        gr = json.loads((res_dir / "gnome_r2scan_full_summary.json").read_text(encoding="utf-8"))

        n_thms = lr["lean_kernel_check"]["axioms_check"]["n_theorems_checked"]
        n_certs = lr["tsv_certificate_verification"]["lean_total_passed"]
        assert f"{n_thms}" in en_text and f"{n_thms}" in ko_text
        assert f"{n_certs:,}" in en_text and f"{n_certs:,}" in ko_text
        for num in (
            je["n_valid_6x6"],
            je["born_pd_count"],
            je["born_non_pd_count"],
            je["certificate_verification"]["mandel_weyl_tsv"]["n_mandel_robust"],
            je["certificate_verification"]["mandel_weyl_tsv"]["n_mandel_fragile_witnesses"],
            jp["n_nom_stable"],
            jp["phase_switching"]["nom_stable_count"],
            wp["mp2020_reported_stable_subset"]["already_unstable_on_wbm_intracatalog_hull"],
            gp["n_total"],
            gp["phase_switching"]["nom_stable_count"],
            gr["n_total"],
            gr["phase_switching"]["nom_stable_count"],
        ):
            assert f"{num:,}" in en_text, f"영문 논문에 {num:,} 수치 누락"
            assert f"{num:,}" in ko_text, f"한국어 요약서에 {num:,} 수치 누락"
