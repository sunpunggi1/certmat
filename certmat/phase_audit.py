"""
CertMat 상평형(Convex Hull) 강건 안정성 감사 엔진.

기능:
1. 화학식 파서(정확한 정수/유리수 화학양론 → 정규화 원자 분율 Fraction)
2. 화학 부분계(Chemical Subsystem) 인덱싱 및 동일 조성 동질이상(Polymorph) 최저 2개 가지치기
   (현재 불확실성 가중치 w_i 가 원소 집합의 함수이므로 동일 조성 내에서는 모든 동질이상의 w_i 가
    동일하며, 따라서 최하 에너지 2개 보존만으로 자기 자신 제외 경쟁상 지배 관계가 수학적으로 완전 성립)
3. 균일 오차(10, 25, 50 meV/atom 등) 및 화학종·보정별 이질적 오차 모델 감사
4. 정확한 임계 전복 반경 ε*(x), 분해 경로 전환(Phase Switching) 검출,
   Lean 4 체커 호환 정확한 유리수 증명서(μ, λ) 생성
"""

from __future__ import annotations

import math
import re
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations
from typing import Dict, FrozenSet, Iterable, List, Mapping, Optional, Sequence, Tuple

from certmat.exact_lp import (
    ExactHullLPResult,
    ExactRadiusResult,
    solve_critical_radius_exact,
    solve_hull_primal_dual_exact,
    to_fraction,
    verify_dual_stable,
    verify_primal_unstable,
)
from certmat.uncertainty import (
    HETERO_CHEM_PROFILE,
    UncertaintyProfile,
    classify_chemistry,
    get_phase_uncertainty,
)

# 주기율표 원소 기호 + 선택적 수량(정수 또는 소수) 파싱 정규식
_FORMULA_TOKEN_RE = re.compile(r"([A-Z][a-z]?)([0-9]*\.?[0-9]*)")


def parse_formula_counts(formula: str) -> Dict[str, Fraction]:
    """화학식 문자열(괄호 포함, 예: 'Cs(ZrS2)3', 'Ac6 U2', 'LiFePO4')을 원소별 정확한 수량(Fraction)으로 파싱한다."""
    s = formula.strip().replace(" ", "")
    if not s:
        raise ValueError("빈 화학식입니다.")

    # 괄호 전개 스택 파서
    stack: List[Dict[str, Fraction]] = [{}]
    i = 0
    n = len(s)
    while i < n:
        ch = s[i]
        if ch in "([":
            stack.append({})
            i += 1
        elif ch in ")]":
            if len(stack) == 1:
                raise ValueError(f"괄호 불일치 화학식: {formula}")
            top = stack.pop()
            i += 1
            j = i
            while j < n and (s[j].isdigit() or s[j] == "."):
                j += 1
            try:
                mult = to_fraction(s[i:j]) if j > i else Fraction(1)
            except Exception as exc:
                raise ValueError(f"화학식 괄호 배수 파싱 실패 ('{formula}': '{s[i:j]}')") from exc
            i = j
            cur = stack[-1]
            for el, cnt in top.items():
                cur[el] = cur.get(el, Fraction(0)) + cnt * mult
        else:
            m = _FORMULA_TOKEN_RE.match(s, i)
            if not m:
                raise ValueError(f"화학식 파싱 실패 ('{formula}' 위치 {i}: '{s[i:]}')")
            el, num_str = m.group(1), m.group(2)
            try:
                cnt = to_fraction(num_str) if num_str else Fraction(1)
            except Exception as exc:
                raise ValueError(f"화학식 원소 수량 파싱 실패 ('{formula}': '{num_str}')") from exc
            cur = stack[-1]
            cur[el] = cur.get(el, Fraction(0)) + cnt
            i = m.end()

    if len(stack) != 1 or not stack[0]:
        raise ValueError(f"유효하지 않은 화학식: {formula}")
    counts = {el: cnt for el, cnt in stack[0].items() if cnt > 0}
    if not counts:
        raise ValueError(f"양의 원자 수가 없는 화학식입니다: {formula}")
    return counts


def formula_to_atom_fractions(formula: str) -> Dict[str, Fraction]:
    """화학식을 합이 정확히 1인 원소별 원자 분율(Fraction) 딕셔너리로 정규화한다."""
    counts = parse_formula_counts(formula)
    total = sum(counts.values(), Fraction(0))
    if total <= 0:
        raise ValueError(f"원자 수 합이 0 이하입니다: {formula}")
    return {el: cnt / total for el, cnt in sorted(counts.items())}


def composition_key(comp: Mapping[str, Fraction]) -> Tuple[Tuple[str, Fraction], ...]:
    """정규화 조성의 해시 가능 키(동질이상 그룹화용)."""
    return tuple(sorted((el, q) for el, q in comp.items() if q > 0))


@dataclass(frozen=True)
class PhaseEntry:
    """상평형 그래프 내 단일 결정상 엔트리."""
    material_id: str
    formula: str
    comp: Dict[str, Fraction]
    energy_per_atom: Fraction       # 형성에너지(eV/atom)
    elements: FrozenSet[str] = field(init=False)
    comp_key: Tuple[Tuple[str, Fraction], ...] = field(init=False)
    chem_class: str = field(init=False)
    reported_ehull: Optional[float] = None
    extra_correction_ev: Optional[float] = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "elements", frozenset(self.comp.keys()))
        object.__setattr__(self, "comp_key", composition_key(self.comp))
        object.__setattr__(self, "chem_class", classify_chemistry(self.comp.keys()))


@dataclass
class PhaseAuditRecord:
    """단일 후보상 x 에 대한 정확한 강건 상평형 감사 결과."""
    material_id: str
    formula: str
    chem_class: str
    n_elements: int
    n_competing: int
    energy_per_atom: float
    # 명목 안정성 (후보상 자체 제외 경쟁상 기준: >0 안정 여유, =0 경계 공존, <0 불안정 ehull=-margin)
    nominal_margin_mev: float
    nominal_ehull_mev: float
    is_nominally_stable: bool
    # 균일 불확실성 (w_i = 1) 임계 반경 ε*_unif (meV/atom) 및 정확 유리수 기반 상태 분류
    eps_uniform_mev: float
    status_10mev: str          # "Certified_Robust_Stable" | "Fragile" | "Certified_Robust_Unstable" | "Uncompeted_Elemental"
    status_25mev: str
    status_50mev: str
    # 이질적 불확실성 (w_i = σ_i) 임계 배율 scale*(x) 및 상태 (scale >= 1 이면 강건 안정, > 1 이면 강건 불안정)
    hetero_sigma_x_mev: float
    hetero_critical_scale: float   # 무한대인 경우 math.inf (유한 sentinel 미사용)
    status_hetero: str
    # 분해 경로 전환(Phase Switching) 분석
    nominal_decomp_ids: List[str]
    adversarial_decomp_ids: List[str]
    phase_switching: bool
    naive_nominal_scale: float     # 명목 분해 경로만 고정했을 때의 임계 배율 (무한대이면 math.inf)
    switching_overestimation_pct: float
    # 검증 메타 및 세분화 지표
    solver_used: str
    exact_verified: bool
    is_uncompeted: bool = False
    is_exact_boundary: bool = False
    near_zero_margin_1mev: bool = False
    critical_robust_to_fragile_flip: bool = False
    same_comp_polymorph_decomp: bool = False
    # 선택적 정확 유리수 증명서(Lean 4 체커 내보내기용, 데이터 바인딩 메타 포함)
    certificate_payload: Optional[Dict[str, object]] = None


class PhaseDiagramIndex:
    """화학 부분계(Element Subset) 기반 고속 상평형 인덱스.

    동일 조성 내 동질이상(Polymorph) 최저 2개 가지치기는 불확실성 가중치 w_i 가
    조성(원소 집합)만의 함수일 때 수학적으로 무손실이며, 중복 material_id 를 엄격 차단한다.
    """

    def __init__(
        self,
        phases: Sequence[PhaseEntry],
        add_elemental_refs: bool = True,
        prune_polymorphs: bool = True,
    ) -> None:
        self.phases: List[PhaseEntry] = list(phases)
        self.by_elem_set: Dict[FrozenSet[str], List[PhaseEntry]] = {}
        self.all_elements: set[str] = set()
        self.injected_elemental_refs: List[str] = []
        self.negative_elemental_phases: List[Tuple[str, str, float]] = []
        self.prune_polymorphs: bool = prune_polymorphs

        seen_ids: set[str] = set()
        for p in self.phases:
            if p.material_id in seen_ids:
                raise ValueError(f"중복된 material_id가 감지되었습니다: {p.material_id}")
            seen_ids.add(p.material_id)
            self.all_elements.update(p.elements)
            self.by_elem_set.setdefault(p.elements, []).append(p)
            if len(p.elements) == 1 and p.energy_per_atom < 0:
                self.negative_elemental_phases.append((p.material_id, p.formula, float(p.energy_per_atom)))

        # 형성에너지(ΔH_f) 기준 순수 원소 참조상(ΔH_f = 0)이 없으면 명시적으로 보충하고 기록
        if add_elemental_refs:
            for el in sorted(self.all_elements):
                eset = frozenset([el])
                existing = self.by_elem_set.get(eset, [])
                has_zero_or_lower = any(p.energy_per_atom <= 0 for p in existing)
                if not has_zero_or_lower:
                    ref_id = f"ELEM_REF_{el}"
                    ref = PhaseEntry(
                        material_id=ref_id,
                        formula=el,
                        comp={el: Fraction(1, 1)},
                        energy_per_atom=Fraction(0, 1),
                    )
                    self.by_elem_set.setdefault(eset, []).append(ref)
                    self.injected_elemental_refs.append(ref_id)

        # 각 원소 집합 내 동일 조성(동질이상)에서 최저 에너지 2개(자기 자신 제외 대비)만 유지하는
        # 고속 후보 테이블 사전 구축 (조성 의존 가중치 모델에서 무손실 지배)
        self._pruned_by_elem_set: Dict[FrozenSet[str], List[PhaseEntry]] = {}
        for eset, plist in self.by_elem_set.items():
            if not prune_polymorphs:
                self._pruned_by_elem_set[eset] = list(plist)
                continue
            by_ck: Dict[Tuple[Tuple[str, Fraction], ...], List[PhaseEntry]] = {}
            for p in plist:
                by_ck.setdefault(p.comp_key, []).append(p)
            kept: List[PhaseEntry] = []
            for ck, group in by_ck.items():
                group.sort(key=lambda x: (x.energy_per_atom, x.material_id))
                # 최하 2개를 보존하여 최하상 자신을 감사할 때 2번째 동질이상이 경쟁상으로 남도록 보장
                kept.extend(group[:2])
            self._pruned_by_elem_set[eset] = kept

    def get_competing_phases(self, candidate: PhaseEntry) -> List[PhaseEntry]:
        """후보상 x 의 부분 원소 집합에 속하는 모든 비지배 경쟁상(자기 자신 제외)을 반환한다."""
        elems = sorted(candidate.elements)
        k = len(elems)
        competing: List[PhaseEntry] = []
        if k <= 10:
            for r in range(1, k + 1):
                for sub in combinations(elems, r):
                    eset = frozenset(sub)
                    plist = self._pruned_by_elem_set.get(eset)
                    if not plist:
                        continue
                    for p in plist:
                        if p.material_id == candidate.material_id:
                            continue
                        competing.append(p)
        else:
            for eset, plist in self._pruned_by_elem_set.items():
                if eset.issubset(candidate.elements):
                    for p in plist:
                        if p.material_id != candidate.material_id:
                            competing.append(p)

        if not getattr(self, "prune_polymorphs", True):
            return competing

        # 동일 조성 내 최하 에너지 1개만 남김 (같은 조성은 chem_class 와 w_i 가 동일하므로 무손실 지배)
        best_by_ck: Dict[Tuple[Tuple[str, Fraction], ...], PhaseEntry] = {}
        for p in competing:
            prev = best_by_ck.get(p.comp_key)
            if prev is None or (p.energy_per_atom, p.material_id) < (prev.energy_per_atom, prev.material_id):
                best_by_ck[p.comp_key] = p
        return list(best_by_ck.values())


def _classify_uniform_status_exact(
    is_nom_stable: bool, eps_crit_ev: Fraction, threshold_ev: Fraction
) -> str:
    """정확한 유리수(Fraction) 비교로 균일 오차 3분류 상태를 판정한다.

    경계 규약(Boundary Convention):
      - 명목 안정(margin ≥ 0): 닫힌 구간 끝점에서 공존(E_x + ε ≤ ∑ λ_i (E_i - ε))까지 허용하므로 ε* ≥ threshold 이면 강건 안정.
      - 명목 불안정(margin < 0): 엄격 불안정(∑ λ_i (E_i + ε) < E_x - ε)을 요구하므로 ε* > threshold 일 때만 강건 불안정.
    """
    if is_nom_stable:
        return "Certified_Robust_Stable" if eps_crit_ev >= threshold_ev else "Fragile"
    return "Certified_Robust_Unstable" if eps_crit_ev > threshold_ev else "Fragile"


def audit_single_phase(
    candidate: PhaseEntry,
    competing: Sequence[PhaseEntry],
    hetero_profile: UncertaintyProfile = HETERO_CHEM_PROFILE,
    custom_class_sigma: Optional[Mapping[str, Fraction]] = None,
    use_z3_fallback: bool = True,
    emit_certificate: bool = False,
    cert_uniform_ev: Fraction = Fraction(25, 1000),
) -> PhaseAuditRecord:
    """단일 후보상 x 에 대해 명목 안정성, 균일/이질적 임계 반경, Phase Switching, Lean 4 TCB 구간 증명서를 정확 계산한다."""
    elems = sorted(candidate.elements)
    E = len(elems)

    cx = [candidate.comp.get(el, Fraction(0)) for el in elems]
    ex = candidate.energy_per_atom

    comp_list = list(competing)
    # 단원소 순수상이고 경쟁상이 전혀 없는 경우: LP 증명서가 없으므로 별도 범주("Uncompeted_Elemental")로 분리
    if not comp_list:
        sigma_x, _ = get_phase_uncertainty(
            elems, mode="hetero", profile=hetero_profile, custom_class_sigma=custom_class_sigma
        )
        return PhaseAuditRecord(
            material_id=candidate.material_id,
            formula=candidate.formula,
            chem_class=candidate.chem_class,
            n_elements=E,
            n_competing=0,
            energy_per_atom=float(ex),
            nominal_margin_mev=0.0,
            nominal_ehull_mev=0.0,
            is_nominally_stable=True,
            eps_uniform_mev=0.0,
            status_10mev="Uncompeted_Elemental",
            status_25mev="Uncompeted_Elemental",
            status_50mev="Uncompeted_Elemental",
            hetero_sigma_x_mev=float(sigma_x) * 1000.0,
            hetero_critical_scale=0.0,
            status_hetero="Uncompeted_Elemental",
            nominal_decomp_ids=[],
            adversarial_decomp_ids=[],
            phase_switching=False,
            naive_nominal_scale=0.0,
            switching_overestimation_pct=0.0,
            solver_used="uncompeted_elemental",
            exact_verified=False,
            is_uncompeted=True,
            is_exact_boundary=True,
            near_zero_margin_1mev=True,
            critical_robust_to_fragile_flip=False,
            same_comp_polymorph_decomp=False,
            certificate_payload=None,
        )

    m = len(comp_list)
    C_mat = [[p.comp.get(el, Fraction(0)) for el in elems] for p in comp_list]
    E_vec = [p.energy_per_atom for p in comp_list]

    # 1) 명목 Convex Hull 정확 유리수 원시·쌍대 해
    nom: ExactHullLPResult = solve_hull_primal_dual_exact(
        C_mat, cx, E_vec, ex, use_z3_fallback=use_z3_fallback
    )
    margin_ev = nom.stability_margin  # >0 안정 여유, =0 경계, <0 불안정(-ehull)
    is_nom_stable = margin_ev >= 0
    nom_ehull_ev = Fraction(0) if is_nom_stable else -margin_ev
    is_exact_boundary = (margin_ev == 0)
    near_zero_1mev = abs(margin_ev) < Fraction(1, 1000)

    # 균일 불확실성 (w_i = w_x = 1, 정규화 조성 ∑λ_i = 1) 에서는 분모가 항등적으로 2 이므로
    # ε*_unif = |margin_ev| / 2 가 정확히 성립 (정리 3c 및 valid_decomp_sum_one 에 의해 보장!)
    eps_unif_ev = abs(margin_ev) / 2
    eps_unif_mev = float(eps_unif_ev) * 1000.0

    # 2) 이질적 화학종·보정별 불확실성 가중치 w_i = σ_i(eV/atom)
    wx, _ = get_phase_uncertainty(
        candidate.elements, mode="hetero", profile=hetero_profile, custom_class_sigma=custom_class_sigma
    )
    W_vec = [
        get_phase_uncertainty(
            p.elements, mode="hetero", profile=hetero_profile, custom_class_sigma=custom_class_sigma
        )[0]
        for p in comp_list
    ]

    # Charnes-Cooper 정확 유리수 LP (전체/부분 0-가중치 및 무한 반경까지 exact_lp 내부에서 완전 처리)
    rad: ExactRadiusResult = solve_critical_radius_exact(
        C_mat, cx, E_vec, ex, W_vec, wx, use_z3_fallback=use_z3_fallback
    )

    # 3) Phase Switching 및 동질이상(same-composition) 분해 분석
    nom_active_idx = [i for i in range(m) if nom.lam[i] > 0]
    nom_support = sorted([comp_list[i].material_id for i in nom_active_idx])
    adv_support = sorted([comp_list[i].material_id for i in range(m) if rad.lam_adv[i] > 0])
    same_comp_poly = (
        len(nom_active_idx) == 1 and comp_list[nom_active_idx[0]].comp_key == candidate.comp_key
    )

    denom_nom = wx + sum(nom.lam[i] * W_vec[i] for i in range(m))
    # 비엄격 안정 규약(≤) 하에서는 분모=0 인 명목 경로가 margin ≥ 0(동률 포함)일 때 유한 ε 에서
    # 결코 엄격 불안정으로 전복되지 않으므로(+∞), margin < 0 일 때(-∞)와 동일하게 무한 반경으로 처리한다.
    naive_is_inf = (denom_nom == 0)
    naive_scale_q: Optional[Fraction] = None if naive_is_inf else (abs(margin_ev) / denom_nom)
    crit_scale_q: Optional[Fraction] = rad.critical_radius

    if rad.is_infinite:
        phase_switching = False
        overest_pct = 0.0
        critical_flip = False
        status_hetero = "Certified_Robust_Stable" if rad.infinite_sign > 0 else "Certified_Robust_Unstable"
    else:
        assert crit_scale_q is not None
        if is_nom_stable:
            if naive_scale_q is None:
                # 명목 경로 분모=0(무한대 추정)인데 실제 양의 가중치 최악 경로는 유한 반경으로 전복!
                phase_switching = (adv_support != nom_support)
                overest_pct = math.inf if phase_switching else 0.0
                critical_flip = (crit_scale_q < 1)
            else:
                phase_switching = (adv_support != nom_support) and (crit_scale_q < naive_scale_q)
                overest_pct = (
                    float((naive_scale_q - crit_scale_q) / crit_scale_q) * 100.0
                    if (phase_switching and crit_scale_q > 0)
                    else 0.0
                )
                critical_flip = phase_switching and (naive_scale_q >= 1) and (crit_scale_q < 1)
            status_hetero = "Certified_Robust_Stable" if crit_scale_q >= 1 else "Fragile"
        else:
            if naive_scale_q is None:
                phase_switching = False
                overest_pct = 0.0
            else:
                phase_switching = (adv_support != nom_support) and (crit_scale_q > naive_scale_q)
                overest_pct = (
                    float((crit_scale_q - naive_scale_q) / crit_scale_q) * 100.0
                    if (phase_switching and crit_scale_q > 0)
                    else 0.0
                )
            critical_flip = False
            status_hetero = "Certified_Robust_Unstable" if crit_scale_q > 1 else "Fragile"

    # 4) Lean 4 커널 TCB 내부에서 명목 에너지·가중치·반경(eps=1)으로부터 직접 구간을 구성해 검증하는 증명서 발급
    cert_payload: Optional[Dict[str, object]] = None
    if emit_certificate:
        L_box = [E_vec[i] - W_vec[i] for i in range(m)]
        U_box = [E_vec[i] + W_vec[i] for i in range(m)]
        Lx = ex - wx
        Ux = ex + wx
        zero_width_box = (wx == 0) and all(w == 0 for w in W_vec)
        meta_info = {
            "material_id": candidate.material_id,
            "formula": candidate.formula,
            "status_hetero": status_hetero,
            "model": hetero_profile.name if custom_class_sigma is None else "custom_sigma",
            "elements": elems,
            "competing_ids": [p.material_id for p in comp_list],
        }
        if status_hetero == "Certified_Robust_Stable":
            mu_cert = rad.mu_star
            if rad.is_infinite and not verify_dual_stable(C_mat, cx, L_box, Ux, mu_cert, Fraction(0)):
                mu_cert = solve_hull_primal_dual_exact(
                    C_mat, cx, L_box, Ux, use_z3_fallback=use_z3_fallback
                ).mu
            if not verify_dual_stable(C_mat, cx, L_box, Ux, mu_cert, Fraction(0)):
                raise RuntimeError("정리 3a 불변식 위반: Certified_Robust_Stable 인데 1x 박스 쌍대 증명 실패")
            cert_payload = {
                "kind": "INTERVAL_STABLE",
                "m": m,
                "E": E,
                "ex": ex,
                "wx": wx,
                "eps": Fraction(1),
                "delta": Fraction(0),
                "cx": cx,
                "c": C_mat,
                "en": E_vec,
                "w": W_vec,
                "mu": mu_cert,
                "meta": meta_info,
            }
        elif status_hetero == "Certified_Robust_Unstable":
            if not verify_primal_unstable(C_mat, cx, U_box, Lx, rad.lam_adv):
                raise RuntimeError("정리 3b 불변식 위반: Certified_Robust_Unstable 인데 1x 박스 원시 반례 실패")
            cert_payload = {
                "kind": "INTERVAL_UNSTABLE",
                "m": m,
                "E": E,
                "ex": ex,
                "wx": wx,
                "eps": Fraction(1),
                "cx": cx,
                "c": C_mat,
                "en": E_vec,
                "w": W_vec,
                "lam": rad.lam_adv,
                "meta": meta_info,
            }
        elif is_nom_stable:
            if zero_width_box:
                if not verify_dual_stable(C_mat, cx, L_box, Ux, rad.mu_star, Fraction(0)):
                    raise RuntimeError("폭 0 경계 구간 안정 증명 실패")
                cert_payload = {
                    "kind": "INTERVAL_STABLE",
                    "m": m,
                    "E": E,
                    "ex": ex,
                    "wx": wx,
                    "eps": Fraction(1),
                    "delta": Fraction(0),
                    "cx": cx,
                    "c": C_mat,
                    "en": E_vec,
                    "w": W_vec,
                    "mu": rad.mu_star,
                    "meta": meta_info,
                }
            else:
                if not verify_primal_unstable(C_mat, cx, L_box, Ux, rad.lam_adv):
                    raise RuntimeError("정리 3d-1 불변식 위반: 명목 안정 Fragile 불안정화 반례 실패")
                cert_payload = {
                    "kind": "INTERVAL_FRAGILE_DESTAB",
                    "m": m,
                    "E": E,
                    "ex": ex,
                    "wx": wx,
                    "eps": Fraction(1),
                    "cx": cx,
                    "c": C_mat,
                    "en": E_vec,
                    "w": W_vec,
                    "lam": rad.lam_adv,
                    "meta": meta_info,
                }
        else:
            # 명목 불안정이지만 Fragile (1x 박스 내부에서 안정화 가능한 극점 존재)
            if not verify_dual_stable(C_mat, cx, U_box, Lx, rad.mu_star, Fraction(0)):
                raise RuntimeError("정리 3d-2 불변식 위반: 명목 불안정 Fragile 안정화 쌍대 증명 실패")
            cert_payload = {
                "kind": "INTERVAL_FRAGILE_STAB",
                "m": m,
                "E": E,
                "ex": ex,
                "wx": wx,
                "eps": Fraction(1),
                "cx": cx,
                "c": C_mat,
                "en": E_vec,
                "w": W_vec,
                "mu": rad.mu_star,
                "meta": meta_info,
            }

    return PhaseAuditRecord(
        material_id=candidate.material_id,
        formula=candidate.formula,
        chem_class=candidate.chem_class,
        n_elements=E,
        n_competing=m,
        energy_per_atom=float(ex),
        nominal_margin_mev=float(margin_ev) * 1000.0,
        nominal_ehull_mev=float(nom_ehull_ev) * 1000.0,
        is_nominally_stable=is_nom_stable,
        eps_uniform_mev=eps_unif_mev,
        status_10mev=_classify_uniform_status_exact(is_nom_stable, eps_unif_ev, Fraction(10, 1000)),
        status_25mev=_classify_uniform_status_exact(is_nom_stable, eps_unif_ev, Fraction(25, 1000)),
        status_50mev=_classify_uniform_status_exact(is_nom_stable, eps_unif_ev, Fraction(50, 1000)),
        hetero_sigma_x_mev=float(wx) * 1000.0,
        hetero_critical_scale=(math.inf if crit_scale_q is None else float(crit_scale_q)),
        status_hetero=status_hetero,
        nominal_decomp_ids=nom_support,
        adversarial_decomp_ids=adv_support,
        phase_switching=phase_switching,
        naive_nominal_scale=(math.inf if naive_scale_q is None else float(naive_scale_q)),
        switching_overestimation_pct=overest_pct,
        solver_used=f"{nom.solver_used}|{rad.solver_used}",
        exact_verified=(nom.exact_verified and rad.exact_verified),
        is_uncompeted=False,
        is_exact_boundary=is_exact_boundary,
        near_zero_margin_1mev=near_zero_1mev,
        critical_robust_to_fragile_flip=critical_flip,
        same_comp_polymorph_decomp=same_comp_poly,
        certificate_payload=cert_payload,
    )
