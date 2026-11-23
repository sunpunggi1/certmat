"""
CertMat 정확한 유리수 선형계획(Exact Rational LP) 및 Z3 SMT 증명서 생성 엔진.

핵심 설계:
1. 빠른 경로(Fast Path): HiGHS(scipy.optimize.linprog)로 활성 기저(basis) 후보를 식별한 뒤,
   소규모 연립방정식을 순수 Python `fractions.Fraction` 가우스 소거법으로 정확하게 풀어
   원시(λ)·쌍대(μ) 유리수 증명서를 복원하고 부동소수점 오차 없이 100% 정확 검증한다.
2. 엄밀 폴백(Exact Fallback): 퇴화(degeneracy)나 동률 등으로 기저 복원이 실패하면
   Z3 SMT/Optimize의 정확한 유리수 산술(Real/Rat)로 직접 증명서를 합성한다.
3. Charnes-Cooper 선형분수계획(LFP) 변환을 통해 이질적 가중치 w_i 하의
   정확한 임계 전복 반경 ε*(x)와 최악 분해 경로 λ_adv, 쌍대 증명서 μ*를 단 한 번의 LP로 산출한다.
"""

from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
from typing import List, Optional, Sequence, Tuple

import numpy as np
from scipy.optimize import linprog
import z3


def to_fraction(val: float | int | str | Fraction, max_den: Optional[int] = None) -> Fraction:
    """실수/문자열/정수를 손실 없는 정확한 유리수(Fraction)로 변환한다.

    문자열(예: CSV/JSON 원본 10진수)은 `Decimal`을 거쳐 100% 정확히 분수로 파싱하며,
    부동소수점 입력은 Python의 최단 왕복 10진 표현(`str(val)`)을 사용해
    IEEE-754 이진 반올림 잔여물(예: 0.1 -> 3602879701896397/36028797018963968)을 방지한다.
    `max_den`이 명시적으로 지정되지 않는 한 분모 절단(`limit_denominator`)을 수행하지 않는다.
    """
    if isinstance(val, Fraction):
        return val
    if isinstance(val, int) and not isinstance(val, bool):
        return Fraction(val, 1)
    if isinstance(val, str):
        s = val.strip()
        if "/" in s:
            p, q = s.split("/", 1)
            return Fraction(int(p), int(q))
        frac = Fraction(Decimal(s))
        if max_den is not None and frac.denominator > max_den:
            frac = frac.limit_denominator(max_den)
        return frac
    if not np.isfinite(val):
        raise ValueError(f"유한하지 않은 수치: {val}")
    frac = Fraction(Decimal(str(val)))
    if max_den is not None and frac.denominator > max_den:
        frac = frac.limit_denominator(max_den)
    return frac


def fraction_to_str(q: Fraction) -> str:
    """Lean 4 `certmat-check` 파서가 읽는 `p/q` 또는 `p` 형식 문자열로 직렬화한다."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def z3_val_to_fraction(v: z3.ExprRef) -> Fraction:
    """Z3 모델의 유리수 값(RatNumRef/IntNumRef)을 정확한 Python Fraction으로 변환한다."""
    if isinstance(v, z3.IntNumRef):
        return Fraction(v.as_long(), 1)
    if isinstance(v, z3.RatNumRef):
        return Fraction(v.numerator_as_long(), v.denominator_as_long())
    if isinstance(v, z3.AlgebraicNumRef):
        raise TypeError(f"선형 유리수 계획에서 예상치 못한 무리 대수적 수 반환: {v}")
    return to_fraction(str(v))


def solve_rational_linear_system(
    A: Sequence[Sequence[Fraction]], b: Sequence[Fraction]
) -> Optional[List[Fraction]]:
    """정확한 유리수 가우스-조르당 소거법 (정방 또는 과결정/미결정 행렬 지원).

    해가 존재하면 최소 자유변수(0 대입) 특이해를 반환하고, 불능이면 None을 반환한다.
    """
    rows = len(A)
    if rows == 0:
        return []
    cols = len(A[0])
    M = [list(A[r]) + [b[r]] for r in range(rows)]

    pivot_cols: List[int] = []
    r = 0
    for c in range(cols):
        if r >= rows:
            break
        # 비영 피벗 탐색
        piv = None
        for i in range(r, rows):
            if M[i][c] != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        pv = M[r][c]
        M[r] = [x / pv for x in M[r]]
        for i in range(rows):
            if i != r and M[i][c] != 0:
                factor = M[i][c]
                M[i] = [M[i][j] - factor * M[r][j] for j in range(cols + 1)]
        pivot_cols.append(c)
        r += 1

    # 일관성 검사: 좌변이 모두 0인데 우변이 0이 아니면 해 없음
    for i in range(r, rows):
        if M[i][cols] != 0:
            return None

    x = [Fraction(0)] * cols
    for idx, c in enumerate(pivot_cols):
        x[c] = M[idx][cols]
    return x


def verify_dual_stable(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    energies: Sequence[Fraction],
    ex: Fraction,
    mu: Sequence[Fraction],
    delta: Fraction = Fraction(0),
) -> bool:
    """정리 1b (쌍대 안정성 증명서)를 정확한 유리수 산술로 검증한다 (음수 여유 δ < 0 엄격 거부)."""
    E = len(cx)
    if delta < 0 or len(mu) != E:
        return False
    for i, ci in enumerate(comp):
        lhs = sum(mu[e] * ci[e] for e in range(E))
        if lhs > energies[i]:
            return False
    cand_dot = sum(mu[e] * cx[e] for e in range(E))
    return ex + delta <= cand_dot


def verify_primal_unstable(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    energies: Sequence[Fraction],
    ex: Fraction,
    lam: Sequence[Fraction],
) -> bool:
    """정리 1a (원시 불안정성 증명서)를 정확한 유리수 산술로 검증한다."""
    m = len(comp)
    E = len(cx)
    if len(lam) != m:
        return False
    if any(li < 0 for li in lam):
        return False
    for e in range(E):
        s = sum(lam[i] * comp[i][e] for i in range(m))
        if s != cx[e]:
            return False
    decomp_e = sum(lam[i] * energies[i] for i in range(m))
    return decomp_e < ex


def verify_valid_decomp(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    lam: Sequence[Fraction],
) -> bool:
    """유효한 조성 보존 분해 λ 조건을 정확 검증한다."""
    m = len(comp)
    E = len(cx)
    if len(lam) != m or any(li < 0 for li in lam):
        return False
    for e in range(E):
        if sum(lam[i] * comp[i][e] for i in range(m)) != cx[e]:
            return False
    return True


@dataclass
class ExactHullLPResult:
    """명목 Convex Hull 정확 유리수 LP 해 및 증명서."""
    hull_energy: Fraction       # min_{λ} E^T λ (후보상 제외 경쟁상 기준)
    stability_margin: Fraction  # hull_energy - ex (>0: 엄격 안정, =0: 경계, <0: 불안정, e_hull = -margin)
    lam: List[Fraction]         # 최적 분해 계수 λ (조성 보존, 비음)
    mu: List[Fraction]          # 최적 쌍대 화학 퍼텐셜 μ (∀i, μ·c_i ≤ E_i, μ·c_x = hull_energy)
    solver_used: str            # "highs_exact_basis" | "z3_exact"
    exact_verified: bool        # 강쌍대성 및 원시·쌍대 가능성 100% 정확 검증 여부


@dataclass
class ExactRadiusResult:
    """이질적/균일 불확실성 하 정확한 임계 전복 반경 ε*(x) 및 증명서."""
    signed_radius: Optional[Fraction]     # 양수: 안정→불안정, 음수: -1*(불안정→안정), None: 무한대(is_infinite=True)
    critical_radius: Optional[Fraction]   # |signed_radius| ≥ 0, 무한대이면 None
    is_nominally_stable: bool
    lam_adv: List[Fraction]               # 최악(또는 최적) 분해 경로 λ_adv
    mu_star: List[Fraction]               # 임계점 ε*에서의 정확 쌍대 증명서 μ* (무한 불안정 시 빈 리스트)
    solver_used: str
    exact_verified: bool
    is_infinite: bool = False             # 모든 유한 ε ≥ 0 에 대해 전복 불가능(±∞) 여부
    infinite_sign: int = 0                # +1: 영구 강건 안정(+∞), -1: 영구 강건 불안정(-∞), 0: 유한


def _validate_normalized_compositions(
    comp: Sequence[Sequence[Fraction]], cx: Sequence[Fraction]
) -> None:
    """조성 행렬 및 후보 조성이 비음·정규화(합 = 1) 조건을 만족하는지 엄격 검사한다."""
    m = len(comp)
    E = len(cx)
    if m == 0 or E == 0:
        raise ValueError(f"비어 있는 조성 차원입니다: m={m}, E={E}")
    if any(x < 0 for x in cx) or sum(cx, Fraction(0)) != 1:
        raise ValueError(f"후보상 조성이 비음 정규화(합=1) 조건을 위반했습니다: {cx}")
    for i, row in enumerate(comp):
        if len(row) != E or any(x < 0 for x in row) or sum(row, Fraction(0)) != 1:
            raise ValueError(f"경쟁상 {i}의 조성이 비음 정규화(합=1) 조건을 위반했습니다: {row}")


def _z3_solve_hull_primal_dual(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    energies: Sequence[Fraction],
    ex: Fraction,
) -> ExactHullLPResult:
    """Z3 Optimize를 이용한 100% 정확한 유리수 원시·쌍대 Hull LP 해법."""
    m = len(comp)
    E = len(cx)

    # 1) 원시 문제: min ∑ λ_i E_i  s.t. λ_i ≥ 0, ∑ λ_i c_ie = c_xe
    opt_p = z3.Optimize()
    lam_vars = [z3.Real(f"l_{i}") for i in range(m)]
    for i in range(m):
        opt_p.add(lam_vars[i] >= 0)
    for e in range(E):
        terms = [lam_vars[i] * z3.Q(comp[i][e].numerator, comp[i][e].denominator) for i in range(m) if comp[i][e] != 0]
        lhs = z3.Sum(terms) if terms else z3.RealVal(0)
        opt_p.add(lhs == z3.Q(cx[e].numerator, cx[e].denominator))
    obj_p = z3.Sum([lam_vars[i] * z3.Q(energies[i].numerator, energies[i].denominator) for i in range(m)])
    opt_p.minimize(obj_p)
    if opt_p.check() != z3.sat:
        raise ValueError("Z3 원시 Hull LP가 실행 불가능(infeasible)합니다. 원소 기준상이 누락되었는지 확인하세요.")
    mp = opt_p.model()
    lam = [z3_val_to_fraction(mp.eval(v, model_completion=True)) for v in lam_vars]
    hull_e = sum(lam[i] * energies[i] for i in range(m))

    # 2) 쌍대 문제: μ·c_i ≤ E_i, μ·c_x == hull_e (상보 여유성 강제 가능)
    sol_d = z3.Solver()
    mu_vars = [z3.Real(f"m_{e}") for e in range(E)]
    for i in range(m):
        terms = [mu_vars[e] * z3.Q(comp[i][e].numerator, comp[i][e].denominator) for e in range(E) if comp[i][e] != 0]
        lhs = z3.Sum(terms) if terms else z3.RealVal(0)
        rhs = z3.Q(energies[i].numerator, energies[i].denominator)
        if lam[i] > 0:
            sol_d.add(lhs == rhs)
        else:
            sol_d.add(lhs <= rhs)
    cand_terms = [mu_vars[e] * z3.Q(cx[e].numerator, cx[e].denominator) for e in range(E) if cx[e] != 0]
    cand_lhs = z3.Sum(cand_terms) if cand_terms else z3.RealVal(0)
    sol_d.add(cand_lhs == z3.Q(hull_e.numerator, hull_e.denominator))
    if sol_d.check() != z3.sat:
        raise RuntimeError("Z3 쌍대 증명서 합성 실패 (강쌍대성 위반).")
    md = sol_d.model()
    mu = [z3_val_to_fraction(md.eval(v, model_completion=True)) for v in mu_vars]

    ok = (
        verify_valid_decomp(comp, cx, lam)
        and verify_dual_stable(comp, cx, energies, hull_e, mu, Fraction(0))
        and sum(mu[e] * cx[e] for e in range(E)) == hull_e
    )
    if not ok:
        raise RuntimeError("Z3 Hull LP 원시·쌍대 정확 검증 실패 (묵시적 실패 차단).")
    return ExactHullLPResult(
        hull_energy=hull_e,
        stability_margin=hull_e - ex,
        lam=lam,
        mu=mu,
        solver_used="z3_exact",
        exact_verified=True,
    )


def solve_hull_primal_dual_exact(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    energies: Sequence[Fraction],
    ex: Fraction,
    use_z3_fallback: bool = True,
) -> ExactHullLPResult:
    """명목 Convex Hull 분해 에너지 및 정확한 유리수 원시·쌍대 증명서를 계산한다."""
    _validate_normalized_compositions(comp, cx)
    m = len(comp)
    E = len(cx)
    if len(energies) != m:
        raise ValueError(f"입력 길이 불일치: m={m}, len(energies)={len(energies)}")

    # 빠른 경로: HiGHS로 기저 탐색
    C_np = np.array([[float(comp[i][e]) for e in range(E)] for i in range(m)], dtype=np.float64)
    cx_np = np.array([float(cx[e]) for e in range(E)], dtype=np.float64)
    E_np = np.array([float(energies[i]) for i in range(m)], dtype=np.float64)

    res = linprog(c=E_np, A_eq=C_np.T, b_eq=cx_np, bounds=(0.0, None), method="highs")
    if res.success and res.x is not None:
        # 1) 활성 원시 기저 후보 추출 (λ_i > 1e-11)
        pos_idx = [i for i in range(m) if res.x[i] > 1e-11]
        # 2) 원시 λ 정확 복원
        lam_exact: Optional[List[Fraction]] = None
        if 0 < len(pos_idx) <= E:
            A_p = [[comp[i][e] for i in pos_idx] for e in range(E)]
            sol_p = solve_rational_linear_system(A_p, cx)
            if sol_p is not None and all(v >= 0 for v in sol_p):
                cand_lam = [Fraction(0)] * m
                for k, idx in enumerate(pos_idx):
                    cand_lam[idx] = sol_p[k]
                if verify_valid_decomp(comp, cx, cand_lam):
                    lam_exact = cand_lam

        # 3) 쌍대 μ 정확 복원 (활성 제약 + 여유가 거의 0인 제약 추가)
        if lam_exact is not None:
            hull_e = sum(lam_exact[i] * energies[i] for i in range(m))
            # HiGHS 쌍대 변수(marginal): A_eq^T mu <= c => scipy eqlin.marginals 부호 주의
            mu_approx = None
            if hasattr(res, "eqlin") and res.eqlin is not None and res.eqlin.marginals is not None:
                mu_approx = np.asarray(res.eqlin.marginals, dtype=np.float64)
                # 부호 확인: C @ mu_approx <= E_np 여야 함
                if np.max(C_np @ mu_approx - E_np) > np.max(C_np @ (-mu_approx) - E_np):
                    mu_approx = -mu_approx

            tight_idx = list(pos_idx)
            if mu_approx is not None and len(tight_idx) < E:
                slacks = np.abs(E_np - C_np @ mu_approx)
                order = np.argsort(slacks)
                for idx in order:
                    idx_int = int(idx)
                    if idx_int not in tight_idx:
                        tight_idx.append(idx_int)
                    if len(tight_idx) >= E:
                        break

            # 선형 독립인 행을 골라 C_tight @ mu = E_tight 풀기
            selected: List[int] = []
            for idx in tight_idx:
                trial = selected + [idx]
                A_d = [list(comp[i]) for i in trial]
                b_d = [energies[i] for i in trial]
                sol_d = solve_rational_linear_system(A_d, b_d)
                if sol_d is not None:
                    selected = trial
                if len(selected) == E:
                    break

            if selected:
                A_d = [list(comp[i]) for i in selected]
                b_d = [energies[i] for i in selected]
                mu_exact = solve_rational_linear_system(A_d, b_d)
                if mu_exact is not None:
                    # 강쌍대성 및 모든 경쟁상 부등식 정확 검증
                    if (
                        verify_dual_stable(comp, cx, energies, hull_e, mu_exact, Fraction(0))
                        and sum(mu_exact[e] * cx[e] for e in range(E)) == hull_e
                    ):
                        return ExactHullLPResult(
                            hull_energy=hull_e,
                            stability_margin=hull_e - ex,
                            lam=lam_exact,
                            mu=mu_exact,
                            solver_used="highs_exact_basis",
                            exact_verified=True,
                        )

    if use_z3_fallback:
        return _z3_solve_hull_primal_dual(comp, cx, energies, ex)
    raise RuntimeError("HiGHS 기저 복원 실패 및 Z3 폴백 비활성화 상태입니다.")


def _z3_solve_charnes_cooper(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    energies: Sequence[Fraction],
    ex: Fraction,
    weights: Sequence[Fraction],
    wx: Fraction,
) -> ExactRadiusResult:
    """Z3 Optimize를 이용한 Charnes-Cooper 선형분수계획(ε*(x)) 100% 정확 해법.

    최소화 문제:
        min_{y ≥ 0, t ≥ 0} ∑_i E_i y_i - E_x t
        s.t.  ∑_i c_ie y_i - c_xe t = 0   (∀ e)
              ∑_i w_i  y_i + w_x  t = 1
    최적값 r = signed_radius:
      - r ≥ 0: 명목 안정, 임계 전복 반경 ε* = r.
        쌍대 증명서 μ* 는 ∀i, μ*·c_i ≤ E_i - r w_i 및 μ*·c_x ≥ E_x + r w_x 만족.
      - r < 0: 명목 불안정, 강건 불안정 임계 반경 ε* = -r > 0.
        쌍대 증명서 μ* 는 ∀i, μ*·c_i ≤ E_i + ε* w_i 및 μ*·c_x ≥ E_x - ε* w_x 만족.
    """
    m = len(comp)
    E = len(cx)

    opt = z3.Optimize()
    y_vars = [z3.Real(f"y_{i}") for i in range(m)]
    t_var = z3.Real("t")
    for i in range(m):
        opt.add(y_vars[i] >= 0)
    # 조성 정규화(∑ c_ie = 1) 및 가중치 합=1 제약에 의해 t=0 은 실행 불가능하므로 t >= 0 으로 엄격 양수가 자동 보장됨
    # (엄격 부등호 t > 0 대신 t >= 0 사용으로 Z3 무한소(infinitesimal) 모델 생성을 원천 차단)
    opt.add(t_var >= 0)

    for e in range(E):
        terms = [y_vars[i] * z3.Q(comp[i][e].numerator, comp[i][e].denominator) for i in range(m) if comp[i][e] != 0]
        if cx[e] != 0:
            terms.append(-t_var * z3.Q(cx[e].numerator, cx[e].denominator))
        opt.add((z3.Sum(terms) if terms else z3.RealVal(0)) == 0)

    w_terms = [y_vars[i] * z3.Q(weights[i].numerator, weights[i].denominator) for i in range(m) if weights[i] != 0]
    if wx != 0:
        w_terms.append(t_var * z3.Q(wx.numerator, wx.denominator))
    opt.add(z3.Sum(w_terms) == 1)

    obj_terms = [y_vars[i] * z3.Q(energies[i].numerator, energies[i].denominator) for i in range(m)]
    obj_terms.append(-t_var * z3.Q(ex.numerator, ex.denominator))
    opt.minimize(z3.Sum(obj_terms))

    if opt.check() != z3.sat:
        raise ValueError("Z3 Charnes-Cooper LP 실행 불가능.")
    mod = opt.model()
    t_val = z3_val_to_fraction(mod.eval(t_var, model_completion=True))
    if t_val <= 0:
        raise RuntimeError(f"Z3 Charnes-Cooper LP에서 비양수 t={t_val} 반환 (정규화/유계성 위반).")
    y_vals = [z3_val_to_fraction(mod.eval(v, model_completion=True)) for v in y_vars]
    lam = [yv / t_val for yv in y_vals]
    denom = wx + sum(lam[i] * weights[i] for i in range(m))
    if denom <= 0:
        raise RuntimeError(f"Z3 Charnes-Cooper LP 분모가 양수가 아닙니다: denom={denom}")
    r_signed = (sum(lam[i] * energies[i] for i in range(m)) - ex) / denom

    # 임계점 r_signed 에서의 쌍대 화학 퍼텐셜 μ* 합성:
    # ∀ i, μ·c_i ≤ E_i - r_signed * w_i  및  μ·c_x ≥ E_x + r_signed * w_x
    eff_en = [energies[i] - r_signed * weights[i] for i in range(m)]
    eff_ex = ex + r_signed * wx
    sol_d = z3.Solver()
    mu_vars = [z3.Real(f"mu_{e}") for e in range(E)]
    for i in range(m):
        terms = [mu_vars[e] * z3.Q(comp[i][e].numerator, comp[i][e].denominator) for e in range(E) if comp[i][e] != 0]
        lhs = z3.Sum(terms) if terms else z3.RealVal(0)
        rhs = z3.Q(eff_en[i].numerator, eff_en[i].denominator)
        if lam[i] > 0:
            sol_d.add(lhs == rhs)
        else:
            sol_d.add(lhs <= rhs)
    cand_terms = [mu_vars[e] * z3.Q(cx[e].numerator, cx[e].denominator) for e in range(E) if cx[e] != 0]
    sol_d.add((z3.Sum(cand_terms) if cand_terms else z3.RealVal(0)) >= z3.Q(eff_ex.numerator, eff_ex.denominator))
    if sol_d.check() != z3.sat:
        raise RuntimeError("Z3 임계 반경 쌍대 증명서 합성 실패.")
    md = sol_d.model()
    mu_star = [z3_val_to_fraction(md.eval(v, model_completion=True)) for v in mu_vars]

    ok = (
        verify_valid_decomp(comp, cx, lam)
        and verify_dual_stable(comp, cx, eff_en, eff_ex, mu_star, Fraction(0))
        and sum(lam[i] * eff_en[i] for i in range(m)) == eff_ex
    )
    if not ok:
        raise RuntimeError("Z3 Charnes-Cooper 정확 증명서 검증 실패 (묵시적 실패 차단).")
    return ExactRadiusResult(
        signed_radius=r_signed,
        critical_radius=abs(r_signed),
        is_nominally_stable=(r_signed >= 0),
        lam_adv=lam,
        mu_star=mu_star,
        solver_used="z3_exact",
        exact_verified=True,
    )


def solve_critical_radius_exact(
    comp: Sequence[Sequence[Fraction]],
    cx: Sequence[Fraction],
    energies: Sequence[Fraction],
    ex: Fraction,
    weights: Sequence[Fraction],
    wx: Fraction,
    use_z3_fallback: bool = True,
) -> ExactRadiusResult:
    """Charnes-Cooper 정확 유리수 LP로 임계 전복 반경 ε*(x), 최악 분해 λ_adv, 쌍대 μ*를 산출한다.

    모든 가중치(wx, weights)의 비음성 및 조성 정규화(∑ c_ie = ∑ c_xe = 1)를 엄격 검증하며,
    일부 또는 전체 가중치가 0인 분모=0 실행가능 분해 경로를 사전에 정확 분류한다.
    """
    _validate_normalized_compositions(comp, cx)
    m = len(comp)
    E = len(cx)
    if len(weights) != m or len(energies) != m:
        raise ValueError(f"입력 길이 불일치: m={m}, len(energies)={len(energies)}, len(weights)={len(weights)}")
    if wx < 0 or any(w < 0 for w in weights):
        raise ValueError("모든 불확실성 가중치(wx, weights)는 비음(≥ 0)이어야 합니다.")

    # 특수 케이스: wx == 0 이고 가중치 0인 경쟁상만으로 후보 조성을 분해할 수 있는지 사전 검사
    zero_fallback_nonneg: Optional[Tuple[List[Fraction], ExactHullLPResult]] = None
    if wx == 0:
        zero_idx = [i for i in range(m) if weights[i] == 0]
        if len(zero_idx) == m:
            # 전체 폭=0 구간 (완전 결정론적 에너지): 비엄격 안정 규약(≤) 하에서 margin ≥ 0 이면
            # 어떤 유한 ε ≥ 0 에서도 엄격 불안정이 불가능(+∞), margin < 0 이면 영구 불안정(-∞)
            nom = solve_hull_primal_dual_exact(comp, cx, energies, ex, use_z3_fallback=use_z3_fallback)
            if nom.stability_margin >= 0:
                return ExactRadiusResult(
                    signed_radius=None,
                    critical_radius=None,
                    is_nominally_stable=True,
                    lam_adv=list(nom.lam),
                    mu_star=list(nom.mu),
                    solver_used="zero_width_exact",
                    exact_verified=True,
                    is_infinite=True,
                    infinite_sign=1,
                )
            return ExactRadiusResult(
                signed_radius=None,
                critical_radius=None,
                is_nominally_stable=False,
                lam_adv=list(nom.lam),
                mu_star=[],
                solver_used="zero_width_exact",
                exact_verified=True,
                is_infinite=True,
                infinite_sign=-1,
            )
        if zero_idx:
            # 부분 0-가중치 집합에서 실행 가능한 분해가 있는지 검사 (분모=0으로 인한 무계/0나눗셈 방지)
            C_z = [comp[i] for i in zero_idx]
            E_z = [energies[i] for i in zero_idx]
            zero_res: Optional[ExactHullLPResult] = None
            try:
                zero_res = solve_hull_primal_dual_exact(C_z, cx, E_z, ex, use_z3_fallback=True)
            except ValueError:
                zero_res = None
            if zero_res is not None:
                lam_full = [Fraction(0)] * m
                for k, orig_i in enumerate(zero_idx):
                    lam_full[orig_i] = zero_res.lam[k]
                if zero_res.stability_margin < 0:
                    # 0-가중치 분해가 엄격 불안정 -> 임의의 유한 ε ≥ 0 에서도 보편 불안정 (r* = -∞)
                    return ExactRadiusResult(
                        signed_radius=None,
                        critical_radius=None,
                        is_nominally_stable=False,
                        lam_adv=lam_full,
                        mu_star=[],
                        solver_used="zero_denom_exact",
                        exact_verified=True,
                        is_infinite=True,
                        infinite_sign=-1,
                    )
                # zero_res.stability_margin >= 0:
                # 0-가중치 경로는 어떤 유한 ε에서도 엄격 불안정을 유발하지 않으므로(동률/여유 유지),
                # 반경을 0으로 단축하지 않고 양의 분모를 갖는 모든 경로에 대해 Charnes-Cooper LP를 계속 푼다.
                # (만약 양의 분모를 갖는 실행 가능 경로가 전혀 없으면 LP가 infeasible이 되며 그때 +∞ 확정)
                zero_fallback_nonneg = (lam_full, zero_res)

    # 변수: [y_0, ..., y_{m-1}, t] (총 m + 1 개)
    c_obj = np.array([float(energies[i]) for i in range(m)] + [-float(ex)], dtype=np.float64)
    A_eq = np.zeros((E + 1, m + 1), dtype=np.float64)
    b_eq = np.zeros(E + 1, dtype=np.float64)
    for e in range(E):
        for i in range(m):
            A_eq[e, i] = float(comp[i][e])
        A_eq[e, m] = -float(cx[e])
    for i in range(m):
        A_eq[E, i] = float(weights[i])
    A_eq[E, m] = float(wx)
    b_eq[E] = 1.0

    res = linprog(c=c_obj, A_eq=A_eq, b_eq=b_eq, bounds=(0.0, None), method="highs")
    if res.success and res.x is not None and res.x[m] > 1e-12:
        pos_idx = [i for i in range(m) if res.x[i] > 1e-11]
        if 0 < len(pos_idx) <= E + 1:
            # 원시 기저 정확 복원: [y_{pos}, t]
            A_p: List[List[Fraction]] = []
            b_p: List[Fraction] = []
            for e in range(E):
                A_p.append([comp[i][e] for i in pos_idx] + [-cx[e]])
                b_p.append(Fraction(0))
            A_p.append([weights[i] for i in pos_idx] + [wx])
            b_p.append(Fraction(1))
            sol_p = solve_rational_linear_system(A_p, b_p)
            if sol_p is not None and sol_p[-1] > 0 and all(v >= 0 for v in sol_p[:-1]):
                t_val = sol_p[-1]
                lam_exact = [Fraction(0)] * m
                for k, idx in enumerate(pos_idx):
                    lam_exact[idx] = sol_p[k] / t_val
                if verify_valid_decomp(comp, cx, lam_exact):
                    denom = wx + sum(lam_exact[i] * weights[i] for i in range(m))
                    if denom > 0:
                        r_signed = (sum(lam_exact[i] * energies[i] for i in range(m)) - ex) / denom
                        eff_en = [energies[i] - r_signed * weights[i] for i in range(m)]
                        eff_ex = ex + r_signed * wx

                        # 쌍대 μ* 정확 복원: 활성 제약 C_B @ mu = eff_en_B
                        mu_approx = None
                        if hasattr(res, "eqlin") and res.eqlin is not None and res.eqlin.marginals is not None:
                            marg = np.asarray(res.eqlin.marginals[:E], dtype=np.float64)
                            eff_np = np.array([float(v) for v in eff_en], dtype=np.float64)
                            C_np = A_eq[:E, :m].T
                            if np.max(C_np @ marg - eff_np) > np.max(C_np @ (-marg) - eff_np):
                                marg = -marg
                            mu_approx = marg

                        tight_idx = list(pos_idx)
                        if mu_approx is not None and len(tight_idx) < E:
                            eff_np = np.array([float(v) for v in eff_en], dtype=np.float64)
                            C_np = A_eq[:E, :m].T
                            slacks = np.abs(eff_np - C_np @ mu_approx)
                            for idx in np.argsort(slacks):
                                idx_int = int(idx)
                                if idx_int not in tight_idx:
                                    tight_idx.append(idx_int)
                                if len(tight_idx) >= E:
                                    break

                        selected: List[int] = []
                        for idx in tight_idx:
                            trial = selected + [idx]
                            A_d = [list(comp[i]) for i in trial]
                            b_d = [eff_en[i] for i in trial]
                            if solve_rational_linear_system(A_d, b_d) is not None:
                                selected = trial
                            if len(selected) == E:
                                break

                        if selected:
                            A_d = [list(comp[i]) for i in selected]
                            b_d = [eff_en[i] for i in selected]
                            mu_exact = solve_rational_linear_system(A_d, b_d)
                            if mu_exact is not None:
                                if (
                                    verify_dual_stable(comp, cx, eff_en, eff_ex, mu_exact, Fraction(0))
                                    and sum(lam_exact[i] * eff_en[i] for i in range(m)) == eff_ex
                                ):
                                    return ExactRadiusResult(
                                        signed_radius=r_signed,
                                        critical_radius=abs(r_signed),
                                        is_nominally_stable=(r_signed >= 0),
                                        lam_adv=lam_exact,
                                        mu_star=mu_exact,
                                        solver_used="highs_exact_basis",
                                        exact_verified=True,
                                    )

    if use_z3_fallback:
        try:
            return _z3_solve_charnes_cooper(comp, cx, energies, ex, weights, wx)
        except ValueError:
            if zero_fallback_nonneg is not None:
                # 모든 유효 분해 경로의 가중치 합이 0 이고 명목 여유 ≥ 0 -> 임의의 유한 ε ≥ 0 에서 영구 안정 (+∞)
                # 단, 도달 불가능한 양의 가중치 경쟁상(w_i > 0)에 대해서도 1x 박스 쌍대 부등식
                # (μ·c_i ≤ E_i - w_i)이 성립하도록 1x 이동 에너지에서 μ* 를 직접 합성한다.
                lam_full, _ = zero_fallback_nonneg
                box_1x_en = [energies[i] - weights[i] for i in range(m)]
                box_1x_ex = ex + wx
                box_1x = solve_hull_primal_dual_exact(comp, cx, box_1x_en, box_1x_ex, use_z3_fallback=True)
                return ExactRadiusResult(
                    signed_radius=None,
                    critical_radius=None,
                    is_nominally_stable=(box_1x.stability_margin >= 0),
                    lam_adv=lam_full,
                    mu_star=list(box_1x.mu) if box_1x.stability_margin >= 0 else [],
                    solver_used="zero_denom_no_pos_path_exact",
                    exact_verified=True,
                    is_infinite=True,
                    infinite_sign=1 if box_1x.stability_margin >= 0 else -1,
                )
            raise
    raise RuntimeError("Charnes-Cooper 기저 복원 실패 및 Z3 폴백 비활성화 상태입니다.")
