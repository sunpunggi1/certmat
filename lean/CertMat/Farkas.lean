/-
  CertMat/Farkas.lean
  정리 1: 상평형(Convex Hull) 분해의 Farkas 쌍대 건전성 정리
  - 정리 1a (원시 분해 증명서): 조성 보존 비음 계수 λ 가 ∑ λ_i E_i < E_x 를 만족하면
    후보상 x는 무조건 열역학적으로 불안정하며(Convex Hull 상부), 어떤 쌍대 화학 퍼텐셜 μ 도 존재할 수 없다.
  - 정리 1b (쌍대 화학 퍼텐셜 증명서): 화학 퍼텐셜 μ 가 ∀ i, μ·c_i ≤ E_i 이고 μ·c_x ≥ E_x + δ 를 만족하면
    모든 유효 분해 λ 에 대해 ∑ λ_i E_i - E_x ≥ δ (특히 δ ≥ 0 이면 무조건 안정) 이 성립한다.
  - 정리 1c (강쌍대성 및 상호 배타성): 원시·쌍대 증명서는 동시에 존재할 수 없으며,
    등호가 성립하는 쌍 (μ, λ) 은 정확한 Convex Hull 거리(또는 역거리 안정성 여유)를 유일하게 확정한다.
  - 보조정리 (정규화 조성 합 = 1 보존): 모든 상의 조성 합이 1이면 조성 보존 분해는 자동으로 ∑ λ_i = 1 을 만족한다.
-/

import CertMat.ExactRat

namespace CertMat

open Q

/-- 유효한 조성 보존 분해 λ: 비음성(λ_i ≥ 0) 및 원소별 조성 보존(∑_i λ_i c_ie = c_xe) -/
structure ValidDecomp {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q) (lam : Fin m → Q) : Prop where
  nonneg : ∀ i, (0 : Q) ≤q lam i
  conserve : ∀ e, sumFin (fun i => lam i * c i e) ≈ cx e

/-- 쌍대 화학 퍼텐셜 안정성 증명서 (여유 δ ≥ 0 포함) -/
structure DualStableCert {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (delta : Q) (mu : Fin E → Q) : Prop where
  hyperplane : ∀ i, dot mu (c i) ≤q en i
  candidate_bound : ex + delta ≤q dot mu cx

/-- 원시 불안정성 증명서 (분해 에너지 > 0) -/
structure PrimalUnstableCert {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (lam : Fin m → Q) : Prop where
  valid : ValidDecomp c cx lam
  lower_energy : sumFin (fun i => lam i * en i) <q ex

/-- 핵심 이중합 교환 항등식: 유효 분해 λ 와 임의의 화학 퍼텐셜 μ 에 대해
    μ · c_x ≈ ∑_i λ_i (μ · c_i) -/
theorem dual_primal_coupling {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {lam : Fin m → Q} (hlam : ValidDecomp c cx lam) (mu : Fin E → Q) :
    dot mu cx ≈ sumFin (fun i => lam i * dot mu (c i)) := by
  unfold dot
  -- ∑_e μ_e c_xe ≈ ∑_e μ_e (∑_i λ_i c_ie)
  have h1 : sumFin (fun e => mu e * cx e) ≈
            sumFin (fun e => mu e * sumFin (fun i => lam i * c i e)) :=
    sumFin_congr (fun e => mul_congr (eqv_refl (mu e)) (eqv_symm (hlam.conserve e)))
  -- ≈ ∑_e ∑_i μ_e (λ_i c_ie)
  have h2 : sumFin (fun e => mu e * sumFin (fun i => lam i * c i e)) ≈
            sumFin (fun e => sumFin (fun i => mu e * (lam i * c i e))) :=
    sumFin_congr (fun e => mul_sumFin (mu e) (fun i => lam i * c i e))
  -- ≈ ∑_i ∑_e μ_e (λ_i c_ie)
  have h3 := sumFin_comm (fun e i => mu e * (lam i * c i e))
  -- 각 항 정렬: μ_e * (λ_i * c_ie) ≈ λ_i * (μ_e * c_ie)
  have h4 : sumFin (fun i => sumFin (fun e => mu e * (lam i * c i e))) ≈
            sumFin (fun i => sumFin (fun e => lam i * (mu e * c i e))) :=
    sumFin_congr (fun i => sumFin_congr (fun e =>
      eqv_trans (eqv_symm (mul_assoc (mu e) (lam i) (c i e)))
        (eqv_trans (mul_congr (mul_comm (mu e) (lam i)) (eqv_refl (c i e)))
                   (mul_assoc (lam i) (mu e) (c i e)))))
  -- ≈ ∑_i λ_i (∑_e μ_e c_ie)
  have h5 : sumFin (fun i => sumFin (fun e => lam i * (mu e * c i e))) ≈
            sumFin (fun i => lam i * sumFin (fun e => mu e * c i e)) :=
    sumFin_congr (fun i => eqv_symm (mul_sumFin (lam i) (fun e => mu e * c i e)))
  exact eqv_trans (eqv_trans (eqv_trans (eqv_trans h1 h2) h3) h4) h5

/-- 정리 1b (쌍대 안정성 건전성):
    쌍대 화학 퍼텐셜 μ 가 ∀ i, μ·c_i ≤ E_i 및 E_x + δ ≤ μ·c_x 를 만족하면,
    모든 유효 분해 λ 에 대해 E_x + δ ≤ ∑_i λ_i E_i (즉 분해 여유 ≥ δ) 가 보편 성립한다. -/
theorem farkas_dual_stable_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {mu : Fin E → Q}
    (hcert : DualStableCert c cx en ex delta mu) :
    ∀ lam, ValidDecomp c cx lam → ex + delta ≤q sumFin (fun i => lam i * en i) := by
  intro lam hlam
  have hcouple := dual_primal_coupling hlam mu
  have hsum : sumFin (fun i => lam i * dot mu (c i)) ≤q sumFin (fun i => lam i * en i) :=
    sumFin_le_sumFin (fun i => mul_le_mul_of_nonneg_left (hlam.nonneg i) (hcert.hyperplane i))
  exact le_trans hcert.candidate_bound (le_trans (le_of_eqv hcouple) hsum)

/-- 따름정리 1b' (δ = 0 일 때 무조건 안정성): E_x ≤ ∑_i λ_i E_i -/
theorem farkas_dual_on_hull {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {mu : Fin E → Q}
    (hcert : DualStableCert c cx en ex 0 mu) :
    ∀ lam, ValidDecomp c cx lam → ex ≤q sumFin (fun i => lam i * en i) := by
  intro lam hlam
  have h := farkas_dual_stable_sound hcert lam hlam
  exact le_trans (le_of_eqv (eqv_symm (add_zero ex))) h

/-- 정리 1a (원시 불안정성 건전성 및 상호 배타성):
    원시 분해 증명서 λ (∑ λ_i E_i < E_x) 가 존재하면,
    δ ≥ 0 인 어떠한 쌍대 안정성 증명서 μ 도 존재할 수 없다. -/
theorem farkas_primal_unstable_excludes_dual {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {lam : Fin m → Q}
    (hprimal : PrimalUnstableCert c cx en ex lam)
    (hdelta : (0 : Q) ≤q delta) :
    ¬ ∃ mu, DualStableCert c cx en ex delta mu := by
  rintro ⟨mu, hdual⟩
  have hge := farkas_dual_stable_sound hdual lam hprimal.valid
  have hex_le : ex ≤q ex + delta :=
    le_trans (le_of_eqv (eqv_symm (add_zero ex))) (add_le_add (le_refl ex) hdelta)
  have hbound : ex ≤q sumFin (fun i => lam i * en i) := le_trans hex_le hge
  exact not_lt_of_le hbound hprimal.lower_energy

/-- 정리 1c (강쌍대성 정확 마진 정리):
    쌍대 증명서 μ 가 E_x + δ ≤ μ·c_x 를 인증하고, 동시에 유효 분해 λ* 가
    ∑_i λ*_i E_i ≈ E_x + δ 를 달성하면, δ 는 정확한 안정성 여유(최소 분해 에너지 차)이다. -/
theorem farkas_exact_margin {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {mu : Fin E → Q} {lamStar : Fin m → Q}
    (hdual : DualStableCert c cx en ex delta mu)
    (hvalid : ValidDecomp c cx lamStar)
    (htight : sumFin (fun i => lamStar i * en i) ≈ ex + delta) :
    ValidDecomp c cx lamStar ∧
    (∀ lam, ValidDecomp c cx lam →
      sumFin (fun i => lamStar i * en i) ≤q sumFin (fun i => lam i * en i)) := by
  refine ⟨hvalid, ?_⟩
  intro lam hlam
  have h1 := farkas_dual_stable_sound hdual lam hlam
  exact le_trans (le_of_eqv htight) h1

/-- 정리 1c' (정확 마진 유일성):
    두 개의 원시·쌍대 강쌍대성 달성 쌍 (μ1, λ1, δ1) 과 (μ2, λ2, δ2) 가 존재하면
    δ1 ≈ δ2 로 정확 마진은 유일하게 확정된다. -/
theorem farkas_exact_margin_unique {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta1 delta2 : Q} {mu1 mu2 : Fin E → Q} {lam1 lam2 : Fin m → Q}
    (hd1 : DualStableCert c cx en ex delta1 mu1)
    (hv1 : ValidDecomp c cx lam1)
    (ht1 : sumFin (fun i => lam1 i * en i) ≈ ex + delta1)
    (hd2 : DualStableCert c cx en ex delta2 mu2)
    (hv2 : ValidDecomp c cx lam2)
    (ht2 : sumFin (fun i => lam2 i * en i) ≈ ex + delta2) :
    delta1 ≈ delta2 := by
  have h12 : ex + delta1 ≤q ex + delta2 :=
    le_trans (farkas_dual_stable_sound hd1 lam2 hv2) (le_of_eqv ht2)
  have h21 : ex + delta2 ≤q ex + delta1 :=
    le_trans (farkas_dual_stable_sound hd2 lam1 hv1) (le_of_eqv ht1)
  have hd12 : delta1 ≤q delta2 :=
    le_of_add_le_add_right
      (le_trans (le_of_eqv (add_comm delta1 ex)) (le_trans h12 (le_of_eqv (add_comm ex delta2))))
  have hd21 : delta2 ≤q delta1 :=
    le_of_add_le_add_right
      (le_trans (le_of_eqv (add_comm delta2 ex)) (le_trans h21 (le_of_eqv (add_comm ex delta1))))
  exact eqv_of_le_of_le hd12 hd21

/-- 보조정리 (원자 분율 정규화 시 ∑ λ_i = 1 자동 보존):
    모든 경쟁상과 후보상의 원소 조성 합이 1이면, 유효 분해 λ 의 계수 합은 정확히 1이다. -/
theorem valid_decomp_sum_one {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {lam : Fin m → Q}
    (hlam : ValidDecomp c cx lam)
    (hc_norm : ∀ i, sumFin (fun e => c i e) ≈ 1)
    (hcx_norm : sumFin (fun e => cx e) ≈ 1) :
    sumFin lam ≈ 1 := by
  -- 1 ≈ ∑_e cx_e ≈ ∑_e ∑_i λ_i c_ie ≈ ∑_i λ_i (∑_e c_ie) ≈ ∑_i λ_i * 1 ≈ ∑_i λ_i
  have h1 : sumFin (fun e => cx e) ≈ sumFin (fun e => sumFin (fun i => lam i * c i e)) :=
    sumFin_congr (fun e => eqv_symm (hlam.conserve e))
  have h2 := sumFin_comm (fun e i => lam i * c i e)
  have h3 : sumFin (fun i => sumFin (fun e => lam i * c i e)) ≈
            sumFin (fun i => lam i * sumFin (fun e => c i e)) :=
    sumFin_congr (fun i => eqv_symm (mul_sumFin (lam i) (fun e => c i e)))
  have h4 : sumFin (fun i => lam i * sumFin (fun e => c i e)) ≈ sumFin lam :=
    sumFin_congr (fun i => eqv_trans (mul_congr (eqv_refl (lam i)) (hc_norm i)) (mul_one (lam i)))
  exact eqv_trans (eqv_symm (eqv_trans (eqv_trans (eqv_trans h1 h2) h3) h4)) hcx_norm

end CertMat
