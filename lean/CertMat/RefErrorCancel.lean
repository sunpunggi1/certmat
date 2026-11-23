/-
  CertMat/RefErrorCancel.lean
  정리 2: 원소 기준 상태 상관 오차(∑_e c_ie δμ_e)의 조성 보존 분해 시 완전 상쇄 정리
  - DFT/MLIP의 체계적 원소 기준 오차 δμ_e 는 조성 보존 분해 에너지에서 항등적으로 0으로 상쇄된다.
  - 따라서 오직 비상관 잔차 오차(η_x - ∑_i λ_i η_i)만이 상 안정성 전복을 유발할 수 있다.
  - 쌍대 화학 퍼텐셜 또한 μ' = μ + δμ 평행이동만으로 동일한 안정성 여유 δ 를 완벽히 보존한다.
-/

import CertMat.Farkas

namespace CertMat

open Q

/-- 원소 기준 상태 오차 δμ 와 비상관 잔차 오차 η 를 포함한 실제 에너지 모델 -/
def shiftedEnergy {E : Nat} (base : Q) (comp : Fin E → Q) (dmu : Fin E → Q) (eta : Q) : Q :=
  base + dot dmu comp + eta

/-- 정리 2a (원소 기준 오차의 완전 상쇄 항등식):
    유효한 조성 보존 분해 λ 에 대해, 실제 분해 에너지 차이는
    (명목 분해 에너지 차이) + (비상관 잔차 오차 차이) 와 정확히 같다. -/
theorem ref_error_exact_cancellation {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {lam : Fin m → Q}
    (hlam : ValidDecomp c cx lam)
    (dmu : Fin E → Q) (eta : Fin m → Q) (etax : Q) :
    shiftedEnergy ex cx dmu etax - sumFin (fun i => lam i * shiftedEnergy (en i) (c i) dmu (eta i)) ≈
    (ex - sumFin (fun i => lam i * en i)) + (etax - sumFin (fun i => lam i * eta i)) := by
  unfold shiftedEnergy
  -- 경쟁상 가중합 전개: ∑ λ_i (E_i + δμ·c_i + η_i) ≈ ∑ λ_i E_i + ∑ λ_i (δμ·c_i) + ∑ λ_i η_i
  have hcomp_sum :
      sumFin (fun i => lam i * (en i + dot dmu (c i) + eta i)) ≈
      (sumFin (fun i => lam i * en i) + sumFin (fun i => lam i * dot dmu (c i))) +
      sumFin (fun i => lam i * eta i) := by
    have s1 := sumFin_congr (fun i =>
      eqv_trans (mul_add (lam i) (en i + dot dmu (c i)) (eta i))
        (add_congr (mul_add (lam i) (en i) (dot dmu (c i))) (eqv_refl _)))
    have s2 := sumFin_add
      (fun i => lam i * en i + lam i * dot dmu (c i))
      (fun i => lam i * eta i)
    have s3 := add_congr
      (sumFin_add (fun i => lam i * en i) (fun i => lam i * dot dmu (c i)))
      (eqv_refl (sumFin (fun i => lam i * eta i)))
    exact eqv_trans (eqv_trans s1 s2) s3
  -- 조성 보존 결합 정리: δμ · c_x ≈ ∑ λ_i (δμ · c_i)
  have hcancel_dmu : dot dmu cx ≈ sumFin (fun i => lam i * dot dmu (c i)) :=
    dual_primal_coupling hlam dmu
  -- 일반 대수 상쇄 보조정리: ((a + r) + b) - ((c + r) + d) ≈ (a - c) + (b - d)
  have halg (a b c d r : Q) : ((a + r) + b) - ((c + r) + d) ≈ (a - c) + (b - d) := by
    -- 먼저 ((a - c) + (b - d)) + ((c + r) + d) ≈ (a + r) + b 를 보인 뒤 양변에서 ((c + r) + d) 빼기
    have hadd_back : ((a - c) + (b - d)) + ((c + r) + d) ≈ (a + r) + b := by
      -- ((a - c) + (b - d)) + ((c + r) + d)
      -- ≈ ((a - c) + c) + (r + ((b - d) + d)) ≈ a + (r + b) ≈ (a + r) + b
      have p1 : ((a - c) + (b - d)) + ((c + r) + d) ≈
                ((a - c) + c) + (r + ((b - d) + d)) := by
        -- 결합/교환 분해
        have s1 : ((a - c) + (b - d)) + ((c + r) + d) ≈
                  (a - c) + ((b - d) + ((c + r) + d)) := add_assoc _ _ _
        have s2 : (b - d) + ((c + r) + d) ≈ (c + r) + ((b - d) + d) := by
          have u1 := eqv_symm (add_assoc (b - d) (c + r) d)
          have u2 := add_congr (add_comm (b - d) (c + r)) (eqv_refl d)
          have u3 := add_assoc (c + r) (b - d) d
          exact eqv_trans (eqv_trans u1 u2) u3
        have s3 : (c + r) + ((b - d) + d) ≈ c + (r + ((b - d) + d)) := add_assoc _ _ _
        have s4 : (a - c) + (c + (r + ((b - d) + d))) ≈ ((a - c) + c) + (r + ((b - d) + d)) :=
          eqv_symm (add_assoc _ _ _)
        exact eqv_trans s1 (eqv_trans (add_congr (eqv_refl _) (eqv_trans s2 s3)) s4)
      have p2 : ((a - c) + c) + (r + ((b - d) + d)) ≈ a + (r + b) :=
        add_congr (sub_add_cancel a c) (add_congr (eqv_refl r) (sub_add_cancel b d))
      have p3 : a + (r + b) ≈ (a + r) + b := eqv_symm (add_assoc a r b)
      exact eqv_trans (eqv_trans p1 p2) p3
    have hsub := sub_congr (eqv_symm hadd_back) (eqv_refl ((c + r) + d))
    exact eqv_trans hsub (add_sub_cancel ((a - c) + (b - d)) ((c + r) + d))
  -- hcomp_sum 및 hcancel_dmu 적용
  have hrhs :
      (sumFin (fun i => lam i * en i) + sumFin (fun i => lam i * dot dmu (c i))) +
      sumFin (fun i => lam i * eta i) ≈
      (sumFin (fun i => lam i * en i) + dot dmu cx) + sumFin (fun i => lam i * eta i) :=
    add_congr (add_congr (eqv_refl _) (eqv_symm hcancel_dmu)) (eqv_refl _)
  have h1 := sub_congr (eqv_refl ((ex + dot dmu cx) + etax)) (eqv_trans hcomp_sum hrhs)
  exact eqv_trans h1 (halg ex etax (sumFin (fun i => lam i * en i)) (sumFin (fun i => lam i * eta i)) (dot dmu cx))

/-- 정리 2b (쌍대 화학 퍼텐셜 평행이동 불변성):
    잔차 오차가 0(η = 0)이고 기준 상태 오차 δμ 만 존재할 때,
    원래의 쌍대 증명서 μ 에 δμ 를 더한 μ' = μ + δμ 는 동일한 안정성 여유 δ 를 인증한다. -/
theorem ref_error_dual_invariance {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {mu : Fin E → Q}
    (hcert : DualStableCert c cx en ex delta mu)
    (dmu : Fin E → Q) :
    DualStableCert c cx (fun i => en i + dot dmu (c i)) (ex + dot dmu cx) delta
      (fun e => mu e + dmu e) := by
  have hdot_add (v : Fin E → Q) : dot (fun e => mu e + dmu e) v ≈ dot mu v + dot dmu v := by
    unfold dot
    have s1 := sumFin_congr (fun e => add_mul (mu e) (dmu e) (v e))
    exact eqv_trans s1 (sumFin_add (fun e => mu e * v e) (fun e => dmu e * v e))
  constructor
  · intro i
    have h1 := add_le_add (hcert.hyperplane i) (le_refl (dot dmu (c i)))
    exact le_trans (le_of_eqv (hdot_add (c i))) h1
  · -- (ex + dot dmu cx) + delta ≈ (ex + delta) + dot dmu cx ≤ dot mu cx + dot dmu cx ≈ dot (mu + dmu) cx
    have h1 := add_le_add hcert.candidate_bound (le_refl (dot dmu cx))
    have hswap : (ex + dot dmu cx) + delta ≈ (ex + delta) + dot dmu cx := by
      have s1 := add_assoc ex (dot dmu cx) delta
      have s2 := add_congr (eqv_refl ex) (add_comm (dot dmu cx) delta)
      have s3 := eqv_symm (add_assoc ex delta (dot dmu cx))
      exact eqv_trans (eqv_trans s1 s2) s3
    exact le_trans (le_of_eqv hswap) (le_trans h1 (le_of_eqv (eqv_symm (hdot_add cx))))

/-- 따름정리 2c (잔차 오차 부재 시 안정성 절대 불변):
    모든 상의 비상관 잔차 오차가 0이면, 임의로 큰 원소 기준 오차 δμ 가 가해져도
    안정상은 결코 불안정상으로 전복되지 않는다. -/
theorem only_residual_error_flips_stability {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {mu : Fin E → Q}
    (hcert : DualStableCert c cx en ex delta mu)
    (dmu : Fin E → Q) :
    ∀ lam, ValidDecomp c cx lam →
      (ex + dot dmu cx) + delta ≤q sumFin (fun i => lam i * (en i + dot dmu (c i))) := by
  exact farkas_dual_stable_sound (ref_error_dual_invariance hcert dmu)

end CertMat
