/-
  CertMat/IntervalHull.lean
  정리 3: 이질적 구간 에너지 불확실성 E_i ∈ [L_i, U_i] 하의 최악 강건 안정성 정리
  - 정리 3a (최악점 (U_x, L) 쌍대 증명서 → 구간 전체 보편 강건 안정성):
    μ 가 후보상 상한 U_x 와 경쟁상 하한 L_i 에 대해 쌍대 안정성(여유 δ)을 인증하면,
    불확실성 초직육면체 [L_x, U_x] × ∏ [L_i, U_i] 내부의 모든 실제 에너지 조합에 대해
    후보상 x 는 최소 여유 δ 이상으로 보편 안정하다.
  - 정리 3b (최악점 (L_x, U) 원시 증명서 → 구간 전체 보편 강건 불안정성):
    유효 분해 λ 가 ∑ λ_i U_i < L_x 를 만족하면, 불확실성 구간 내부의 모든 실제 에너지 조합에서
    후보상 x 는 보편적으로 불안정하다.
  - 정리 3c (이질적 가중 반경 ε*(x) 하한·상한·유일성 및 취약성 증인 정리):
    가중치 w_x, w_i ≥ 0 에 대해 E_x + ε w_x vs E_i - ε w_i 로 정의된 임계 전복 반경 ε*(x) 의
    쌍대 하한 부등식, 원시 상한 부등식, 동시 등호 달성 시 유일성, 그리고 구간 내부 취약점(Fragile) 존재 증인을 증명한다.
-/

import CertMat.Farkas

namespace CertMat

open Q

/-- 에너지 구간 소속 조건: 모든 경쟁상 E_i^true ∈ [L_i, U_i], 후보상 E_x^true ∈ [L_x, U_x] -/
structure InEnergyBox {m : Nat} (L U : Fin m → Q) (Lx Ux : Q)
    (enTrue : Fin m → Q) (exTrue : Q) : Prop where
  comp_lower : ∀ i, L i ≤q enTrue i
  comp_upper : ∀ i, enTrue i ≤q U i
  cand_lower : Lx ≤q exTrue
  cand_upper : exTrue ≤q Ux

/-- 정리 3a (구간 불확실성 하 최악 강건 안정성 정리):
    최악 극점 (U_x, L) 에 대한 쌍대 증명서 μ 가 존재하면,
    구간 내부의 모든 실제 에너지 (E_x^true, E^true) 와 모든 유효 분해 λ 에 대해
    E_x^true + δ ≤ ∑_i λ_i E_i^true 가 보편 성립한다. -/
theorem interval_robust_stable_universal {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {L U : Fin m → Q} {Lx Ux delta : Q} {mu : Fin E → Q}
    (hcert : DualStableCert c cx L Ux delta mu) :
    ∀ enTrue exTrue, InEnergyBox L U Lx Ux enTrue exTrue →
      ∀ lam, ValidDecomp c cx lam →
        exTrue + delta ≤q sumFin (fun i => lam i * enTrue i) := by
  intro enTrue exTrue hbox lam hlam
  -- 1. E_x^true + δ ≤ U_x + δ
  have h1 : exTrue + delta ≤q Ux + delta := add_le_add hbox.cand_upper (le_refl delta)
  -- 2. U_x + δ ≤ ∑ λ_i L_i  (정리 1b 적용)
  have h2 : Ux + delta ≤q sumFin (fun i => lam i * L i) :=
    farkas_dual_stable_sound hcert lam hlam
  -- 3. ∑ λ_i L_i ≤ ∑ λ_i E_i^true  (λ_i ≥ 0 및 L_i ≤ E_i^true)
  have h3 : sumFin (fun i => lam i * L i) ≤q sumFin (fun i => lam i * enTrue i) :=
    sumFin_le_sumFin (fun i => mul_le_mul_of_nonneg_left (hlam.nonneg i) (hbox.comp_lower i))
  exact le_trans h1 (le_trans h2 h3)

/-- 정리 3b (구간 불확실성 하 보편 강건 불안정성 정리):
    최악 극점 (L_x, U) 에 대한 원시 분해 증명서 λ (∑ λ_i U_i < L_x) 가 존재하면,
    구간 내부의 모든 실제 에너지 (E_x^true, E^true) 에 대해
    ∑_i λ_i E_i^true < E_x^true 가 보편 성립한다. -/
theorem interval_robust_unstable_universal {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {L U : Fin m → Q} {Lx Ux : Q} {lam : Fin m → Q}
    (hcert : PrimalUnstableCert c cx U Lx lam) :
    ∀ enTrue exTrue, InEnergyBox L U Lx Ux enTrue exTrue →
      sumFin (fun i => lam i * enTrue i) <q exTrue := by
  intro enTrue exTrue hbox
  have h1 : sumFin (fun i => lam i * enTrue i) ≤q sumFin (fun i => lam i * U i) :=
    sumFin_le_sumFin (fun i => mul_le_mul_of_nonneg_left (hcert.valid.nonneg i) (hbox.comp_upper i))
  have h2 : sumFin (fun i => lam i * U i) <q Lx := hcert.lower_energy
  exact lt_of_lt_of_le (lt_of_le_of_lt h1 h2) hbox.cand_lower

/-- 정리 3c-1 (이질적 가중치 하 임계 전복 반경 ε*(x) 의 인증 하한):
    가중치 w_x, w_i ≥ 0 및 반경 eps 에 대해 최악 에너지 (E_x + eps·w_x, E_i - eps·w_i) 에서
    쌍대 증명서 μ 가 존재하면, 모든 유효 분해 λ 에 대해
    eps * (w_x + ∑ λ_i w_i) ≤ ∑ λ_i E_i - E_x 가 성립한다 (즉 eps ≤ ε*(x)). -/
theorem critical_radius_lower_bound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {mu : Fin E → Q}
    (hcert : DualStableCert c cx (fun i => en i - eps * w i) (ex + eps * wx) 0 mu) :
    ∀ lam, ValidDecomp c cx lam →
      eps * (wx + sumFin (fun i => lam i * w i)) ≤q
      sumFin (fun i => lam i * en i) - ex := by
  intro lam hlam
  -- 정리 1b': ex + eps * wx ≤ ∑ λ_i (en_i - eps * w_i)
  have hbase := farkas_dual_on_hull hcert lam hlam
  -- ∑ λ_i (en_i - eps * w_i) ≈ ∑ λ_i en_i - eps * ∑ λ_i w_i
  have hexpand :
      sumFin (fun i => lam i * (en i - eps * w i)) ≈
      sumFin (fun i => lam i * en i) - eps * sumFin (fun i => lam i * w i) := by
    have s1 := sumFin_congr (fun i =>
      eqv_trans (mul_add (lam i) (en i) (-(eps * w i)))
        (add_congr (eqv_refl _)
          (eqv_trans (mul_comm (lam i) (-(eps * w i)))
            (eqv_trans (neg_mul (eps * w i) (lam i))
              (neg_congr (eqv_trans (mul_assoc eps (w i) (lam i))
                (mul_congr (eqv_refl eps) (mul_comm (w i) (lam i)))))))))
    have s2 := sumFin_sub (fun i => lam i * en i) (fun i => eps * (lam i * w i))
    have s3 := sub_congr (eqv_refl (sumFin (fun i => lam i * en i)))
      (eqv_symm (mul_sumFin eps (fun i => lam i * w i)))
    exact eqv_trans (eqv_trans s1 s2) s3
  have hle : ex + eps * wx ≤q sumFin (fun i => lam i * en i) - eps * sumFin (fun i => lam i * w i) :=
    le_trans hbase (le_of_eqv hexpand)
  -- 양변에 eps * ∑ λ_i w_i 를 더하고 ex 를 뺌
  let Se := sumFin (fun i => lam i * en i)
  let Sw := sumFin (fun i => lam i * w i)
  have hadd := add_le_add hle (le_refl (eps * Sw))
  have hrhs : (Se - eps * Sw) + eps * Sw ≈ Se := sub_add_cancel Se (eps * Sw)
  have hlhs : (ex + eps * wx) + eps * Sw ≈ (eps * (wx + Sw)) + ex := by
    have p1 := add_assoc ex (eps * wx) (eps * Sw)
    have p2 := add_congr (eqv_refl ex) (eqv_symm (mul_add eps wx Sw))
    have p3 := add_comm ex (eps * (wx + Sw))
    exact eqv_trans (eqv_trans p1 p2) p3
  have hcombined : eps * (wx + Sw) + ex ≤q Se :=
    le_trans (le_of_eqv (eqv_symm hlhs)) (le_trans hadd (le_of_eqv hrhs))
  -- Se ≈ (Se - ex) + ex 이므로 양변에서 ex 소거
  have hse : Se ≈ (Se - ex) + ex := eqv_symm (sub_add_cancel Se ex)
  exact le_of_add_le_add_right (le_trans hcombined (le_of_eqv hse))

/-- 따름정리 3c-1' (비음 가중치·비음 반경 명시 버전):
    w_x ≥ 0, ∀i w_i ≥ 0, eps ≥ 0 하에서 분모 w_x + ∑ λ_i w_i ≥ 0 임과 동시에
    eps * (w_x + ∑ λ_i w_i) ≤ ∑ λ_i E_i - E_x 를 보증한다. -/
theorem critical_radius_lower_bound_nonneg {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {mu : Fin E → Q}
    (hwx : (0 : Q) ≤q wx)
    (hw : ∀ i, (0 : Q) ≤q w i)
    (heps : (0 : Q) ≤q eps)
    (hcert : DualStableCert c cx (fun i => en i - eps * w i) (ex + eps * wx) 0 mu) :
    ∀ lam, ValidDecomp c cx lam →
      (0 : Q) ≤q eps ∧
      (0 : Q) ≤q (wx + sumFin (fun i => lam i * w i)) ∧
      eps * (wx + sumFin (fun i => lam i * w i)) ≤q
      sumFin (fun i => lam i * en i) - ex := by
  intro lam hlam
  have hsw : (0 : Q) ≤q sumFin (fun i => lam i * w i) :=
    sumFin_nonneg (fun i => mul_nonneg (hlam.nonneg i) (hw i))
  have hdenom : (0 : Q) ≤q wx + sumFin (fun i => lam i * w i) :=
    le_trans (le_of_eqv (eqv_symm (add_zero 0))) (add_le_add hwx hsw)
  exact ⟨heps, hdenom, critical_radius_lower_bound hcert lam hlam⟩

/-- 정리 3c-2 (취약성 / 임계 전복 반경 상한 증명서):
    반경 eps 에서 유효 분해 λ 가 ∑ λ_i (E_i - eps·w_i) < E_x + eps·w_x 를 만족하면,
    후보상 x 는 반경 eps 불확실성 구간 내부의 실제 극점 (E_x + eps·w_x, E_i - eps·w_i) 에서
    반드시 불안정하므로 강건 안정하지 않다(Fragile). -/
theorem critical_radius_upper_bound_fragile {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {lam : Fin m → Q}
    (hprimal : PrimalUnstableCert c cx (fun i => en i - eps * w i) (ex + eps * wx) lam) :
    ¬ ∃ mu, DualStableCert c cx (fun i => en i - eps * w i) (ex + eps * wx) 0 mu :=
  farkas_primal_unstable_excludes_dual hprimal (le_refl 0)

/-- 정리 3c-2' (임계 전복 반경의 명시적 대수 상한 부등식):
    원시 취약 반례 λ 가 ∑ λ_i (E_i - eps·w_i) < E_x + eps·w_x 를 만족하면,
    ∑ λ_i E_i - E_x < eps * (w_x + ∑ λ_i w_i) 가 성립하여 ε*(x) < eps 임을 직접 증명한다. -/
theorem critical_radius_upper_bound_ineq {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {lam : Fin m → Q}
    (hprimal : PrimalUnstableCert c cx (fun i => en i - eps * w i) (ex + eps * wx) lam) :
    sumFin (fun i => lam i * en i) - ex <q eps * (wx + sumFin (fun i => lam i * w i)) := by
  have hexpand :
      sumFin (fun i => lam i * (en i - eps * w i)) ≈
      sumFin (fun i => lam i * en i) - eps * sumFin (fun i => lam i * w i) := by
    have s1 := sumFin_congr (fun i =>
      eqv_trans (mul_add (lam i) (en i) (-(eps * w i)))
        (add_congr (eqv_refl _)
          (eqv_trans (mul_comm (lam i) (-(eps * w i)))
            (eqv_trans (neg_mul (eps * w i) (lam i))
              (neg_congr (eqv_trans (mul_assoc eps (w i) (lam i))
                (mul_congr (eqv_refl eps) (mul_comm (w i) (lam i)))))))))
    have s2 := sumFin_sub (fun i => lam i * en i) (fun i => eps * (lam i * w i))
    have s3 := sub_congr (eqv_refl (sumFin (fun i => lam i * en i)))
      (eqv_symm (mul_sumFin eps (fun i => lam i * w i)))
    exact eqv_trans (eqv_trans s1 s2) s3
  let Se := sumFin (fun i => lam i * en i)
  let Sw := sumFin (fun i => lam i * w i)
  have hlt : Se - eps * Sw <q ex + eps * wx :=
    lt_of_le_of_lt (le_of_eqv (eqv_symm hexpand)) hprimal.lower_energy
  have hadd := add_lt_add_of_le_of_lt (le_refl (eps * Sw)) hlt
  have hl : eps * Sw + (Se - eps * Sw) ≈ Se :=
    eqv_trans (add_comm _ _) (sub_add_cancel Se (eps * Sw))
  have hr : eps * Sw + (ex + eps * wx) ≈ eps * (wx + Sw) + ex := by
    have p1 := add_comm (eps * Sw) (ex + eps * wx)
    have p2 := add_assoc ex (eps * wx) (eps * Sw)
    have p3 := add_congr (eqv_refl ex) (eqv_symm (mul_add eps wx Sw))
    have p4 := add_comm ex (eps * (wx + Sw))
    exact eqv_trans (eqv_trans (eqv_trans p1 p2) p3) p4
  have hcomb : Se <q eps * (wx + Sw) + ex :=
    lt_of_le_of_lt (le_of_eqv (eqv_symm hl)) (lt_of_lt_of_le hadd (le_of_eqv hr))
  -- Se - ex < eps * (wx + Sw)
  have hsub := add_lt_add_of_le_of_lt (le_refl (-ex)) hcomb
  have hl2 : (-ex) + Se ≈ Se - ex := add_comm (-ex) Se
  have hr2 : (-ex) + (eps * (wx + Sw) + ex) ≈ eps * (wx + Sw) :=
    eqv_trans (add_comm _ _) (add_sub_cancel (eps * (wx + Sw)) ex)
  exact lt_of_le_of_lt (le_of_eqv (eqv_symm hl2)) (lt_of_lt_of_le hsub (le_of_eqv hr2))

/-- 정리 3c-3 (임계 전복 반경 유일성):
    두 반경 eps1, eps2 가 각각 쌍대 하한(DualStableCert)과 양의 분모 유효 분해 등호 달성을 만족하면
    eps1 ≈ eps2 로 정확 임계 전복 반경은 유일하다. -/
theorem critical_radius_unique {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps1 eps2 : Q}
    {mu1 mu2 : Fin E → Q} {lam1 lam2 : Fin m → Q}
    (hd1 : DualStableCert c cx (fun i => en i - eps1 * w i) (ex + eps1 * wx) 0 mu1)
    (hv1 : ValidDecomp c cx lam1)
    (hden1 : (0 : Q) <q wx + sumFin (fun i => lam1 i * w i))
    (ht1 : eps1 * (wx + sumFin (fun i => lam1 i * w i)) ≈ sumFin (fun i => lam1 i * en i) - ex)
    (hd2 : DualStableCert c cx (fun i => en i - eps2 * w i) (ex + eps2 * wx) 0 mu2)
    (hv2 : ValidDecomp c cx lam2)
    (hden2 : (0 : Q) <q wx + sumFin (fun i => lam2 i * w i))
    (ht2 : eps2 * (wx + sumFin (fun i => lam2 i * w i)) ≈ sumFin (fun i => lam2 i * en i) - ex) :
    eps1 ≈ eps2 := by
  let D1 := wx + sumFin (fun i => lam1 i * w i)
  let D2 := wx + sumFin (fun i => lam2 i * w i)
  have h12_mul : eps1 * D2 ≤q eps2 * D2 :=
    le_trans (critical_radius_lower_bound hd1 lam2 hv2) (le_of_eqv (eqv_symm ht2))
  have h21_mul : eps2 * D1 ≤q eps1 * D1 :=
    le_trans (critical_radius_lower_bound hd2 lam1 hv1) (le_of_eqv (eqv_symm ht1))
  have cancel_pos {a b d : Q} (hd : (0 : Q) <q d) (h : a * d ≤q b * d) : a ≤q b := by
    have hinv_nn : (0 : Q) ≤q invPos d hd := by
      rw [zero_le_iff]
      change (0 : Int) ≤ d.denI
      exact Int.le_of_lt (denI_pos d)
    have hm := mul_le_mul_of_nonneg_left hinv_nn h
    have la : invPos d hd * (a * d) ≈ a := by
      have p1 := eqv_symm (mul_assoc (invPos d hd) a d)
      have p2 := mul_congr (mul_comm (invPos d hd) a) (eqv_refl d)
      have p3 := mul_assoc a (invPos d hd) d
      have p4 := mul_congr (eqv_refl a) (invPos_mul_cancel d hd)
      exact eqv_trans (eqv_trans (eqv_trans (eqv_trans p1 p2) p3) p4) (mul_one a)
    have lb : invPos d hd * (b * d) ≈ b := by
      have p1 := eqv_symm (mul_assoc (invPos d hd) b d)
      have p2 := mul_congr (mul_comm (invPos d hd) b) (eqv_refl d)
      have p3 := mul_assoc b (invPos d hd) d
      have p4 := mul_congr (eqv_refl b) (invPos_mul_cancel d hd)
      exact eqv_trans (eqv_trans (eqv_trans (eqv_trans p1 p2) p3) p4) (mul_one b)
    exact le_trans (le_of_eqv (eqv_symm la)) (le_trans hm (le_of_eqv lb))
  exact eqv_of_le_of_le (cancel_pos hden2 h12_mul) (cancel_pos hden1 h21_mul)

/-- 보조: a - d ≤ a + d (d ≥ 0) -/
private theorem sub_le_add_of_nonneg (a d : Q) (hd : (0 : Q) ≤q d) : a - d ≤q a + d := by
  have h1 : a - d ≤q a := by
    have h := add_le_add (le_refl a) (show (-d) ≤q (0 : Q) by
      unfold le; rw [zero_le_iff] at hd; change (-d.num) * (1 : Int) ≤ (0 : Int) * d.denI; omega)
    exact le_trans h (le_of_eqv (add_zero a))
  have h2 : a ≤q a + d :=
    le_trans (le_of_eqv (eqv_symm (add_zero a))) (add_le_add (le_refl a) hd)
  exact le_trans h1 h2

/-- 정리 3d-1 (구간 내부 불안정화 취약점 존재 증인 — 명목 안정 Fragile 증명):
    eps ≥ 0, wx ≥ 0, ∀i w_i ≥ 0 이고 최악 극점 (ex + eps·wx, en - eps·w) 에서 원시 불안정 증명서 λ 가
    성립하면, 불확실성 구간 내부에 실제로 후보상 x 가 엄격 불안정해지는 실제 에너지 조합이 존재한다. -/
theorem interval_fragile_destab_witness {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {lam : Fin m → Q}
    (heps : (0 : Q) ≤q eps) (hwx : (0 : Q) ≤q wx) (hw : ∀ i, (0 : Q) ≤q w i)
    (hprimal : PrimalUnstableCert c cx (fun i => en i - eps * w i) (ex + eps * wx) lam) :
    ∃ enTrue exTrue,
      InEnergyBox (fun i => en i - eps * w i) (fun i => en i + eps * w i)
                  (ex - eps * wx) (ex + eps * wx) enTrue exTrue ∧
      ValidDecomp c cx lam ∧
      sumFin (fun i => lam i * enTrue i) <q exTrue := by
  refine ⟨fun i => en i - eps * w i, ex + eps * wx, ?_, hprimal.valid, hprimal.lower_energy⟩
  exact {
    comp_lower := fun i => le_refl _
    comp_upper := fun i => sub_le_add_of_nonneg (en i) (eps * w i) (mul_nonneg heps (hw i))
    cand_lower := sub_le_add_of_nonneg ex (eps * wx) (mul_nonneg heps hwx)
    cand_upper := le_refl _
  }

/-- 정리 3d-2 (구간 내부 안정화 취약점 존재 증인 — 명목 불안정 Fragile 증명):
    eps ≥ 0, wx ≥ 0, ∀i w_i ≥ 0 이고 유리 극점 (ex - eps·wx, en + eps·w) 에서 쌍대 안정 증명서 μ 가
    성립하면, 불확실성 구간 내부에 실제로 후보상 x 가 열역학적으로 안정해지는 실제 에너지 조합이 존재한다. -/
theorem interval_fragile_stab_witness {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {mu : Fin E → Q}
    (heps : (0 : Q) ≤q eps) (hwx : (0 : Q) ≤q wx) (hw : ∀ i, (0 : Q) ≤q w i)
    (hdual : DualStableCert c cx (fun i => en i + eps * w i) (ex - eps * wx) 0 mu) :
    ∃ enTrue exTrue,
      InEnergyBox (fun i => en i - eps * w i) (fun i => en i + eps * w i)
                  (ex - eps * wx) (ex + eps * wx) enTrue exTrue ∧
      ∀ lam, ValidDecomp c cx lam → exTrue ≤q sumFin (fun i => lam i * enTrue i) := by
  refine ⟨fun i => en i + eps * w i, ex - eps * wx, ?_, farkas_dual_on_hull hdual⟩
  exact {
    comp_lower := fun i => sub_le_add_of_nonneg (en i) (eps * w i) (mul_nonneg heps (hw i))
    comp_upper := fun i => le_refl _
    cand_lower := le_refl _
    cand_upper := sub_le_add_of_nonneg ex (eps * wx) (mul_nonneg heps hwx)
  }

end CertMat
