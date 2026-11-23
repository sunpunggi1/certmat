/-
  CertMat/BornElastic.lean
  정리 4: 6x6 탄성 텐서 Born 안정성 형식 증명
  - 정리 4a (정확한 유리수 LDL^T 양정치 충분조건):
    단위 하삼각 행렬 L (L_ii = 1, j > i 이면 L_ij = 0) 과 양의 대각 벡터 d (∀ k, d_k > 0) 에 대해
    C = L · diag(d) · L^T 가 항별로 성립하면, 모든 비영 변형률 벡터 v ≠ 0 에 대해 v^T C v > 0 이다.
  - 정리 4b (비양정치 반례 벡터 조건):
    v ≠ 0 이고 v^T C v ≤ 0 인 유리수 반례 벡터 v 가 존재하면 C 는 Born 양정치가 아니다.
  - 정리 4c (대칭 섭동 Weyl 고유값 하한 및 강건 Born 안정성):
    1) (이동 LDL^T 고유값 하한) C - λ_0 I = L diag(d) L^T (d_k > 0) 이면 ∀ v ≠ 0, v^T C v > λ_0 ‖v‖^2.
    2) (Frobenius 노름 → Rayleigh 몫 상계, 코시-슈바르츠 순수 유리수 증명)
       ‖ΔC‖_F^2 ≤ δ^2 (δ ≥ 0) 이면 ∀ v, |v^T ΔC v| ≤ δ ‖v‖^2.
    3) (Weyl 강건 Born 안정성) v^T C v > λ_0 ‖v‖^2 이고 |v^T ΔC v| ≤ δ ‖v‖^2 이며 δ ≤ λ_0 이면
       ∀ v ≠ 0, v^T (C + ΔC) v > 0 (섭동된 결정 C + ΔC 역시 보편 Born 안정).
-/

import CertMat.ExactRat

namespace CertMat

open Q

/-- n × n 행렬과 n차원 벡터 -/
abbrev Mat (n : Nat) := Fin n → Fin n → Q
abbrev Vec (n : Nat) := Fin n → Q

/-- 이차 형식 v^T C v = ∑_i ∑_j v_i C_ij v_j -/
def quadForm {n : Nat} (C : Mat n) (v : Vec n) : Q :=
  sumFin (fun i => sumFin (fun j => v i * (C i j * v j)))

/-- 유클리드 노름 제곱 ‖v‖^2 = ∑_i v_i^2 -/
def normSq {n : Nat} (v : Vec n) : Q :=
  sumFin (fun i => v i * v i)

/-- 프로베니우스 노름 제곱 ‖A‖_F^2 = ∑_i ∑_j A_ij^2 -/
def frobSq {n : Nat} (A : Mat n) : Q :=
  sumFin (fun i => sumFin (fun j => A i j * A i j))

/-- 비영 벡터 조건 -/
def NonZeroVec {n : Nat} (v : Vec n) : Prop :=
  ∃ k : Fin n, ¬ (v k ≈ 0)

/-- Born 양정치성 (엄격 양정치): ∀ v ≠ 0, v^T C v > 0 -/
def IsBornPD {n : Nat} (C : Mat n) : Prop :=
  ∀ v : Vec n, NonZeroVec v → (0 : Q) <q quadForm C v

/-- 단위 하삼각 행렬 조건: 대각선은 1, 상삼각(i < j)은 0 -/
structure IsUnitLower {n : Nat} (L : Mat n) : Prop where
  diag_one : ∀ i : Fin n, L i i ≈ 1
  upper_zero : ∀ i j : Fin n, i.val < j.val → L i j ≈ 0

/-- 정확한 유리수 LDL^T 분해 증명서 -/
structure LDLTCert {n : Nat} (C : Mat n) (L : Mat n) (d : Vec n) : Prop where
  unit_lower : IsUnitLower L
  diag_pos : ∀ k : Fin n, (0 : Q) <q d k
  factor_eq : ∀ i j : Fin n, C i j ≈ sumFin (fun k => L i k * (d k * L j k))

/-- L^T v 벡터 곱: (L^T v)_k = ∑_i L_ik v_i -/
def matTransposeMulVec {n : Nat} (L : Mat n) (v : Vec n) : Vec n :=
  fun k => sumFin (fun i => L i k * v i)

/-- 보조정리 1: C = L diag(d) L^T 일 때 v^T C v ≈ ∑_k d_k (L^T v)_k^2 -/
theorem quadForm_eq_ldlt {n : Nat} {C L : Mat n} {d : Vec n}
    (hfac : ∀ i j : Fin n, C i j ≈ sumFin (fun k => L i k * (d k * L j k)))
    (v : Vec n) :
    quadForm C v ≈ sumFin (fun k => d k * (matTransposeMulVec L v k * matTransposeMulVec L v k)) := by
  unfold quadForm matTransposeMulVec
  -- 단계 1: C_ij 를 합으로 치환하고 v_i, v_j 분배
  have hstep1 :
      sumFin (fun i => sumFin (fun j => v i * (C i j * v j))) ≈
      sumFin (fun i => sumFin (fun j => sumFin (fun k => d k * ((L i k * v i) * (L j k * v j))))) := by
    apply sumFin_congr; intro i
    apply sumFin_congr; intro j
    have e1 : v i * (C i j * v j) ≈
              v i * (sumFin (fun k => L i k * (d k * L j k)) * v j) :=
      mul_congr (eqv_refl (v i)) (mul_congr (hfac i j) (eqv_refl (v j)))
    have e2 : sumFin (fun k => L i k * (d k * L j k)) * v j ≈
              sumFin (fun k => (L i k * (d k * L j k)) * v j) :=
      sumFin_mul _ (v j)
    have e3 : v i * sumFin (fun k => (L i k * (d k * L j k)) * v j) ≈
              sumFin (fun k => v i * ((L i k * (d k * L j k)) * v j)) :=
      mul_sumFin (v i) _
    have e4 : sumFin (fun k => v i * ((L i k * (d k * L j k)) * v j)) ≈
              sumFin (fun k => d k * ((L i k * v i) * (L j k * v j))) := by
      apply sumFin_congr; intro k
      -- 순수 곱셈 교환/결합 재배열: v_i * ((L_ik * (d_k * L_jk)) * v_j) ≈ d_k * ((L_ik * v_i) * (L_jk * v_j))
      have r1 : (L i k * (d k * L j k)) * v j ≈ L i k * (d k * (L j k * v j)) :=
        eqv_trans (mul_assoc (L i k) (d k * L j k) (v j))
          (mul_congr (eqv_refl (L i k)) (mul_assoc (d k) (L j k) (v j)))
      have r2 : L i k * (d k * (L j k * v j)) ≈ d k * (L i k * (L j k * v j)) :=
        eqv_trans (eqv_symm (mul_assoc (L i k) (d k) (L j k * v j)))
          (eqv_trans (mul_congr (mul_comm (L i k) (d k)) (eqv_refl _))
                     (mul_assoc (d k) (L i k) (L j k * v j)))
      have r3 : v i * (d k * (L i k * (L j k * v j))) ≈ d k * (v i * (L i k * (L j k * v j))) :=
        eqv_trans (eqv_symm (mul_assoc (v i) (d k) _))
          (eqv_trans (mul_congr (mul_comm (v i) (d k)) (eqv_refl _))
                     (mul_assoc (d k) (v i) _))
      have r4 : v i * (L i k * (L j k * v j)) ≈ (L i k * v i) * (L j k * v j) :=
        eqv_trans (eqv_symm (mul_assoc (v i) (L i k) (L j k * v j)))
          (mul_congr (mul_comm (v i) (L i k)) (eqv_refl _))
      exact eqv_trans (mul_congr (eqv_refl (v i)) (eqv_trans r1 r2))
        (eqv_trans r3 (mul_congr (eqv_refl (d k)) r4))
    exact eqv_trans (eqv_trans e1 (mul_congr (eqv_refl (v i)) e2)) (eqv_trans e3 e4)
  -- 단계 2: 합산 순서 교환 (∑_i ∑_j ∑_k → ∑_k ∑_i ∑_j)
  have hstep2 :
      sumFin (fun i => sumFin (fun j => sumFin (fun k => d k * ((L i k * v i) * (L j k * v j))))) ≈
      sumFin (fun k => sumFin (fun i => sumFin (fun j => d k * ((L i k * v i) * (L j k * v j))))) := by
    have s1 := sumFin_congr (fun i => sumFin_comm (fun j k => d k * ((L i k * v i) * (L j k * v j))))
    have s2 := sumFin_comm (fun i k => sumFin (fun j => d k * ((L i k * v i) * (L j k * v j))))
    exact eqv_trans s1 s2
  -- 단계 3: 각 k에 대해 d_k 및 (∑_i L_ik v_i) 인수분해
  have hstep3 :
      sumFin (fun k => sumFin (fun i => sumFin (fun j => d k * ((L i k * v i) * (L j k * v j))))) ≈
      sumFin (fun k => d k * (sumFin (fun i => L i k * v i) * sumFin (fun j => L j k * v j))) := by
    apply sumFin_congr; intro k
    have f1 : sumFin (fun i => sumFin (fun j => d k * ((L i k * v i) * (L j k * v j)))) ≈
              sumFin (fun i => d k * sumFin (fun j => (L i k * v i) * (L j k * v j))) :=
      sumFin_congr (fun i => eqv_symm (mul_sumFin (d k) (fun j => (L i k * v i) * (L j k * v j))))
    have f2 : sumFin (fun i => d k * sumFin (fun j => (L i k * v i) * (L j k * v j))) ≈
              d k * sumFin (fun i => sumFin (fun j => (L i k * v i) * (L j k * v j))) :=
      eqv_symm (mul_sumFin (d k) _)
    have f3 : sumFin (fun i => sumFin (fun j => (L i k * v i) * (L j k * v j))) ≈
              sumFin (fun i => (L i k * v i) * sumFin (fun j => L j k * v j)) :=
      sumFin_congr (fun i => eqv_symm (mul_sumFin (L i k * v i) (fun j => L j k * v j)))
    have f4 : sumFin (fun i => (L i k * v i) * sumFin (fun j => L j k * v j)) ≈
              sumFin (fun i => L i k * v i) * sumFin (fun j => L j k * v j) :=
      eqv_symm (sumFin_mul (fun i => L i k * v i) (sumFin (fun j => L j k * v j)))
    exact eqv_trans (eqv_trans f1 f2) (mul_congr (eqv_refl (d k)) (eqv_trans f3 f4))
  exact eqv_trans (eqv_trans hstep1 hstep2) hstep3

/-- 보조정리 2: Fin n 위의 합에서 단 하나의 인덱스 k 외 모든 항이 0이면 합 ≈ f k -/
private theorem sumFin_single_nonzero {n : Nat} (f : Fin n → Q) (k : Fin n)
    (hzero : ∀ i : Fin n, i ≠ k → f i ≈ 0) :
    sumFin f ≈ f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    change sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n) ≈ f k
    revert hzero
    refine Fin.lastCases ?_ ?_ k
    · -- k = Fin.last n
      intro hzero
      have hprev : sumFin (fun i : Fin n => f i.castSucc) ≈ 0 :=
        eqv_trans (sumFin_congr (fun i => hzero i.castSucc (fun heq => by
          have hv : i.val = n := congrArg Fin.val heq
          omega))) sumFin_zero
      exact eqv_trans (add_congr hprev (eqv_refl (f (Fin.last n)))) (zero_add _)
    · -- k = j.castSucc
      intro j hzero
      have hlast : f (Fin.last n) ≈ 0 := hzero (Fin.last n) (fun heq => by
        have hv : n = j.val := congrArg Fin.val heq
        omega)
      have hprev : sumFin (fun i : Fin n => f i.castSucc) ≈ f j.castSucc :=
        ih (fun i => f i.castSucc) j (fun i hi =>
          hzero i.castSucc (fun heq => by
            have hv : i.castSucc.val = j.castSucc.val := congrArg (fun x : Fin (n + 1) => x.val) heq
            exact hi (Fin.ext hv)))
      exact eqv_trans (add_congr hprev hlast) (add_zero _)

/-- 보조정리 3: 비영 벡터 v 는 가장 큰 비영 인덱스 k* 를 가진다 -/
private theorem exists_max_nonzero {n : Nat} (v : Vec n) (hne : NonZeroVec v) :
    ∃ k : Fin n, ¬ (v k ≈ 0) ∧ ∀ i : Fin n, k.val < i.val → v i ≈ 0 := by
  induction n with
  | zero =>
    rcases hne with ⟨k, _⟩
    exact Fin.elim0 k
  | succ n ih =>
    by_cases hlast : v (Fin.last n) ≈ 0
    · -- 마지막 원소가 0이면 앞의 n개 중에 비영 원소 존재
      have hne_prev : NonZeroVec (fun i : Fin n => v i.castSucc) := by
        rcases hne with ⟨idx, hidx⟩
        refine Fin.lastCases ?_ ?_ idx hidx
        · intro hcontrad; exact False.elim (hcontrad hlast)
        · intro j hj; exact ⟨j, hj⟩
      rcases ih (fun i => v i.castSucc) hne_prev with ⟨k, hk_ne, hk_max⟩
      refine ⟨k.castSucc, hk_ne, ?_⟩
      intro i hki
      refine Fin.lastCases ?_ ?_ i hki
      · intro _; exact hlast
      · intro j hj
        exact hk_max j hj
    · -- 마지막 원소가 비영이면 그것이 최대 인덱스
      refine ⟨Fin.last n, hlast, ?_⟩
      intro i hi
      have hlt : i.val < n + 1 := i.isLt
      simp only [Fin.val_last] at hi
      omega

/-- 보조정리 4: 단위 하삼각 행렬 L 의 전치 L^T 는 비영 벡터를 비영 벡터로 보낸다 -/
theorem unitLower_transpose_injective {n : Nat} {L : Mat n} (hL : IsUnitLower L)
    {v : Vec n} (hne : NonZeroVec v) :
    NonZeroVec (matTransposeMulVec L v) := by
  rcases exists_max_nonzero v hne with ⟨k, hk_ne, hk_max⟩
  refine ⟨k, ?_⟩
  unfold matTransposeMulVec
  -- (L^T v)_k = ∑_i L_ik v_i 에서 i ≠ k 인 모든 항은 0이다:
  -- i < k 이면 L_ik = 0 (하삼각), i > k 이면 v_i = 0 (최대 비영 인덱스 k)
  have hsingle : sumFin (fun i => L i k * v i) ≈ L k k * v k := by
    apply sumFin_single_nonzero (fun i => L i k * v i) k
    intro i hik
    by_cases hlt : i.val < k.val
    · exact eqv_trans (mul_congr (hL.upper_zero i k hlt) (eqv_refl (v i))) (zero_mul (v i))
    · have hgt : k.val < i.val := by
        have hne_val : i.val ≠ k.val := fun h => hik (Fin.ext h)
        omega
      exact eqv_trans (mul_congr (eqv_refl (L i k)) (hk_max i hgt)) (mul_zero (L i k))
  have hval : sumFin (fun i => L i k * v i) ≈ v k :=
    eqv_trans hsingle (eqv_trans (mul_congr (hL.diag_one k) (eqv_refl (v k))) (one_mul (v k)))
  intro hzero
  exact hk_ne (eqv_trans (eqv_symm hval) hzero)

/-- 정리 4a (정확한 유리수 LDL^T 양정치 충분조건):
    LDL^T 증명서가 성립하면 C 는 모든 비영 벡터 v 에 대해 v^T C v > 0 (Born 안정) 이다. -/
theorem born_pd_of_ldlt {n : Nat} {C L : Mat n} {d : Vec n}
    (hcert : LDLTCert C L d) : IsBornPD C := by
  intro v hne
  have heq := quadForm_eq_ldlt hcert.factor_eq v
  rcases unitLower_transpose_injective hcert.unit_lower hne with ⟨k, hk_ne⟩
  let w := matTransposeMulVec L v
  have hnn : ∀ j : Fin n, (0 : Q) ≤q d j * (w j * w j) :=
    fun j => mul_nonneg (le_of_lt (hcert.diag_pos j)) (sq_nonneg (w j))
  have hpos_k : (0 : Q) <q d k * (w k * w k) :=
    mul_pos (hcert.diag_pos k) (sq_pos_of_ne_zero hk_ne)
  have hsum_pos : (0 : Q) <q sumFin (fun j => d j * (w j * w j)) :=
    sumFin_pos_of_exists_pos hnn k hpos_k
  exact lt_of_lt_of_le hsum_pos (le_of_eqv (eqv_symm heq))

/-- 정리 4b (비양정치 반례 벡터 조건):
    비영 벡터 v 가 v^T C v ≤ 0 을 만족하면 C 는 Born 양정치가 아니다. -/
theorem not_born_pd_of_witness {n : Nat} {C : Mat n} {v : Vec n}
    (hne : NonZeroVec v) (hnonpos : quadForm C v ≤q 0) :
    ¬ IsBornPD C := by
  intro hpd
  exact not_lt_of_le hnonpos (hpd v hne)

/-- 보조정리 5: 비영 벡터 v 의 노름 제곱 ‖v‖^2 > 0 -/
theorem normSq_pos {n : Nat} {v : Vec n} (hne : NonZeroVec v) : (0 : Q) <q normSq v := by
  rcases hne with ⟨k, hk⟩
  exact sumFin_pos_of_exists_pos (fun i => sq_nonneg (v i)) k (sq_pos_of_ne_zero hk)

/-- 이동 행렬 (C - lam0 * I) 정의 -/
def shiftMat {n : Nat} (C : Mat n) (lam0 : Q) : Mat n :=
  fun i j => if i = j then C i j - lam0 else C i j

/-- 행렬 덧셈 (C + dC) 정의 -/
def addMat {n : Nat} (C dC : Mat n) : Mat n :=
  fun i j => C i j + dC i j

/-- 보조정리 6: 이차 형식의 행렬 덧셈 선형성 -/
theorem quadForm_add {n : Nat} (C dC : Mat n) (v : Vec n) :
    quadForm (addMat C dC) v ≈ quadForm C v + quadForm dC v := by
  unfold quadForm addMat
  have hinner (i : Fin n) :
      sumFin (fun j => v i * ((C i j + dC i j) * v j)) ≈
      sumFin (fun j => v i * (C i j * v j)) + sumFin (fun j => v i * (dC i j * v j)) := by
    have s1 := sumFin_congr (fun j =>
      eqv_trans (mul_congr (eqv_refl (v i)) (add_mul (C i j) (dC i j) (v j)))
                (mul_add (v i) (C i j * v j) (dC i j * v j)))
    exact eqv_trans s1 (sumFin_add _ _)
  exact eqv_trans (sumFin_congr hinner) (sumFin_add _ _)

/-- 보조정리 7: 이동 행렬의 이차 형식 v^T (C - lam0 I) v ≈ v^T C v - lam0 * ‖v‖^2 -/
theorem quadForm_shift {n : Nat} (C : Mat n) (lam0 : Q) (v : Vec n) :
    quadForm (shiftMat C lam0) v ≈ quadForm C v - lam0 * normSq v := by
  unfold quadForm shiftMat normSq
  -- 각 i에 대해 ∑_j v_i * ((if i=j then C_ij - lam0 else C_ij) * v_j) ≈ ∑_j v_i*(C_ij*v_j) - lam0*(v_i*v_i)
  have hinner (i : Fin n) :
      sumFin (fun j => v i * ((if i = j then C i j - lam0 else C i j) * v j)) ≈
      sumFin (fun j => v i * (C i j * v j)) - lam0 * (v i * v i) := by
    -- 항 분리: f_j - g_j 형태 (j = i 일 때만 lam0 * v_i * v_i)
    let g : Fin n → Q := fun j => if i = j then lam0 * (v i * v i) else 0
    have hdiff : sumFin (fun j => v i * ((if i = j then C i j - lam0 else C i j) * v j)) ≈
                 sumFin (fun j => v i * (C i j * v j) - g j) := by
      apply sumFin_congr; intro j
      by_cases hij : i = j
      · subst hij
        simp only [g, ↓reduceIte]
        have e1 := mul_congr (eqv_refl (v i)) (add_mul (C i i) (-lam0) (v i))
        have e2 := mul_add (v i) (C i i * v i) ((-lam0) * v i)
        have e3 : v i * ((-lam0) * v i) ≈ -(lam0 * (v i * v i)) := by
          have p1 : (-lam0) * v i ≈ -(lam0 * v i) := neg_mul lam0 (v i)
          have p2 : v i * (-(lam0 * v i)) ≈ -(v i * (lam0 * v i)) :=
            eqv_trans (mul_comm (v i) _) (eqv_trans (neg_mul (lam0 * v i) (v i)) (neg_congr (mul_comm _ _)))
          have p3 : v i * (lam0 * v i) ≈ lam0 * (v i * v i) :=
            eqv_trans (eqv_symm (mul_assoc (v i) lam0 (v i)))
              (eqv_trans (mul_congr (mul_comm (v i) lam0) (eqv_refl (v i))) (mul_assoc lam0 (v i) (v i)))
          exact eqv_trans (mul_congr (eqv_refl (v i)) p1) (eqv_trans p2 (neg_congr p3))
        exact eqv_trans (eqv_trans e1 e2) (add_congr (eqv_refl _) e3)
      · simp only [g, hij, ↓reduceIte]
        have hzero : v i * (C i j * v j) - 0 ≈ v i * (C i j * v j) := by
          have hn0 : -(0 : Q) ≈ 0 := by
            change (-(0 : Int)) * (1 : Int) = (0 : Int) * (1 : Int)
            omega
          exact eqv_trans (add_congr (eqv_refl _) hn0) (add_zero _)
        exact eqv_symm hzero
    have hsub := sumFin_sub (fun j => v i * (C i j * v j)) g
    have hg : sumFin g ≈ lam0 * (v i * v i) := by
      have hsingle := sumFin_single_nonzero g i (fun j hji => by
        have hneq : ¬ (i = j) := Ne.symm hji
        simp only [g, hneq, ↓reduceIte]
        exact eqv_refl 0)
      simp only [g, ↓reduceIte] at hsingle
      exact hsingle
    exact eqv_trans (eqv_trans hdiff hsub) (sub_congr (eqv_refl _) hg)
  have houter := eqv_trans (sumFin_congr hinner)
    (sumFin_sub (fun i => sumFin (fun j => v i * (C i j * v j))) (fun i => lam0 * (v i * v i)))
  exact eqv_trans houter (sub_congr (eqv_refl _) (eqv_symm (mul_sumFin lam0 (fun i => v i * v i))))

/-- 정리 4c-1 (이동 LDL^T 에 의한 엄격 고유값 하한 증명):
    C - λ_0 I 가 LDL^T 증명서를 가지면, 모든 비영 벡터 v 에 대해 v^T C v > λ_0 ‖v‖^2 이다. -/
theorem eigenvalue_lower_bound_of_shifted_ldlt {n : Nat} {C L : Mat n} {d : Vec n} {lam0 : Q}
    (hcert : LDLTCert (shiftMat C lam0) L d) :
    ∀ v : Vec n, NonZeroVec v → lam0 * normSq v <q quadForm C v := by
  intro v hne
  have hpos : (0 : Q) <q quadForm (shiftMat C lam0) v := born_pd_of_ldlt hcert v hne
  have hpos2 : (0 : Q) <q quadForm C v - lam0 * normSq v :=
    lt_of_lt_of_le hpos (le_of_eqv (quadForm_shift C lam0 v))
  exact (sub_pos_iff (quadForm C v) (lam0 * normSq v)).mp hpos2

/-- 정리 4c-2 (대칭 섭동 Weyl 고유값 하한 및 강건 Born 안정성):
    1) C 의 최소 고유값이 λ_0 보다 크고 (∀ v ≠ 0, λ_0 ‖v‖^2 < v^T C v),
    2) 섭동 ΔC 의 스펙트럼 반경이 δ 이하이며 (∀ v, -(δ ‖v‖^2) ≤ v^T ΔC v),
    3) δ ≤ λ_0 이면,
    섭동된 탄성 텐서 C + ΔC 는 무조건 Born 양정치이다. -/
theorem weyl_robust_born_pd {n : Nat} {C dC : Mat n} {lam0 delta : Q}
    (heig : ∀ v : Vec n, NonZeroVec v → lam0 * normSq v <q quadForm C v)
    (hpert : ∀ v : Vec n, -(delta * normSq v) ≤q quadForm dC v)
    (hmargin : delta ≤q lam0) :
    IsBornPD (addMat C dC) := by
  intro v hne
  have hns : (0 : Q) ≤q normSq v := le_of_lt (normSq_pos hne)
  have h1 : delta * normSq v ≤q lam0 * normSq v := by
    have p := mul_le_mul_of_nonneg_left hns hmargin
    exact le_trans (le_of_eqv (mul_comm delta (normSq v)))
      (le_trans p (le_of_eqv (mul_comm (normSq v) lam0)))
  have h2 : delta * normSq v <q quadForm C v := lt_of_le_of_lt h1 (heig v hne)
  have hsum : delta * normSq v + -(delta * normSq v) <q quadForm C v + quadForm dC v := by
    have hadd := add_lt_add_of_le_of_lt (hpert v) h2
    have hl : -(delta * normSq v) + delta * normSq v ≈ delta * normSq v + -(delta * normSq v) := add_comm _ _
    have hr : quadForm dC v + quadForm C v ≈ quadForm C v + quadForm dC v := add_comm _ _
    exact lt_of_le_of_lt (le_of_eqv (eqv_symm hl)) (lt_of_lt_of_le hadd (le_of_eqv hr))
  have h0 : (0 : Q) ≈ delta * normSq v + -(delta * normSq v) := eqv_symm (sub_self (delta * normSq v))
  have hpos : (0 : Q) <q quadForm C v + quadForm dC v := lt_of_le_of_lt (le_of_eqv h0) hsum
  exact lt_of_lt_of_le hpos (le_of_eqv (eqv_symm (quadForm_add C dC v)))

/-- 정리 4c-3 (프로베니우스 노름 섭동 상계 → Weyl 조건 자동 충족, 코시-슈바르츠 순수 유리수 증명):
    ‖ΔC‖_F^2 ≤ δ^2 이고 δ ≥ 0 이면 모든 벡터 v 에 대해 -(δ ‖v‖^2) ≤ v^T ΔC v 가 성립한다. -/
theorem frobenius_implies_weyl_bound {n : Nat} {dC : Mat n} {delta : Q}
    (hdelta : (0 : Q) ≤q delta)
    (hfrob : frobSq dC ≤q delta * delta) :
    ∀ v : Vec n, -(delta * normSq v) ≤q quadForm dC v := by
  intro v
  -- 행별 코시-슈바르츠 적용:
  -- (v^T dC v)^2 = (∑_i v_i (∑_j dC_ij v_j))^2 ≤ (∑_i v_i^2) * ∑_i (∑_j dC_ij v_j)^2
  -- ≤ (∑_i v_i^2) * ∑_i ((∑_j dC_ij^2)(∑_j v_j^2)) = ‖dC‖_F^2 * ‖v‖^4 ≤ δ^2 * ‖v‖^4
  let qv := quadForm dC v
  let ns := normSq v
  let u : Vec n := fun i => sumFin (fun j => dC i j * v j)
  have hqv_eq : qv ≈ sumFin (fun i => v i * u i) := by
    exact sumFin_congr (fun i => eqv_symm (mul_sumFin (v i) (fun j => dC i j * v j)))
  have hcs1 : sumFin (fun i => v i * u i) * sumFin (fun i => v i * u i) ≤q
              ns * sumFin (fun i => u i * u i) := cauchy_schwarz v u
  have hcs2 : sumFin (fun i => u i * u i) ≤q frobSq dC * ns := by
    have hrow (i : Fin n) : u i * u i ≤q sumFin (fun j => dC i j * dC i j) * ns :=
      cauchy_schwarz (fun j => dC i j) v
    have hsum := sumFin_le_sumFin hrow
    have hfac : sumFin (fun i => sumFin (fun j => dC i j * dC i j) * ns) ≈ frobSq dC * ns :=
      eqv_symm (sumFin_mul (fun i => sumFin (fun j => dC i j * dC i j)) ns)
    exact le_trans hsum (le_of_eqv hfac)
  have hns_nn : (0 : Q) ≤q ns := sumFin_nonneg (fun i => sq_nonneg (v i))
  have hqv_sq : qv * qv ≤q (delta * ns) * (delta * ns) := by
    have p1 : qv * qv ≈ sumFin (fun i => v i * u i) * sumFin (fun i => v i * u i) :=
      mul_congr hqv_eq hqv_eq
    have p2 : ns * sumFin (fun i => u i * u i) ≤q ns * (frobSq dC * ns) :=
      mul_le_mul_of_nonneg_left hns_nn hcs2
    have p3 : ns * (frobSq dC * ns) ≈ frobSq dC * (ns * ns) :=
      eqv_trans (eqv_symm (mul_assoc ns (frobSq dC) ns))
        (eqv_trans (mul_congr (mul_comm ns (frobSq dC)) (eqv_refl ns)) (mul_assoc (frobSq dC) ns ns))
    have p4 : frobSq dC * (ns * ns) ≤q (delta * delta) * (ns * ns) := by
      have hnn := mul_nonneg hns_nn hns_nn
      have q := mul_le_mul_of_nonneg_left hnn hfrob
      exact le_trans (le_of_eqv (mul_comm (frobSq dC) (ns * ns)))
        (le_trans q (le_of_eqv (mul_comm (ns * ns) (delta * delta))))
    have p5 : (delta * delta) * (ns * ns) ≈ (delta * ns) * (delta * ns) := by
      have e1 := mul_assoc delta delta (ns * ns)
      have e2 : delta * (ns * ns) ≈ ns * (delta * ns) :=
        eqv_trans (eqv_symm (mul_assoc delta ns ns))
          (eqv_trans (mul_congr (mul_comm delta ns) (eqv_refl ns)) (mul_assoc ns delta ns))
      exact eqv_trans (eqv_trans e1 (mul_congr (eqv_refl delta) e2)) (eqv_symm (mul_assoc delta ns (delta * ns)))
    exact le_trans (le_of_eqv p1) (le_trans hcs1 (le_trans p2 (le_trans (le_of_eqv p3) (le_trans p4 (le_of_eqv p5)))))
  -- qv^2 ≤ B^2 (B = delta * ns ≥ 0) 이면 -B ≤ qv 를 귀류법으로 증명
  let B := delta * ns
  have hB_nn : (0 : Q) ≤q B := mul_nonneg hdelta hns_nn
  by_cases hge : -B ≤q qv
  · exact hge
  · have hqv_lt : qv <q -B := by
      unfold le lt at *
      omega
    -- -qv > B ≥ 0 이므로 (-qv)^2 > B^2, 즉 qv^2 > B^2 로 모순!
    have hpos_neg : B <q -qv := by
      unfold lt at *
      change B.num * qv.denI < (-qv.num) * B.denI
      change qv.num * B.denI < (-B.num) * qv.denI at hqv_lt
      rw [Int.neg_mul] at hqv_lt ⊢
      omega
    have hnqv_pos : (0 : Q) <q -qv := lt_of_le_of_lt hB_nn hpos_neg
    -- B * B ≤ B * (-qv) < (-qv) * (-qv) ≈ qv * qv
    have stepA : B * B ≤q B * (-qv) := mul_le_mul_of_nonneg_left hB_nn (le_of_lt hpos_neg)
    have stepB : B * (-qv) <q (-qv) * (-qv) := by
      -- (-qv) * B < (-qv) * (-qv)
      have hdiff : (0 : Q) <q (-qv) - B := (sub_pos_iff (-qv) B).mpr hpos_neg
      have hprod : (0 : Q) <q (-qv) * ((-qv) - B) := mul_pos hnqv_pos hdiff
      have heq : (-qv) * ((-qv) - B) ≈ (-qv) * (-qv) - B * (-qv) := by
        have d1 := mul_add (-qv) (-qv) (-B)
        have d2 : (-qv) * (-B) ≈ -(B * (-qv)) :=
          eqv_trans (mul_comm (-qv) (-B)) (neg_mul B (-qv))
        exact eqv_trans d1 (add_congr (eqv_refl _) d2)
      have hpos_sub : (0 : Q) <q (-qv) * (-qv) - B * (-qv) := lt_of_lt_of_le hprod (le_of_eqv heq)
      exact (sub_pos_iff _ _).mp hpos_sub
    have hsq_eq : (-qv) * (-qv) ≈ qv * qv := by
      unfold eqv
      change ((-qv.num) * (-qv.num)) * (qv * qv).denI = (qv.num * qv.num) * ((-qv) * (-qv)).denI
      rw [denI_mul, denI_mul, denI_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have hB_lt_qv : B * B <q qv * qv := lt_of_lt_of_le (lt_of_le_of_lt stepA stepB) (le_of_eqv hsq_eq)
    exact False.elim (not_lt_of_le hqv_sq hB_lt_qv)

/-- 따름정리 4c (프로베니우스 섭동 하 강건 Born 안정성 최종 정리):
    이동 LDL^T 로 λ_min(C) > λ_0 를 인증하고 ‖ΔC‖_F^2 ≤ δ^2 (0 ≤ δ ≤ λ_0) 이면
    섭동된 텐서 C + ΔC 는 무조건 Born 양정치이다. -/
theorem shifted_ldlt_frob_robust_born {n : Nat} {C dC L : Mat n} {d : Vec n} {lam0 delta : Q}
    (hcert : LDLTCert (shiftMat C lam0) L d)
    (hdelta : (0 : Q) ≤q delta)
    (hfrob : frobSq dC ≤q delta * delta)
    (hmargin : delta ≤q lam0) :
    IsBornPD (addMat C dC) :=
  weyl_robust_born_pd
    (eigenvalue_lower_bound_of_shifted_ldlt hcert)
    (frobenius_implies_weyl_bound hdelta hfrob)
    hmargin

/-- 행렬 대칭성 술어: ∀ i j, A_ij ≈ A_ji -/
def IsSymmetricMat {n : Nat} (A : Mat n) : Prop :=
  ∀ i j : Fin n, A i j ≈ A j i

/-- Rayleigh 몫 하계 술어 (실수 대칭 행렬의 스펙트럼 노름 ‖ΔC‖_2 ≤ δ 또는 λ_min(ΔC) ≥ -δ 의 정확한 유리수 대수 표현) -/
def IsRayleighBounded {n : Nat} (dC : Mat n) (delta : Q) : Prop :=
  ∀ v : Vec n, -(delta * normSq v) ≤q quadForm dC v

/-- 정리 4c' (Rayleigh/스펙트럼 하계 섭동 하 강건 Born 안정성 최종 정리):
    이동 LDL^T 로 C - λ_0 I ≻ 0 을 인증하고 δ ≤ λ_0 이면,
    Rayleigh 하계 -(δ‖v‖^2) ≤ v^T ΔC v 를 만족하는 모든 섭동 ΔC 에 대해 C + ΔC 는 Born 양정치이다. -/
theorem shifted_ldlt_rayleigh_robust_born {n : Nat} {C dC L : Mat n} {d : Vec n} {lam0 delta : Q}
    (hcert : LDLTCert (shiftMat C lam0) L d)
    (hpert : IsRayleighBounded dC delta)
    (hmargin : delta ≤q lam0) :
    IsBornPD (addMat C dC) :=
  weyl_robust_born_pd (eigenvalue_lower_bound_of_shifted_ldlt hcert) hpert hmargin

/-- 정리 4d (Weyl 기계적 취약성 구성적 반례 섭동 정리):
    비영 유리수 변형률 벡터 v ≠ 0 가 v^T C v ≤ δ ‖v‖^2 (즉 v^T (C - δ I) v ≤ 0) 를 만족하면,
    명시적 대칭 랭크-1 유리수 섭동 행렬 ΔC_ij = -(δ / ‖v‖^2) v_i v_j 는
    1) 대칭 행렬이며 (ΔC_ij ≈ ΔC_ji),
    2) 정확히 프로베니우스 노름 ‖ΔC‖_F^2 ≈ δ^2 을 가지며,
    3) C + ΔC 가 Born 비양정치(v^T (C + ΔC) v ≤ 0)임을 구성적으로 증명한다. -/
theorem weyl_fragile_of_witness {n : Nat} {C : Mat n} {v : Vec n} {delta : Q}
    (hne : NonZeroVec v)
    (hweak : quadForm C v ≤q delta * normSq v) :
    ∃ dC : Mat n,
      IsSymmetricMat dC ∧
      frobSq dC ≈ delta * delta ∧
      ¬ IsBornPD (addMat C dC) := by
  have hns_pos : (0 : Q) <q normSq v := normSq_pos hne
  let invNs : Q := invPos (normSq v) hns_pos
  let alpha : Q := -(delta * invNs)
  let dC : Mat n := fun i j => alpha * (v i * v j)
  refine ⟨dC, ?_, ?_, ?_⟩
  · -- 1) 대칭성: alpha * (v i * v j) ≈ alpha * (v j * v i)
    intro i j
    exact mul_congr (eqv_refl alpha) (mul_comm (v i) (v j))
  · -- 2) 프로베니우스 노름 제곱: ∑_i ∑_j (alpha * (v_i v_j))^2 ≈ alpha^2 * ‖v‖^4 ≈ delta^2
    unfold frobSq
    have hterm (i j : Fin n) :
        (alpha * (v i * v j)) * (alpha * (v i * v j)) ≈
        (alpha * alpha) * ((v i * v i) * (v j * v j)) := by
      have p1 : (alpha * (v i * v j)) * (alpha * (v i * v j)) ≈
                (alpha * alpha) * ((v i * v j) * (v i * v j)) := by
        have s1 := mul_assoc alpha (v i * v j) (alpha * (v i * v j))
        have s2 : (v i * v j) * (alpha * (v i * v j)) ≈ alpha * ((v i * v j) * (v i * v j)) :=
          eqv_trans (eqv_symm (mul_assoc (v i * v j) alpha (v i * v j)))
            (eqv_trans (mul_congr (mul_comm (v i * v j) alpha) (eqv_refl _))
                       (mul_assoc alpha (v i * v j) (v i * v j)))
        exact eqv_trans (eqv_trans s1 (mul_congr (eqv_refl alpha) s2))
          (eqv_symm (mul_assoc alpha alpha ((v i * v j) * (v i * v j))))
      have p2 : (v i * v j) * (v i * v j) ≈ (v i * v i) * (v j * v j) := by
        have s1 := mul_assoc (v i) (v j) (v i * v j)
        have s2 : v j * (v i * v j) ≈ v i * (v j * v j) :=
          eqv_trans (eqv_symm (mul_assoc (v j) (v i) (v j)))
            (eqv_trans (mul_congr (mul_comm (v j) (v i)) (eqv_refl (v j)))
                       (mul_assoc (v i) (v j) (v j)))
        exact eqv_trans (eqv_trans s1 (mul_congr (eqv_refl (v i)) s2))
          (eqv_symm (mul_assoc (v i) (v i) (v j * v j)))
      exact eqv_trans p1 (mul_congr (eqv_refl (alpha * alpha)) p2)
    have hsum1 :
        sumFin (fun i => sumFin (fun j => dC i j * dC i j)) ≈
        sumFin (fun i => sumFin (fun j => (alpha * alpha) * ((v i * v i) * (v j * v j)))) :=
      sumFin_congr (fun i => sumFin_congr (fun j => hterm i j))
    have hsum2 :
        sumFin (fun i => sumFin (fun j => (alpha * alpha) * ((v i * v i) * (v j * v j)))) ≈
        (alpha * alpha) * (normSq v * normSq v) := by
      have f1 := sumFin_congr (fun i =>
        eqv_symm (mul_sumFin (alpha * alpha) (fun j => (v i * v i) * (v j * v j))))
      have f2 := eqv_symm (mul_sumFin (alpha * alpha)
        (fun i => sumFin (fun j => (v i * v i) * (v j * v j))))
      have f3 : sumFin (fun i => sumFin (fun j => (v i * v i) * (v j * v j))) ≈
                normSq v * normSq v := by
        have g1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (v i * v i) (fun j => v j * v j)))
        exact eqv_trans g1 (eqv_symm (sumFin_mul (fun i => v i * v i) (normSq v)))
      exact eqv_trans (eqv_trans f1 f2) (mul_congr (eqv_refl (alpha * alpha)) f3)
    have halpha_sq : alpha * alpha ≈ (delta * invNs) * (delta * invNs) :=
      neg_mul_neg (delta * invNs) (delta * invNs)
    have hcancel_pair : (delta * invNs) * normSq v ≈ delta :=
      eqv_trans (mul_assoc delta invNs (normSq v))
        (eqv_trans (mul_congr (eqv_refl delta) (invPos_mul_cancel (normSq v) hns_pos)) (mul_one delta))
    have hfinal : ((delta * invNs) * (delta * invNs)) * (normSq v * normSq v) ≈ delta * delta := by
      have q1 := mul_assoc (delta * invNs) (delta * invNs) (normSq v * normSq v)
      have q2 : (delta * invNs) * (normSq v * normSq v) ≈ normSq v * ((delta * invNs) * normSq v) :=
        eqv_trans (eqv_symm (mul_assoc (delta * invNs) (normSq v) (normSq v)))
          (eqv_trans (mul_congr (mul_comm (delta * invNs) (normSq v)) (eqv_refl (normSq v)))
                     (mul_assoc (normSq v) (delta * invNs) (normSq v)))
      have q3 := eqv_trans q1 (mul_congr (eqv_refl (delta * invNs)) q2)
      have q4 := eqv_trans q3 (eqv_symm (mul_assoc (delta * invNs) (normSq v) ((delta * invNs) * normSq v)))
      exact eqv_trans q4 (mul_congr hcancel_pair hcancel_pair)
    exact eqv_trans (eqv_trans hsum1 hsum2) (eqv_trans (mul_congr halpha_sq (eqv_refl _)) hfinal)
  · -- 3) 이차 형식 비양수: v^T (C + dC) v ≈ v^T C v - delta * ‖v‖^2 ≤ 0
    have hqdC : quadForm dC v ≈ -(delta * normSq v) := by
      unfold quadForm
      have ht (i j : Fin n) : v i * (dC i j * v j) ≈ alpha * ((v i * v i) * (v j * v j)) := by
        -- v_i * ((alpha * (v_i * v_j)) * v_j) ≈ alpha * ((v_i * v_i) * (v_j * v_j))
        have e1 : (alpha * (v i * v j)) * v j ≈ alpha * (v i * (v j * v j)) :=
          eqv_trans (mul_assoc alpha (v i * v j) (v j))
            (mul_congr (eqv_refl alpha) (mul_assoc (v i) (v j) (v j)))
        have e2 : v i * (alpha * (v i * (v j * v j))) ≈ alpha * ((v i * v i) * (v j * v j)) := by
          have s1 := eqv_symm (mul_assoc (v i) alpha (v i * (v j * v j)))
          have s2 := mul_congr (mul_comm (v i) alpha) (eqv_refl (v i * (v j * v j)))
          have s3 := mul_assoc alpha (v i) (v i * (v j * v j))
          have s4 := mul_congr (eqv_refl alpha) (eqv_symm (mul_assoc (v i) (v i) (v j * v j)))
          exact eqv_trans (eqv_trans (eqv_trans s1 s2) s3) s4
        exact eqv_trans (mul_congr (eqv_refl (v i)) e1) e2
      have s1 := sumFin_congr (fun i => sumFin_congr (fun j => ht i j))
      have s2 : sumFin (fun i => sumFin (fun j => alpha * ((v i * v i) * (v j * v j)))) ≈
                alpha * (normSq v * normSq v) := by
        have f1 := sumFin_congr (fun i =>
          eqv_symm (mul_sumFin alpha (fun j => (v i * v i) * (v j * v j))))
        have f2 := eqv_symm (mul_sumFin alpha
          (fun i => sumFin (fun j => (v i * v i) * (v j * v j))))
        have f3 : sumFin (fun i => sumFin (fun j => (v i * v i) * (v j * v j))) ≈
                  normSq v * normSq v := by
          have g1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (v i * v i) (fun j => v j * v j)))
          exact eqv_trans g1 (eqv_symm (sumFin_mul (fun i => v i * v i) (normSq v)))
        exact eqv_trans (eqv_trans f1 f2) (mul_congr (eqv_refl alpha) f3)
      have s3 : alpha * (normSq v * normSq v) ≈ -(delta * normSq v) := by
        have m1 : (-(delta * invNs)) * (normSq v * normSq v) ≈
                  -((delta * invNs) * (normSq v * normSq v)) := neg_mul _ _
        have m2 : (delta * invNs) * (normSq v * normSq v) ≈ delta * normSq v := by
          have p1 := eqv_symm (mul_assoc (delta * invNs) (normSq v) (normSq v))
          have p2 : (delta * invNs) * normSq v ≈ delta :=
            eqv_trans (mul_assoc delta invNs (normSq v))
              (eqv_trans (mul_congr (eqv_refl delta) (invPos_mul_cancel (normSq v) hns_pos)) (mul_one delta))
          exact eqv_trans p1 (mul_congr p2 (eqv_refl (normSq v)))
        exact eqv_trans m1 (neg_congr m2)
      exact eqv_trans (eqv_trans s1 s2) s3
    have hqadd : quadForm (addMat C dC) v ≈ quadForm C v - delta * normSq v :=
      eqv_trans (quadForm_add C dC v) (add_congr (eqv_refl (quadForm C v)) hqdC)
    have hle0 : quadForm (addMat C dC) v ≤q 0 := by
      have hdiff_le : quadForm C v - delta * normSq v ≤q 0 := by
        have h := add_le_add hweak (le_refl (-(delta * normSq v)))
        exact le_trans h (le_of_eqv (sub_self (delta * normSq v)))
      exact le_trans (le_of_eqv hqadd) hdiff_le
    exact not_born_pd_of_witness hne hle0

/-- 대각 가중 이동 행렬 (C - lam0 * diag(s)) 정의 (SO(3)-불변 Mandel 고유값의 순수 유리수 인증: s = (1,1,1,1/2,1/2,1/2)) -/
def weightedShiftMat {n : Nat} (C : Mat n) (lam0 : Q) (s : Vec n) : Mat n :=
  fun i j => if i = j then C i j - lam0 * s i else C i j

/-- 대각 가중 노름 제곱 ‖v‖_s^2 = ∑_i s_i v_i^2 -/
def weightedNormSq {n : Nat} (s v : Vec n) : Q :=
  sumFin (fun i => s i * (v i * v i))

/-- 보조정리 8: 가중 이동 행렬의 이차 형식 v^T (C - lam0 diag(s)) v ≈ v^T C v - lam0 * ‖v‖_s^2 -/
theorem quadForm_weightedShift {n : Nat} (C : Mat n) (lam0 : Q) (s v : Vec n) :
    quadForm (weightedShiftMat C lam0 s) v ≈ quadForm C v - lam0 * weightedNormSq s v := by
  unfold quadForm weightedShiftMat weightedNormSq
  have hinner (i : Fin n) :
      sumFin (fun j => v i * ((if i = j then C i j - lam0 * s i else C i j) * v j)) ≈
      sumFin (fun j => v i * (C i j * v j)) - lam0 * (s i * (v i * v i)) := by
    let g : Fin n → Q := fun j => if i = j then lam0 * (s i * (v i * v i)) else 0
    have hdiff : sumFin (fun j => v i * ((if i = j then C i j - lam0 * s i else C i j) * v j)) ≈
                 sumFin (fun j => v i * (C i j * v j) - g j) := by
      apply sumFin_congr; intro j
      by_cases hij : i = j
      · subst hij
        simp only [g, ↓reduceIte]
        have e1 := mul_congr (eqv_refl (v i)) (add_mul (C i i) (-(lam0 * s i)) (v i))
        have e2 := mul_add (v i) (C i i * v i) ((-(lam0 * s i)) * v i)
        have e3 : v i * ((-(lam0 * s i)) * v i) ≈ -(lam0 * (s i * (v i * v i))) := by
          have p1 : (-(lam0 * s i)) * v i ≈ -((lam0 * s i) * v i) := neg_mul (lam0 * s i) (v i)
          have p2 := mul_neg (v i) ((lam0 * s i) * v i)
          have p3 : v i * ((lam0 * s i) * v i) ≈ lam0 * (s i * (v i * v i)) := by
            have a1 := eqv_symm (mul_assoc (v i) (lam0 * s i) (v i))
            have a2 := mul_congr (mul_comm (v i) (lam0 * s i)) (eqv_refl (v i))
            have a3 := mul_assoc (lam0 * s i) (v i) (v i)
            have a4 := mul_assoc lam0 (s i) (v i * v i)
            exact eqv_trans (eqv_trans (eqv_trans a1 a2) a3) a4
          exact eqv_trans (mul_congr (eqv_refl (v i)) p1) (eqv_trans p2 (neg_congr p3))
        exact eqv_trans (eqv_trans e1 e2) (add_congr (eqv_refl _) e3)
      · simp only [g, hij, ↓reduceIte]
        have hzero : v i * (C i j * v j) - 0 ≈ v i * (C i j * v j) := by
          have hn0 : -(0 : Q) ≈ 0 := by
            change (-(0 : Int)) * (1 : Int) = (0 : Int) * (1 : Int)
            omega
          exact eqv_trans (add_congr (eqv_refl _) hn0) (add_zero _)
        exact eqv_symm hzero
    have hsub := sumFin_sub (fun j => v i * (C i j * v j)) g
    have hg : sumFin g ≈ lam0 * (s i * (v i * v i)) := by
      have hsingle := sumFin_single_nonzero g i (fun j hji => by
        have hneq : ¬ (i = j) := Ne.symm hji
        simp only [g, hneq, ↓reduceIte]
        exact eqv_refl 0)
      simp only [g, ↓reduceIte] at hsingle
      exact hsingle
    exact eqv_trans (eqv_trans hdiff hsub) (sub_congr (eqv_refl _) hg)
  have houter := eqv_trans (sumFin_congr hinner)
    (sumFin_sub (fun i => sumFin (fun j => v i * (C i j * v j))) (fun i => lam0 * (s i * (v i * v i))))
  exact eqv_trans houter (sub_congr (eqv_refl _) (eqv_symm (mul_sumFin lam0 (fun i => s i * (v i * v i)))))

/-- 정리 4e (SO(3)-불변 Mandel/Kelvin 고유값 하한의 순수 유리수 LDL^T 인증):
    s = (1,1,1,1/2,1/2,1/2) 일 때 C_Voigt - λ_0 diag(s) = L diag(d) L^T (d_k > 0) 이면,
    모든 비영 변형률 벡터 v ≠ 0 에 대해 v^T C_Voigt v > λ_0 ‖v‖_s^2 (= λ_0 ‖D⁻¹ v‖_2^2) 가 성립하여
    무리수 √2 없이도 Mandel 텐서 고유값 하한 λ_min(C_Mandel) > λ_0 를 100% 유리수로 인증한다. -/
theorem weighted_eigenvalue_lower_bound_of_shifted_ldlt {n : Nat} {C L : Mat n} {d s : Vec n} {lam0 : Q}
    (hcert : LDLTCert (weightedShiftMat C lam0 s) L d) :
    ∀ v : Vec n, NonZeroVec v → lam0 * weightedNormSq s v <q quadForm C v := by
  intro v hne
  have hpos : (0 : Q) <q quadForm (weightedShiftMat C lam0 s) v := born_pd_of_ldlt hcert v hne
  have hpos2 : (0 : Q) <q quadForm C v - lam0 * weightedNormSq s v :=
    lt_of_lt_of_le hpos (le_of_eqv (quadForm_weightedShift C lam0 s v))
  exact (sub_pos_iff (quadForm C v) (lam0 * weightedNormSq s v)).mp hpos2

/-- 대각 가중 프로베니우스 노름 제곱: ∑_{i,j} (r_i r_j) dC_{ij}^2
    (Mandel 좌표에서 r = (1,1,1,2,2,2) 일 때 정확히 ‖D ΔC D‖_F^2 = ‖ΔC_Mandel‖_F^2 와 항등 일치하며 무리수 √2 불필요) -/
def weightedFrobSq {n : Nat} (r : Vec n) (dC : Mat n) : Q :=
  sumFin (fun i => sumFin (fun j => (r i * r j) * (dC i j * dC i j)))

/-- 가중 Rayleigh/Mandel 스펙트럼 하계 술어: ∀ v, -(δ ‖v‖_s^2) ≤ v^T ΔC v -/
def IsWeightedRayleighBounded {n : Nat} (s : Vec n) (dC : Mat n) (delta : Q) : Prop :=
  ∀ v : Vec n, -(delta * weightedNormSq s v) ≤q quadForm dC v

/-- 정리 4e-2 (가중 프로베니우스 노름 상계 → 가중 Weyl Rayleigh 하계, 순수 유리수 가중 코시-슈바르츠 증명):
    s_i ≥ 0, r_i ≥ 0, s_i * r_i ≈ 1 이고 ‖ΔC‖_{F,r}^2 ≤ δ^2 (δ ≥ 0) 이면
    모든 벡터 v 에 대해 -(δ ‖v‖_s^2) ≤ v^T ΔC v 가 성립한다. -/
theorem weighted_frobenius_implies_weyl_bound {n : Nat} {s r : Vec n} {dC : Mat n} {delta : Q}
    (hs : ∀ i, (0 : Q) ≤q s i)
    (hr : ∀ i, (0 : Q) ≤q r i)
    (hsr : ∀ i, s i * r i ≈ 1)
    (hdelta : (0 : Q) ≤q delta)
    (hfrob : weightedFrobSq r dC ≤q delta * delta) :
    IsWeightedRayleighBounded s dC delta := by
  intro v
  let qv := quadForm dC v
  let wns := weightedNormSq s v
  let u : Vec n := fun i => sumFin (fun j => dC i j * v j)
  have hcancel (i : Fin n) (x : Q) : s i * (r i * x) ≈ x :=
    eqv_trans (eqv_symm (mul_assoc (s i) (r i) x))
      (eqv_trans (mul_congr (hsr i) (eqv_refl x)) (one_mul x))
  -- 1) qv ≈ ∑_i s_i * (v_i * (r_i * u_i))
  have hqv_eq : qv ≈ sumFin (fun i => s i * (v i * (r i * u i))) := by
    have h1 : qv ≈ sumFin (fun i => v i * u i) :=
      sumFin_congr (fun i => eqv_symm (mul_sumFin (v i) (fun j => dC i j * v j)))
    have h2 : sumFin (fun i => v i * u i) ≈ sumFin (fun i => s i * (v i * (r i * u i))) := by
      apply sumFin_congr; intro i
      have e1 : s i * (v i * (r i * u i)) ≈ (s i * r i) * (v i * u i) := by
        have p1 : v i * (r i * u i) ≈ r i * (v i * u i) :=
          eqv_trans (eqv_symm (mul_assoc (v i) (r i) (u i)))
            (eqv_trans (mul_congr (mul_comm (v i) (r i)) (eqv_refl (u i))) (mul_assoc (r i) (v i) (u i)))
        exact eqv_trans (mul_congr (eqv_refl (s i)) p1) (eqv_symm (mul_assoc (s i) (r i) (v i * u i)))
      have e2 : (s i * r i) * (v i * u i) ≈ v i * u i :=
        eqv_trans (mul_congr (hsr i) (eqv_refl (v i * u i))) (one_mul (v i * u i))
      exact eqv_symm (eqv_trans e1 e2)
    exact eqv_trans h1 h2
  -- 2) 외부 가중 코시-슈바르츠: qv^2 ≤ wns * ∑_i s_i * (r_i * u_i)^2 ≈ wns * ∑_i r_i * u_i^2
  have hcs1 := weighted_cauchy_schwarz s v (fun i => r i * u i) hs
  have hsr_sq (i : Fin n) (x : Q) : s i * ((r i * x) * (r i * x)) ≈ r i * (x * x) := by
    have p1 : (r i * x) * (r i * x) ≈ r i * (r i * (x * x)) := by
      have q1 := mul_assoc (r i) x (r i * x)
      have q2 : x * (r i * x) ≈ r i * (x * x) :=
        eqv_trans (eqv_symm (mul_assoc x (r i) x))
          (eqv_trans (mul_congr (mul_comm x (r i)) (eqv_refl x)) (mul_assoc (r i) x x))
      exact eqv_trans q1 (mul_congr (eqv_refl (r i)) q2)
    exact eqv_trans (mul_congr (eqv_refl (s i)) p1) (hcancel i (r i * (x * x)))
  have hsum_ru : sumFin (fun i => s i * ((r i * u i) * (r i * u i))) ≈
                 sumFin (fun i => r i * (u i * u i)) :=
    sumFin_congr (fun i => hsr_sq i (u i))
  -- 3) 행별 가중 코시-슈바르츠: u_i^2 ≤ (∑_j r_j dC_ij^2) * wns
  have hrow_cs (i : Fin n) :
      u i * u i ≤q sumFin (fun j => r j * (dC i j * dC i j)) * wns := by
    have hu_eq : u i ≈ sumFin (fun j => s j * ((r j * dC i j) * v j)) := by
      apply sumFin_congr; intro j
      have e1 : s j * ((r j * dC i j) * v j) ≈ (s j * (r j * dC i j)) * v j :=
        eqv_symm (mul_assoc (s j) (r j * dC i j) (v j))
      have e2 : (s j * (r j * dC i j)) * v j ≈ dC i j * v j :=
        mul_congr (hcancel j (dC i j)) (eqv_refl (v j))
      exact eqv_symm (eqv_trans e1 e2)
    have hcs_r := weighted_cauchy_schwarz s (fun j => r j * dC i j) v hs
    have hcoef : sumFin (fun j => s j * ((r j * dC i j) * (r j * dC i j))) ≈
                 sumFin (fun j => r j * (dC i j * dC i j)) :=
      sumFin_congr (fun j => hsr_sq j (dC i j))
    exact le_trans (le_of_eqv (mul_congr hu_eq hu_eq))
      (le_trans hcs_r (le_of_eqv (mul_congr hcoef (eqv_refl wns))))
  -- 4) 가중합 ∑_i r_i u_i^2 ≤ weightedFrobSq r dC * wns
  have hcs2 : sumFin (fun i => r i * (u i * u i)) ≤q weightedFrobSq r dC * wns := by
    have hrow_r (i : Fin n) :
        r i * (u i * u i) ≤q sumFin (fun j => (r i * r j) * (dC i j * dC i j)) * wns := by
      have p1 := mul_le_mul_of_nonneg_left (hr i) (hrow_cs i)
      have p2 : r i * (sumFin (fun j => r j * (dC i j * dC i j)) * wns) ≈
                (r i * sumFin (fun j => r j * (dC i j * dC i j))) * wns :=
        eqv_symm (mul_assoc (r i) _ wns)
      have p3 : r i * sumFin (fun j => r j * (dC i j * dC i j)) ≈
                sumFin (fun j => (r i * r j) * (dC i j * dC i j)) :=
        eqv_trans (mul_sumFin (r i) (fun j => r j * (dC i j * dC i j)))
          (sumFin_congr (fun j => eqv_symm (mul_assoc (r i) (r j) (dC i j * dC i j))))
      exact le_trans p1 (le_of_eqv (eqv_trans p2 (mul_congr p3 (eqv_refl wns))))
    have hsum := sumFin_le_sumFin hrow_r
    have hfac : sumFin (fun i => sumFin (fun j => (r i * r j) * (dC i j * dC i j)) * wns) ≈
                weightedFrobSq r dC * wns :=
      eqv_symm (sumFin_mul (fun i => sumFin (fun j => (r i * r j) * (dC i j * dC i j))) wns)
    exact le_trans hsum (le_of_eqv hfac)
  -- 5) 최종 결합: qv^2 ≤ (delta * wns)^2 → -(delta * wns) ≤ qv
  have hwns_nn : (0 : Q) ≤q wns := sumFin_nonneg (fun i => mul_nonneg (hs i) (sq_nonneg (v i)))
  have hqv_sq : qv * qv ≤q (delta * wns) * (delta * wns) := by
    have p1 : qv * qv ≈
        sumFin (fun i => s i * (v i * (r i * u i))) * sumFin (fun i => s i * (v i * (r i * u i))) :=
      mul_congr hqv_eq hqv_eq
    have p2 : wns * sumFin (fun i => s i * ((r i * u i) * (r i * u i))) ≤q
              wns * (weightedFrobSq r dC * wns) :=
      le_trans (le_of_eqv (mul_congr (eqv_refl wns) hsum_ru))
        (mul_le_mul_of_nonneg_left hwns_nn hcs2)
    have p3 : wns * (weightedFrobSq r dC * wns) ≈ weightedFrobSq r dC * (wns * wns) :=
      eqv_trans (eqv_symm (mul_assoc wns (weightedFrobSq r dC) wns))
        (eqv_trans (mul_congr (mul_comm wns (weightedFrobSq r dC)) (eqv_refl wns))
                   (mul_assoc (weightedFrobSq r dC) wns wns))
    have p4 : weightedFrobSq r dC * (wns * wns) ≤q (delta * delta) * (wns * wns) := by
      have hnn := mul_nonneg hwns_nn hwns_nn
      have q := mul_le_mul_of_nonneg_left hnn hfrob
      exact le_trans (le_of_eqv (mul_comm (weightedFrobSq r dC) (wns * wns)))
        (le_trans q (le_of_eqv (mul_comm (wns * wns) (delta * delta))))
    have p5 : (delta * delta) * (wns * wns) ≈ (delta * wns) * (delta * wns) := by
      have e1 := mul_assoc delta delta (wns * wns)
      have e2 : delta * (wns * wns) ≈ wns * (delta * wns) :=
        eqv_trans (eqv_symm (mul_assoc delta wns wns))
          (eqv_trans (mul_congr (mul_comm delta wns) (eqv_refl wns)) (mul_assoc wns delta wns))
      exact eqv_trans (eqv_trans e1 (mul_congr (eqv_refl delta) e2))
        (eqv_symm (mul_assoc delta wns (delta * wns)))
    exact le_trans (le_of_eqv p1)
      (le_trans hcs1 (le_trans p2 (le_trans (le_of_eqv p3) (le_trans p4 (le_of_eqv p5)))))
  exact neg_le_of_sq_le_sq (mul_nonneg hdelta hwns_nn) hqv_sq

/-- 정리 4e-3 (가중 Rayleigh/Mandel 섭동 하 강건 Born 안정성 최종 정리):
    가중 이동 LDL^T 로 v^T C v > λ_0 ‖v‖_s^2 를 인증하고 -(δ ‖v‖_s^2) ≤ v^T ΔC v 및 δ ≤ λ_0 이면
    섭동된 텐서 C + ΔC 는 무조건 Born 양정치이다. -/
theorem weighted_shifted_ldlt_rayleigh_robust_born {n : Nat} {C dC L : Mat n} {d s : Vec n} {lam0 delta : Q}
    (hs : ∀ i, (0 : Q) ≤q s i)
    (hcert : LDLTCert (weightedShiftMat C lam0 s) L d)
    (hpert : IsWeightedRayleighBounded s dC delta)
    (hmargin : delta ≤q lam0) :
    IsBornPD (addMat C dC) := by
  intro v hne
  have hwns : (0 : Q) ≤q weightedNormSq s v :=
    sumFin_nonneg (fun i => mul_nonneg (hs i) (sq_nonneg (v i)))
  have h1 : delta * weightedNormSq s v ≤q lam0 * weightedNormSq s v := by
    have p := mul_le_mul_of_nonneg_left hwns hmargin
    exact le_trans (le_of_eqv (mul_comm delta (weightedNormSq s v)))
      (le_trans p (le_of_eqv (mul_comm (weightedNormSq s v) lam0)))
  have h2 : delta * weightedNormSq s v <q quadForm C v :=
    lt_of_le_of_lt h1 (weighted_eigenvalue_lower_bound_of_shifted_ldlt hcert v hne)
  have hsum : delta * weightedNormSq s v + -(delta * weightedNormSq s v) <q
              quadForm C v + quadForm dC v := by
    have hadd := add_lt_add_of_le_of_lt (hpert v) h2
    have hl : -(delta * weightedNormSq s v) + delta * weightedNormSq s v ≈
              delta * weightedNormSq s v + -(delta * weightedNormSq s v) := add_comm _ _
    have hr : quadForm dC v + quadForm C v ≈ quadForm C v + quadForm dC v := add_comm _ _
    exact lt_of_le_of_lt (le_of_eqv (eqv_symm hl)) (lt_of_lt_of_le hadd (le_of_eqv hr))
  have h0 : (0 : Q) ≈ delta * weightedNormSq s v + -(delta * weightedNormSq s v) :=
    eqv_symm (sub_self (delta * weightedNormSq s v))
  have hpos : (0 : Q) <q quadForm C v + quadForm dC v := lt_of_le_of_lt (le_of_eqv h0) hsum
  exact lt_of_lt_of_le hpos (le_of_eqv (eqv_symm (quadForm_add C dC v)))

/-- 정리 4e-4 (SO(3)-불변 Mandel 프로베니우스 섭동 하 강건 Born 안정성 최종 정리):
    가중 이동 LDL^T 로 λ_min(C_Mandel) > λ_0 를 인증하고 ‖ΔC_Mandel‖_F^2 = weightedFrobSq r ΔC ≤ δ^2 (0 ≤ δ ≤ λ_0) 이면
    섭동된 텐서 C + ΔC 는 무조건 Born 양정치이다. -/
theorem weighted_shifted_ldlt_frob_robust_born {n : Nat} {C dC L : Mat n} {d s r : Vec n} {lam0 delta : Q}
    (hs : ∀ i, (0 : Q) ≤q s i)
    (hr : ∀ i, (0 : Q) ≤q r i)
    (hsr : ∀ i, s i * r i ≈ 1)
    (hcert : LDLTCert (weightedShiftMat C lam0 s) L d)
    (hdelta : (0 : Q) ≤q delta)
    (hfrob : weightedFrobSq r dC ≤q delta * delta)
    (hmargin : delta ≤q lam0) :
    IsBornPD (addMat C dC) :=
  weighted_shifted_ldlt_rayleigh_robust_born hs hcert
    (weighted_frobenius_implies_weyl_bound hs hr hsr hdelta hfrob)
    hmargin

/-- 보조정리 9: 양의 대각 가중치 s_i > 0 과 비영 벡터 v 에 대해 가중 노름 제곱 ‖v‖_s^2 > 0 -/
theorem weightedNormSq_pos {n : Nat} {s v : Vec n}
    (hs_pos : ∀ i, (0 : Q) <q s i) (hne : NonZeroVec v) :
    (0 : Q) <q weightedNormSq s v := by
  rcases hne with ⟨k, hk⟩
  exact sumFin_pos_of_exists_pos
    (fun i => mul_nonneg (le_of_lt (hs_pos i)) (sq_nonneg (v i)))
    k
    (mul_pos (hs_pos k) (sq_pos_of_ne_zero hk))

/-- 정리 4e-5 (SO(3)-불변 가중/Mandel 기계적 취약성 구성적 반례 섭동 정리, 무리수 √2 불필요):
    s_i > 0, s_i * r_i ≈ 1 이고 비영 변형률 벡터 v ≠ 0 가 v^T C v ≤ δ ‖v‖_s^2 를 만족하면,
    명시적 대칭 랭크-1 유리수 섭동 ΔC_ij = -(δ / ‖v‖_s^2) (s_i v_i)(s_j v_j) 는
    1) 대칭 행렬이며 (ΔC_ij ≈ ΔC_ji),
    2) 정확히 가중 프로베니우스 노름 ‖ΔC‖_{F,r}^2 ≈ δ^2 (= ‖D ΔC D‖_F^2) 을 가지며,
    3) C + ΔC 가 Born 비양정치(v^T (C + ΔC) v ≤ 0)임을 순수 유리수로 구성 증명한다. -/
theorem weighted_weyl_fragile_of_witness {n : Nat} {C : Mat n} {s r v : Vec n} {delta : Q}
    (hs_pos : ∀ i, (0 : Q) <q s i)
    (hsr : ∀ i, s i * r i ≈ 1)
    (hne : NonZeroVec v)
    (hweak : quadForm C v ≤q delta * weightedNormSq s v) :
    ∃ dC : Mat n,
      IsSymmetricMat dC ∧
      weightedFrobSq r dC ≈ delta * delta ∧
      ¬ IsBornPD (addMat C dC) := by
  have hwns_pos : (0 : Q) <q weightedNormSq s v := weightedNormSq_pos hs_pos hne
  let wns : Q := weightedNormSq s v
  let invWns : Q := invPos wns hwns_pos
  let alpha : Q := -(delta * invWns)
  let dC : Mat n := fun i j => alpha * ((s i * v i) * (s j * v j))
  have hmul4 (a b c d : Q) : (a * b) * (c * d) ≈ (a * c) * (b * d) := by
    have q1 := mul_assoc a b (c * d)
    have q2 : b * (c * d) ≈ c * (b * d) :=
      eqv_trans (eqv_symm (mul_assoc b c d))
        (eqv_trans (mul_congr (mul_comm b c) (eqv_refl d)) (mul_assoc c b d))
    exact eqv_trans (eqv_trans q1 (mul_congr (eqv_refl a) q2)) (eqv_symm (mul_assoc a c (b * d)))
  have hcancel_rs (i : Fin n) : r i * ((s i * v i) * (s i * v i)) ≈ s i * (v i * v i) := by
    have p1 : (s i * v i) * (s i * v i) ≈ (s i * s i) * (v i * v i) := hmul4 (s i) (v i) (s i) (v i)
    have p2 : r i * ((s i * s i) * (v i * v i)) ≈ ((r i * s i) * s i) * (v i * v i) :=
      eqv_trans (eqv_symm (mul_assoc (r i) (s i * s i) (v i * v i)))
        (mul_congr (eqv_symm (mul_assoc (r i) (s i) (s i))) (eqv_refl (v i * v i)))
    have p3 : (r i * s i) * s i ≈ s i :=
      eqv_trans (mul_congr (eqv_trans (mul_comm (r i) (s i)) (hsr i)) (eqv_refl (s i))) (one_mul (s i))
    exact eqv_trans (mul_congr (eqv_refl (r i)) p1)
      (eqv_trans p2 (mul_congr p3 (eqv_refl (v i * v i))))
  have hcancel_pair : (delta * invWns) * wns ≈ delta :=
    eqv_trans (mul_assoc delta invWns wns)
      (eqv_trans (mul_congr (eqv_refl delta) (invPos_mul_cancel wns hwns_pos)) (mul_one delta))
  refine ⟨dC, ?_, ?_, ?_⟩
  · -- 1) 대칭성
    intro i j
    exact mul_congr (eqv_refl alpha) (mul_comm (s i * v i) (s j * v j))
  · -- 2) 가중 프로베니우스 노름 제곱: ∑_{i,j} (r_i r_j) dC_{ij}^2 ≈ alpha^2 * wns^2 ≈ delta^2
    unfold weightedFrobSq
    have hterm (i j : Fin n) :
        (r i * r j) * (dC i j * dC i j) ≈
        (alpha * alpha) * ((s i * (v i * v i)) * (s j * (v j * v j))) := by
      have t1 : dC i j * dC i j ≈
                (alpha * alpha) * (((s i * v i) * (s i * v i)) * ((s j * v j) * (s j * v j))) := by
        have q1 := hmul4 alpha ((s i * v i) * (s j * v j)) alpha ((s i * v i) * (s j * v j))
        have q2 := hmul4 (s i * v i) (s j * v j) (s i * v i) (s j * v j)
        exact eqv_trans q1 (mul_congr (eqv_refl (alpha * alpha)) q2)
      have t2 : (r i * r j) * ((alpha * alpha) * (((s i * v i) * (s i * v i)) * ((s j * v j) * (s j * v j)))) ≈
                (alpha * alpha) * ((r i * r j) * (((s i * v i) * (s i * v i)) * ((s j * v j) * (s j * v j)))) :=
        eqv_trans (eqv_symm (mul_assoc (r i * r j) (alpha * alpha) _))
          (eqv_trans (mul_congr (mul_comm (r i * r j) (alpha * alpha)) (eqv_refl _))
                     (mul_assoc (alpha * alpha) (r i * r j) _))
      have t3 : (r i * r j) * (((s i * v i) * (s i * v i)) * ((s j * v j) * (s j * v j))) ≈
                (s i * (v i * v i)) * (s j * (v j * v j)) :=
        eqv_trans (hmul4 (r i) (r j) ((s i * v i) * (s i * v i)) ((s j * v j) * (s j * v j)))
          (mul_congr (hcancel_rs i) (hcancel_rs j))
      exact eqv_trans (mul_congr (eqv_refl (r i * r j)) t1)
        (eqv_trans t2 (mul_congr (eqv_refl (alpha * alpha)) t3))
    have hsum1 := sumFin_congr (fun i => sumFin_congr (fun j => hterm i j))
    have hsum2 :
        sumFin (fun i => sumFin (fun j => (alpha * alpha) * ((s i * (v i * v i)) * (s j * (v j * v j))))) ≈
        (alpha * alpha) * (wns * wns) := by
      have f1 := sumFin_congr (fun i =>
        eqv_symm (mul_sumFin (alpha * alpha) (fun j => (s i * (v i * v i)) * (s j * (v j * v j)))))
      have f2 := eqv_symm (mul_sumFin (alpha * alpha)
        (fun i => sumFin (fun j => (s i * (v i * v i)) * (s j * (v j * v j)))))
      have f3 : sumFin (fun i => sumFin (fun j => (s i * (v i * v i)) * (s j * (v j * v j)))) ≈
                wns * wns := by
        have g1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (s i * (v i * v i)) (fun j => s j * (v j * v j))))
        exact eqv_trans g1 (eqv_symm (sumFin_mul (fun i => s i * (v i * v i)) wns))
      exact eqv_trans (eqv_trans f1 f2) (mul_congr (eqv_refl (alpha * alpha)) f3)
    have halpha_sq : alpha * alpha ≈ (delta * invWns) * (delta * invWns) :=
      neg_mul_neg (delta * invWns) (delta * invWns)
    have hfinal : ((delta * invWns) * (delta * invWns)) * (wns * wns) ≈ delta * delta :=
      eqv_trans (hmul4 (delta * invWns) (delta * invWns) wns wns) (mul_congr hcancel_pair hcancel_pair)
    exact eqv_trans (eqv_trans hsum1 hsum2) (eqv_trans (mul_congr halpha_sq (eqv_refl _)) hfinal)
  · -- 3) 이차 형식 비양수: v^T (C + dC) v ≈ v^T C v - delta * ‖v‖_s^2 ≤ 0
    have hqdC : quadForm dC v ≈ -(delta * wns) := by
      unfold quadForm
      have ht (i j : Fin n) :
          v i * (dC i j * v j) ≈ alpha * ((s i * (v i * v i)) * (s j * (v j * v j))) := by
        have e1 : (alpha * ((s i * v i) * (s j * v j))) * v j ≈
                  alpha * ((s i * v i) * (s j * (v j * v j))) :=
          eqv_trans (mul_assoc alpha ((s i * v i) * (s j * v j)) (v j))
            (mul_congr (eqv_refl alpha)
              (eqv_trans (mul_assoc (s i * v i) (s j * v j) (v j))
                (mul_congr (eqv_refl (s i * v i)) (mul_assoc (s j) (v j) (v j)))))
        have e2 : v i * (alpha * ((s i * v i) * (s j * (v j * v j)))) ≈
                  alpha * ((v i * (s i * v i)) * (s j * (v j * v j))) :=
          eqv_trans (eqv_symm (mul_assoc (v i) alpha _))
            (eqv_trans (mul_congr (mul_comm (v i) alpha) (eqv_refl _))
              (eqv_trans (mul_assoc alpha (v i) _)
                (mul_congr (eqv_refl alpha) (eqv_symm (mul_assoc (v i) (s i * v i) _)))))
        have e3 : v i * (s i * v i) ≈ s i * (v i * v i) :=
          eqv_trans (eqv_symm (mul_assoc (v i) (s i) (v i)))
            (eqv_trans (mul_congr (mul_comm (v i) (s i)) (eqv_refl (v i))) (mul_assoc (s i) (v i) (v i)))
        exact eqv_trans (mul_congr (eqv_refl (v i)) e1)
          (eqv_trans e2 (mul_congr (eqv_refl alpha) (mul_congr e3 (eqv_refl _))))
      have s1 := sumFin_congr (fun i => sumFin_congr (fun j => ht i j))
      have s2 : sumFin (fun i => sumFin (fun j => alpha * ((s i * (v i * v i)) * (s j * (v j * v j))))) ≈
                alpha * (wns * wns) := by
        have f1 := sumFin_congr (fun i =>
          eqv_symm (mul_sumFin alpha (fun j => (s i * (v i * v i)) * (s j * (v j * v j)))))
        have f2 := eqv_symm (mul_sumFin alpha
          (fun i => sumFin (fun j => (s i * (v i * v i)) * (s j * (v j * v j)))))
        have f3 : sumFin (fun i => sumFin (fun j => (s i * (v i * v i)) * (s j * (v j * v j)))) ≈
                  wns * wns := by
          have g1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (s i * (v i * v i)) (fun j => s j * (v j * v j))))
          exact eqv_trans g1 (eqv_symm (sumFin_mul (fun i => s i * (v i * v i)) wns))
        exact eqv_trans (eqv_trans f1 f2) (mul_congr (eqv_refl alpha) f3)
      have s3 : alpha * (wns * wns) ≈ -(delta * wns) :=
        eqv_trans (neg_mul (delta * invWns) (wns * wns))
          (neg_congr (eqv_trans (eqv_symm (mul_assoc (delta * invWns) wns wns))
            (mul_congr hcancel_pair (eqv_refl wns))))
      exact eqv_trans (eqv_trans s1 s2) s3
    have hqadd : quadForm (addMat C dC) v ≈ quadForm C v - delta * wns :=
      eqv_trans (quadForm_add C dC v) (add_congr (eqv_refl (quadForm C v)) hqdC)
    have hle0 : quadForm (addMat C dC) v ≤q 0 := by
      have hdiff_le : quadForm C v - delta * wns ≤q 0 :=
        le_trans (add_le_add hweak (le_refl (-(delta * wns)))) (le_of_eqv (sub_self (delta * wns)))
      exact le_trans (le_of_eqv hqadd) hdiff_le
    exact not_born_pd_of_witness hne hle0

end CertMat
