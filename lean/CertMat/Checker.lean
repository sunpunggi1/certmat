/-
  CertMat/Checker.lean
  실행 가능한 결정 가능(Decidable) 증명서 검증 함수들과 각각의 건전성(Soundness) 정리.
  checkX cert = true 가 반환되면 앞서 증명한 4대 정리(Farkas, RefErrorCancel, IntervalHull, BornElastic)에 의해
  수학적 안전성이 기계적으로 보장된다.
-/

import CertMat.ExactRat
import CertMat.Farkas
import CertMat.RefErrorCancel
import CertMat.IntervalHull
import CertMat.BornElastic

namespace CertMat

open Q

/-- Fin n 위의 전칭 불리언 검사: ∀ i : Fin n, p i = true -/
def allFin : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, p => allFin (fun i : Fin n => p i.castSucc) && p (Fin.last n)

theorem allFin_iff {n : Nat} (p : Fin n → Bool) :
    allFin p = true ↔ ∀ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro _ i; exact Fin.elim0 i
    · intro _; rfl
  | succ n ih =>
    unfold allFin
    rw [Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hprev, hlast⟩ i
      refine Fin.lastCases hlast hprev i
    · intro hall
      exact ⟨fun i => hall i.castSucc, hall (Fin.last n)⟩

/-- Fin n 위의 존재 불리언 검사: ∃ i : Fin n, p i = true -/
def anyFin : {n : Nat} → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, p => anyFin (fun i : Fin n => p i.castSucc) || p (Fin.last n)

theorem anyFin_iff {n : Nat} (p : Fin n → Bool) :
    anyFin p = true ↔ ∃ i : Fin n, p i = true := by
  induction n with
  | zero =>
    constructor
    · intro h; cases h
    · rintro ⟨i, _⟩; exact Fin.elim0 i
  | succ n ih =>
    unfold anyFin
    rw [Bool.or_eq_true, ih]
    constructor
    · rintro (⟨j, hj⟩ | hlast)
      · exact ⟨j.castSucc, hj⟩
      · exact ⟨Fin.last n, hlast⟩
    · rintro ⟨i, hi⟩
      refine Fin.lastCases ?_ ?_ i hi
      · intro h; exact Or.inr h
      · intro j hj; exact Or.inl ⟨j, hj⟩

/-! ### 1. 조성 정규화 및 Farkas 쌍대/원시 증명서 체커 및 건전성 -/

/-- 비퇴화·정규화 조성 조건: m > 0, E > 0, 모든 조성 비음 및 합 = 1 -/
structure NormalizedComps {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q) : Prop where
  m_pos : 0 < m
  E_pos : 0 < E
  c_nonneg : ∀ i e, (0 : Q) ≤q c i e
  cx_nonneg : ∀ e, (0 : Q) ≤q cx e
  c_sum_one : ∀ i, sumFin (fun e => c i e) ≈ 1
  cx_sum_one : sumFin (fun e => cx e) ≈ 1

def checkNormalizedComps {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q) : Bool :=
  decide (0 < m) &&
  decide (0 < E) &&
  allFin (fun i => allFin (fun e => ble 0 (c i e))) &&
  allFin (fun e => ble 0 (cx e)) &&
  allFin (fun i => beq (sumFin (fun e => c i e)) 1) &&
  beq (sumFin (fun e => cx e)) 1

theorem checkNormalizedComps_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    (h : checkNormalizedComps c cx = true) : NormalizedComps c cx := by
  unfold checkNormalizedComps at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hm, hE⟩, hcnn⟩, hcxnn⟩, hcsum⟩, hcxsum⟩
  rw [allFin_iff] at hcnn hcxnn hcsum
  exact {
    m_pos := decide_eq_true_iff.mp hm
    E_pos := decide_eq_true_iff.mp hE
    c_nonneg := fun i e => (ble_iff _ _).mp ((allFin_iff _).mp (hcnn i) e)
    cx_nonneg := fun e => (ble_iff _ _).mp (hcxnn e)
    c_sum_one := fun i => (beq_iff _ _).mp (hcsum i)
    cx_sum_one := (beq_iff _ _).mp hcxsum
  }

/-- 쌍대 안정성 증명서 검증기 (음수 여유 δ < 0 엄격 차단: 반드시 δ ≥ 0 요구) -/
def checkDualStable {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex delta : Q) (mu : Fin E → Q) : Bool :=
  ble 0 delta && allFin (fun i => ble (dot mu (c i)) (en i)) && ble (ex + delta) (dot mu cx)

theorem checkDualStable_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {mu : Fin E → Q}
    (h : checkDualStable c cx en ex delta mu = true) :
    (0 : Q) ≤q delta ∧ DualStableCert c cx en ex delta mu := by
  unfold checkDualStable at h
  rw [Bool.and_eq_true, Bool.and_eq_true, allFin_iff] at h
  rcases h with ⟨⟨hdelta, hhyp⟩, hcand⟩
  exact ⟨(ble_iff _ _).mp hdelta, ⟨fun i => (ble_iff _ _).mp (hhyp i), (ble_iff _ _).mp hcand⟩⟩

/-- 따름정리: `checkDualStable = true` 이면 δ ≥ 0 이므로 후보상은 모든 유효 분해 λ 에 대해 E_x ≤ ∑ λ_i E_i (무조건 안정) -/
theorem checkDualStable_on_hull_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex delta : Q} {mu : Fin E → Q}
    (h : checkDualStable c cx en ex delta mu = true) :
    ∀ lam, ValidDecomp c cx lam → ex ≤q sumFin (fun i => lam i * en i) := by
  rcases checkDualStable_sound h with ⟨hdelta, hcert⟩
  intro lam hlam
  have hge := farkas_dual_stable_sound hcert lam hlam
  have hex_le : ex ≤q ex + delta :=
    le_trans (le_of_eqv (eqv_symm (add_zero ex))) (add_le_add (le_refl ex) hdelta)
  exact le_trans hex_le hge

/-- 유효 분해 검증기 -/
def checkValidDecomp {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (lam : Fin m → Q) : Bool :=
  allFin (fun i => ble 0 (lam i)) &&
  allFin (fun e => beq (sumFin (fun i => lam i * c i e)) (cx e))

theorem checkValidDecomp_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {lam : Fin m → Q} (h : checkValidDecomp c cx lam = true) :
    ValidDecomp c cx lam := by
  unfold checkValidDecomp at h
  rw [Bool.and_eq_true, allFin_iff, allFin_iff] at h
  rcases h with ⟨hnn, hcons⟩
  exact ⟨fun i => (ble_iff _ _).mp (hnn i), fun e => (beq_iff _ _).mp (hcons e)⟩

/-- 원시 불안정성 증명서 검증기 -/
def checkPrimalUnstable {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (lam : Fin m → Q) : Bool :=
  checkValidDecomp c cx lam && blt (sumFin (fun i => lam i * en i)) ex

theorem checkPrimalUnstable_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {lam : Fin m → Q}
    (h : checkPrimalUnstable c cx en ex lam = true) :
    PrimalUnstableCert c cx en ex lam := by
  unfold checkPrimalUnstable at h
  rw [Bool.and_eq_true] at h
  exact ⟨checkValidDecomp_sound h.1, (blt_iff _ _).mp h.2⟩

/-! ### 2. 구간 불확실성 강건 안정성/불안정성 체커 및 건전성 -/

/-- 구간 강건 안정성 체커 (최악 극점 U_x vs L_i) -/
def checkIntervalStable {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (L : Fin m → Q) (Ux delta : Q) (mu : Fin E → Q) : Bool :=
  checkDualStable c cx L Ux delta mu

theorem checkIntervalStable_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {L U : Fin m → Q} {Lx Ux delta : Q} {mu : Fin E → Q}
    (h : checkIntervalStable c cx L Ux delta mu = true) :
    (0 : Q) ≤q delta ∧
    (∀ enTrue exTrue, InEnergyBox L U Lx Ux enTrue exTrue →
      ∀ lam, ValidDecomp c cx lam →
        exTrue + delta ≤q sumFin (fun i => lam i * enTrue i) ∧
        exTrue ≤q sumFin (fun i => lam i * enTrue i)) := by
  rcases checkDualStable_sound h with ⟨hdelta, hcert⟩
  refine ⟨hdelta, ?_⟩
  intro enTrue exTrue hbox lam hlam
  have hge := interval_robust_stable_universal hcert enTrue exTrue hbox lam hlam
  have hex_le : exTrue ≤q exTrue + delta :=
    le_trans (le_of_eqv (eqv_symm (add_zero exTrue))) (add_le_add (le_refl exTrue) hdelta)
  exact ⟨hge, le_trans hex_le hge⟩

/-- 구간 강건 불안정성 체커 (최악 극점 L_x vs U_i) -/
def checkIntervalUnstable {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (U : Fin m → Q) (Lx : Q) (lam : Fin m → Q) : Bool :=
  checkPrimalUnstable c cx U Lx lam

theorem checkIntervalUnstable_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {L U : Fin m → Q} {Lx Ux : Q} {lam : Fin m → Q}
    (h : checkIntervalUnstable c cx U Lx lam = true) :
    ∀ enTrue exTrue, InEnergyBox L U Lx Ux enTrue exTrue →
      sumFin (fun i => lam i * enTrue i) <q exTrue :=
  interval_robust_unstable_universal (checkPrimalUnstable_sound h)

/-- 명목 에너지·가중치·반경으로부터 Lean 내부에서 최악 극점 (Ux, L) 을 직접 계산해 검증하는 구간 강건 안정성 체커 -/
def checkIntervalStableFromNominal {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (w : Fin m → Q) (wx eps delta : Q) (mu : Fin E → Q) : Bool :=
  checkNormalizedComps c cx &&
  ble 0 eps &&
  ble 0 wx &&
  allFin (fun i => ble 0 (w i)) &&
  checkIntervalStable c cx (fun i => en i - eps * w i) (ex + eps * wx) delta mu

theorem checkIntervalStableFromNominal_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps delta : Q} {mu : Fin E → Q}
    (h : checkIntervalStableFromNominal c cx en ex w wx eps delta mu = true) :
    NormalizedComps c cx ∧
    (0 : Q) ≤q delta ∧
    (∀ enTrue exTrue,
      InEnergyBox (fun i => en i - eps * w i) (fun i => en i + eps * w i)
                  (ex - eps * wx) (ex + eps * wx) enTrue exTrue →
      ∀ lam, ValidDecomp c cx lam →
        exTrue + delta ≤q sumFin (fun i => lam i * enTrue i) ∧
        exTrue ≤q sumFin (fun i => lam i * enTrue i)) := by
  unfold checkIntervalStableFromNominal at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hnorm, _⟩, _⟩, _⟩, hint⟩
  rcases checkIntervalStable_sound hint with ⟨hdelta, huniv⟩
  exact ⟨checkNormalizedComps_sound hnorm, hdelta, huniv⟩

/-- 명목 에너지·가중치·반경으로부터 Lean 내부에서 최악 극점 (Lx, U) 을 직접 계산해 검증하는 구간 강건 불안정성 체커 -/
def checkIntervalUnstableFromNominal {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (w : Fin m → Q) (wx eps : Q) (lam : Fin m → Q) : Bool :=
  checkNormalizedComps c cx &&
  ble 0 eps &&
  ble 0 wx &&
  allFin (fun i => ble 0 (w i)) &&
  checkIntervalUnstable c cx (fun i => en i + eps * w i) (ex - eps * wx) lam

theorem checkIntervalUnstableFromNominal_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {lam : Fin m → Q}
    (h : checkIntervalUnstableFromNominal c cx en ex w wx eps lam = true) :
    NormalizedComps c cx ∧
    (∀ enTrue exTrue,
      InEnergyBox (fun i => en i - eps * w i) (fun i => en i + eps * w i)
                  (ex - eps * wx) (ex + eps * wx) enTrue exTrue →
      sumFin (fun i => lam i * enTrue i) <q exTrue) := by
  unfold checkIntervalUnstableFromNominal at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hnorm, _⟩, _⟩, _⟩, hint⟩
  exact ⟨checkNormalizedComps_sound hnorm, checkIntervalUnstable_sound hint⟩

/-- 명목 에너지·가중치·반경으로부터 구간 내부 불안정화 취약점(Fragile) 존재를 검증하는 체커 -/
def checkIntervalFragileDestabFromNominal {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (w : Fin m → Q) (wx eps : Q) (lam : Fin m → Q) : Bool :=
  checkNormalizedComps c cx &&
  ble 0 eps &&
  ble 0 wx &&
  allFin (fun i => ble 0 (w i)) &&
  checkPrimalUnstable c cx (fun i => en i - eps * w i) (ex + eps * wx) lam

theorem checkIntervalFragileDestabFromNominal_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {lam : Fin m → Q}
    (h : checkIntervalFragileDestabFromNominal c cx en ex w wx eps lam = true) :
    NormalizedComps c cx ∧
    (∃ enTrue exTrue,
      InEnergyBox (fun i => en i - eps * w i) (fun i => en i + eps * w i)
                  (ex - eps * wx) (ex + eps * wx) enTrue exTrue ∧
      ValidDecomp c cx lam ∧
      sumFin (fun i => lam i * enTrue i) <q exTrue) := by
  unfold checkIntervalFragileDestabFromNominal at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hnorm, heps⟩, hwx⟩, hw⟩, hprim⟩
  rw [allFin_iff] at hw
  exact ⟨
    checkNormalizedComps_sound hnorm,
    interval_fragile_destab_witness
      ((ble_iff _ _).mp heps)
      ((ble_iff _ _).mp hwx)
      (fun i => (ble_iff _ _).mp (hw i))
      (checkPrimalUnstable_sound hprim)
  ⟩

/-- 명목 에너지·가중치·반경으로부터 구간 내부 안정화 취약점(명목 불안정 Fragile) 존재를 검증하는 체커 -/
def checkIntervalFragileStabFromNominal {m E : Nat} (c : Fin m → Fin E → Q) (cx : Fin E → Q)
    (en : Fin m → Q) (ex : Q) (w : Fin m → Q) (wx eps : Q) (mu : Fin E → Q) : Bool :=
  checkNormalizedComps c cx &&
  ble 0 eps &&
  ble 0 wx &&
  allFin (fun i => ble 0 (w i)) &&
  checkDualStable c cx (fun i => en i + eps * w i) (ex - eps * wx) 0 mu

theorem checkIntervalFragileStabFromNominal_sound {m E : Nat} {c : Fin m → Fin E → Q} {cx : Fin E → Q}
    {en : Fin m → Q} {ex : Q} {w : Fin m → Q} {wx eps : Q} {mu : Fin E → Q}
    (h : checkIntervalFragileStabFromNominal c cx en ex w wx eps mu = true) :
    NormalizedComps c cx ∧
    (∃ enTrue exTrue,
      InEnergyBox (fun i => en i - eps * w i) (fun i => en i + eps * w i)
                  (ex - eps * wx) (ex + eps * wx) enTrue exTrue ∧
      ∀ lam, ValidDecomp c cx lam → exTrue ≤q sumFin (fun i => lam i * enTrue i)) := by
  unfold checkIntervalFragileStabFromNominal at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨hnorm, heps⟩, hwx⟩, hw⟩, hdual⟩
  rw [allFin_iff] at hw
  exact ⟨
    checkNormalizedComps_sound hnorm,
    interval_fragile_stab_witness
      ((ble_iff _ _).mp heps)
      ((ble_iff _ _).mp hwx)
      (fun i => (ble_iff _ _).mp (hw i))
      (checkDualStable_sound hdual).2
  ⟩

/-! ### 3. 탄성 텐서 Born 안정성 / 반례 / Weyl 강건성 체커 및 건전성 -/

/-- LDL^T 양정치 증명서 체커 -/
def checkBornLDLT {n : Nat} (C L : Mat n) (d : Vec n) : Bool :=
  allFin (fun i => beq (L i i) 1) &&
  allFin (fun i => allFin (fun j => if i.val < j.val then beq (L i j) 0 else true)) &&
  allFin (fun k => blt 0 (d k)) &&
  allFin (fun i => allFin (fun j => beq (C i j) (sumFin (fun k => L i k * (d k * L j k)))))

theorem checkBornLDLT_sound {n : Nat} {C L : Mat n} {d : Vec n}
    (h : checkBornLDLT C L d = true) : IsBornPD C := by
  unfold checkBornLDLT at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hdiag, hupp⟩, hdpos⟩, hfac⟩
  rw [allFin_iff] at hdiag hupp hdpos hfac
  have hcert : LDLTCert C L d := {
    unit_lower := {
      diag_one := fun i => (beq_iff _ _).mp (hdiag i)
      upper_zero := fun i j hlt => by
        have hj := (allFin_iff _).mp (hupp i) j
        simp only [hlt, ↓reduceIte] at hj
        exact (beq_iff _ _).mp hj
    }
    diag_pos := fun k => (blt_iff _ _).mp (hdpos k)
    factor_eq := fun i j => (beq_iff _ _).mp ((allFin_iff _).mp (hfac i) j)
  }
  exact born_pd_of_ldlt hcert

/-- 비양정치 반례 벡터 체커 -/
def checkBornNonPD {n : Nat} (C : Mat n) (v : Vec n) : Bool :=
  anyFin (fun k => !(beq (v k) 0)) && ble (quadForm C v) 0

theorem checkBornNonPD_sound {n : Nat} {C : Mat n} {v : Vec n}
    (h : checkBornNonPD C v = true) : ¬ IsBornPD C := by
  unfold checkBornNonPD at h
  rw [Bool.and_eq_true, anyFin_iff] at h
  rcases h with ⟨⟨k, hk⟩, hle⟩
  have hne : NonZeroVec v := ⟨k, fun heq => by
    have htrue : beq (v k) 0 = true := (beq_iff _ _).mpr heq
    rw [htrue] at hk
    cases hk⟩
  exact not_born_pd_of_witness hne ((ble_iff _ _).mp hle)

/-- 이동 LDL^T 기반 Weyl 강건 Born 안정성 체커 (C - lam0 I = L diag(d) L^T, 0 ≤ delta ≤ lam0) -/
def checkWeylRobustBorn {n : Nat} (C L : Mat n) (d : Vec n) (lam0 delta : Q) : Bool :=
  checkBornLDLT (shiftMat C lam0) L d && ble 0 delta && ble delta lam0

theorem checkWeylRobustBorn_sound {n : Nat} {C L : Mat n} {d : Vec n} {lam0 delta : Q}
    (h : checkWeylRobustBorn C L d lam0 delta = true) :
    ∀ dC : Mat n, frobSq dC ≤q delta * delta → IsBornPD (addMat C dC) := by
  unfold checkWeylRobustBorn at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hldlt, hdelta⟩, hmargin⟩
  -- checkBornLDLT 에서 LDLTCert 복원
  unfold checkBornLDLT at hldlt
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hldlt
  rcases hldlt with ⟨⟨⟨hdiag, hupp⟩, hdpos⟩, hfac⟩
  rw [allFin_iff] at hdiag hupp hdpos hfac
  have hcert : LDLTCert (shiftMat C lam0) L d := {
    unit_lower := {
      diag_one := fun i => (beq_iff _ _).mp (hdiag i)
      upper_zero := fun i j hlt => by
        have hj := (allFin_iff _).mp (hupp i) j
        simp only [hlt, ↓reduceIte] at hj
        exact (beq_iff _ _).mp hj
    }
    diag_pos := fun k => (blt_iff _ _).mp (hdpos k)
    factor_eq := fun i j => (beq_iff _ _).mp ((allFin_iff _).mp (hfac i) j)
  }
  intro dC hfrob
  exact shifted_ldlt_frob_robust_born hcert ((ble_iff _ _).mp hdelta) hfrob ((ble_iff _ _).mp hmargin)

/-- 이동 LDL^T 기반 Weyl 강건 Born 체커의 Rayleigh/스펙트럼 하계 건전성 정리 -/
theorem checkWeylRobustBorn_rayleigh_sound {n : Nat} {C L : Mat n} {d : Vec n} {lam0 delta : Q}
    (h : checkWeylRobustBorn C L d lam0 delta = true) :
    ∀ dC : Mat n, IsRayleighBounded dC delta → IsBornPD (addMat C dC) := by
  unfold checkWeylRobustBorn at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hldlt, _⟩, hmargin⟩
  unfold checkBornLDLT at hldlt
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hldlt
  rcases hldlt with ⟨⟨⟨hdiag, hupp⟩, hdpos⟩, hfac⟩
  rw [allFin_iff] at hdiag hupp hdpos hfac
  have hcert : LDLTCert (shiftMat C lam0) L d := {
    unit_lower := {
      diag_one := fun i => (beq_iff _ _).mp (hdiag i)
      upper_zero := fun i j hlt => by
        have hj := (allFin_iff _).mp (hupp i) j
        simp only [hlt, ↓reduceIte] at hj
        exact (beq_iff _ _).mp hj
    }
    diag_pos := fun k => (blt_iff _ _).mp (hdpos k)
    factor_eq := fun i j => (beq_iff _ _).mp ((allFin_iff _).mp (hfac i) j)
  }
  intro dC hpert
  exact shifted_ldlt_rayleigh_robust_born hcert hpert ((ble_iff _ _).mp hmargin)

/-- Weyl 기계적 취약성 반례 체커: v ≠ 0, delta ≥ 0, v^T C v ≤ delta * ‖v‖^2 -/
def checkWeylFragile {n : Nat} (C : Mat n) (delta : Q) (v : Vec n) : Bool :=
  ble 0 delta && anyFin (fun k => !(beq (v k) 0)) && ble (quadForm C v) (delta * normSq v)

theorem checkWeylFragile_sound {n : Nat} {C : Mat n} {delta : Q} {v : Vec n}
    (h : checkWeylFragile C delta v = true) :
    ∃ dC : Mat n,
      IsSymmetricMat dC ∧
      frobSq dC ≈ delta * delta ∧
      ¬ IsBornPD (addMat C dC) := by
  unfold checkWeylFragile at h
  rw [Bool.and_eq_true, Bool.and_eq_true, anyFin_iff] at h
  rcases h with ⟨⟨_, ⟨k, hk⟩⟩, hweak⟩
  have hne : NonZeroVec v := ⟨k, fun heq => by
    have htrue : beq (v k) 0 = true := (beq_iff _ _).mpr heq
    rw [htrue] at hk
    cases hk⟩
  exact weyl_fragile_of_witness hne ((ble_iff _ _).mp hweak)

/-- 6x6 SO(3)-불변 Mandel/Kelvin 가중 벡터 s = (1, 1, 1, 1/2, 1/2, 1/2) 및 역가중치 r = (1, 1, 1, 2, 2, 2) -/
def mandelWeightVec : Vec 6 :=
  fun i => if i.val < 3 then 1 else ⟨1, 2, by decide⟩

def mandelInvWeightVec : Vec 6 :=
  fun i => if i.val < 3 then 1 else Q.ofInt 2

private theorem mandelWeightVec_pos (i : Fin 6) : (0 : Q) <q mandelWeightVec i := by
  unfold mandelWeightVec
  split <;> (rw [zero_lt_iff]; decide)

private theorem mandelWeightVec_nonneg (i : Fin 6) : (0 : Q) ≤q mandelWeightVec i := by
  exact le_of_lt (mandelWeightVec_pos i)

private theorem mandelInvWeightVec_nonneg (i : Fin 6) : (0 : Q) ≤q mandelInvWeightVec i := by
  unfold mandelInvWeightVec
  split <;> (rw [zero_le_iff]; decide)

private theorem mandelWeightVec_mul_inv (i : Fin 6) :
    mandelWeightVec i * mandelInvWeightVec i ≈ 1 := by
  unfold mandelWeightVec mandelInvWeightVec
  split
  · exact mul_one 1
  · unfold eqv; decide

/-- 순수 유리수 SO(3)-불변 Mandel/Kelvin 고유값 하한 및 섭동 강건성 체커
    (C_Voigt - lam0 diag(1,1,1,1/2,1/2,1/2) = L diag(d) L^T, 0 ≤ delta ≤ lam0) -/
def checkMandelWeylRobustBorn (C L : Mat 6) (d : Vec 6) (lam0 delta : Q) : Bool :=
  checkBornLDLT (weightedShiftMat C lam0 mandelWeightVec) L d && ble 0 delta && ble delta lam0

theorem checkMandelWeylRobustBorn_sound {C L : Mat 6} {d : Vec 6} {lam0 delta : Q}
    (h : checkMandelWeylRobustBorn C L d lam0 delta = true) :
    ∀ v : Vec 6, NonZeroVec v → delta * weightedNormSq mandelWeightVec v <q quadForm C v := by
  unfold checkMandelWeylRobustBorn at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hldlt, _⟩, hmargin⟩
  unfold checkBornLDLT at hldlt
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hldlt
  rcases hldlt with ⟨⟨⟨hdiag, hupp⟩, hdpos⟩, hfac⟩
  rw [allFin_iff] at hdiag hupp hdpos hfac
  have hcert : LDLTCert (weightedShiftMat C lam0 mandelWeightVec) L d := {
    unit_lower := {
      diag_one := fun i => (beq_iff _ _).mp (hdiag i)
      upper_zero := fun i j hlt => by
        have hj := (allFin_iff _).mp (hupp i) j
        simp only [hlt, ↓reduceIte] at hj
        exact (beq_iff _ _).mp hj
    }
    diag_pos := fun k => (blt_iff _ _).mp (hdpos k)
    factor_eq := fun i j => (beq_iff _ _).mp ((allFin_iff _).mp (hfac i) j)
  }
  intro v hne
  have hbase := weighted_eigenvalue_lower_bound_of_shifted_ldlt hcert v hne
  have hwnn : (0 : Q) ≤q weightedNormSq mandelWeightVec v :=
    sumFin_nonneg (fun i => mul_nonneg (mandelWeightVec_nonneg i) (sq_nonneg (v i)))
  have hle : delta * weightedNormSq mandelWeightVec v ≤q lam0 * weightedNormSq mandelWeightVec v := by
    have p := mul_le_mul_of_nonneg_left hwnn ((ble_iff _ _).mp hmargin)
    exact le_trans (le_of_eqv (mul_comm delta _)) (le_trans p (le_of_eqv (mul_comm _ lam0)))
  exact lt_of_le_of_lt hle hbase

/-- `checkMandelWeylRobustBorn` 의 SO(3)-불변 Mandel 프로베니우스 섭동 강건 Born 양정치성 정리:
    ‖ΔC_Mandel‖_F^2 = weightedFrobSq mandelInvWeightVec ΔC ≤ δ^2 인 모든 섭동 ΔC 에 대해 C + ΔC ≻ 0 -/
theorem checkMandelWeylRobustBorn_frob_sound {C L : Mat 6} {d : Vec 6} {lam0 delta : Q}
    (h : checkMandelWeylRobustBorn C L d lam0 delta = true) :
    ∀ dC : Mat 6, weightedFrobSq mandelInvWeightVec dC ≤q delta * delta → IsBornPD (addMat C dC) := by
  unfold checkMandelWeylRobustBorn at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hldlt, hdelta⟩, hmargin⟩
  unfold checkBornLDLT at hldlt
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hldlt
  rcases hldlt with ⟨⟨⟨hdiag, hupp⟩, hdpos⟩, hfac⟩
  rw [allFin_iff] at hdiag hupp hdpos hfac
  have hcert : LDLTCert (weightedShiftMat C lam0 mandelWeightVec) L d := {
    unit_lower := {
      diag_one := fun i => (beq_iff _ _).mp (hdiag i)
      upper_zero := fun i j hlt => by
        have hj := (allFin_iff _).mp (hupp i) j
        simp only [hlt, ↓reduceIte] at hj
        exact (beq_iff _ _).mp hj
    }
    diag_pos := fun k => (blt_iff _ _).mp (hdpos k)
    factor_eq := fun i j => (beq_iff _ _).mp ((allFin_iff _).mp (hfac i) j)
  }
  intro dC hfrob
  exact weighted_shifted_ldlt_frob_robust_born
    mandelWeightVec_nonneg mandelInvWeightVec_nonneg mandelWeightVec_mul_inv
    hcert ((ble_iff _ _).mp hdelta) hfrob ((ble_iff _ _).mp hmargin)

/-- `checkMandelWeylRobustBorn` 의 SO(3)-불변 Mandel Rayleigh/스펙트럼 섭동 강건 Born 양정치성 정리 -/
theorem checkMandelWeylRobustBorn_rayleigh_sound {C L : Mat 6} {d : Vec 6} {lam0 delta : Q}
    (h : checkMandelWeylRobustBorn C L d lam0 delta = true) :
    ∀ dC : Mat 6, IsWeightedRayleighBounded mandelWeightVec dC delta → IsBornPD (addMat C dC) := by
  unfold checkMandelWeylRobustBorn at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨hldlt, _⟩, hmargin⟩
  unfold checkBornLDLT at hldlt
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hldlt
  rcases hldlt with ⟨⟨⟨hdiag, hupp⟩, hdpos⟩, hfac⟩
  rw [allFin_iff] at hdiag hupp hdpos hfac
  have hcert : LDLTCert (weightedShiftMat C lam0 mandelWeightVec) L d := {
    unit_lower := {
      diag_one := fun i => (beq_iff _ _).mp (hdiag i)
      upper_zero := fun i j hlt => by
        have hj := (allFin_iff _).mp (hupp i) j
        simp only [hlt, ↓reduceIte] at hj
        exact (beq_iff _ _).mp hj
    }
    diag_pos := fun k => (blt_iff _ _).mp (hdpos k)
    factor_eq := fun i j => (beq_iff _ _).mp ((allFin_iff _).mp (hfac i) j)
  }
  intro dC hpert
  exact weighted_shifted_ldlt_rayleigh_robust_born
    mandelWeightVec_nonneg hcert hpert ((ble_iff _ _).mp hmargin)

/-- 순수 유리수 SO(3)-불변 Mandel/Kelvin 기계적 취약성 반례 체커:
    delta ≥ 0, v ≠ 0, v^T C_Voigt v ≤ delta * ‖v‖_s^2 (s = (1,1,1,1/2,1/2,1/2)) -/
def checkMandelWeylFragile (C : Mat 6) (delta : Q) (v : Vec 6) : Bool :=
  ble 0 delta && anyFin (fun k => !(beq (v k) 0)) && ble (quadForm C v) (delta * weightedNormSq mandelWeightVec v)

/-- `checkMandelWeylFragile` 의 건전성 정리:
    대칭 랭크-1 유리수 섭동 ΔC 가 정확히 ‖D ΔC D‖_F^2 = weightedFrobSq r ΔC ≈ δ^2 을 가지면서
    C + ΔC 의 Born 양정치성을 붕괴시킴을 무리수 √2 없이 구성 증명한다. -/
theorem checkMandelWeylFragile_sound {C : Mat 6} {delta : Q} {v : Vec 6}
    (h : checkMandelWeylFragile C delta v = true) :
    ∃ dC : Mat 6,
      IsSymmetricMat dC ∧
      weightedFrobSq mandelInvWeightVec dC ≈ delta * delta ∧
      ¬ IsBornPD (addMat C dC) := by
  unfold checkMandelWeylFragile at h
  rw [Bool.and_eq_true, Bool.and_eq_true, anyFin_iff] at h
  rcases h with ⟨⟨_, ⟨k, hk⟩⟩, hweak⟩
  have hne : NonZeroVec v := ⟨k, fun heq => by
    have htrue : beq (v k) 0 = true := (beq_iff _ _).mpr heq
    rw [htrue] at hk
    cases hk⟩
  exact weighted_weyl_fragile_of_witness
    mandelWeightVec_pos mandelWeightVec_mul_inv hne ((ble_iff _ _).mp hweak)

end CertMat
