/-
  CertMat/ExactRat.lean
  외부 Mathlib 의존성 없이 Lean 4 코어(Init)만으로 구축한 정확한 유리수(Q) 구조체와
  순서체/순서환(Ordered Field/Ring) 보조정리 및 유한합(sumFin) 연산 라이브러리.
  모든 정리는 `sorry` 없이 완결 증명된다.
-/

namespace CertMat

/-- 분모가 양수인 정확한 유리수 표현 (정규화 불필요, 등치는 교차곱으로 정의) -/
structure Q where
  num : Int
  den : Nat
  den_pos : 0 < den
  deriving Repr

namespace Q

/-- 양의 분모를 Int로 변환 -/
def denI (q : Q) : Int := Int.ofNat q.den

theorem denI_pos (q : Q) : (0 : Int) < q.denI := by
  unfold denI
  exact Int.ofNat_pos.mpr q.den_pos

theorem denI_ne_zero (q : Q) : q.denI ≠ 0 := by
  have h := denI_pos q
  omega

/-- 정수에서 유리수로의 임베딩 -/
def ofInt (n : Int) : Q := ⟨n, 1, Nat.zero_lt_one⟩

/-- 0과 1 상수 -/
def zero : Q := ofInt 0
def one  : Q := ofInt 1

/-- 유리수 교차곱 동치 관계 (값 등치) -/
def eqv (a b : Q) : Prop := a.num * b.denI = b.num * a.denI

/-- 유리수 대소 비교 (≤, <) -/
def le (a b : Q) : Prop := a.num * b.denI ≤ b.num * a.denI
def lt (a b : Q) : Prop := a.num * b.denI < b.num * a.denI

/-- 결정 가능한 비교 연산자 -/
def beq (a b : Q) : Bool := decide (a.num * b.denI = b.num * a.denI)
def ble (a b : Q) : Bool := decide (a.num * b.denI ≤ b.num * a.denI)
def blt (a b : Q) : Bool := decide (a.num * b.denI < b.num * a.denI)

theorem beq_iff (a b : Q) : beq a b = true ↔ eqv a b := by
  unfold beq eqv; exact decide_eq_true_iff

theorem ble_iff (a b : Q) : ble a b = true ↔ le a b := by
  unfold ble le; exact decide_eq_true_iff

theorem blt_iff (a b : Q) : blt a b = true ↔ lt a b := by
  unfold blt lt; exact decide_eq_true_iff

/-- 유리수 사칙연산 -/
def add (a b : Q) : Q :=
  ⟨a.num * b.denI + b.num * a.denI, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def neg (a : Q) : Q :=
  ⟨-a.num, a.den, a.den_pos⟩

def sub (a b : Q) : Q := add a (neg b)

def mul (a b : Q) : Q :=
  ⟨a.num * b.num, a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩

def sq (a : Q) : Q := mul a a

instance : Add Q := ⟨Q.add⟩
instance : Neg Q := ⟨Q.neg⟩
instance : Sub Q := ⟨Q.sub⟩
instance : Mul Q := ⟨Q.mul⟩
instance : OfNat Q 0 := ⟨Q.zero⟩
instance : OfNat Q 1 := ⟨Q.one⟩

infix:50 " ≈ " => Q.eqv
infix:50 " ≤q " => Q.le
infix:50 " <q " => Q.lt

/-- 보조: 정수 곱셈 소거 법칙 (양수 인자) -/
private theorem int_eq_of_mul_pos {x y c : Int} (hc : 0 < c) (h : x * c = y * c) : x = y := by
  have h1 : (x - y) * c = 0 := by
    rw [Int.sub_mul, h, Int.sub_self]
  rcases Int.mul_eq_zero.mp h1 with hxy | hc0
  · omega
  · omega

private theorem int_le_of_mul_pos {x y c : Int} (hc : 0 < c) (h : x * c ≤ y * c) : x ≤ y := by
  by_cases hxy : x ≤ y
  · exact hxy
  · have hdiff : 0 < x - y := by omega
    have hprod : 0 < (x - y) * c := Int.mul_pos hdiff hc
    rw [Int.sub_mul] at hprod
    omega

private theorem int_lt_of_mul_pos {x y c : Int} (hc : 0 < c) (h : x * c < y * c) : x < y := by
  by_cases hxy : x < y
  · exact hxy
  · have hyx : y ≤ x := by omega
    have hprod : y * c ≤ x * c := Int.mul_le_mul_of_nonneg_right hyx (by omega)
    omega

theorem denI_mul (a b : Q) : (a * b).denI = a.denI * b.denI :=
  Int.ofNat_mul a.den b.den

theorem denI_add (a b : Q) : (a + b).denI = a.denI * b.denI :=
  Int.ofNat_mul a.den b.den

theorem denI_neg (a : Q) : (-a).denI = a.denI := rfl

/-! ### 동치 관계(≈) 및 순서(≤q, <q) 기본 성질 -/

theorem eqv_refl (a : Q) : a ≈ a := rfl

theorem eqv_symm {a b : Q} (h : a ≈ b) : b ≈ a := h.symm

theorem eqv_trans {a b c : Q} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c := by
  unfold eqv at *
  have hb : 0 < b.denI := denI_pos b
  apply int_eq_of_mul_pos hb
  calc (a.num * c.denI) * b.denI
      = (a.num * b.denI) * c.denI := by
          rw [Int.mul_assoc, Int.mul_comm c.denI b.denI, ← Int.mul_assoc]
    _ = (b.num * a.denI) * c.denI := by rw [hab]
    _ = (b.num * c.denI) * a.denI := by
          rw [Int.mul_assoc, Int.mul_comm a.denI c.denI, ← Int.mul_assoc]
    _ = (c.num * b.denI) * a.denI := by rw [hbc]
    _ = (c.num * a.denI) * b.denI := by
          rw [Int.mul_assoc, Int.mul_comm b.denI a.denI, ← Int.mul_assoc]

theorem le_refl (a : Q) : a ≤q a := Int.le_refl _

theorem le_of_eqv {a b : Q} (h : a ≈ b) : a ≤q b := by
  unfold le; unfold eqv at h; omega

theorem le_trans {a b c : Q} (hab : a ≤q b) (hbc : b ≤q c) : a ≤q c := by
  unfold le at *
  have hb : 0 < b.denI := denI_pos b
  have ha : 0 ≤ a.denI := Int.le_of_lt (denI_pos a)
  have hc : 0 ≤ c.denI := Int.le_of_lt (denI_pos c)
  apply int_le_of_mul_pos hb
  have h1 : (a.num * b.denI) * c.denI ≤ (b.num * a.denI) * c.denI :=
    Int.mul_le_mul_of_nonneg_right hab hc
  have h2 : (b.num * c.denI) * a.denI ≤ (c.num * b.denI) * a.denI :=
    Int.mul_le_mul_of_nonneg_right hbc ha
  have e1 : (a.num * c.denI) * b.denI = (a.num * b.denI) * c.denI := by
    rw [Int.mul_assoc, Int.mul_comm c.denI b.denI, ← Int.mul_assoc]
  have e2 : (b.num * a.denI) * c.denI = (b.num * c.denI) * a.denI := by
    rw [Int.mul_assoc, Int.mul_comm a.denI c.denI, ← Int.mul_assoc]
  have e3 : (c.num * b.denI) * a.denI = (c.num * a.denI) * b.denI := by
    rw [Int.mul_assoc, Int.mul_comm b.denI a.denI, ← Int.mul_assoc]
  omega

theorem lt_of_le_of_lt {a b c : Q} (hab : a ≤q b) (hbc : b <q c) : a <q c := by
  unfold le lt at *
  have hb : 0 < b.denI := denI_pos b
  have ha : 0 < a.denI := denI_pos a
  have hc : 0 ≤ c.denI := Int.le_of_lt (denI_pos c)
  apply int_lt_of_mul_pos hb
  have h1 : (a.num * b.denI) * c.denI ≤ (b.num * a.denI) * c.denI :=
    Int.mul_le_mul_of_nonneg_right hab hc
  have h2 : (b.num * c.denI) * a.denI < (c.num * b.denI) * a.denI := by
    have hd : 0 < c.num * b.denI - b.num * c.denI := by omega
    have hp := Int.mul_pos hd ha
    rw [Int.sub_mul] at hp; omega
  have e1 : (a.num * c.denI) * b.denI = (a.num * b.denI) * c.denI := by
    rw [Int.mul_assoc, Int.mul_comm c.denI b.denI, ← Int.mul_assoc]
  have e2 : (b.num * a.denI) * c.denI = (b.num * c.denI) * a.denI := by
    rw [Int.mul_assoc, Int.mul_comm a.denI c.denI, ← Int.mul_assoc]
  have e3 : (c.num * b.denI) * a.denI = (c.num * a.denI) * b.denI := by
    rw [Int.mul_assoc, Int.mul_comm b.denI a.denI, ← Int.mul_assoc]
  omega

theorem lt_of_lt_of_le {a b c : Q} (hab : a <q b) (hbc : b ≤q c) : a <q c := by
  unfold le lt at *
  have hb : 0 < b.denI := denI_pos b
  have ha : 0 ≤ a.denI := Int.le_of_lt (denI_pos a)
  have hc : 0 < c.denI := denI_pos c
  apply int_lt_of_mul_pos hb
  have h1 : (a.num * b.denI) * c.denI < (b.num * a.denI) * c.denI := by
    have hd : 0 < b.num * a.denI - a.num * b.denI := by omega
    have hp := Int.mul_pos hd hc
    rw [Int.sub_mul] at hp; omega
  have h2 : (b.num * c.denI) * a.denI ≤ (c.num * b.denI) * a.denI :=
    Int.mul_le_mul_of_nonneg_right hbc ha
  have e1 : (a.num * c.denI) * b.denI = (a.num * b.denI) * c.denI := by
    rw [Int.mul_assoc, Int.mul_comm c.denI b.denI, ← Int.mul_assoc]
  have e2 : (b.num * a.denI) * c.denI = (b.num * c.denI) * a.denI := by
    rw [Int.mul_assoc, Int.mul_comm a.denI c.denI, ← Int.mul_assoc]
  have e3 : (c.num * b.denI) * a.denI = (c.num * a.denI) * b.denI := by
    rw [Int.mul_assoc, Int.mul_comm b.denI a.denI, ← Int.mul_assoc]
  omega

theorem le_of_lt {a b : Q} (h : a <q b) : a ≤q b := Int.le_of_lt h

theorem not_lt_of_le {a b : Q} (h : b ≤q a) : ¬ (a <q b) := by
  unfold le lt at *; omega

theorem zero_le_iff (a : Q) : (0 : Q) ≤q a ↔ 0 ≤ a.num := by
  change (0 : Int) * a.denI ≤ a.num * (1 : Int) ↔ 0 ≤ a.num
  omega

theorem zero_lt_iff (a : Q) : (0 : Q) <q a ↔ 0 < a.num := by
  change (0 : Int) * a.denI < a.num * (1 : Int) ↔ 0 < a.num
  omega

theorem eqv_zero_iff (a : Q) : a ≈ (0 : Q) ↔ a.num = 0 := by
  change a.num * (1 : Int) = (0 : Int) * a.denI ↔ a.num = 0
  omega

/-! ### 대수 법칙 (동치 ≈ 기준) -/

theorem add_comm (a b : Q) : a + b ≈ b + a := by
  unfold eqv
  change (a.num * b.denI + b.num * a.denI) * (b + a).denI =
         (b.num * a.denI + a.num * b.denI) * (a + b).denI
  rw [denI_add, denI_add, Int.add_comm (a.num * b.denI), Int.mul_comm b.denI a.denI]

theorem mul_comm (a b : Q) : a * b ≈ b * a := by
  unfold eqv
  change (a.num * b.num) * (b * a).denI = (b.num * a.num) * (a * b).denI
  rw [denI_mul, denI_mul, Int.mul_comm a.num b.num, Int.mul_comm b.denI a.denI]

theorem add_zero (a : Q) : a + 0 ≈ a := by
  unfold eqv
  change (a.num * (0 : Q).denI + (0 : Q).num * a.denI) * a.denI = a.num * (a + 0).denI
  rw [denI_add]
  have hz1 : (0 : Q).denI = 1 := rfl
  have hz0 : (0 : Q).num = 0 := rfl
  rw [hz1, hz0]
  simp [Int.mul_one, Int.zero_mul, Int.add_zero]

theorem zero_add (a : Q) : 0 + a ≈ a := eqv_trans (add_comm 0 a) (add_zero a)

theorem mul_zero (a : Q) : a * 0 ≈ 0 := by
  rw [eqv_zero_iff]
  change a.num * 0 = 0
  exact Int.mul_zero a.num

theorem zero_mul (a : Q) : 0 * a ≈ 0 := eqv_trans (mul_comm 0 a) (mul_zero a)

theorem mul_one (a : Q) : a * 1 ≈ a := by
  unfold eqv
  change (a.num * 1) * a.denI = a.num * (a * 1).denI
  rw [denI_mul]
  have h1 : (1 : Q).denI = 1 := rfl
  rw [h1, Int.mul_one, Int.mul_one]

theorem one_mul (a : Q) : 1 * a ≈ a := eqv_trans (mul_comm 1 a) (mul_one a)

theorem add_assoc (a b c : Q) : (a + b) + c ≈ a + (b + c) := by
  unfold eqv
  change ((a.num * b.denI + b.num * a.denI) * c.denI + c.num * (a + b).denI) * (a + (b + c)).denI =
         (a.num * (b + c).denI + (b.num * c.denI + c.num * b.denI) * a.denI) * ((a + b) + c).denI
  rw [denI_add, denI_add, denI_add, denI_add]
  have hden : a.denI * (b.denI * c.denI) = (a.denI * b.denI) * c.denI := (Int.mul_assoc _ _ _).symm
  rw [hden]
  apply congrArg (· * (a.denI * b.denI * c.denI))
  rw [Int.add_mul, Int.add_mul, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc]
  rw [Int.mul_comm a.denI c.denI, Int.mul_comm a.denI b.denI, Int.add_assoc]

theorem mul_assoc (a b c : Q) : (a * b) * c ≈ a * (b * c) := by
  unfold eqv
  change ((a.num * b.num) * c.num) * (a * (b * c)).denI =
         (a.num * (b.num * c.num)) * ((a * b) * c).denI
  rw [denI_mul, denI_mul, denI_mul, denI_mul]
  simp only [Int.mul_assoc]

theorem mul_add (a b c : Q) : a * (b + c) ≈ a * b + a * c := by
  unfold eqv
  change (a.num * (b.num * c.denI + c.num * b.denI)) * (a * b + a * c).denI =
         ((a.num * b.num) * (a * c).denI + (a.num * c.num) * (a * b).denI) * (a * (b + c)).denI
  rw [denI_add, denI_mul, denI_mul, denI_mul, denI_add]
  rw [Int.mul_add, Int.add_mul, Int.add_mul]
  congr 1
  · simp only [Int.mul_assoc]
    have h1 : c.denI * (a.denI * (b.denI * (a.denI * c.denI))) =
              a.denI * (c.denI * (a.denI * (b.denI * c.denI))) := by
      rw [Int.mul_left_comm c.denI a.denI, Int.mul_left_comm b.denI a.denI]
    exact congrArg (a.num * ·) (congrArg (b.num * ·) h1)
  · simp only [Int.mul_assoc]
    have h2 : b.denI * (a.denI * (b.denI * (a.denI * c.denI))) =
              a.denI * (b.denI * (a.denI * (b.denI * c.denI))) := by
      rw [Int.mul_left_comm b.denI a.denI]
      rw [Int.mul_left_comm b.denI a.denI]
    exact congrArg (a.num * ·) (congrArg (c.num * ·) h2)

theorem add_mul (a b c : Q) : (a + b) * c ≈ a * c + b * c := by
  have h1 := mul_comm (a + b) c
  have h2 := mul_add c a b
  have h3 : c * a + c * b ≈ a * c + b * c := by
    -- add_congr는 아래에 정의하므로 직접 조합
    unfold eqv
    change ((c.num * a.num) * (c * b).denI + (c.num * b.num) * (c * a).denI) * (a * c + b * c).denI =
           ((a.num * c.num) * (b * c).denI + (b.num * c.num) * (a * c).denI) * (c * a + c * b).denI
    rw [denI_add, denI_add, denI_mul, denI_mul, denI_mul, denI_mul]
    rw [Int.mul_comm c.num a.num, Int.mul_comm c.num b.num, Int.mul_comm c.denI a.denI, Int.mul_comm c.denI b.denI]
  exact eqv_trans (eqv_trans h1 h2) h3

theorem add_congr {a b c d : Q} (hab : a ≈ b) (hcd : c ≈ d) : a + c ≈ b + d := by
  unfold eqv at *
  change (a.num * c.denI + c.num * a.denI) * (b + d).denI =
         (b.num * d.denI + d.num * b.denI) * (a + c).denI
  rw [denI_add, denI_add, Int.add_mul, Int.add_mul]
  have h1 : (a.num * c.denI) * (b.denI * d.denI) = (b.num * d.denI) * (a.denI * c.denI) := by
    calc (a.num * c.denI) * (b.denI * d.denI)
        = (a.num * b.denI) * (c.denI * d.denI) := by
            simp only [Int.mul_assoc]; rw [Int.mul_left_comm c.denI b.denI]
      _ = (b.num * a.denI) * (c.denI * d.denI) := by rw [hab]
      _ = (b.num * d.denI) * (a.denI * c.denI) := by
            simp only [Int.mul_assoc]; rw [Int.mul_comm c.denI d.denI, Int.mul_left_comm a.denI d.denI]
  have h2 : (c.num * a.denI) * (b.denI * d.denI) = (d.num * b.denI) * (a.denI * c.denI) := by
    calc (c.num * a.denI) * (b.denI * d.denI)
        = (c.num * d.denI) * (a.denI * b.denI) := by
            simp only [Int.mul_assoc]; rw [Int.mul_comm b.denI d.denI, Int.mul_left_comm a.denI d.denI]
      _ = (d.num * c.denI) * (a.denI * b.denI) := by rw [hcd]
      _ = (d.num * b.denI) * (a.denI * c.denI) := by
            simp only [Int.mul_assoc]; rw [Int.mul_comm a.denI b.denI, Int.mul_left_comm c.denI b.denI, Int.mul_comm c.denI a.denI]
  omega

theorem mul_congr {a b c d : Q} (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d := by
  unfold eqv at *
  change (a.num * c.num) * (b * d).denI = (b.num * d.num) * (a * c).denI
  rw [denI_mul, denI_mul]
  calc (a.num * c.num) * (b.denI * d.denI)
      = (a.num * b.denI) * (c.num * d.denI) := by
          simp only [Int.mul_assoc]; rw [Int.mul_left_comm c.num b.denI]
    _ = (b.num * a.denI) * (d.num * c.denI) := by rw [hab, hcd]
    _ = (b.num * d.num) * (a.denI * c.denI) := by
          simp only [Int.mul_assoc]; rw [Int.mul_left_comm a.denI d.num]

theorem neg_congr {a b : Q} (hab : a ≈ b) : -a ≈ -b := by
  unfold eqv at *
  change (-a.num) * b.denI = (-b.num) * a.denI
  rw [Int.neg_mul, Int.neg_mul, hab]

theorem sub_congr {a b c d : Q} (hab : a ≈ b) (hcd : c ≈ d) : a - c ≈ b - d :=
  add_congr hab (neg_congr hcd)

theorem sub_self (a : Q) : a - a ≈ 0 := by
  rw [eqv_zero_iff]
  change a.num * a.denI + (-a.num) * a.denI = 0
  rw [Int.neg_mul]; omega

theorem add_sub_cancel (a b : Q) : (a + b) - b ≈ a := by
  unfold eqv
  change ((a.num * b.denI + b.num * a.denI) * b.denI + (-b.num) * (a + b).denI) * a.denI =
         a.num * ((a + b) + (-b)).denI
  rw [denI_add, denI_add, denI_neg, denI_add]
  have hmid : (a.num * b.denI + b.num * a.denI) * b.denI + (-b.num) * (a.denI * b.denI) =
              a.num * b.denI * b.denI := by
    rw [Int.add_mul, Int.neg_mul, Int.mul_assoc b.num a.denI b.denI]
    omega
  rw [hmid]
  simp only [Int.mul_assoc]
  rw [Int.mul_comm b.denI a.denI, Int.mul_left_comm b.denI a.denI]

theorem sub_add_cancel (a b : Q) : (a - b) + b ≈ a := by
  have h1 : (a - b) + b ≈ a + ((-b) + b) := add_assoc a (-b) b
  have h2 : (-b) + b ≈ 0 := eqv_trans (add_comm (-b) b) (sub_self b)
  exact eqv_trans h1 (eqv_trans (add_congr (eqv_refl a) h2) (add_zero a))

theorem neg_mul (a b : Q) : (-a) * b ≈ -(a * b) := by
  unfold eqv
  change ((-a.num) * b.num) * (a * b).denI = (-(a.num * b.num)) * ((-a) * b).denI
  rw [denI_mul, denI_mul, denI_neg, Int.neg_mul]

/-! ### 순서와 연산의 호환성 -/

theorem add_le_add {a b c d : Q} (hab : a ≤q b) (hcd : c ≤q d) : a + c ≤q b + d := by
  unfold le at *
  change (a.num * c.denI + c.num * a.denI) * (b + d).denI ≤
         (b.num * d.denI + d.num * b.denI) * (a + c).denI
  rw [denI_add, denI_add, Int.add_mul, Int.add_mul]
  have hcd_nn : 0 ≤ c.denI * d.denI := Int.mul_nonneg (Int.le_of_lt (denI_pos c)) (Int.le_of_lt (denI_pos d))
  have hab_nn : 0 ≤ a.denI * b.denI := Int.mul_nonneg (Int.le_of_lt (denI_pos a)) (Int.le_of_lt (denI_pos b))
  have h1 : (a.num * c.denI) * (b.denI * d.denI) ≤ (b.num * d.denI) * (a.denI * c.denI) := by
    have p := Int.mul_le_mul_of_nonneg_right hab hcd_nn
    have l : (a.num * c.denI) * (b.denI * d.denI) = (a.num * b.denI) * (c.denI * d.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_left_comm c.denI b.denI]
    have r : (b.num * d.denI) * (a.denI * c.denI) = (b.num * a.denI) * (c.denI * d.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_comm c.denI d.denI, Int.mul_left_comm a.denI d.denI]
    omega
  have h2 : (c.num * a.denI) * (b.denI * d.denI) ≤ (d.num * b.denI) * (a.denI * c.denI) := by
    have p := Int.mul_le_mul_of_nonneg_right hcd hab_nn
    have l : (c.num * a.denI) * (b.denI * d.denI) = (c.num * d.denI) * (a.denI * b.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_comm b.denI d.denI, Int.mul_left_comm a.denI d.denI]
    have r : (d.num * b.denI) * (a.denI * c.denI) = (d.num * c.denI) * (a.denI * b.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_comm a.denI b.denI, Int.mul_left_comm c.denI b.denI, Int.mul_comm c.denI a.denI]
    omega
  omega

theorem add_lt_add_of_le_of_lt {a b c d : Q} (hab : a ≤q b) (hcd : c <q d) : a + c <q b + d := by
  unfold le lt at *
  change (a.num * c.denI + c.num * a.denI) * (b + d).denI <
         (b.num * d.denI + d.num * b.denI) * (a + c).denI
  rw [denI_add, denI_add, Int.add_mul, Int.add_mul]
  have hcd_nn : 0 ≤ c.denI * d.denI := Int.mul_nonneg (Int.le_of_lt (denI_pos c)) (Int.le_of_lt (denI_pos d))
  have hab_pos : 0 < a.denI * b.denI := Int.mul_pos (denI_pos a) (denI_pos b)
  have h1 : (a.num * c.denI) * (b.denI * d.denI) ≤ (b.num * d.denI) * (a.denI * c.denI) := by
    have p := Int.mul_le_mul_of_nonneg_right hab hcd_nn
    have l : (a.num * c.denI) * (b.denI * d.denI) = (a.num * b.denI) * (c.denI * d.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_left_comm c.denI b.denI]
    have r : (b.num * d.denI) * (a.denI * c.denI) = (b.num * a.denI) * (c.denI * d.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_comm c.denI d.denI, Int.mul_left_comm a.denI d.denI]
    omega
  have h2 : (c.num * a.denI) * (b.denI * d.denI) < (d.num * b.denI) * (a.denI * c.denI) := by
    have hd : 0 < d.num * c.denI - c.num * d.denI := by omega
    have p := Int.mul_pos hd hab_pos
    rw [Int.sub_mul] at p
    have l : (c.num * a.denI) * (b.denI * d.denI) = (c.num * d.denI) * (a.denI * b.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_comm b.denI d.denI, Int.mul_left_comm a.denI d.denI]
    have r : (d.num * b.denI) * (a.denI * c.denI) = (d.num * c.denI) * (a.denI * b.denI) := by
      simp only [Int.mul_assoc]; rw [Int.mul_comm a.denI b.denI, Int.mul_left_comm c.denI b.denI, Int.mul_comm c.denI a.denI]
    omega
  omega

theorem mul_le_mul_of_nonneg_left {a b c : Q} (hc : (0 : Q) ≤q c) (hab : a ≤q b) : c * a ≤q c * b := by
  rw [zero_le_iff] at hc
  unfold le at *
  change (c.num * a.num) * (c * b).denI ≤ (c.num * b.num) * (c * a).denI
  rw [denI_mul, denI_mul]
  have hcd : 0 ≤ c.num * c.denI := Int.mul_nonneg hc (Int.le_of_lt (denI_pos c))
  have p := Int.mul_le_mul_of_nonneg_left hab hcd
  have l : (c.num * a.num) * (c.denI * b.denI) = (c.num * c.denI) * (a.num * b.denI) := by
    simp only [Int.mul_assoc]; rw [Int.mul_left_comm a.num c.denI]
  have r : (c.num * b.num) * (c.denI * a.denI) = (c.num * c.denI) * (b.num * a.denI) := by
    simp only [Int.mul_assoc]; rw [Int.mul_left_comm b.num c.denI]
  omega

theorem mul_nonneg {a b : Q} (ha : (0 : Q) ≤q a) (hb : (0 : Q) ≤q b) : (0 : Q) ≤q a * b := by
  rw [zero_le_iff] at *
  exact Int.mul_nonneg ha hb

theorem mul_pos {a b : Q} (ha : (0 : Q) <q a) (hb : (0 : Q) <q b) : (0 : Q) <q a * b := by
  rw [zero_lt_iff] at *
  exact Int.mul_pos ha hb

theorem sq_nonneg (a : Q) : (0 : Q) ≤q a * a := by
  rw [zero_le_iff]
  change 0 ≤ a.num * a.num
  rcases Int.le_total 0 a.num with h | h
  · exact Int.mul_nonneg h h
  · have hn : 0 ≤ -a.num := by omega
    have hsq : (-a.num) * (-a.num) = a.num * a.num := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← hsq]
    exact Int.mul_nonneg hn hn

theorem sq_pos_of_ne_zero {a : Q} (hne : ¬ (a ≈ 0)) : (0 : Q) <q a * a := by
  rw [eqv_zero_iff] at hne
  rw [zero_lt_iff]
  change 0 < a.num * a.num
  rcases Int.lt_or_gt_of_ne hne with h | h
  · have hn : 0 < -a.num := by omega
    have hsq : (-a.num) * (-a.num) = a.num * a.num := by
      rw [Int.neg_mul, Int.mul_neg, Int.neg_neg]
    rw [← hsq]
    exact Int.mul_pos hn hn
  · exact Int.mul_pos h h

theorem sub_nonneg_iff (a b : Q) : (0 : Q) ≤q a - b ↔ b ≤q a := by
  rw [zero_le_iff]
  unfold le
  change 0 ≤ a.num * b.denI + (-b.num) * a.denI ↔ b.num * a.denI ≤ a.num * b.denI
  rw [Int.neg_mul]; omega

theorem sub_pos_iff (a b : Q) : (0 : Q) <q a - b ↔ b <q a := by
  rw [zero_lt_iff]
  unfold lt
  change 0 < a.num * b.denI + (-b.num) * a.denI ↔ b.num * a.denI < a.num * b.denI
  rw [Int.neg_mul]; omega

theorem le_of_add_le_add_right {a b c : Q} (h : a + c ≤q b + c) : a ≤q b := by
  have h1 := add_le_add h (le_refl (-c))
  have ha : (a + c) - c ≈ a := add_sub_cancel a c
  have hb : (b + c) - c ≈ b := add_sub_cancel b c
  exact le_trans (le_of_eqv (eqv_symm ha)) (le_trans h1 (le_of_eqv hb))

/-! ### 유한합 (Fin n 기반) 및 핵심 합산 정리 -/

/-- Fin n 위의 유한합: f 0 + f 1 + ... + f (n-1) -/
def sumFin : {n : Nat} → (Fin n → Q) → Q
  | 0, _ => 0
  | n + 1, f => sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)

theorem sumFin_zero {n : Nat} : sumFin (fun _ : Fin n => (0 : Q)) ≈ 0 := by
  induction n with
  | zero => exact eqv_refl 0
  | succ n ih =>
    unfold sumFin
    exact eqv_trans (add_congr ih (eqv_refl 0)) (add_zero 0)

theorem sumFin_congr {n : Nat} {f g : Fin n → Q} (h : ∀ i, f i ≈ g i) :
    sumFin f ≈ sumFin g := by
  induction n with
  | zero => exact eqv_refl 0
  | succ n ih =>
    unfold sumFin
    exact add_congr (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem sumFin_add {n : Nat} (f g : Fin n → Q) :
    sumFin (fun i => f i + g i) ≈ sumFin f + sumFin g := by
  induction n with
  | zero => exact eqv_symm (add_zero 0)
  | succ n ih =>
    unfold sumFin
    have h1 := add_congr (ih (fun i => f i.castSucc) (fun i => g i.castSucc)) (eqv_refl (f (Fin.last n) + g (Fin.last n)))
    -- (sf + sg) + (fl + gl) ≈ (sf + fl) + (sg + gl)
    have hswap (a b c d : Q) : (a + b) + (c + d) ≈ (a + c) + (b + d) := by
      have s1 := add_assoc a b (c + d)
      have s2 : b + (c + d) ≈ c + (b + d) :=
        eqv_trans (eqv_symm (add_assoc b c d))
          (eqv_trans (add_congr (add_comm b c) (eqv_refl d)) (add_assoc c b d))
      have s3 := add_congr (eqv_refl a) s2
      have s4 := eqv_symm (add_assoc a c (b + d))
      exact eqv_trans (eqv_trans s1 s3) s4
    exact eqv_trans h1 (hswap _ _ _ _)

theorem sumFin_sub {n : Nat} (f g : Fin n → Q) :
    sumFin (fun i => f i - g i) ≈ sumFin f - sumFin g := by
  induction n with
  | zero => exact eqv_symm (sub_self 0)
  | succ n ih =>
    unfold sumFin
    -- sum (f - g) + (fl - gl) ≈ (sf - sg) + (fl - gl) ≈ (sf + fl) - (sg + gl)
    have hneg_add (x y : Q) : -(x + y) ≈ (-x) + (-y) := by
      unfold eqv
      change (-(x.num * y.denI + y.num * x.denI)) * ((-x) + (-y)).denI =
             ((-x.num) * y.denI + (-y.num) * x.denI) * (-(x + y)).denI
      rw [denI_neg, denI_add, denI_add, denI_neg, denI_neg]
      apply congrArg (· * (x.denI * y.denI))
      rw [Int.neg_mul, Int.neg_mul]
      omega
    have h1 := add_congr (ih (fun i => f i.castSucc) (fun i => g i.castSucc))
      (eqv_refl (f (Fin.last n) - g (Fin.last n)))
    have hswap (a b c d : Q) : (a + (-b)) + (c + (-d)) ≈ (a + c) + (-(b + d)) := by
      have s1 := add_assoc a (-b) (c + (-d))
      have s2 : (-b) + (c + (-d)) ≈ c + ((-b) + (-d)) :=
        eqv_trans (eqv_symm (add_assoc (-b) c (-d)))
          (eqv_trans (add_congr (add_comm (-b) c) (eqv_refl (-d))) (add_assoc c (-b) (-d)))
      have s3 := eqv_trans (add_congr (eqv_refl a) s2) (eqv_symm (add_assoc a c ((-b) + (-d))))
      exact eqv_trans (eqv_trans s1 s3) (add_congr (eqv_refl (a + c)) (eqv_symm (hneg_add b d)))
    exact eqv_trans h1 (hswap _ _ _ _)

theorem mul_sumFin {n : Nat} (c : Q) (f : Fin n → Q) :
    c * sumFin f ≈ sumFin (fun i => c * f i) := by
  induction n with
  | zero => exact mul_zero c
  | succ n ih =>
    unfold sumFin
    exact eqv_trans (mul_add c _ _) (add_congr (ih (fun i => f i.castSucc)) (eqv_refl _))

theorem sumFin_mul {n : Nat} (f : Fin n → Q) (c : Q) :
    sumFin f * c ≈ sumFin (fun i => f i * c) := by
  have h1 := mul_comm (sumFin f) c
  have h2 := mul_sumFin c f
  have h3 := sumFin_congr (fun i => mul_comm c (f i))
  exact eqv_trans (eqv_trans h1 h2) h3

theorem sumFin_comm {m n : Nat} (f : Fin m → Fin n → Q) :
    sumFin (fun i => sumFin (fun j => f i j)) ≈
    sumFin (fun j => sumFin (fun i => f i j)) := by
  induction m with
  | zero =>
    change (0 : Q) ≈ sumFin (fun _ : Fin n => (0 : Q))
    exact eqv_symm sumFin_zero
  | succ m ih =>
    change sumFin (fun i : Fin m => sumFin (fun j => f i.castSucc j)) +
           sumFin (fun j => f (Fin.last m) j) ≈
           sumFin (fun j => sumFin (fun i : Fin m => f i.castSucc j) + f (Fin.last m) j)
    have h1 := add_congr (ih (fun i j => f i.castSucc j)) (eqv_refl (sumFin (fun j => f (Fin.last m) j)))
    exact eqv_trans h1 (eqv_symm (sumFin_add (fun j => sumFin (fun i : Fin m => f i.castSucc j))
                                             (fun j => f (Fin.last m) j)))

theorem sumFin_le_sumFin {n : Nat} {f g : Fin n → Q} (h : ∀ i, f i ≤q g i) :
    sumFin f ≤q sumFin g := by
  induction n with
  | zero => exact le_refl 0
  | succ n ih =>
    unfold sumFin
    exact add_le_add (ih (fun i => h i.castSucc)) (h (Fin.last n))

theorem sumFin_nonneg {n : Nat} {f : Fin n → Q} (h : ∀ i, (0 : Q) ≤q f i) :
    (0 : Q) ≤q sumFin f := by
  have hle : sumFin (fun _ : Fin n => (0 : Q)) ≤q sumFin f := sumFin_le_sumFin h
  exact le_trans (le_of_eqv (eqv_symm sumFin_zero)) hle

theorem sumFin_pos_of_exists_pos {n : Nat} {f : Fin n → Q}
    (hnn : ∀ i, (0 : Q) ≤q f i) (k : Fin n) (hpos : (0 : Q) <q f k) :
    (0 : Q) <q sumFin f := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    change (0 : Q) <q sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n)
    revert hpos
    refine Fin.lastCases ?_ ?_ k
    · -- k = Fin.last n
      intro hpos
      have h1 : (0 : Q) ≤q sumFin (fun i : Fin n => f i.castSucc) :=
        sumFin_nonneg (fun i => hnn i.castSucc)
      have h2 := add_lt_add_of_le_of_lt h1 hpos
      exact lt_of_le_of_lt (le_of_eqv (eqv_symm (add_zero 0))) h2
    · -- k = j.castSucc
      intro j hpos
      have hj : (0 : Q) <q sumFin (fun i : Fin n => f i.castSucc) :=
        ih (fun i => hnn i.castSucc) j hpos
      have hlast : (0 : Q) ≤q f (Fin.last n) := hnn (Fin.last n)
      have h2 := add_lt_add_of_le_of_lt hlast hj
      have hcomm : f (Fin.last n) + sumFin (fun i : Fin n => f i.castSucc) ≈
                   sumFin (fun i : Fin n => f i.castSucc) + f (Fin.last n) := add_comm _ _
      exact lt_of_le_of_lt (le_of_eqv (eqv_symm (add_zero 0))) (lt_of_lt_of_le h2 (le_of_eqv hcomm))

/-- 내적 (dot product) -/
def dot {n : Nat} (u v : Fin n → Q) : Q :=
  sumFin (fun i => u i * v i)

/-- 대칭 내적 교환 법칙 -/
theorem dot_comm {n : Nat} (u v : Fin n → Q) : dot u v ≈ dot v u :=
  sumFin_congr (fun i => mul_comm (u i) (v i))

/-- 유한합 코시-슈바르츠 부등식: (∑ f_i g_i)^2 ≤ (∑ f_i^2) (∑ g_i^2) -/
theorem cauchy_schwarz {n : Nat} (f g : Fin n → Q) :
    (sumFin (fun i => f i * g i)) * (sumFin (fun i => f i * g i)) ≤q
    (sumFin (fun i => f i * f i)) * (sumFin (fun i => g i * g i)) := by
  -- 2 * ((∑ f^2)(∑ g^2) - (∑ f g)^2) = ∑_i ∑_j (f_i g_j - f_j g_i)^2 ≥ 0 을 직접 증명
  -- 우선 전개 항등식: ∑_i ∑_j (f_i g_j - f_j g_i)^2 ≥ 0
  have hnonneg : (0 : Q) ≤q
      sumFin (fun i => sumFin (fun j => (f i * g j - f j * g i) * (f i * g j - f j * g i))) :=
    sumFin_nonneg (fun i => sumFin_nonneg (fun j => sq_nonneg _))
  -- (a - b)^2 = a^2 + b^2 - 2ab 보조정리
  have hsq_sub (a b : Q) : (a - b) * (a - b) ≈ (a * a + b * b) - (a * b + a * b) := by
    -- 직접 전개
    have e1 := add_mul a (-b) (a - b)
    have e2 := mul_add a a (-b)
    have e3 := mul_add (-b) a (-b)
    have e4 : a * (-b) ≈ -(a * b) := eqv_trans (mul_comm a (-b)) (eqv_trans (neg_mul b a) (neg_congr (mul_comm b a)))
    have e5 : (-b) * a ≈ -(a * b) := eqv_trans (neg_mul b a) (neg_congr (mul_comm b a))
    have e6 : (-b) * (-b) ≈ b * b := by
      unfold eqv
      change ((-b.num) * (-b.num)) * (b * b).denI = (b.num * b.num) * ((-b) * (-b)).denI
      rw [denI_mul, denI_mul, denI_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg]
    have hstep := eqv_trans e1 (add_congr (eqv_trans e2 (add_congr (eqv_refl _) e4))
                                          (eqv_trans e3 (add_congr e5 e6)))
    -- (a*a + -(a*b)) + (-(a*b) + b*b) ≈ (a*a + b*b) + -(a*b + a*b)
    have hrearr (x y z : Q) : (x + (-y)) + ((-y) + z) ≈ (x + z) - (y + y) := by
      have hny : -(y + y) ≈ (-y) + (-y) := by
        unfold eqv
        change (-(y.num * y.denI + y.num * y.denI)) * ((-y) + (-y)).denI =
               ((-y.num) * y.denI + (-y.num) * y.denI) * (-(y + y)).denI
        rw [denI_neg, denI_add, denI_add, denI_neg]
        apply congrArg (· * (y.denI * y.denI))
        rw [Int.neg_mul]
        omega
      -- 재배열
      have p1 := add_assoc x (-y) ((-y) + z)
      have p2 : (-y) + ((-y) + z) ≈ z + ((-y) + (-y)) :=
        eqv_trans (eqv_symm (add_assoc (-y) (-y) z)) (add_comm ((-y) + (-y)) z)
      have p3 := eqv_trans (add_congr (eqv_refl x) p2) (eqv_symm (add_assoc x z ((-y) + (-y))))
      exact eqv_trans (eqv_trans p1 p3) (add_congr (eqv_refl (x + z)) (eqv_symm hny))
    exact eqv_trans hstep (hrearr (a * a) (a * b) (b * b))
  -- 이중합 분리
  let Sff := sumFin (fun i => f i * f i)
  let Sgg := sumFin (fun i => g i * g i)
  let Sfg := sumFin (fun i => f i * g i)
  -- 각 항 (f_i g_j)^2 = (f_i^2)(g_j^2), (f_i g_j)(f_j g_i) = (f_i g_i)(f_j g_j)
  have hterm (i j : Fin n) :
      (f i * g j - f j * g i) * (f i * g j - f j * g i) ≈
      ((f i * f i) * (g j * g j) + (f j * f j) * (g i * g i)) -
      ((f i * g i) * (f j * g j) + (f i * g i) * (f j * g j)) := by
    have t1 : (f i * g j) * (f i * g j) ≈ (f i * f i) * (g j * g j) := by
      have p1 := mul_assoc (f i) (g j) (f i * g j)
      have p2 : g j * (f i * g j) ≈ f i * (g j * g j) :=
        eqv_trans (eqv_symm (mul_assoc (g j) (f i) (g j)))
          (eqv_trans (mul_congr (mul_comm (g j) (f i)) (eqv_refl (g j))) (mul_assoc (f i) (g j) (g j)))
      exact eqv_trans (eqv_trans p1 (mul_congr (eqv_refl (f i)) p2)) (eqv_symm (mul_assoc (f i) (f i) (g j * g j)))
    have t2 : (f j * g i) * (f j * g i) ≈ (f j * f j) * (g i * g i) := by
      have p1 := mul_assoc (f j) (g i) (f j * g i)
      have p2 : g i * (f j * g i) ≈ f j * (g i * g i) :=
        eqv_trans (eqv_symm (mul_assoc (g i) (f j) (g i)))
          (eqv_trans (mul_congr (mul_comm (g i) (f j)) (eqv_refl (g i))) (mul_assoc (f j) (g i) (g i)))
      exact eqv_trans (eqv_trans p1 (mul_congr (eqv_refl (f j)) p2)) (eqv_symm (mul_assoc (f j) (f j) (g i * g i)))
    have t3 : (f i * g j) * (f j * g i) ≈ (f i * g i) * (f j * g j) := by
      have p1 := mul_assoc (f i) (g j) (f j * g i)
      have p2 : g j * (f j * g i) ≈ g i * (f j * g j) :=
        eqv_trans (mul_comm (g j) (f j * g i))
          (eqv_trans (mul_assoc (f j) (g i) (g j))
            (eqv_trans (mul_comm (f j) (g i * g j))
              (eqv_trans (mul_assoc (g i) (g j) (f j))
                (mul_congr (eqv_refl (g i)) (mul_comm (g j) (f j))))))
      exact eqv_trans (eqv_trans p1 (mul_congr (eqv_refl (f i)) p2))
        (eqv_symm (mul_assoc (f i) (g i) (f j * g j)))
    exact eqv_trans (hsq_sub (f i * g j) (f j * g i))
      (sub_congr (add_congr t1 t2) (add_congr t3 t3))
  -- 이중합 계산: ∑_i ∑_j (...) ≈ (Sff*Sgg + Sff*Sgg) - (Sfg*Sfg + Sfg*Sfg)
  have hsum_eq :
      sumFin (fun i => sumFin (fun j => (f i * g j - f j * g i) * (f i * g j - f j * g i))) ≈
      (Sff * Sgg + Sff * Sgg) - (Sfg * Sfg + Sfg * Sfg) := by
    have h1 := sumFin_congr (fun i => sumFin_congr (fun j => hterm i j))
    -- 각 이중합을 분리
    have hA : sumFin (fun i => sumFin (fun j => (f i * f i) * (g j * g j))) ≈ Sff * Sgg := by
      have s1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (f i * f i) (fun j => g j * g j)))
      exact eqv_trans s1 (eqv_symm (sumFin_mul (fun i => f i * f i) Sgg))
    have hB : sumFin (fun i => sumFin (fun j => (f j * f j) * (g i * g i))) ≈ Sff * Sgg := by
      have s1 := sumFin_comm (fun i j => (f j * f j) * (g i * g i))
      exact eqv_trans s1 hA
    have hC : sumFin (fun i => sumFin (fun j => (f i * g i) * (f j * g j))) ≈ Sfg * Sfg := by
      have s1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (f i * g i) (fun j => f j * g j)))
      exact eqv_trans s1 (eqv_symm (sumFin_mul (fun i => f i * g i) Sfg))
    -- 합/차 분배
    have hsplit :
        sumFin (fun i => sumFin (fun j =>
          ((f i * f i) * (g j * g j) + (f j * f j) * (g i * g i)) -
          ((f i * g i) * (f j * g j) + (f i * g i) * (f j * g j)))) ≈
        (Sff * Sgg + Sff * Sgg) - (Sfg * Sfg + Sfg * Sfg) := by
      have inner_sub (i : Fin n) :=
        sumFin_sub
          (fun j => (f i * f i) * (g j * g j) + (f j * f j) * (g i * g i))
          (fun j => (f i * g i) * (f j * g j) + (f i * g i) * (f j * g j))
      have outer_sub := eqv_trans (sumFin_congr inner_sub)
        (sumFin_sub
          (fun i => sumFin (fun j => (f i * f i) * (g j * g j) + (f j * f j) * (g i * g i)))
          (fun i => sumFin (fun j => (f i * g i) * (f j * g j) + (f i * g i) * (f j * g j))))
      have left_add :=
        eqv_trans
          (sumFin_congr (fun i => sumFin_add (fun j => (f i * f i) * (g j * g j))
                                             (fun j => (f j * f j) * (g i * g i))))
          (eqv_trans (sumFin_add _ _) (add_congr hA hB))
      have right_add :=
        eqv_trans
          (sumFin_congr (fun i => sumFin_add (fun j => (f i * g i) * (f j * g j))
                                             (fun j => (f i * g i) * (f j * g j))))
          (eqv_trans (sumFin_add _ _) (add_congr hC hC))
      exact eqv_trans outer_sub (sub_congr left_add right_add)
    exact eqv_trans h1 hsplit
  have hge0 : (0 : Q) ≤q (Sff * Sgg + Sff * Sgg) - (Sfg * Sfg + Sfg * Sfg) :=
    le_trans hnonneg (le_of_eqv hsum_eq)
  rw [sub_nonneg_iff] at hge0
  -- x + x ≤ y + y → x ≤ y
  have h2x (x y : Q) (h : x + x ≤q y + y) : x ≤q y := by
    unfold le at *
    change (x.num * x.denI + x.num * x.denI) * (y + y).denI ≤
           (y.num * y.denI + y.num * y.denI) * (x + x).denI at h
    rw [denI_add, denI_add] at h
    have hx := denI_pos x
    have hy := denI_pos y
    have hxy : 0 < x.denI * y.denI := Int.mul_pos hx hy
    have l : (x.num * x.denI + x.num * x.denI) * (y.denI * y.denI) =
             (2 * (x.num * y.denI)) * (x.denI * y.denI) := by
      have : x.num * x.denI + x.num * x.denI = 2 * (x.num * x.denI) := by omega
      rw [this]; simp only [Int.mul_assoc]; rw [Int.mul_left_comm x.denI y.denI]
    have r : (y.num * y.denI + y.num * y.denI) * (x.denI * x.denI) =
             (2 * (y.num * x.denI)) * (x.denI * y.denI) := by
      have : y.num * y.denI + y.num * y.denI = 2 * (y.num * y.denI) := by omega
      rw [this]; simp only [Int.mul_assoc]; rw [Int.mul_left_comm y.denI x.denI, Int.mul_comm y.denI x.denI]
    rw [l, r] at h
    have h2 := int_le_of_mul_pos hxy h
    omega
  exact h2x (Sfg * Sfg) (Sff * Sgg) hge0

/-- 순서 반대칭성: a ≤ b 이고 b ≤ a 이면 a ≈ b -/
theorem eqv_of_le_of_le {a b : Q} (hab : a ≤q b) (hba : b ≤q a) : a ≈ b := by
  unfold le eqv at *
  omega

/-- 양의 유리수의 정확한 역수 (b > 0 일 때 b⁻¹) -/
def invPos (b : Q) (hb : (0 : Q) <q b) : Q :=
  ⟨b.denI, b.num.toNat, by
    have hnum : (0 : Int) < b.num := (zero_lt_iff b).mp hb
    omega⟩

/-- 역수 소거 항등식: invPos b hb * b ≈ 1 -/
theorem invPos_mul_cancel (b : Q) (hb : (0 : Q) <q b) : invPos b hb * b ≈ 1 := by
  unfold eqv invPos
  have hnum : (0 : Int) < b.num := (zero_lt_iff b).mp hb
  have htoNat : Int.ofNat b.num.toNat = b.num := Int.toNat_of_nonneg (Int.le_of_lt hnum)
  have hden_mul : ((⟨b.denI, b.num.toNat, by omega⟩ : Q) * b).denI = b.num * b.denI := by
    rw [denI_mul]
    unfold denI
    change Int.ofNat b.num.toNat * Int.ofNat b.den = b.num * Int.ofNat b.den
    rw [htoNat]
  change (b.denI * b.num) * (1 : Int) = (1 : Int) * ((⟨b.denI, b.num.toNat, by omega⟩ : Q) * b).denI
  rw [hden_mul, Int.mul_one, Int.one_mul, Int.mul_comm]

/-- 역수 우측 소거 항등식: b * invPos b hb ≈ 1 -/
theorem mul_invPos_cancel (b : Q) (hb : (0 : Q) <q b) : b * invPos b hb ≈ 1 :=
  eqv_trans (mul_comm b (invPos b hb)) (invPos_mul_cancel b hb)

/-- 음수 곱셈 부호: a * (-b) ≈ -(a * b) -/
theorem mul_neg (a b : Q) : a * (-b) ≈ -(a * b) :=
  eqv_trans (mul_comm a (-b)) (eqv_trans (neg_mul b a) (neg_congr (mul_comm b a)))

/-- 이중 음수 곱셈: (-a) * (-b) ≈ a * b -/
theorem neg_mul_neg (a b : Q) : (-a) * (-b) ≈ a * b := by
  unfold eqv
  change ((-a.num) * (-b.num)) * (a * b).denI = (a.num * b.num) * ((-a) * (-b)).denI
  rw [denI_mul, denI_mul, denI_neg, denI_neg, Int.neg_mul, Int.mul_neg, Int.neg_neg]

/-- 제곱 상계로부터 하한 도출: B ≥ 0 이고 x^2 ≤ B^2 이면 -B ≤ x -/
theorem neg_le_of_sq_le_sq {x B : Q} (hB_nn : (0 : Q) ≤q B) (hsq : x * x ≤q B * B) :
    -B ≤q x := by
  by_cases hge : -B ≤q x
  · exact hge
  · have hx_lt : x <q -B := by
      unfold le lt at *
      omega
    have hpos_neg : B <q -x := by
      unfold lt at *
      change B.num * x.denI < (-x.num) * B.denI
      change x.num * B.denI < (-B.num) * x.denI at hx_lt
      rw [Int.neg_mul] at hx_lt ⊢
      omega
    have hnx_pos : (0 : Q) <q -x := lt_of_le_of_lt hB_nn hpos_neg
    have stepA : B * B ≤q B * (-x) := mul_le_mul_of_nonneg_left hB_nn (le_of_lt hpos_neg)
    have stepB : B * (-x) <q (-x) * (-x) := by
      have hdiff : (0 : Q) <q (-x) - B := (sub_pos_iff (-x) B).mpr hpos_neg
      have hprod : (0 : Q) <q (-x) * ((-x) - B) := mul_pos hnx_pos hdiff
      have heq : (-x) * ((-x) - B) ≈ (-x) * (-x) - B * (-x) := by
        have d1 := mul_add (-x) (-x) (-B)
        have d2 : (-x) * (-B) ≈ -(B * (-x)) :=
          eqv_trans (mul_comm (-x) (-B)) (neg_mul B (-x))
        exact eqv_trans d1 (add_congr (eqv_refl _) d2)
      have hpos_sub : (0 : Q) <q (-x) * (-x) - B * (-x) := lt_of_lt_of_le hprod (le_of_eqv heq)
      exact (sub_pos_iff _ _).mp hpos_sub
    have hB_lt_x : B * B <q x * x :=
      lt_of_lt_of_le (lt_of_le_of_lt stepA stepB) (le_of_eqv (neg_mul_neg x x))
    exact False.elim (not_lt_of_le hsq hB_lt_x)

/-- 가중 코시-슈바르츠 부등식 (무리수 √p 없이 순수 유리수 라그랑주 항등식 증명):
    ∀ i, p_i ≥ 0 이면 (∑ p_i f_i g_i)^2 ≤ (∑ p_i f_i^2) * (∑ p_i g_i^2) -/
theorem weighted_cauchy_schwarz {n : Nat} (p f g : Fin n → Q)
    (hp : ∀ i, (0 : Q) ≤q p i) :
    sumFin (fun i => p i * (f i * g i)) * sumFin (fun i => p i * (f i * g i)) ≤q
    sumFin (fun i => p i * (f i * f i)) * sumFin (fun i => p i * (g i * g i)) := by
  have hnonneg : (0 : Q) ≤q
      sumFin (fun i => sumFin (fun j =>
        (p i * p j) * ((f i * g j - f j * g i) * (f i * g j - f j * g i)))) :=
    sumFin_nonneg (fun i => sumFin_nonneg (fun j =>
      mul_nonneg (mul_nonneg (hp i) (hp j)) (sq_nonneg (f i * g j - f j * g i))))
  have hsq_sub (a b : Q) : (a - b) * (a - b) ≈ (a * a + b * b) - (a * b + a * b) := by
    have e1 := add_mul a (-b) (a - b)
    have e2 := mul_add a a (-b)
    have e3 := mul_add (-b) a (-b)
    have e4 : a * (-b) ≈ -(a * b) := mul_neg a b
    have e5 : (-b) * a ≈ -(a * b) := eqv_trans (neg_mul b a) (neg_congr (mul_comm b a))
    have e6 : (-b) * (-b) ≈ b * b := neg_mul_neg b b
    have hstep := eqv_trans e1 (add_congr (eqv_trans e2 (add_congr (eqv_refl _) e4))
                                          (eqv_trans e3 (add_congr e5 e6)))
    have hrearr (x y z : Q) : (x + (-y)) + ((-y) + z) ≈ (x + z) - (y + y) := by
      have hny : -(y + y) ≈ (-y) + (-y) := by
        unfold eqv
        change (-(y.num * y.denI + y.num * y.denI)) * ((-y) + (-y)).denI =
               ((-y.num) * y.denI + (-y.num) * y.denI) * (-(y + y)).denI
        rw [denI_neg, denI_add, denI_add, denI_neg]
        apply congrArg (· * (y.denI * y.denI))
        rw [Int.neg_mul]
        omega
      have p1 := add_assoc x (-y) ((-y) + z)
      have p2 : (-y) + ((-y) + z) ≈ z + ((-y) + (-y)) :=
        eqv_trans (eqv_symm (add_assoc (-y) (-y) z)) (add_comm ((-y) + (-y)) z)
      have p3 := eqv_trans (add_congr (eqv_refl x) p2) (eqv_symm (add_assoc x z ((-y) + (-y))))
      exact eqv_trans (eqv_trans p1 p3) (add_congr (eqv_refl (x + z)) (eqv_symm hny))
    exact eqv_trans hstep (hrearr (a * a) (a * b) (b * b))
  have hmul4 (a b c d : Q) : (a * b) * (c * d) ≈ (a * c) * (b * d) := by
    have q1 := mul_assoc a b (c * d)
    have q2 : b * (c * d) ≈ c * (b * d) :=
      eqv_trans (eqv_symm (mul_assoc b c d))
        (eqv_trans (mul_congr (mul_comm b c) (eqv_refl d)) (mul_assoc c b d))
    exact eqv_trans (eqv_trans q1 (mul_congr (eqv_refl a) q2)) (eqv_symm (mul_assoc a c (b * d)))
  let Sff := sumFin (fun i => p i * (f i * f i))
  let Sgg := sumFin (fun i => p i * (g i * g i))
  let Sfg := sumFin (fun i => p i * (f i * g i))
  have hterm (i j : Fin n) :
      (p i * p j) * ((f i * g j - f j * g i) * (f i * g j - f j * g i)) ≈
      ((p i * (f i * f i)) * (p j * (g j * g j)) + (p j * (f j * f j)) * (p i * (g i * g i))) -
      ((p i * (f i * g i)) * (p j * (f j * g j)) + (p i * (f i * g i)) * (p j * (f j * g j))) := by
    have t1 : (f i * g j) * (f i * g j) ≈ (f i * f i) * (g j * g j) := hmul4 (f i) (g j) (f i) (g j)
    have t2 : (f j * g i) * (f j * g i) ≈ (f j * f j) * (g i * g i) := hmul4 (f j) (g i) (f j) (g i)
    have t3 : (f i * g j) * (f j * g i) ≈ (f i * g i) * (f j * g j) := by
      have q1 := hmul4 (f i) (g j) (f j) (g i)
      have q2 := mul_congr (eqv_refl (f i * f j)) (mul_comm (g j) (g i))
      exact eqv_trans (eqv_trans q1 q2) (hmul4 (f i) (f j) (g i) (g j))
    have hinner := eqv_trans (hsq_sub (f i * g j) (f j * g i))
      (sub_congr (add_congr t1 t2) (add_congr t3 t3))
    have hmul_sub (w a b : Q) : w * (a - b) ≈ w * a - w * b :=
      eqv_trans (mul_add w a (-b)) (add_congr (eqv_refl (w * a)) (mul_neg w b))
    have hdist1 := eqv_trans (mul_congr (eqv_refl (p i * p j)) hinner)
      (hmul_sub (p i * p j)
        ((f i * f i) * (g j * g j) + (f j * f j) * (g i * g i))
        ((f i * g i) * (f j * g j) + (f i * g i) * (f j * g j)))
    have hdist2 := sub_congr
      (mul_add (p i * p j) ((f i * f i) * (g j * g j)) ((f j * f j) * (g i * g i)))
      (mul_add (p i * p j) ((f i * g i) * (f j * g j)) ((f i * g i) * (f j * g j)))
    have ha : (p i * p j) * ((f i * f i) * (g j * g j)) ≈ (p i * (f i * f i)) * (p j * (g j * g j)) :=
      hmul4 (p i) (p j) (f i * f i) (g j * g j)
    have hb : (p i * p j) * ((f j * f j) * (g i * g i)) ≈ (p j * (f j * f j)) * (p i * (g i * g i)) :=
      eqv_trans (mul_congr (mul_comm (p i) (p j)) (eqv_refl _))
        (hmul4 (p j) (p i) (f j * f j) (g i * g i))
    have hc : (p i * p j) * ((f i * g i) * (f j * g j)) ≈ (p i * (f i * g i)) * (p j * (f j * g j)) :=
      hmul4 (p i) (p j) (f i * g i) (f j * g j)
    exact eqv_trans (eqv_trans hdist1 hdist2) (sub_congr (add_congr ha hb) (add_congr hc hc))
  have hsum_eq :
      sumFin (fun i => sumFin (fun j =>
        (p i * p j) * ((f i * g j - f j * g i) * (f i * g j - f j * g i)))) ≈
      (Sff * Sgg + Sff * Sgg) - (Sfg * Sfg + Sfg * Sfg) := by
    have h1 := sumFin_congr (fun i => sumFin_congr (fun j => hterm i j))
    have hA : sumFin (fun i => sumFin (fun j => (p i * (f i * f i)) * (p j * (g j * g j)))) ≈ Sff * Sgg := by
      have s1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (p i * (f i * f i)) (fun j => p j * (g j * g j))))
      exact eqv_trans s1 (eqv_symm (sumFin_mul (fun i => p i * (f i * f i)) Sgg))
    have hB : sumFin (fun i => sumFin (fun j => (p j * (f j * f j)) * (p i * (g i * g i)))) ≈ Sff * Sgg :=
      eqv_trans (sumFin_comm (fun i j => (p j * (f j * f j)) * (p i * (g i * g i)))) hA
    have hC : sumFin (fun i => sumFin (fun j => (p i * (f i * g i)) * (p j * (f j * g j)))) ≈ Sfg * Sfg := by
      have s1 := sumFin_congr (fun i => eqv_symm (mul_sumFin (p i * (f i * g i)) (fun j => p j * (f j * g j))))
      exact eqv_trans s1 (eqv_symm (sumFin_mul (fun i => p i * (f i * g i)) Sfg))
    have inner_sub (i : Fin n) :=
      sumFin_sub
        (fun j => (p i * (f i * f i)) * (p j * (g j * g j)) + (p j * (f j * f j)) * (p i * (g i * g i)))
        (fun j => (p i * (f i * g i)) * (p j * (f j * g j)) + (p i * (f i * g i)) * (p j * (f j * g j)))
    have outer_sub := eqv_trans (sumFin_congr inner_sub)
      (sumFin_sub
        (fun i => sumFin (fun j =>
          (p i * (f i * f i)) * (p j * (g j * g j)) + (p j * (f j * f j)) * (p i * (g i * g i))))
        (fun i => sumFin (fun j =>
          (p i * (f i * g i)) * (p j * (f j * g j)) + (p i * (f i * g i)) * (p j * (f j * g j)))))
    have left_add := eqv_trans
      (sumFin_congr (fun i => sumFin_add
        (fun j => (p i * (f i * f i)) * (p j * (g j * g j)))
        (fun j => (p j * (f j * f j)) * (p i * (g i * g i)))))
      (eqv_trans (sumFin_add _ _) (add_congr hA hB))
    have right_add := eqv_trans
      (sumFin_congr (fun i => sumFin_add
        (fun j => (p i * (f i * g i)) * (p j * (f j * g j)))
        (fun j => (p i * (f i * g i)) * (p j * (f j * g j)))))
      (eqv_trans (sumFin_add _ _) (add_congr hC hC))
    exact eqv_trans h1 (eqv_trans outer_sub (sub_congr left_add right_add))
  have hge0 : (0 : Q) ≤q (Sff * Sgg + Sff * Sgg) - (Sfg * Sfg + Sfg * Sfg) :=
    le_trans hnonneg (le_of_eqv hsum_eq)
  rw [sub_nonneg_iff] at hge0
  have h2x (x y : Q) (h : x + x ≤q y + y) : x ≤q y := by
    unfold le at *
    change (x.num * x.denI + x.num * x.denI) * (y + y).denI ≤
           (y.num * y.denI + y.num * y.denI) * (x + x).denI at h
    rw [denI_add, denI_add] at h
    have hx := denI_pos x
    have hy := denI_pos y
    have hxy : 0 < x.denI * y.denI := Int.mul_pos hx hy
    have l : (x.num * x.denI + x.num * x.denI) * (y.denI * y.denI) =
             (2 * (x.num * y.denI)) * (x.denI * y.denI) := by
      have : x.num * x.denI + x.num * x.denI = 2 * (x.num * x.denI) := by omega
      rw [this]; simp only [Int.mul_assoc]; rw [Int.mul_left_comm x.denI y.denI]
    have r : (y.num * y.denI + y.num * y.denI) * (x.denI * x.denI) =
             (2 * (y.num * x.denI)) * (x.denI * y.denI) := by
      have : y.num * y.denI + y.num * y.denI = 2 * (y.num * y.denI) := by omega
      rw [this]; simp only [Int.mul_assoc]; rw [Int.mul_left_comm y.denI x.denI, Int.mul_comm y.denI x.denI]
    rw [l, r] at h
    have h2 := int_le_of_mul_pos hxy h
    omega
  exact h2x (Sfg * Sfg) (Sff * Sgg) hge0

end Q
end CertMat
