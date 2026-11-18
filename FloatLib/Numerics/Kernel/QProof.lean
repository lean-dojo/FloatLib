/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Q
public import FloatLib.Numerics.Kernel.ZProof

public import Mathlib.Data.Rat.Floor

/-!
# The kernel `Rat` operations are the `Rat` operations

Each function of `FloatLib.Numerics.Kernel.Q` equals the operation of core Lean and Mathlib it
stands for, for all rationals: `normalize_eq`, `mk_eq` (`mkRat`), `add_eq`, `sub_eq`, `mul_eq`,
`neg_eq`, `inv_eq`, `div_eq`, `pow_eq`, `abs_eq`, `mulPow2_eq`, `divPow2_eq`, `min_eq`, `max_eq`,
`floor_eq`, `ceil_eq`, and the Boolean comparisons decide the order and equality (`le_iff`,
`lt_iff`, `beq_iff`, and `le_eq_decide`, `lt_eq_decide`, `beq_eq_decide`). The equations are
`simp` lemmas, so a proof that unfolds a definition written with these functions sees ordinary
notation.

The theorems named `…_eq_compiled` are tagged `@[csimp]`: compiled code runs core's operation in
place of each kernel function.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Q

/-- `Q.normalize` is `Rat.normalize`. -/
@[simp] theorem normalize_eq (num : Int) (den : Nat) (h : den ≠ 0) :
    normalize num den h = Rat.normalize num den h := by
  rw [Rat.normalize_eq]
  apply Rat.ext
  · change Z.tdivNat num (Nat.gcd (Z.natAbs num) den) = num / ((num.natAbs.gcd den : Nat) : Int)
    rw [Z.tdivNat_eq, Z.natAbs_eq]
    exact Int.tdiv_eq_ediv_of_dvd (Rat.normalize.dvd_num rfl)
  · change den / Nat.gcd (Z.natAbs num) den = den / num.natAbs.gcd den
    rw [Z.natAbs_eq]

/-- `Q.mk` is `mkRat`. -/
@[simp] theorem mk_eq (num : Int) (den : Nat) : mk num den = mkRat num den := by
  cases den with
  | zero => rfl
  | succ k =>
    change normalize num (k + 1) (Nat.succ_ne_zero k) = _
    rw [normalize_eq, Rat.normalize_eq_mkRat]

/-- `Q.add` is the sum. -/
@[simp] theorem add_eq (a b : ℚ) : add a b = a + b := by
  unfold add
  rw [normalize_eq, Rat.normalize_eq_mkRat, Rat.add_def', Z.add_eq, Z.mul_eq, Z.mul_eq]
  rfl

/-- `Q.sub` is the difference. -/
@[simp] theorem sub_eq (a b : ℚ) : sub a b = a - b := by
  unfold sub
  rw [normalize_eq, Rat.normalize_eq_mkRat, Rat.sub_def', Z.sub_eq, Z.mul_eq, Z.mul_eq]
  rfl

/-- `Q.mul` is the product. -/
@[simp] theorem mul_eq (a b : ℚ) : mul a b = a * b := by
  unfold mul
  rw [normalize_eq, Rat.normalize_eq_mkRat, Rat.mul_def', Z.mul_eq]
  rfl

/-- `Q.neg` is the negation. -/
@[simp] theorem neg_eq (a : ℚ) : neg a = -a := by
  apply Rat.ext
  · change Z.neg a.num = (-a).num
    rw [Z.neg_eq, Rat.neg_num]
  · rfl

/-- `Q.inv` is the inverse. -/
@[simp] theorem inv_eq (a : ℚ) : inv a = a⁻¹ := by
  rw [Rat.inv_def]
  unfold inv
  cases a.num with
  | ofNat n =>
    change mk (Int.ofNat a.den) n = _
    rw [mk_eq]
    rfl
  | negSucc n =>
    change mk (Z.negOfNat a.den) (n + 1) = _
    rw [mk_eq, Z.negOfNat_eq]
    exact (Rat.normalize_eq_mkRat (Nat.succ_ne_zero n)).symm

/-- `Q.div` is the quotient. -/
@[simp] theorem div_eq (a b : ℚ) : div a b = a / b := by
  unfold div
  rw [mul_eq, inv_eq, div_eq_mul_inv]

/-- `Q.pow` is the power. -/
@[simp] theorem pow_eq (a : ℚ) (n : Nat) : pow a n = a ^ n := by
  apply Rat.ext
  · change Z.pow a.num n = (a ^ n).num
    rw [Z.pow_eq, Rat.num_pow]
  · change a.den ^ n = (a ^ n).den
    rw [Rat.den_pow]

/-- `Q.abs` is the absolute value. -/
@[simp] theorem abs_eq (a : ℚ) : abs a = |a| := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]
    apply Rat.ext
    · change ((Z.natAbs a.num : Nat) : Int) = a.num
      rw [Z.natAbs_eq]
      exact Int.natAbs_of_nonneg (Rat.num_nonneg.2 h)
    · rfl
  · rw [abs_of_nonpos h]
    apply Rat.ext
    · change ((Z.natAbs a.num : Nat) : Int) = (-a).num
      rw [Z.natAbs_eq, Rat.neg_num]
      exact Int.ofNat_natAbs_of_nonpos (Rat.num_nonpos.2 h)
    · rfl

/-- `Q.mulPow2` multiplies by `2 ^ k`. -/
@[simp] theorem mulPow2_eq (a : ℚ) (k : Nat) : mulPow2 a k = a * 2 ^ k := by
  have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 a.den_nz
  unfold mulPow2
  rw [normalize_eq, Rat.normalize_eq_mkRat, Rat.mkRat_eq_div, Z.shiftLeft_eq, Int.shiftLeft_eq]
  conv_rhs => rw [← Rat.num_div_den a]
  push_cast
  field_simp

/-- `Q.divPow2` divides by `2 ^ k`. -/
@[simp] theorem divPow2_eq (a : ℚ) (k : Nat) : divPow2 a k = a / 2 ^ k := by
  have hden : (a.den : ℚ) ≠ 0 := Nat.cast_ne_zero.2 a.den_nz
  unfold divPow2
  rw [normalize_eq, Rat.normalize_eq_mkRat, Rat.mkRat_eq_div]
  change (a.num : ℚ) / ((a.den <<< k : Nat) : ℚ) = _
  rw [Nat.shiftLeft_eq]
  conv_rhs => rw [← Rat.num_div_den a]
  push_cast
  field_simp

/-- `Q.le` decides `≤`. -/
theorem le_iff (a b : ℚ) : le a b = true ↔ a ≤ b := by
  unfold le
  rw [Z.ble'_iff, Z.mul_eq, Z.mul_eq, Rat.le_iff]
  rfl

/-- `Q.lt` decides `<`. -/
theorem lt_iff (a b : ℚ) : lt a b = true ↔ a < b := by
  unfold lt
  rw [Z.blt'_iff, Z.mul_eq, Z.mul_eq, Rat.lt_iff]
  rfl

/-- `Q.beq` decides equality. -/
theorem beq_iff (a b : ℚ) : beq a b = true ↔ a = b := by
  have hrec : ∀ x y : Bool, Bool.rec (motive := fun _ => Bool) false y x = (x && y) := by
    intro x y
    cases x <;> rfl
  unfold beq
  rw [hrec, Bool.and_eq_true, Z.beq'_iff, Nat.beq_eq]
  constructor
  · rintro ⟨hnum, hden⟩
    exact Rat.ext hnum hden
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- `Q.le` is the decision of `≤`. -/
@[simp] theorem le_eq_decide (a b : ℚ) : le a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, le_iff, decide_eq_true_eq]

/-- `Q.lt` is the decision of `<`. -/
@[simp] theorem lt_eq_decide (a b : ℚ) : lt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, lt_iff, decide_eq_true_eq]

/-- `Q.beq` is the decision of equality. -/
@[simp] theorem beq_eq_decide (a b : ℚ) : beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, beq_iff, decide_eq_true_eq]

/-- A `Bool.casesOn` on `Q.le` is the `if` on `≤`. -/
theorem casesOn_le {α : Sort*} (a b : ℚ) (e t : α) :
    Bool.casesOn (motive := fun _ => α) (le a b) e t = if a ≤ b then t else e :=
  Z.casesOn_eq_ite (le_iff a b) e t

/-- A `Bool.casesOn` on `Q.lt` is the `if` on `<`. -/
theorem casesOn_lt {α : Sort*} (a b : ℚ) (e t : α) :
    Bool.casesOn (motive := fun _ => α) (lt a b) e t = if a < b then t else e :=
  Z.casesOn_eq_ite (lt_iff a b) e t

/-- The absolute value of a rational is the absolute value of its numerator over its denominator. -/
theorem abs_eq_natAbs_div (a : ℚ) : |a| = (a.num.natAbs : ℚ) / a.den := by
  have hden : (0 : ℚ) < a.den := Nat.cast_pos.2 a.den_pos
  conv_lhs => rw [← Rat.num_div_den a]
  rw [abs_div, abs_of_pos hden, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]

/-- `Q.min` is the smaller of the two. -/
@[simp] theorem min_eq (a b : ℚ) : min a b = Min.min a b := by
  unfold min
  cases h : le a b with
  | false =>
    have hlt : ¬a ≤ b := fun hle => by rw [(le_iff a b).2 hle] at h; exact Bool.noConfusion h
    exact (min_eq_right (le_of_not_ge hlt)).symm
  | true => exact (min_eq_left ((le_iff a b).1 h)).symm

/-- `Q.max` is the larger of the two. -/
@[simp] theorem max_eq (a b : ℚ) : max a b = Max.max a b := by
  unfold max
  cases h : le a b with
  | false =>
    have hlt : ¬a ≤ b := fun hle => by rw [(le_iff a b).2 hle] at h; exact Bool.noConfusion h
    exact (max_eq_left (le_of_not_ge hlt)).symm
  | true => exact (max_eq_right ((le_iff a b).1 h)).symm

/-- `Q.floor` is the floor. -/
@[simp] theorem floor_eq (a : ℚ) : floor a = ⌊a⌋ := by
  unfold floor
  rw [Z.floorDiv_eq, Rat.floor_def']

/-- `Q.ceil` is the ceiling. -/
@[simp] theorem ceil_eq (a : ℚ) : ceil a = ⌈a⌉ := by
  have h : ⌈a⌉ = -⌊-a⌋ := by rw [Int.floor_neg, neg_neg]
  unfold ceil
  rw [Z.ceilDiv_eq, h, Rat.floor_def', Rat.neg_num, Rat.neg_den]

/-! ### Compiled code -/

namespace Compiled

/-- Compiled form of `Q.abs`. -/
def abs (a : ℚ) : ℚ := |a|

/-- Compiled form of `Q.mulPow2`. -/
def mulPow2 (a : ℚ) (k : Nat) : ℚ := a * 2 ^ k

/-- Compiled form of `Q.divPow2`. -/
def divPow2 (a : ℚ) (k : Nat) : ℚ := a / 2 ^ k

/-- Compiled form of `Q.le`. -/
def le (a b : ℚ) : Bool := decide (a ≤ b)

/-- Compiled form of `Q.lt`. -/
def lt (a b : ℚ) : Bool := decide (a < b)

/-- Compiled form of `Q.beq`. -/
def beq (a b : ℚ) : Bool := decide (a = b)

/-- Compiled form of `Q.min`. -/
def min (a b : ℚ) : ℚ := Min.min a b

/-- Compiled form of `Q.max`. -/
def max (a b : ℚ) : ℚ := Max.max a b

/-- Compiled form of `Q.floor`. -/
def floor (a : ℚ) : Int := ⌊a⌋

/-- Compiled form of `Q.ceil`. -/
def ceil (a : ℚ) : Int := ⌈a⌉

end Compiled

compiled_as normalize := Rat.normalize by normalize_eq

compiled_as mk := mkRat by mk_eq

compiled_as add := Rat.add by add_eq

compiled_as sub := Rat.sub by sub_eq

compiled_as mul := Rat.mul by mul_eq

compiled_as neg := Rat.neg by neg_eq

compiled_as inv := Rat.inv by inv_eq

compiled_as div := Rat.div by div_eq

compiled_as pow := Rat.pow by pow_eq

compiled_as abs := Compiled.abs by abs_eq

compiled_as mulPow2 := Compiled.mulPow2 by mulPow2_eq

compiled_as divPow2 := Compiled.divPow2 by divPow2_eq

/-- Compiled code runs `Q.Compiled.le` in place of `Q.le`. -/
@[csimp] theorem le_eq_compiled : @le = @Compiled.le := by
  funext a b
  rw [Compiled.le, Bool.eq_iff_iff, le_iff, decide_eq_true_eq]

/-- Compiled code runs `Q.Compiled.lt` in place of `Q.lt`. -/
@[csimp] theorem lt_eq_compiled : @lt = @Compiled.lt := by
  funext a b
  rw [Compiled.lt, Bool.eq_iff_iff, lt_iff, decide_eq_true_eq]

/-- Compiled code runs `Q.Compiled.beq` in place of `Q.beq`. -/
@[csimp] theorem beq_eq_compiled : @beq = @Compiled.beq := by
  funext a b
  rw [Compiled.beq, Bool.eq_iff_iff, beq_iff, decide_eq_true_eq]

compiled_as min := Compiled.min by min_eq

compiled_as max := Compiled.max by max_eq

compiled_as floor := Compiled.floor by floor_eq

compiled_as ceil := Compiled.ceil by ceil_eq

end FloatLib.Numerics.Kernel.Q
