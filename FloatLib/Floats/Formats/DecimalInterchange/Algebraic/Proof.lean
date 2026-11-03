/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Special
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Semantics
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction

/-!
# Numerical guarantees for decimal algebraic operations

The bounds compare delivered values with the exact square, integer power,
reciprocal square root, or hypotenuse. They hold for arbitrary decimal formats.
The one-unit bounds cover all five rounding modes; nearest modes satisfy the
half-unit bound. Overflow is excluded explicitly, as in the underlying rounders, except in the
inexact and underflow laws and the toward-zero bounds, which also cover overflow.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Squaring always delivers a valid datum of the format, including NaN, infinite and overflowed
results. -/
theorem square_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (square f mode x).value.Valid f :=
  mul_valid f mode x x

/-- An integer power always delivers a valid datum of the format, including NaN, pole, infinite and
overflowed results. -/
theorem powInt_valid (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    (powInt f mode x n).value.Valid f := by
  cases x <;> simp only [powInt]
  all_goals repeat first
    | exact project_valid ..
    | exact projectMagnitude_valid f mode _ (by rfl) _
    | exact nanResult_valid ..
    | trivial
    | split

/-- The reciprocal square root always delivers a valid datum of the format, including
invalid-operation NaNs, the infinities of signed zeros, and overflowed results. -/
theorem rsqrt_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (rsqrt f mode x).value.Valid f := by
  cases x with
  | nan s t p => exact nanResult_valid ..
  | infinity s =>
    simp only [rsqrt]
    split
    · exact invalidResult_valid f
    · exact projectMagnitude_valid f mode false (by rfl) _
  | finite s c q =>
    simp only [rsqrt]
    split
    · trivial
    · split
      · exact invalidResult_valid f
      · exact sqrtMagnitude_valid f mode
          (inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg c)
            (zpow_pos (by norm_num) q).le)) _

/-- The hypotenuse always delivers a valid datum of the format, including propagated NaNs and the
positive infinity of an infinite operand. -/
theorem hypot_valid (f : Format) (mode : RoundingMode) (x y : Datum) :
    (hypot f mode x y).value.Valid f := by
  cases x <;> cases y <;> simp only [hypot]
  all_goals repeat first
    | exact nanResult_valid ..
    | exact sqrtMagnitude_valid f mode (add_nonneg (sq_nonneg _) (sq_nonneg _)) _
    | trivial
    | split

/-- A finite integer power is exactly one rational projection whenever it has no pole. -/
theorem powInt_eq_project (f : Format) (mode : RoundingMode) (x : Datum)
    (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n) :
    ∃ preferred negativeZero,
      powInt f mode x n = project f mode (a ^ n) preferred negativeZero := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  rename_i s c q
  have hpole : ¬(n < 0 ∧ c = 0) := by
    rintro ⟨hn, hc⟩
    rcases ha with ha | ha
    · simp [hc] at ha
    · omega
  exact ⟨q * n, powerSign s n, by simp [powInt, hpole, Datum.finiteValue]⟩

/-- Positive finite reciprocal square root uses the exact reciprocal as its radicand. -/
theorem rsqrt_eq_sqrtMagnitude (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a) :
    ∃ preferred, rsqrt f mode x = sqrtMagnitude f mode a⁻¹ preferred := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  rename_i s c q
  have hc : c ≠ 0 := by
    intro h
    simp [h] at ha
  have hs : s = false := by
    cases s
    · rfl
    · have hm := mul_nonneg (Nat.cast_nonneg (α := ℚ) c)
        (zpow_pos (by norm_num : (0 : ℚ) < 10) q).le
      simp only [↓reduceIte, neg_mul] at ha
      linarith
  subst s
  exact ⟨(-q) / 2, by simp [rsqrt, hc]⟩

/-- Hypotenuse uses an unrounded sum of squares, including when both operands are zero. -/
theorem hypot_eq_sqrtMagnitude (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    ∃ preferred, hypot f mode x y = sqrtMagnitude f mode (a ^ 2 + b ^ 2) preferred := by
  cases x <;> cases y <;>
    simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx hy
  subst a
  subst b
  exact ⟨_, rfl⟩

/-- The square of a finite datum is one projection of the exact square, with some preferred quantum
and a positive sign when the square is exactly zero, so the square of either zero is `+0`. -/
theorem square_eq_project (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) :
    ∃ preferred, square f mode x = project f mode (a ^ 2) preferred false := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  rename_i s c q
  exact ⟨q + q, by cases s <;> simp [square, mul, Datum.finiteValue, pow_two]⟩

/-- In both nearest modes, a nonoverflowing square of a finite datum is finite and within half a
grid unit of the exact square. -/
theorem square_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f mode x).status.overflow = false) :
    ∃ value, (square f mode x).value.toRat? = some value ∧
      |value - a ^ 2| ≤ (10 : ℚ) ^ roundingQuantum f |a ^ 2| / 2 := by
  simpa only [square, pow_two] using mul_error_le_half f mode hm x x a a hx hx hfinite

/-- In every rounding direction, a nonoverflowing square of a finite datum is finite and less than
one grid unit from the exact square. -/
theorem square_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f mode x).status.overflow = false) :
    ∃ value, (square f mode x).value.toRat? = some value ∧
      |value - a ^ 2| < (10 : ℚ) ^ roundingQuantum f |a ^ 2| := by
  obtain ⟨preferred, he⟩ := square_eq_project f mode x a hx
  rw [he] at hfinite ⊢
  exact project_error_lt_one f mode _ _ _ hfinite

/-- The square of a finite datum raises inexact exactly when a finite result differs from the exact
square, also when it overflows to the greatest finite datum. -/
theorem square_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a)
    (hv : (square f mode x).value.toRat? = some value) :
    (square f mode x).status.inexact = true ↔ value ≠ a ^ 2 := by
  obtain ⟨preferred, he⟩ := square_eq_project f mode x a hx
  rw [he] at hv ⊢
  exact project_inexact_iff f mode _ _ _ _ hv

/-- The square of a finite datum raises underflow exactly when the exact square is below the least
normal magnitude and the result is inexact; an overflowing square is never tiny. -/
theorem square_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) :
    (square f mode x).status.underflow = true ↔
      |a ^ 2| < f.minNormal ∧ (square f mode x).status.inexact = true := by
  obtain ⟨preferred, he⟩ := square_eq_project f mode x a hx
  rw [he]
  exact project_underflow_iff f mode _ _ _

/-- Rounding toward positive, a nonoverflowing square of a finite datum is finite and at least the
exact square. -/
theorem le_square_up (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f .up x).status.overflow = false) :
    ∃ value : ℚ, (square f .up x).value.toRat? = some value ∧ a ^ 2 ≤ value := by
  obtain ⟨preferred, he⟩ := square_eq_project f .up x a hx
  rw [he] at hfinite ⊢
  exact le_project_up f _ _ _ hfinite

/-- Rounding toward negative, the square of a finite datum is finite and at most the exact square.
A square is nonnegative, so an overflow delivers the greatest finite datum, which lies below it. -/
theorem square_down_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) :
    ∃ value : ℚ, (square f .down x).value.toRat? = some value ∧ value ≤ a ^ 2 := by
  obtain ⟨preferred, he⟩ := square_eq_project f .down x a hx
  rw [he]
  have hp : project f .down (a ^ 2) preferred false =
      projectMagnitude f .down false |a ^ 2| preferred := by
    have hs : (if a ^ 2 = 0 then false else decide (a ^ 2 < 0)) = false := by
      split <;> simp [not_lt.mpr (sq_nonneg a)]
    simp only [project, hs]
  cases hfinite : (project f .down (a ^ 2) preferred false).status.overflow
  · exact project_down_le f _ _ _ hfinite
  · rw [hp] at hfinite ⊢
    have hq := (projectMagnitude_overflow_iff f .down false _ preferred).mp hfinite
    have hlt := maxFinite_lt_of_roundedPair_overflow f _ _ (abs_nonneg _) hq
    rw [abs_of_nonneg (sq_nonneg a)] at hq hlt ⊢
    refine ⟨_, ?_, hlt.le⟩
    simp [projectMagnitude_eq, hq, RoundingMode.overflowToInfinity, Format.maxFinite,
      Datum.toRat?_eq]

/-- Rounding toward zero, the square of a finite datum is finite and no larger in magnitude than
the exact square, also when it overflows to the greatest finite datum. -/
theorem abs_square_towardZero_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) :
    ∃ value : ℚ, (square f .towardZero x).value.toRat? = some value ∧
      |value| ≤ |a ^ 2| := by
  obtain ⟨preferred, he⟩ := square_eq_project f .towardZero x a hx
  rw [he]
  exact abs_project_towardZero_le f _ _ _

/-- In both nearest modes, a nonoverflowing integer power of a finite datum without a pole (a
nonzero base or a nonnegative exponent) is finite and within half a grid unit of the exact power. -/
theorem powInt_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f mode x n).status.overflow = false) :
    ∃ value, (powInt f mode x n).value.toRat? = some value ∧
      |value - a ^ n| ≤ (10 : ℚ) ^ roundingQuantum f |a ^ n| / 2 := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n ha
  rw [he] at hfinite ⊢
  exact project_error_le_half f mode hm _ _ _ hfinite

/-- In every rounding direction, a nonoverflowing integer power of a finite datum without a pole is
finite and less than one grid unit from the exact power. -/
theorem powInt_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f mode x n).status.overflow = false) :
    ∃ value, (powInt f mode x n).value.toRat? = some value ∧
      |value - a ^ n| < (10 : ℚ) ^ roundingQuantum f |a ^ n| := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n ha
  rw [he] at hfinite ⊢
  exact project_error_lt_one f mode _ _ _ hfinite

/-- An integer power of a finite datum raises inexact exactly when a finite result differs from the
exact power, also when it overflows to the greatest finite datum. A pole gives an infinity, so a
finite result excludes it. -/
theorem powInt_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a) (n : Int)
    (hv : (powInt f mode x n).value.toRat? = some value) :
    (powInt f mode x n).status.inexact = true ↔ value ≠ a ^ n := by
  by_cases hpole : a = 0 ∧ n < 0
  · obtain ⟨s, q, rfl⟩ := Datum.toRat?_eq_some_zero_iff.mp (hpole.1 ▸ hx)
    simp [powInt_zero_neg f mode s q n hpole.2, Datum.toRat?_eq] at hv
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n
    ((not_and_or.mp hpole).imp id le_of_not_gt)
  rw [he] at hv ⊢
  exact project_inexact_iff f mode _ _ _ _ hv

/-- An integer power of a finite datum raises underflow exactly when the exact power is below the
least normal magnitude in absolute value and the result is inexact. A pole raises only
divide-by-zero, and an overflowing power is never tiny. -/
theorem powInt_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) :
    (powInt f mode x n).status.underflow = true ↔
      |a ^ n| < f.minNormal ∧ (powInt f mode x n).status.inexact = true := by
  by_cases hpole : a = 0 ∧ n < 0
  · obtain ⟨s, q, rfl⟩ := Datum.toRat?_eq_some_zero_iff.mp (hpole.1 ▸ hx)
    simp [powInt_zero_neg f mode s q n hpole.2]
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n
    ((not_and_or.mp hpole).imp id le_of_not_gt)
  rw [he]
  exact project_underflow_iff f mode _ _ _

/-- In both nearest modes, a nonoverflowing reciprocal square root of a positive finite datum is
finite and within half a grid unit of the real reciprocal square root. -/
theorem rsqrt_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f mode x).value.toRat? = some value ∧
      |(value : ℝ) - (Real.sqrt (a : ℝ))⁻¹| ≤
        (10 : ℝ) ^ sqrtQuantum f a⁻¹ / 2 := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_error_le_half f mode hm (inv_nonneg.mpr ha.le) preferred hfinite

/-- In every rounding direction, a nonoverflowing reciprocal square root of a positive finite datum
is finite and less than one grid unit from the real reciprocal square root. -/
theorem rsqrt_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f mode x).value.toRat? = some value ∧
      |(value : ℝ) - (Real.sqrt (a : ℝ))⁻¹| < (10 : ℝ) ^ sqrtQuantum f a⁻¹ := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_error_lt_one f mode (inv_nonneg.mpr ha.le) preferred hfinite

/-- In both nearest modes, a nonoverflowing hypotenuse of two finite datums is finite and within
half a grid unit of the real square root of the exact sum of squares. -/
theorem hypot_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearest ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f mode x y).status.overflow = false) :
    ∃ value : ℚ, (hypot f mode x y).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)| ≤
        (10 : ℝ) ^ sqrtQuantum f (a ^ 2 + b ^ 2) / 2 := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_error_le_half f mode hm
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

/-- In every rounding direction, a nonoverflowing hypotenuse of two finite datums is finite and less
than one grid unit from the real square root of the exact sum of squares. -/
theorem hypot_error_lt_one (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f mode x y).status.overflow = false) :
    ∃ value : ℚ, (hypot f mode x y).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)| <
        (10 : ℝ) ^ sqrtQuantum f (a ^ 2 + b ^ 2) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_error_lt_one f mode
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

/-- A finite datum with a nonpositive value has an infinite or NaN reciprocal square root, which
raises neither underflow nor inexact. -/
private theorem rsqrt_of_nonpos (f : Format) (mode : RoundingMode) (x : Datum) (a : ℚ)
    (hx : x.toRat? = some a) (ha : a ≤ 0) :
    (rsqrt f mode x).value.toRat? = none ∧ (rsqrt f mode x).status.underflow = false ∧
      (rsqrt f mode x).status.inexact = false := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  rename_i s c q
  by_cases hc : c = 0
  · simp [rsqrt, hc, Datum.toRat?_eq]
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at hx
    have hpos : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) (zpow_pos (by norm_num) _)
    linarith
  · simp [rsqrt, hc, invalidResult, Datum.toRat?_eq]

/-- An overflowing square root with a finite result raises inexact and lies below the exact root. -/
private theorem sqrtMagnitude_value_lt_of_overflow (f : Format) (mode : RoundingMode) {x : ℚ}
    (hx : 0 ≤ x) (preferred : Int) (value : ℚ)
    (hfinite : (sqrtMagnitude f mode x preferred).status.overflow = true)
    (hv : (sqrtMagnitude f mode x preferred).value.toRat? = some value) :
    (sqrtMagnitude f mode x preferred).status.inexact = true ∧
      (value : ℝ) < Real.sqrt (x : ℝ) := by
  have hq := (sqrtMagnitude_overflow_iff f mode x preferred).mp hfinite
  have hlt := maxFinite_lt_sqrt_of_overflow f mode hx hq
  simp only [sqrtMagnitude, hq, ↓reduceIte] at hv ⊢
  refine ⟨by simp, ?_⟩
  split at hv
  · simp [Datum.toRat?_eq] at hv
  · simp only [Format.maxFinite, Datum.toRat?_eq, Bool.false_eq_true, ↓reduceIte, one_mul,
      Option.some.injEq] at hv
    rw [← hv, Rat.cast_mul, Rat.cast_natCast, Rat.cast_zpow, Rat.cast_ofNat]
    exact hlt

/-- A finite square root raises inexact exactly when its value differs from the real root, also
when it overflows to the greatest finite datum, which lies below the root. -/
private theorem sqrtMagnitude_inexact_iff_of_eq_some (f : Format) (mode : RoundingMode) {x : ℚ}
    (hx : 0 ≤ x) (preferred : Int) (value : ℚ)
    (hv : (sqrtMagnitude f mode x preferred).value.toRat? = some value) :
    (sqrtMagnitude f mode x preferred).status.inexact = true ↔
      (value : ℝ) ≠ Real.sqrt (x : ℝ) := by
  cases hfinite : (sqrtMagnitude f mode x preferred).status.overflow
  · exact sqrtMagnitude_inexact_iff f mode hx value preferred
      (sqrtMagnitude_quantum_le_of_no_overflow f mode x preferred hfinite) hv
  · obtain ⟨hinexact, hlt⟩ :=
      sqrtMagnitude_value_lt_of_overflow f mode hx preferred value hfinite hv
    exact iff_of_true hinexact hlt.ne

/-- The reciprocal square root of a finite datum raises inexact exactly when a finite result differs
from the real reciprocal square root, also when it overflows to the greatest finite datum. A zero or
negative operand gives an infinity or a NaN, so a finite result has a positive operand. -/
theorem rsqrt_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a)
    (hv : (rsqrt f mode x).value.toRat? = some value) :
    (rsqrt f mode x).status.inexact = true ↔
      (value : ℝ) ≠ (Real.sqrt (a : ℝ))⁻¹ := by
  rcases le_or_gt a 0 with ha | ha
  · simp [(rsqrt_of_nonpos f mode x a hx ha).1] at hv
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hv ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_inexact_iff_of_eq_some f mode (inv_nonneg.mpr ha.le) preferred value hv

/-- The reciprocal square root of a finite datum raises underflow exactly when the real reciprocal
square root is below the least normal magnitude and the result is inexact. A zero or negative
operand raises only divide-by-zero or invalid, and an overflowing root is never tiny. -/
theorem rsqrt_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) :
    (rsqrt f mode x).status.underflow = true ↔
      (Real.sqrt (a : ℝ))⁻¹ < (f.minNormal : ℝ) ∧
        (rsqrt f mode x).status.inexact = true := by
  rcases le_or_gt a 0 with ha | ha
  · obtain ⟨-, hu, hi⟩ := rsqrt_of_nonpos f mode x a hx ha
    simp [hu, hi]
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he]
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_underflow_iff f mode (inv_nonneg.mpr ha.le) preferred

/-- The hypotenuse of two finite datums raises inexact exactly when a finite result differs from the
real square root of the exact sum of squares, also when it overflows to the greatest finite datum.
-/
theorem hypot_inexact_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b value : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hv : (hypot f mode x y).value.toRat? = some value) :
    (hypot f mode x y).status.inexact = true ↔
      (value : ℝ) ≠ Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hv ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_inexact_iff_of_eq_some f mode
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred value hv

/-- The hypotenuse of two finite datums raises underflow exactly when the real hypotenuse is below
the least normal magnitude and the result is inexact; an overflowing hypotenuse is never tiny. -/
theorem hypot_underflow_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    (hypot f mode x y).status.underflow = true ↔
      Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) < (f.minNormal : ℝ) ∧
        (hypot f mode x y).status.inexact = true := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he]
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_underflow_iff f mode
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred

/-- Rounding toward positive, a nonoverflowing reciprocal square root of a positive finite datum is
finite and at least the real reciprocal square root. -/
theorem le_rsqrt_up (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f .up x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f .up x).value.toRat? = some value ∧
      (Real.sqrt (a : ℝ))⁻¹ ≤ (value : ℝ) := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f .up x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    le_sqrtMagnitude_up f (inv_nonneg.mpr ha.le) preferred hfinite

/-- Rounding toward zero or toward negative, the reciprocal square root of a positive finite datum
is finite and at most the real reciprocal square root; the two modes agree because the result is
positive. An overflow delivers the greatest finite datum, which lies below the root. -/
theorem rsqrt_directed_le (f : Format) (mode : RoundingMode)
    (hm : mode = .towardZero ∨ mode = .down)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a) :
    ∃ value : ℚ, (rsqrt f mode x).value.toRat? = some value ∧
      (value : ℝ) ≤ (Real.sqrt (a : ℝ))⁻¹ := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he]
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_directed_le f mode hm (inv_nonneg.mpr ha.le) preferred

/-- Rounding toward positive, a nonoverflowing hypotenuse of two finite datums is finite and at
least the real hypotenuse. -/
theorem le_hypot_up (f : Format)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f .up x y).status.overflow = false) :
    ∃ value : ℚ, (hypot f .up x y).value.toRat? = some value ∧
      Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ≤ (value : ℝ) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f .up x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using le_sqrtMagnitude_up f
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

/-- Rounding toward zero or toward negative, the hypotenuse of two finite datums is finite and at
most the real hypotenuse; the two modes agree because the result is nonnegative. An overflow
delivers the greatest finite datum, which lies below the hypotenuse. -/
theorem hypot_directed_le (f : Format) (mode : RoundingMode)
    (hm : mode = .towardZero ∨ mode = .down)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b) :
    ∃ value : ℚ, (hypot f mode x y).value.toRat? = some value ∧
      (value : ℝ) ≤ Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he]
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_directed_le f mode hm
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred

/-- Rounding toward positive, a nonoverflowing integer power of a finite datum without a pole is
finite and at least the exact power. -/
theorem le_powInt_up (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f .up x n).status.overflow = false) :
    ∃ value : ℚ, (powInt f .up x n).value.toRat? = some value ∧ a ^ n ≤ value := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f .up x a hx n ha
  rw [he] at hfinite ⊢
  exact le_project_up f _ _ _ hfinite

/-- Rounding toward negative, a nonoverflowing integer power of a finite datum without a pole is
finite and at most the exact power. -/
theorem powInt_down_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f .down x n).status.overflow = false) :
    ∃ value : ℚ, (powInt f .down x n).value.toRat? = some value ∧ value ≤ a ^ n := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f .down x a hx n ha
  rw [he] at hfinite ⊢
  exact project_down_le f _ _ _ hfinite

/-- Rounding toward zero, an integer power of a finite datum without a pole is finite and no larger
in magnitude than the exact power, also when it overflows to the greatest finite datum. -/
theorem abs_powInt_towardZero_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n) :
    ∃ value : ℚ, (powInt f .towardZero x n).value.toRat? = some value ∧ |value| ≤ |a ^ n| := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f .towardZero x a hx n ha
  rw [he]
  exact abs_project_towardZero_le f _ _ _

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
