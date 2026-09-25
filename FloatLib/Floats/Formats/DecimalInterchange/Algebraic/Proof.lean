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
half-unit bound. Overflow is excluded explicitly, as in the underlying rounders.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

theorem square_valid (f : Format) (mode : RoundingMode) (x : Datum) :
    (square f mode x).value.Valid f :=
  mul_valid f mode x x

theorem powInt_valid (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    (powInt f mode x n).value.Valid f := by
  cases x <;> simp only [powInt]
  all_goals repeat first
    | exact project_valid ..
    | exact projectMagnitude_valid f mode _ (by rfl) _
    | exact nanResult_valid ..
    | trivial
    | split

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

theorem square_eq_project (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) :
    ∃ preferred, square f mode x = project f mode (a ^ 2) preferred false := by
  cases x <;> simp only [Datum.toRat?_eq, Option.some.injEq, reduceCtorEq] at hx
  subst a
  rename_i s c q
  exact ⟨q + q, by cases s <;> simp [square, mul, Datum.finiteValue, pow_two]⟩

theorem square_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f mode x).status.overflow = false) :
    ∃ value, (square f mode x).value.toRat? = some value ∧
      |value - a ^ 2| ≤ (10 : ℚ) ^ roundingQuantum f |a ^ 2| / 2 := by
  simpa only [square, pow_two] using mul_error_le_half f mode hm x x a a hx hx hfinite

theorem square_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f mode x).status.overflow = false) :
    ∃ value, (square f mode x).value.toRat? = some value ∧
      |value - a ^ 2| < (10 : ℚ) ^ roundingQuantum f |a ^ 2| := by
  obtain ⟨preferred, he⟩ := square_eq_project f mode x a hx
  rw [he] at hfinite ⊢
  exact project_error_lt_one f mode _ _ _ hfinite

theorem square_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f mode x).status.overflow = false)
    (hv : (square f mode x).value.toRat? = some value) :
    (square f mode x).status.inexact = true ↔ value ≠ a ^ 2 := by
  obtain ⟨preferred, he⟩ := square_eq_project f mode x a hx
  rw [he] at hfinite hv ⊢
  exact project_inexact_iff f mode _ _ _ _ hfinite hv

theorem square_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f mode x).status.overflow = false) :
    (square f mode x).status.underflow = true ↔
      |a ^ 2| < f.minNormal ∧ (square f mode x).status.inexact = true := by
  obtain ⟨preferred, he⟩ := square_eq_project f mode x a hx
  rw [he] at hfinite ⊢
  exact project_underflow_iff f mode _ _ _ hfinite

theorem le_square_towardPositive (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f .towardPositive x).status.overflow = false) :
    ∃ value : ℚ, (square f .towardPositive x).value.toRat? = some value ∧ a ^ 2 ≤ value := by
  obtain ⟨preferred, he⟩ := square_eq_project f .towardPositive x a hx
  rw [he] at hfinite ⊢
  exact le_project_towardPositive f _ _ _ hfinite

theorem square_towardNegative_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f .towardNegative x).status.overflow = false) :
    ∃ value : ℚ, (square f .towardNegative x).value.toRat? = some value ∧ value ≤ a ^ 2 := by
  obtain ⟨preferred, he⟩ := square_eq_project f .towardNegative x a hx
  rw [he] at hfinite ⊢
  exact project_towardNegative_le f _ _ _ hfinite

theorem abs_square_towardZero_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a)
    (hfinite : (square f .towardZero x).status.overflow = false) :
    ∃ value : ℚ, (square f .towardZero x).value.toRat? = some value ∧
      |value| ≤ |a ^ 2| := by
  obtain ⟨preferred, he⟩ := square_eq_project f .towardZero x a hx
  rw [he] at hfinite ⊢
  exact abs_project_towardZero_le f _ _ _ hfinite

theorem powInt_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f mode x n).status.overflow = false) :
    ∃ value, (powInt f mode x n).value.toRat? = some value ∧
      |value - a ^ n| ≤ (10 : ℚ) ^ roundingQuantum f |a ^ n| / 2 := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n ha
  rw [he] at hfinite ⊢
  exact project_error_le_half f mode hm _ _ _ hfinite

theorem powInt_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f mode x n).status.overflow = false) :
    ∃ value, (powInt f mode x n).value.toRat? = some value ∧
      |value - a ^ n| < (10 : ℚ) ^ roundingQuantum f |a ^ n| := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n ha
  rw [he] at hfinite ⊢
  exact project_error_lt_one f mode _ _ _ hfinite

theorem powInt_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a) (n : Int)
    (ha : a ≠ 0 ∨ 0 ≤ n) (hfinite : (powInt f mode x n).status.overflow = false)
    (hv : (powInt f mode x n).value.toRat? = some value) :
    (powInt f mode x n).status.inexact = true ↔ value ≠ a ^ n := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n ha
  rw [he] at hfinite hv ⊢
  exact project_inexact_iff f mode _ _ _ _ hfinite hv

theorem powInt_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f mode x n).status.overflow = false) :
    (powInt f mode x n).status.underflow = true ↔
      |a ^ n| < f.minNormal ∧ (powInt f mode x n).status.inexact = true := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f mode x a hx n ha
  rw [he] at hfinite ⊢
  exact project_underflow_iff f mode _ _ _ hfinite

theorem rsqrt_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f mode x).value.toRat? = some value ∧
      |(value : ℝ) - (Real.sqrt (a : ℝ))⁻¹| ≤
        (10 : ℝ) ^ sqrtQuantum f a⁻¹ / 2 := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_error_le_half f mode hm (inv_nonneg.mpr ha.le) preferred hfinite

theorem rsqrt_error_lt_one (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f mode x).value.toRat? = some value ∧
      |(value : ℝ) - (Real.sqrt (a : ℝ))⁻¹| < (10 : ℝ) ^ sqrtQuantum f a⁻¹ := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_error_lt_one f mode (inv_nonneg.mpr ha.le) preferred hfinite

theorem hypot_error_le_half (f : Format) (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f mode x y).status.overflow = false) :
    ∃ value : ℚ, (hypot f mode x y).value.toRat? = some value ∧
      |(value : ℝ) - Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)| ≤
        (10 : ℝ) ^ sqrtQuantum f (a ^ 2 + b ^ 2) / 2 := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_error_le_half f mode hm
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

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

theorem rsqrt_inexact_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a value : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false)
    (hv : (rsqrt f mode x).value.toRat? = some value) :
    (rsqrt f mode x).status.inexact = true ↔
      (value : ℝ) ≠ (Real.sqrt (a : ℝ))⁻¹ := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite hv ⊢
  have hq := sqrtMagnitude_quantum_le_of_no_overflow f mode a⁻¹ preferred hfinite
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_inexact_iff f mode (inv_nonneg.mpr ha.le) value preferred hq hv

theorem rsqrt_underflow_iff (f : Format) (mode : RoundingMode)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false) :
    (rsqrt f mode x).status.underflow = true ↔
      (Real.sqrt (a : ℝ))⁻¹ < (f.minNormal : ℝ) ∧
        (rsqrt f mode x).status.inexact = true := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_underflow_iff f mode (inv_nonneg.mpr ha.le) preferred hfinite

theorem hypot_inexact_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b value : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f mode x y).status.overflow = false)
    (hv : (hypot f mode x y).value.toRat? = some value) :
    (hypot f mode x y).status.inexact = true ↔
      (value : ℝ) ≠ Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hfinite hv ⊢
  have hq := sqrtMagnitude_quantum_le_of_no_overflow f mode (a ^ 2 + b ^ 2) preferred hfinite
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_inexact_iff f mode
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) value preferred hq hv

theorem hypot_underflow_iff (f : Format) (mode : RoundingMode)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f mode x y).status.overflow = false) :
    (hypot f mode x y).status.underflow = true ↔
      Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) < (f.minNormal : ℝ) ∧
        (hypot f mode x y).status.inexact = true := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_underflow_iff f mode
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

theorem le_rsqrt_towardPositive (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f .towardPositive x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f .towardPositive x).value.toRat? = some value ∧
      (Real.sqrt (a : ℝ))⁻¹ ≤ (value : ℝ) := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f .towardPositive x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    le_sqrtMagnitude_towardPositive f (inv_nonneg.mpr ha.le) preferred hfinite

theorem rsqrt_directed_le (f : Format) (mode : RoundingMode)
    (hm : mode = .towardZero ∨ mode = .towardNegative)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (ha : 0 < a)
    (hfinite : (rsqrt f mode x).status.overflow = false) :
    ∃ value : ℚ, (rsqrt f mode x).value.toRat? = some value ∧
      (value : ℝ) ≤ (Real.sqrt (a : ℝ))⁻¹ := by
  obtain ⟨preferred, he⟩ := rsqrt_eq_sqrtMagnitude f mode x a hx ha
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_inv, Real.sqrt_inv] using
    sqrtMagnitude_directed_le f mode hm (inv_nonneg.mpr ha.le) preferred hfinite

theorem le_hypot_towardPositive (f : Format)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f .towardPositive x y).status.overflow = false) :
    ∃ value : ℚ, (hypot f .towardPositive x y).value.toRat? = some value ∧
      Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ≤ (value : ℝ) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f .towardPositive x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using le_sqrtMagnitude_towardPositive f
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

theorem hypot_directed_le (f : Format) (mode : RoundingMode)
    (hm : mode = .towardZero ∨ mode = .towardNegative)
    (x y : Datum) (a b : ℚ) (hx : x.toRat? = some a) (hy : y.toRat? = some b)
    (hfinite : (hypot f mode x y).status.overflow = false) :
    ∃ value : ℚ, (hypot f mode x y).value.toRat? = some value ∧
      (value : ℝ) ≤ Real.sqrt ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
  obtain ⟨preferred, he⟩ := hypot_eq_sqrtMagnitude f mode x y a b hx hy
  rw [he] at hfinite ⊢
  simpa only [Rat.cast_add, Rat.cast_pow] using sqrtMagnitude_directed_le f mode hm
    (add_nonneg (sq_nonneg a) (sq_nonneg b)) preferred hfinite

theorem le_powInt_towardPositive (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f .towardPositive x n).status.overflow = false) :
    ∃ value : ℚ, (powInt f .towardPositive x n).value.toRat? = some value ∧ a ^ n ≤ value := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f .towardPositive x a hx n ha
  rw [he] at hfinite ⊢
  exact le_project_towardPositive f _ _ _ hfinite

theorem powInt_towardNegative_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f .towardNegative x n).status.overflow = false) :
    ∃ value : ℚ, (powInt f .towardNegative x n).value.toRat? = some value ∧ value ≤ a ^ n := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f .towardNegative x a hx n ha
  rw [he] at hfinite ⊢
  exact project_towardNegative_le f _ _ _ hfinite

theorem abs_powInt_towardZero_le (f : Format)
    (x : Datum) (a : ℚ) (hx : x.toRat? = some a) (n : Int) (ha : a ≠ 0 ∨ 0 ≤ n)
    (hfinite : (powInt f .towardZero x n).status.overflow = false) :
    ∃ value : ℚ, (powInt f .towardZero x n).value.toRat? = some value ∧ |value| ≤ |a ^ n| := by
  obtain ⟨preferred, negativeZero, he⟩ := powInt_eq_project f .towardZero x a hx n ha
  rw [he] at hfinite ⊢
  exact abs_project_towardZero_le f _ _ _ hfinite

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
