/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Proof

/-!
# Integer-grid rounding guarantees

The rounded integer fixes every exact integer, satisfies the directed bounds,
and lies within half a unit in either nearest mode. The midpoint theorems specify
the tie choice, which an error bound alone would not determine.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer

private theorem signed_abs_value (value : ℚ) :
    (if decide (value < 0) then -|value| else |value|) = value := by
  by_cases h : value < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (le_of_not_gt h)]

theorem cast_roundInteger (mode : RoundingMode) (value : ℚ) :
    (roundInteger mode value : ℚ) =
      mode.roundSigned (decide (value < 0)) |value| := by
  by_cases h : value < 0 <;> simp [roundInteger, RoundingMode.roundSigned, h]

private theorem signed_error (s : Bool) (n : Nat) (x : ℚ) :
    |(if s then -(n : ℚ) else n) - (if s then -x else x)| = |(n : ℚ) - x| := by
  cases s with
  | false => rfl
  | true =>
      change |-(n : ℚ) - -x| = |(n : ℚ) - x|
      have he : -(n : ℚ) - -x = -((n : ℚ) - x) := by ring
      rw [he, abs_neg]

theorem roundInteger_error_eq (mode : RoundingMode) (value : ℚ) :
    |(roundInteger mode value : ℚ) - value| =
      abs ((mode.roundMagnitude (decide (value < 0)) |value| : ℚ) - |value|) := by
  calc
    _ = |mode.roundSigned (decide (value < 0)) |value| -
        (if decide (value < 0) then -|value| else |value|)| := by
          rw [cast_roundInteger, signed_abs_value]
    _ = _ := signed_error _ _ _

/-- All five directions change a rational by strictly less than one integer unit. -/
theorem roundInteger_error_lt_one (mode : RoundingMode) (value : ℚ) :
    |(roundInteger mode value : ℚ) - value| < 1 := by
  rw [roundInteger_error_eq]
  exact mode.roundMagnitude_error_lt_one _ (abs_nonneg value)

/-- The two nearest modes have at most one-half unit of error. -/
theorem roundInteger_error_le_half (mode : RoundingMode)
    (hm : mode = .nearestEven ∨ mode = .nearestAway) (value : ℚ) :
    |(roundInteger mode value : ℚ) - value| ≤ 1 / 2 := by
  rw [roundInteger_error_eq]
  exact mode.roundMagnitude_error_le_half hm _ (abs_nonneg value)

theorem roundInteger_of_nonneg (mode : RoundingMode) (value : ℚ) (h : 0 ≤ value) :
    roundInteger mode value = (mode.roundMagnitude false value : Int) := by
  simp only [roundInteger, not_lt.mpr h, decide_false, Bool.false_eq_true, ite_false,
    abs_of_nonneg h]

theorem roundInteger_of_neg (mode : RoundingMode) (value : ℚ) (h : value < 0) :
    roundInteger mode value = -(mode.roundMagnitude true (-value) : Int) := by
  simp only [roundInteger, h, decide_true, ite_true, abs_of_neg h]

/-- Exact integers are fixed in every direction, including either sign and zero. -/
@[simp] theorem roundInteger_intCast (mode : RoundingMode) (value : Int) :
    roundInteger mode (value : ℚ) = value := by
  cases value with
  | ofNat n =>
      change roundInteger mode (n : ℚ) = (n : Int)
      rw [roundInteger_of_nonneg _ _ (Nat.cast_nonneg n),
        RoundingMode.roundMagnitude_natCast]
  | negSucc n =>
      change roundInteger mode (-((n + 1 : Nat) : ℚ)) = -((n + 1 : Nat) : Int)
      have hn : -((n + 1 : Nat) : ℚ) < 0 :=
        neg_lt_zero.mpr (Nat.cast_pos.mpr (Nat.succ_pos n))
      rw [roundInteger_of_neg _ _ hn, neg_neg, RoundingMode.roundMagnitude_natCast]

theorem le_roundInteger_towardPositive (value : ℚ) :
    value ≤ (roundInteger .towardPositive value : ℚ) := by
  rw [cast_roundInteger]
  simpa only [signed_abs_value] using
    RoundingMode.le_roundSigned_towardPositive (decide (value < 0)) (abs_nonneg value)

theorem roundInteger_towardNegative_le (value : ℚ) :
    (roundInteger .towardNegative value : ℚ) ≤ value := by
  rw [cast_roundInteger]
  simpa only [signed_abs_value] using
    RoundingMode.roundSigned_towardNegative_le (decide (value < 0)) (abs_nonneg value)

theorem abs_roundInteger_towardZero_le (value : ℚ) :
    |(roundInteger .towardZero value : ℚ)| ≤ |value| := by
  have h := RoundingMode.roundMagnitude_towardZero_le
    (decide (value < 0)) (abs_nonneg value)
  rw [cast_roundInteger]
  cases hs : decide (value < 0) <;> simpa [RoundingMode.roundSigned, hs] using h

/-- The sign is applied after the even adjacent magnitude has been selected. -/
theorem roundInteger_nearestEven_midpoint (negative : Bool) (n : Nat) :
    roundInteger .nearestEven (if negative then -((n : ℚ) + 1 / 2) else n + 1 / 2) =
      let rounded : Int := if n % 2 = 1 then (n + 1 : Nat) else n
      if negative then -rounded else rounded := by
  have hp : (0 : ℚ) < n + 1 / 2 := by positivity
  cases negative with
  | false =>
      simp only [Bool.false_eq_true, ite_false, roundInteger_of_nonneg _ _ hp.le,
        RoundingMode.roundMagnitude_nearestEven_midpoint]
      split <;> rfl
  | true =>
      simp only [ite_true, roundInteger_of_neg _ _ (neg_lt_zero.mpr hp), neg_neg,
        RoundingMode.roundMagnitude_nearestEven_midpoint]
      split <;> rfl

theorem roundInteger_nearestAway_midpoint (negative : Bool) (n : Nat) :
    roundInteger .nearestAway (if negative then -((n : ℚ) + 1 / 2) else n + 1 / 2) =
      if negative then -((n + 1 : Nat) : Int) else (n + 1 : Nat) := by
  have hp : (0 : ℚ) < n + 1 / 2 := by positivity
  cases negative with
  | false =>
      simp only [Bool.false_eq_true, ite_false, roundInteger_of_nonneg _ _ hp.le,
        RoundingMode.roundMagnitude_nearestAway_midpoint]
  | true =>
      simp only [ite_true, roundInteger_of_neg _ _ (neg_lt_zero.mpr hp), neg_neg,
        RoundingMode.roundMagnitude_nearestAway_midpoint]

end FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer
