/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.GridProof
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Zero

/-!
# Algebraic special values and preferred zero cohorts

These theorems pin down what the algebraic operations do at zeros, infinities, and NaNs.
Reciprocal square root keeps the sign of zero at its pole, so `-0` goes to `-∞`. In a hypotenuse an
infinity beats a quiet NaN, but a signaling NaN raises invalid either way. Exact zeros take the
preferred quantum, clamped to the destination format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The square root of an exact zero radicand is `+0` with no flags, in the cohort member whose
quantum is the preferred quantum clamped to the format's quantum range. -/
theorem sqrtMagnitude_zero (f : Format) (mode : RoundingMode) (preferred : Int) :
    sqrtMagnitude f mode 0 preferred =
      { value := .finite false 0 (max f.minQuantum (min preferred f.maxQuantum)) } := by
  have hq : sqrtQuantum f 0 = f.minQuantum := by
    have hp := f.precision_pos
    simp only [sqrtQuantum, zero_div, sqrtScaleShift, Nat.floor_zero, Nat.log_zero_right,
      Nat.zero_div, zero_add]
    omega
  have hr : mode.sqrtRound 0 = 0 := by simpa using mode.sqrtRound_nat_sq 0
  have hp : sqrtPair f mode 0 = (0, f.minQuantum) := by
    simp [sqrtPair, hq, hr, Numerics.RadixText.carry]
    exact (pow_pos (by decide : 0 < (10 : Nat)) f.precision).ne
  calc
    sqrtMagnitude f mode 0 preferred = projectMagnitude f mode false 0 preferred := by
      simp [sqrtMagnitude, hp, not_lt.mpr f.minQuantum_le_maxQuantum, projectMagnitude]
    _ = _ := projectMagnitude_zero f mode false preferred

namespace Arithmetic

/-- The square of either signed zero is `+0` with no flags. Its quantum is twice the operand
quantum, clamped to the format's quantum range. -/
theorem square_zero (f : Format) (mode : RoundingMode) (s : Bool) (q : Int) :
    square f mode (.finite s 0 q) =
      { value := .finite false 0 (max f.minQuantum (min (q + q) f.maxQuantum)) } := by
  simp [square, mul, Datum.finiteValue, project_zero]

/-- The square of either infinity is `+∞` with no flags. -/
theorem square_infinity (f : Format) (mode : RoundingMode) (s : Bool) :
    square f mode (.infinity s) = { value := .infinity false } := by
  simp [square, mul]

/-- This is the IEEE signed-zero rule: reciprocal square root of `-0` is `-∞`. -/
theorem rsqrt_zero (f : Format) (mode : RoundingMode) (s : Bool) (q : Int) :
    rsqrt f mode (.finite s 0 q) =
      { value := .infinity s, status := { divideByZero := true } } := by
  simp [rsqrt]

/-- The reciprocal square root of `+∞` is `+0` at the least quantum, with no flags. -/
theorem rsqrt_infinity (f : Format) (mode : RoundingMode) :
    rsqrt f mode (.infinity false) = { value := .finite false 0 f.minQuantum } := by
  simp [rsqrt, projectMagnitude_zero, f.minQuantum_le_maxQuantum]

/-- The reciprocal square root of `-∞` is the default quiet NaN with the invalid flag. -/
theorem rsqrt_negative_infinity (f : Format) (mode : RoundingMode) :
    rsqrt f mode (.infinity true) = invalidResult := by
  simp [rsqrt]

/-- The reciprocal square root of a negative nonzero finite datum is the default quiet NaN with the
invalid flag. -/
theorem rsqrt_negative (f : Format) (mode : RoundingMode) (c : Nat) (q : Int)
    (hc : c ≠ 0) : rsqrt f mode (.finite true c q) = invalidResult := by
  simp [rsqrt, hc]

/-- A hypotenuse of two zeros is `+0` whatever their signs, in the finer operand cohort. -/
theorem hypot_zero (f : Format) (mode : RoundingMode) (sx sy : Bool) (qx qy : Int) :
    hypot f mode (.finite sx 0 qx) (.finite sy 0 qy) =
      { value := .finite false 0 (max f.minQuantum (min (min qx qy) f.maxQuantum)) } := by
  simp [hypot, Datum.finiteValue, sqrtMagnitude_zero]

/-- An infinite first operand dominates a quiet NaN second operand: the hypotenuse is `+∞` with no
flags. -/
theorem hypot_infinity_quietNaN (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (payload : Nat) :
    hypot f mode (.infinity sx) (.nan sy false payload) = { value := .infinity false } := by
  simp [hypot]

/-- An infinite second operand dominates a quiet NaN first operand: the hypotenuse is `+∞` with no
flags. -/
theorem hypot_quietNaN_infinity (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (payload : Nat) :
    hypot f mode (.nan sx false payload) (.infinity sy) = { value := .infinity false } := by
  simp [hypot, Datum.isSNaN]

/-- An infinity does not absorb a signaling NaN: the hypotenuse quiets the second operand's NaN,
keeping its sign and representable payload, and raises invalid. -/
theorem hypot_infinity_signalingNaN (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (payload : Nat) :
    hypot f mode (.infinity sx) (.nan sy true payload) = nanResult f sy payload true := by
  simp [hypot]

/-- Whatever the second operand, a signaling NaN first operand gives its quieted NaN, keeping its
sign and representable payload, and raises invalid. -/
theorem hypot_signalingNaN (f : Format) (mode : RoundingMode)
    (s : Bool) (payload : Nat) (y : Datum) :
    hypot f mode (.nan s true payload) y = nanResult f s payload true := by
  simp [hypot]

/-- When a quiet NaN meets a signaling NaN second operand, the hypotenuse propagates the first NaN's
sign and representable payload and raises invalid. -/
theorem hypot_quietNaN_signalingNaN (f : Format) (mode : RoundingMode)
    (sx sy : Bool) (px py : Nat) :
    hypot f mode (.nan sx false px) (.nan sy true py) = nanResult f sx px true := by
  simp [hypot, Datum.isSNaN]

/-- A negative integer power of a signed zero is a pole: an infinity with the sign of the power,
negative only for `-0` with an odd exponent, and the divide-by-zero flag. -/
theorem powInt_zero_neg (f : Format) (mode : RoundingMode) (s : Bool) (q n : Int)
    (hn : n < 0) :
    powInt f mode (.finite s 0 q) n =
      { value := .infinity (powerSign s n), status := { divideByZero := true } } := by
  simp [powInt, hn]

/-- A positive integer power of a signed zero is an exact zero with the sign of the power, negative
only for `-0` with an odd exponent, and no flags. Its quantum is the operand quantum times the
exponent, clamped to the format's quantum range. -/
theorem powInt_zero_pos (f : Format) (mode : RoundingMode) (s : Bool) (q n : Int)
    (hn : 0 < n) :
    powInt f mode (.finite s 0 q) n =
      { value := .finite (powerSign s n) 0
          (max f.minQuantum (min (q * n) f.maxQuantum)) } := by
  simp [powInt, not_lt.mpr hn.le, Datum.finiteValue, zero_zpow n hn.ne', project_zero]

/-- Every finite datum, either zero included, to the power zero gives one, projected with preferred
quantum zero. -/
theorem powInt_degree_zero_finite (f : Format) (mode : RoundingMode)
    (s : Bool) (c : Nat) (q : Int) :
    powInt f mode (.finite s c q) 0 = project f mode 1 0 := by
  simp [powInt, powerSign]

/-- A quiet NaN to the power zero gives one, projected with preferred quantum zero, and raises no
invalid flag. -/
theorem powInt_degree_zero_quietNaN (f : Format) (mode : RoundingMode)
    (s : Bool) (payload : Nat) :
    powInt f mode (.nan s false payload) 0 = project f mode 1 0 := by
  simp [powInt]

/-- A signaling NaN to any integer power, zero included, gives its quieted NaN, keeping its sign and
representable payload, and raises invalid. -/
theorem powInt_signalingNaN (f : Format) (mode : RoundingMode)
    (s : Bool) (payload : Nat) (n : Int) :
    powInt f mode (.nan s true payload) n = nanResult f s payload true := by
  simp [powInt]

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
