/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Proof

/-!
# Correctly rounded exponential and logarithm for configured binary values

This module lifts the total functions of `Model.Transcendentals.CorrectlyRounded` to
`ExecFloat.Binary`: `exp`, `log`, `expMinus1`, `logPlus1`, and the weighted exponential `expMul`,
which rounds `exp x * w` once. Each always returns a value. For an IEEE descriptor and a finite
input in the domain whose exact result, in absolute value for `log`, `logPlus1`, and `expMul`,
lies below `Certified.overflowThreshold`, the result is finite and is the nearest-even rounding
of the real function. At or beyond the threshold it decodes to the infinity with the sign of the
real result, and a finite logarithm or `logPlus1` comes from an input in the domain. The sign
theorems state when rounding keeps the sign of the real result. At a zero the exponential is
exactly one, and `expMinus1` and `logPlus1` return the zero. None of these theorems has a premise
on the search `budget`, which only bounds the enclosure attempts before exact comparisons decide
the rounding. The certified searches of `Configured.Transcendentals`,
`ExecFloat.Binary.Certified.exp`, `log`, `pow`, `expMinus1`, and `logPlus1`, can fail instead,
and return `Except Certified.Failure`.

```lean
ExecFloat.Binary.CorrectlyRounded.exp x
ExecFloat.Binary.CorrectlyRounded.expMul x w (budget := { maxAttempts := 4 })
```

Like `Configured.Transcendentals`, this is a named import outside `import FloatLib`. The
`MathFunctions` instance there keeps the approximation kernels. Its `CorrectlyRounded.mathFunctions`
dictionary, or the scope `FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`, gives
generic code these `exp` and `log` instead.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
The exponential, correctly rounded for an IEEE format, searching within `budget` before exact
comparisons.
-/
@[inline] def exp (value : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.exp input budget) value

/--
`exp x - 1` with one rounding, correctly rounded for an IEEE format, searching within `budget`
before exact comparisons.
-/
@[inline] def expMinus1 (value : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.expMinus1 input budget) value

/--
The natural logarithm, correctly rounded for an IEEE format, searching within `budget.maxAttempts`
before exact comparisons. `budget.initialDegree` has no effect.
-/
@[inline] def log (value : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.log input budget) value

/--
`log (1 + x)` with one rounding, correctly rounded for an IEEE format, searching within
`budget.maxAttempts` before exact comparisons. `budget.initialDegree` has no effect.
-/
@[inline] def logPlus1 (value : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.logPlus1 input budget) value

/--
`exp x * w` with one rounding, correctly rounded for an IEEE format, searching within `budget`
before exact comparisons. For finite operands it is finite whenever the rounded product is, and
a finite `x` times a zero weight gives the zero with the weight's sign. NaN operands propagate
first, and a positive infinite `x` times a zero weight, like an infinite weight times `exp (-∞)`,
is invalid, as `Model.Transcendentals.CorrectlyRounded.expMul` describes.
-/
@[inline] def expMul (value weight : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan)
    (fun input factor => Model.Transcendentals.CorrectlyRounded.expMul input factor budget)
    value weight

/-! ## Representation bridge theorems -/

/-- Decoding the configured exponential gives the model function. -/
@[simp, grind =] theorem toModel_exp (value : Value) (budget : Certified.Budget) :
    toModel (exp value budget) =
      Model.Transcendentals.CorrectlyRounded.exp (toModel value) budget := by
  simp [exp, toModel, Configured.Family.toModel]

/-- Decoding the configured `expMinus1` gives the model function. -/
@[simp, grind =] theorem toModel_expMinus1 (value : Value) (budget : Certified.Budget) :
    toModel (expMinus1 value budget) =
      Model.Transcendentals.CorrectlyRounded.expMinus1 (toModel value) budget := by
  simp [expMinus1, toModel, Configured.Family.toModel]

/-- Decoding the configured logarithm gives the model function. -/
@[simp, grind =] theorem toModel_log (value : Value) (budget : Certified.Budget) :
    toModel (log value budget) =
      Model.Transcendentals.CorrectlyRounded.log (toModel value) budget := by
  simp [log, toModel, Configured.Family.toModel]

/-- Decoding the configured `logPlus1` gives the model function. -/
@[simp, grind =] theorem toModel_logPlus1 (value : Value) (budget : Certified.Budget) :
    toModel (logPlus1 value budget) =
      Model.Transcendentals.CorrectlyRounded.logPlus1 (toModel value) budget := by
  simp [logPlus1, toModel, Configured.Family.toModel]

/-- Decoding the configured weighted exponential gives the model function. -/
@[simp, grind =] theorem toModel_expMul (value weight : Value) (budget : Certified.Budget) :
    toModel (expMul value weight budget) =
      Model.Transcendentals.CorrectlyRounded.expMul (toModel value) (toModel weight) budget := by
  simp [expMul, toModel, Configured.Family.toModel]

/-! ## Correct rounding -/

/--
The exponential of a finite value is finite when its exact result is below the overflow threshold.
-/
theorem isFinite_exp {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (exp value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_exp hformat hvalue hrange

/--
The exponential of a finite value is correctly rounded when its exact result is below the overflow
threshold.
-/
theorem toReal_exp_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (exp value budget) = Model.roundAt format (Real.exp (toReal value)) := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.toReal_exp_eq_roundAt hformat hvalue hrange

/--
`expMinus1` of a finite value is finite when its exact result is below the overflow threshold.
-/
theorem isFinite_expMinus1 {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expMinus1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expMinus1 hformat hvalue hrange

/--
`expMinus1` of a finite value is correctly rounded when its exact result is below the overflow
threshold.
-/
theorem toReal_expMinus1_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expMinus1 value budget) = Model.roundAt format (Real.exp (toReal value) - 1) := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMinus1_eq_roundAt hformat hvalue hrange

/--
The logarithm of a finite positive value is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_log {value : Value} (hvalue : isFinite value = true) (hpositive : 0 < toReal value)
    (hrange : |Real.log (toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (log value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_log]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_log hformat hvalue hpositive hrange

/--
The logarithm of a finite positive value is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_log_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value)
    (hrange : |Real.log (toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (log value budget) = Model.roundAt format (Real.log (toReal value)) := by
  unfold isFinite toReal at *
  rw [toModel_log]
  exact Model.Transcendentals.CorrectlyRounded.toReal_log_eq_roundAt hformat hvalue hpositive hrange

/--
`logPlus1` of a finite value above `-1` is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_logPlus1 {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : |Real.log (1 + toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (logPlus1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_logPlus1 hformat hvalue hdomain hrange

/--
`logPlus1` of a finite value above `-1` is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_logPlus1_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : |Real.log (1 + toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (logPlus1 value budget) = Model.roundAt format (Real.log (1 + toReal value)) := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_logPlus1_eq_roundAt hformat hvalue hdomain
    hrange

/--
The weighted exponential of finite values is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_expMul {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal value) * toReal weight| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expMul value weight budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expMul hformat hvalue hweight hrange

/--
The weighted exponential of finite values is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_expMul_eq_roundAt {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal value) * toReal weight| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expMul value weight budget) =
      Model.roundAt format (Real.exp (toReal value) * toReal weight) := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMul_eq_roundAt hformat hvalue hweight
    hrange

/-! ## Overflow -/

/--
The exponential of a finite value is finite exactly when its exact result is below the overflow
threshold.
-/
theorem isFinite_exp_iff {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (exp value budget) = true ↔
      Real.exp (toReal value) < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_exp_iff hformat hvalue

/--
`expMinus1` of a finite value is finite exactly when its exact result is below the overflow
threshold.
-/
theorem isFinite_expMinus1_iff {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expMinus1 value budget) = true ↔
      Real.exp (toReal value) - 1 < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expMinus1_iff hformat hvalue

/--
The logarithm of a finite positive value is finite exactly when its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_log_iff {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (log value budget) = true ↔
      |Real.log (toReal value)| < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_log]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_log_iff hformat hvalue hpositive

/--
`logPlus1` of a finite value above `-1` is finite exactly when its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_logPlus1_iff {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (logPlus1 value budget) = true ↔
      |Real.log (1 + toReal value)| < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_logPlus1_iff hformat hvalue hdomain

/--
The weighted exponential of finite values is finite exactly when its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_expMul_iff {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expMul value weight budget) = true ↔
      |Real.exp (toReal value) * toReal weight| < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expMul_iff hformat hvalue hweight

/--
The exponential of a finite value is `+∞` when its exact result is at or above the overflow
threshold.
-/
theorem toModel_exp_eq_nativeOverflow {value : Value} (hvalue : isFinite value = true)
    (hrange : Certified.overflowThreshold format ≤ Real.exp (toReal value))
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (exp value budget) = Model.nativeOverflow format false := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.exp_eq_nativeOverflow hformat hvalue hrange

/--
`expMinus1` of a finite value is `+∞` when its exact result is at or above the overflow threshold.
-/
theorem toModel_expMinus1_eq_nativeOverflow {value : Value} (hvalue : isFinite value = true)
    (hrange : Certified.overflowThreshold format ≤ Real.exp (toReal value) - 1)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (expMinus1 value budget) = Model.nativeOverflow format false := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.expMinus1_eq_nativeOverflow hformat hvalue hrange

/--
The logarithm of a finite positive value is the infinity with the sign of its exact result when that
result is at or above the overflow threshold in magnitude.
-/
theorem toModel_log_eq_nativeOverflow {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value)
    (hrange : Certified.overflowThreshold format ≤ |Real.log (toReal value)|)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (log value budget) = Model.nativeOverflow format (decide (toReal value < 1)) := by
  unfold isFinite toReal at *
  rw [toModel_log]
  exact Model.Transcendentals.CorrectlyRounded.log_eq_nativeOverflow hformat hvalue hpositive
    hrange

/--
`logPlus1` of a finite value above `-1` is the infinity with the sign of its exact result when that
result is at or above the overflow threshold in magnitude.
-/
theorem toModel_logPlus1_eq_nativeOverflow {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : Certified.overflowThreshold format ≤ |Real.log (1 + toReal value)|)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (logPlus1 value budget) = Model.nativeOverflow format (decide (toReal value < 0)) := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.logPlus1_eq_nativeOverflow hformat hvalue hdomain
    hrange

/--
The weighted exponential of finite values is the infinity with the sign of the weight when its exact
result is at or above the overflow threshold in magnitude.
-/
theorem toModel_expMul_eq_nativeOverflow {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true)
    (hrange : Certified.overflowThreshold format ≤ |Real.exp (toReal value) * toReal weight|)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (expMul value weight budget) = Model.nativeOverflow format (signBit weight) := by
  unfold isFinite toReal signBit at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.expMul_eq_nativeOverflow hformat hvalue hweight
    hrange

/-! ## The domain -/

/-- A finite logarithm of a finite value comes from a positive value. -/
theorem toReal_pos_of_isFinite_log {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hfinite : isFinite (log value budget) = true)
    (hformat : format.isIEEE = true := by ieee_format) : 0 < toReal value := by
  unfold isFinite toReal at *
  rw [toModel_log] at hfinite
  exact Model.Transcendentals.CorrectlyRounded.toReal_pos_of_isFinite_log hformat hvalue hfinite

/-- A finite `logPlus1` of a finite value comes from a value above `-1`. -/
theorem neg_one_lt_toReal_of_isFinite_logPlus1 {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hfinite : isFinite (logPlus1 value budget) = true)
    (hformat : format.isIEEE = true := by ieee_format) : -1 < toReal value := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1] at hfinite
  exact Model.Transcendentals.CorrectlyRounded.neg_one_lt_toReal_of_isFinite_logPlus1 hformat
    hvalue hfinite

/-! ## Mixed error bounds -/

/--
For a finite input `x` with `exp x` below the overflow threshold, the exponential differs from
`exp x` by at most `Model.unitRoundoffAt format * |exp x| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_exp_sub_le {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (exp value budget) - Real.exp (toReal value)| ≤
      Model.unitRoundoffAt format * |Real.exp (toReal value)| + Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_exp_sub_le hformat hvalue hrange

/--
For a finite input `x` with `exp x - 1` below the overflow threshold, `expMinus1` differs from
`exp x - 1` by at most `Model.unitRoundoffAt format * |exp x - 1| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_expMinus1_sub_le {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (expMinus1 value budget) - (Real.exp (toReal value) - 1)| ≤
      Model.unitRoundoffAt format * |Real.exp (toReal value) - 1| +
        Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_expMinus1_sub_le hformat hvalue hrange

/--
For a finite positive input `x` with `|log x|` below the overflow threshold, the logarithm differs
from `log x` by at most `Model.unitRoundoffAt format * |log x| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_log_sub_le {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value)
    (hrange : |Real.log (toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (log value budget) - Real.log (toReal value)| ≤
      Model.unitRoundoffAt format * |Real.log (toReal value)| + Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_log]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_log_sub_le hformat hvalue hpositive
    hrange

/--
For a finite input `x > -1` with `|log (1 + x)|` below the overflow threshold, `logPlus1` differs
from `log (1 + x)` by at most
`Model.unitRoundoffAt format * |log (1 + x)| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_logPlus1_sub_le {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : |Real.log (1 + toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (logPlus1 value budget) - Real.log (1 + toReal value)| ≤
      Model.unitRoundoffAt format * |Real.log (1 + toReal value)| +
        Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_logPlus1_sub_le hformat hvalue hdomain
    hrange

/--
For finite `x` and `w` with `|exp x * w|` below the overflow threshold, the weighted exponential
differs from `exp x * w` by at most
`Model.unitRoundoffAt format * |exp x * w| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_expMul_sub_le {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal value) * toReal weight| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (expMul value weight budget) - Real.exp (toReal value) * toReal weight| ≤
      Model.unitRoundoffAt format * |Real.exp (toReal value) * toReal weight| +
        Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_expMul_sub_le hformat hvalue hweight
    hrange

/-! ## Signs -/

/-- The exponential never has a negative real value. -/
theorem toReal_exp_nonneg (value : Value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : 0 ≤ toReal (exp value budget) := by
  unfold toReal
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.toReal_exp_nonneg hformat _

/--
The exponential of a finite value is positive when its exact result exceeds `underflowErrorAt` and
is below the overflow threshold.
-/
theorem toReal_exp_pos {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) < Certified.overflowThreshold format)
    (hlarge : Model.underflowErrorAt format < Real.exp (toReal value)) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : 0 < toReal (exp value budget) := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.toReal_exp_pos hformat hvalue hrange hlarge

/-- `expMinus1` of a finite negative value is negative. -/
theorem toReal_expMinus1_lt_zero {value : Value} (hvalue : isFinite value = true)
    (hnegative : toReal value < 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : toReal (expMinus1 value budget) < 0 := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMinus1_lt_zero hformat hvalue hnegative

/--
`expMinus1` of a finite positive value is positive when its exact result is below the overflow
threshold.
-/
theorem toReal_expMinus1_pos {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    0 < toReal (expMinus1 value budget) := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMinus1_pos hformat hvalue hpositive
    hrange

/-- The exponential of a finite nonpositive value is finite. -/
theorem isFinite_exp_of_nonpos {value : Value} (hvalue : isFinite value = true)
    (hnonpos : toReal value ≤ 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (exp value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_exp_of_nonpos hformat hvalue hnonpos

/-- `expMinus1` of a finite nonpositive value is finite. -/
theorem isFinite_expMinus1_of_nonpos {value : Value} (hvalue : isFinite value = true)
    (hnonpos : toReal value ≤ 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expMinus1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_expMinus1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expMinus1_of_nonpos hformat hvalue hnonpos

/-- `logPlus1` of a finite nonnegative value is finite. -/
theorem isFinite_logPlus1_of_nonneg {value : Value} (hvalue : isFinite value = true)
    (hnonneg : 0 ≤ toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (logPlus1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_logPlus1_of_nonneg hformat hvalue hnonneg

/-- `logPlus1` of a finite positive value is positive. -/
theorem toReal_logPlus1_pos {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : 0 < toReal (logPlus1 value budget) := by
  unfold isFinite toReal at *
  rw [toModel_logPlus1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_logPlus1_pos hformat hvalue hpositive

/-- The weighted exponential of finite values with a nonnegative weight is nonnegative. -/
theorem toReal_expMul_nonneg {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true) (hnonneg : 0 ≤ toReal weight) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    0 ≤ toReal (expMul value weight budget) := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMul_nonneg hformat hvalue hweight
    hnonneg

/-- The weighted exponential of finite values with a nonpositive weight is nonpositive. -/
theorem toReal_expMul_nonpos {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true) (hnonpos : toReal weight ≤ 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expMul value weight budget) ≤ 0 := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMul_nonpos hformat hvalue hweight
    hnonpos

/--
The weighted exponential of finite values is positive when its exact result exceeds
`underflowErrorAt` and is below the overflow threshold.
-/
theorem toReal_expMul_pos {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal value) * toReal weight| < Certified.overflowThreshold format)
    (hlarge : Model.underflowErrorAt format < Real.exp (toReal value) * toReal weight)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    0 < toReal (expMul value weight budget) := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMul_pos hformat hvalue hweight hrange
    hlarge

/--
The weighted exponential of finite values is negative when its exact result is below
`-underflowErrorAt` and above minus the overflow threshold.
-/
theorem toReal_expMul_lt_zero {value weight : Value} (hvalue : isFinite value = true)
    (hweight : isFinite weight = true)
    (hrange : |Real.exp (toReal value) * toReal weight| < Certified.overflowThreshold format)
    (hlarge : Real.exp (toReal value) * toReal weight < -Model.underflowErrorAt format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expMul value weight budget) < 0 := by
  unfold isFinite toReal at *
  rw [toModel_expMul]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expMul_lt_zero hformat hvalue hweight
    hrange hlarge

/-! ## Zero inputs -/

/-- The exponential of a zero is exactly one. -/
theorem toReal_exp_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (exp value budget) = 1 := by
  have hvalue : isFinite value = true := by
    unfold isFinite isZero at *
    exact Model.isFinite_eq_true_of_isZero_eq_true _ hzero
  have hreal : toReal value = 0 := by
    unfold toReal isZero at *
    exact Model.toReal_eq_zero_of_isZero _ hzero
  rw [toReal_exp_eq_roundAt hvalue (by
      rw [hreal, Real.exp_zero]
      exact Model.Transcendentals.CorrectlyRounded.one_lt_overflowThreshold hformat),
    hreal, Real.exp_zero, Model.roundAt_one]

/-- The exponential of a zero is finite. -/
theorem isFinite_exp_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (exp value budget) = true := by
  refine isFinite_exp_of_nonpos ?_ ?_
  · unfold isFinite isZero at *
    exact Model.isFinite_eq_true_of_isZero_eq_true _ hzero
  · unfold toReal isZero at *
    exact (Model.toReal_eq_zero_of_isZero _ hzero).le

/-- `expMinus1` returns a zero unchanged, so its real value is zero. -/
theorem toReal_expMinus1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : toReal (expMinus1 value budget) = 0 := by
  unfold toReal isZero at *
  rw [toModel_expMinus1, Model.Transcendentals.CorrectlyRounded.expMinus1_of_isZero hzero]
  exact Model.toReal_eq_zero_of_isZero _ hzero

/-- `expMinus1` of a zero is finite. -/
theorem isFinite_expMinus1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : isFinite (expMinus1 value budget) = true := by
  unfold isFinite isZero at *
  rw [toModel_expMinus1, Model.Transcendentals.CorrectlyRounded.expMinus1_of_isZero hzero]
  exact Model.isFinite_eq_true_of_isZero_eq_true _ hzero

/-- `logPlus1` returns a zero unchanged, so its real value is zero. -/
theorem toReal_logPlus1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : toReal (logPlus1 value budget) = 0 := by
  unfold toReal isZero at *
  rw [toModel_logPlus1, Model.Transcendentals.CorrectlyRounded.logPlus1_of_isZero hzero]
  exact Model.toReal_eq_zero_of_isZero _ hzero

/-- `logPlus1` of a zero is finite. -/
theorem isFinite_logPlus1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : isFinite (logPlus1 value budget) = true := by
  unfold isFinite isZero at *
  rw [toModel_logPlus1, Model.Transcendentals.CorrectlyRounded.logPlus1_of_isZero hzero]
  exact Model.isFinite_eq_true_of_isZero_eq_true _ hzero

end FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded
