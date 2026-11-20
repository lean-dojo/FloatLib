/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public meta import FloatLib.Tactic.IeeeConfiguredFunctions
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Recommended.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public meta import FloatLib.Tactic.IEEENames

/-!
# Correctly rounded exponential and logarithm for configured binary values

This module lifts the total functions of `Model.Transcendentals.CorrectlyRounded` to
`ExecFloat.Binary`: `exp`, `log`, `expm1`, `logp1`, and the weighted exponential `expMul`,
which rounds `exp x * w` once. Each always returns a value.

Take an IEEE descriptor and a finite input in the domain whose exact result lies below
`Certified.overflowThreshold`, in absolute value for `log`, `logp1` and `expMul`. Then the
result is finite and is the nearest-even rounding of the real function. At or beyond the threshold
it decodes to the infinity with the sign of the real result, and a finite logarithm or `logp1`
comes from an input in the domain. The sign theorems state when rounding keeps the sign of the
real result. At a zero the exponential returns one, and `expm1` and `logp1` return the
zero.

None of these theorems has a premise on the search `budget`, which only bounds the enclosure
attempts before exact comparisons decide the rounding. That is the difference from the certified
searches of `Configured.Transcendentals`, `ExecFloat.Binary.Certified.exp`, `log`, `pow`,
`expm1` and `logp1`, which can fail and return `Except Certified.Failure`.

```lean
ExecFloat.Binary.CorrectlyRounded.exp x
ExecFloat.Binary.CorrectlyRounded.expMul x w (budget := { maxAttempts := 4 })
```

The other recommended functions of IEEE 754-2019 §9.2 are here too, from
`Model.Transcendentals.CorrectlyRounded` (`Transcendentals.Recommended`): `exp2`, `exp2m1`,
`exp10`, `exp10m1`, `log2`, `log10`, `log2p1`, `log10p1`, `sin`, `cos`, `tan`, `sinPi`, `cosPi`,
`tanPi`, `asin`, `acos`, `atan`, `asinPi`, `acosPi`, `atanPi`, `sinh`, `cosh`, `tanh`, `asinh`,
`acosh`, `atanh`, and `atan2`, `atan2Pi`, `powr`, `pow`, `compound`. Each returns an
`IEEEOutcome`, the value with its flags, and rounds the exact result once by exact comparisons,
with no budget, in the direction `mode` (nearest-even by default). For the 26 functions of one
argument, `toReal_apply` states the correct rounding to nearest-even and `apply_roundsTo` the
correct rounding in every direction.

```lean
(ExecFloat.Binary.CorrectlyRounded.sinPi x).value
(ExecFloat.Binary.CorrectlyRounded.atanh x).status.divideByZero
```

Like `Configured.Transcendentals`, this is a named import outside `import FloatLib`. The
`MathFunctions` instance there keeps the approximation kernels. This module's
`CorrectlyRounded.mathFunctions` dictionary, or the scope
`FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`, gives generic code these `exp`
and `log` instead.
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
@[inline] def expm1 (value : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.expm1 input budget) value

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
@[inline] def logp1 (value : Value) (budget : Certified.Budget := {}) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.logp1 input budget) value

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

/-- Decoding the configured `expm1` gives the model function. -/
@[simp, grind =] theorem toModel_expm1 (value : Value) (budget : Certified.Budget) :
    toModel (expm1 value budget) =
      Model.Transcendentals.CorrectlyRounded.expm1 (toModel value) budget := by
  simp [expm1, toModel, Configured.Family.toModel]

/-- Decoding the configured logarithm gives the model function. -/
@[simp, grind =] theorem toModel_log (value : Value) (budget : Certified.Budget) :
    toModel (log value budget) =
      Model.Transcendentals.CorrectlyRounded.log (toModel value) budget := by
  simp [log, toModel, Configured.Family.toModel]

/-- Decoding the configured `logp1` gives the model function. -/
@[simp, grind =] theorem toModel_logp1 (value : Value) (budget : Certified.Budget) :
    toModel (logp1 value budget) =
      Model.Transcendentals.CorrectlyRounded.logp1 (toModel value) budget := by
  simp [logp1, toModel, Configured.Family.toModel]

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
`expm1` of a finite value is finite when its exact result is below the overflow threshold.
-/
theorem isFinite_expm1 {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expm1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expm1 hformat hvalue hrange

/--
`expm1` of a finite value is correctly rounded when its exact result is below the overflow
threshold.
-/
theorem toReal_expm1_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expm1 value budget) = Model.roundAt format (Real.exp (toReal value) - 1) := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1_eq_roundAt hformat hvalue hrange

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
`logp1` of a finite value above `-1` is finite when its exact result is below the overflow
threshold in magnitude.
-/
theorem isFinite_logp1 {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : |Real.log (1 + toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (logp1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_logp1 hformat hvalue hdomain hrange

/--
`logp1` of a finite value above `-1` is correctly rounded when its exact result is below the
overflow threshold in magnitude.
-/
theorem toReal_logp1_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : |Real.log (1 + toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toReal (logp1 value budget) = Model.roundAt format (Real.log (1 + toReal value)) := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_logp1_eq_roundAt hformat hvalue hdomain
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
The exponential of a finite value is finite if and only if its exact result is below the
overflow threshold.
-/
theorem isFinite_exp_iff {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (exp value budget) = true ↔
      Real.exp (toReal value) < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_exp_iff hformat hvalue

/--
`expm1` of a finite value is finite if and only if its exact result is below the overflow
threshold.
-/
theorem isFinite_expm1_iff {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expm1 value budget) = true ↔
      Real.exp (toReal value) - 1 < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expm1_iff hformat hvalue

/--
The logarithm of a finite positive value is finite if and only if its exact result is below the
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
`logp1` of a finite value above `-1` is finite if and only if its exact result is below the
overflow threshold in magnitude.
-/
theorem isFinite_logp1_iff {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (logp1 value budget) = true ↔
      |Real.log (1 + toReal value)| < Certified.overflowThreshold format := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_logp1_iff hformat hvalue hdomain

/--
The weighted exponential of finite values is finite if and only if its exact result is below
the overflow threshold in magnitude.
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
`expm1` of a finite value is `+∞` when its exact result is at or above the overflow threshold.
-/
theorem toModel_expm1_eq_nativeOverflow {value : Value} (hvalue : isFinite value = true)
    (hrange : Certified.overflowThreshold format ≤ Real.exp (toReal value) - 1)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (expm1 value budget) = Model.nativeOverflow format false := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.expm1_eq_nativeOverflow hformat hvalue hrange

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
`logp1` of a finite value above `-1` is the infinity with the sign of its exact result when that
result is at or above the overflow threshold in magnitude.
-/
theorem toModel_logp1_eq_nativeOverflow {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : Certified.overflowThreshold format ≤ |Real.log (1 + toReal value)|)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    toModel (logp1 value budget) = Model.nativeOverflow format (decide (toReal value < 0)) := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.logp1_eq_nativeOverflow hformat hvalue hdomain
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

/-- A finite `logp1` of a finite value comes from a value above `-1`. -/
theorem neg_one_lt_toReal_of_isFinite_logp1 {value : Value} (hvalue : isFinite value = true)
    {budget : Certified.Budget} (hfinite : isFinite (logp1 value budget) = true)
    (hformat : format.isIEEE = true := by ieee_format) : -1 < toReal value := by
  unfold isFinite toReal at *
  rw [toModel_logp1] at hfinite
  exact Model.Transcendentals.CorrectlyRounded.neg_one_lt_toReal_of_isFinite_logp1 hformat
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
For a finite input `x` with `exp x - 1` below the overflow threshold, `expm1` differs from
`exp x - 1` by at most `Model.unitRoundoffAt format * |exp x - 1| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_expm1_sub_le {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (expm1 value budget) - (Real.exp (toReal value) - 1)| ≤
      Model.unitRoundoffAt format * |Real.exp (toReal value) - 1| +
        Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_expm1_sub_le hformat hvalue hrange

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
For a finite input `x > -1` with `|log (1 + x)|` below the overflow threshold, `logp1` differs
from `log (1 + x)` by at most
`Model.unitRoundoffAt format * |log (1 + x)| + Model.underflowErrorAt format`.
-/
theorem abs_toReal_logp1_sub_le {value : Value} (hvalue : isFinite value = true)
    (hdomain : -1 < toReal value)
    (hrange : |Real.log (1 + toReal value)| < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    |toReal (logp1 value budget) - Real.log (1 + toReal value)| ≤
      Model.unitRoundoffAt format * |Real.log (1 + toReal value)| +
        Model.underflowErrorAt format := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.abs_toReal_logp1_sub_le hformat hvalue hdomain
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

/-- `expm1` of a finite negative value is negative. -/
theorem toReal_expm1_lt_zero {value : Value} (hvalue : isFinite value = true)
    (hnegative : toReal value < 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : toReal (expm1 value budget) < 0 := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1_lt_zero hformat hvalue hnegative

/--
`expm1` of a finite positive value is positive when its exact result is below the overflow
threshold.
-/
theorem toReal_expm1_pos {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value)
    (hrange : Real.exp (toReal value) - 1 < Certified.overflowThreshold format)
    {budget : Certified.Budget} (hformat : format.isIEEE = true := by ieee_format) :
    0 < toReal (expm1 value budget) := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1_pos hformat hvalue hpositive
    hrange

/-- The exponential of a finite nonpositive value is finite. -/
theorem isFinite_exp_of_nonpos {value : Value} (hvalue : isFinite value = true)
    (hnonpos : toReal value ≤ 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : isFinite (exp value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_exp]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_exp_of_nonpos hformat hvalue hnonpos

/-- `expm1` of a finite nonpositive value is finite. -/
theorem isFinite_expm1_of_nonpos {value : Value} (hvalue : isFinite value = true)
    (hnonpos : toReal value ≤ 0) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expm1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_expm1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expm1_of_nonpos hformat hvalue hnonpos

/-- `logp1` of a finite nonnegative value is finite. -/
theorem isFinite_logp1_of_nonneg {value : Value} (hvalue : isFinite value = true)
    (hnonneg : 0 ≤ toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (logp1 value budget) = true := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_logp1_of_nonneg hformat hvalue hnonneg

/-- `logp1` of a finite positive value is positive. -/
theorem toReal_logp1_pos {value : Value} (hvalue : isFinite value = true)
    (hpositive : 0 < toReal value) {budget : Certified.Budget}
    (hformat : format.isIEEE = true := by ieee_format) : 0 < toReal (logp1 value budget) := by
  unfold isFinite toReal at *
  rw [toModel_logp1]
  exact Model.Transcendentals.CorrectlyRounded.toReal_logp1_pos hformat hvalue hpositive

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

/-- The exponential of a zero has real value one. -/
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

/-- `expm1` returns a zero unchanged, so its real value is zero. -/
theorem toReal_expm1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : toReal (expm1 value budget) = 0 := by
  unfold toReal isZero at *
  rw [toModel_expm1, Model.Transcendentals.CorrectlyRounded.expm1_of_isZero hzero]
  exact Model.toReal_eq_zero_of_isZero _ hzero

/-- `expm1` of a zero is finite. -/
theorem isFinite_expm1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : isFinite (expm1 value budget) = true := by
  unfold isFinite isZero at *
  rw [toModel_expm1, Model.Transcendentals.CorrectlyRounded.expm1_of_isZero hzero]
  exact Model.isFinite_eq_true_of_isZero_eq_true _ hzero

/-- `logp1` returns a zero unchanged, so its real value is zero. -/
theorem toReal_logp1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : toReal (logp1 value budget) = 0 := by
  unfold toReal isZero at *
  rw [toModel_logp1, Model.Transcendentals.CorrectlyRounded.logp1_of_isZero hzero]
  exact Model.toReal_eq_zero_of_isZero _ hzero

/-- `logp1` of a zero is finite. -/
theorem isFinite_logp1_of_isZero {value : Value} (hzero : isZero value = true)
    {budget : Certified.Budget} : isFinite (logp1 value budget) = true := by
  unfold isFinite isZero at *
  rw [toModel_logp1, Model.Transcendentals.CorrectlyRounded.logp1_of_isZero hzero]
  exact Model.isFinite_eq_true_of_isZero_eq_true _ hzero

/-! ## The recommended functions of IEEE 754-2019 §9.2 -/

open Model.Transcendentals.CorrectlyRounded (Function)

/--
A recommended function of one argument on a configured value: `Function.apply` of
`Model.Transcendentals.CorrectlyRounded` through the storage codec, the value with its flags
and ternary value.
-/
@[inline] def apply (function : Function) (value : Value)
    (mode : Model.IEEERoundingMode := .nearest) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel (function.apply (ExecFloat.Binary.toModel value) mode)

ieee_recommended apply (value : Value) (mode : Model.IEEERoundingMode := .nearest) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  fun function => apply function value mode


/--
IEEE 754-2019 §9.2 `atan2` (ISO/IEC 9899:2024 7.12.4.4, F.10.1.4) on configured values: the
angle of the point `(right, left)` in radians, `Model.Transcendentals.CorrectlyRounded.atan2`
through the storage codec, the value with its flags.
-/
configured_binary atan2

/--
IEEE 754-2019 §9.2 `atan2Pi` (ISO/IEC 9899:2024 7.12.4.11, F.10.1.11) on configured values:
the angle of the point `(right, left)` in half-turns,
`Model.Transcendentals.CorrectlyRounded.atan2Pi` through the storage codec, the value with its
flags.
-/
configured_binary atan2Pi

/--
IEEE 754-2019 §9.2 `powr` (ISO/IEC 9899:2024 7.12.7.7, F.10.4.7) on configured values:
`left ^ right` as `exp (right * log left)`, `Model.Transcendentals.CorrectlyRounded.powr`
through the storage codec, the value with its flags.
-/
configured_binary powr

/--
IEEE 754-2019 §9.2 `pow` (ISO/IEC 9899:2024 7.12.7.5, F.10.4.5) on configured values:
`left ^ right` with the special cases of §9.2.1, `Model.Transcendentals.CorrectlyRounded.pow`
through the storage codec, the value with its flags.
-/
configured_binary pow

/--
IEEE 754-2019 §9.2 `compound` (ISO/IEC 9899:2024 `compoundn`, 7.12.7.2, F.10.4.2) on a
configured value: `(1 + value) ^ n`, `Model.Transcendentals.CorrectlyRounded.compound` through
the storage codec, the value with its flags.
-/
@[inline] def compound (value : Value) (n : ℤ) (mode : Model.IEEERoundingMode := .nearest) :
    IEEEOutcome (format := format) (plan := plan) (code := code) :=
  IEEEOutcome.ofModel
    (Model.Transcendentals.CorrectlyRounded.compound (ExecFloat.Binary.toModel value) n mode)

/-- Decoding a configured recommended function of one argument gives the model function. -/
@[simp] theorem toModel_apply (function : Function) (value : Value)
    (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (apply function value mode) = function.apply (toModel value) mode := by
  simp [apply]

/--
**The recommended functions of one argument are correctly rounded on configured values.** For
an IEEE format and a finite value whose exact value `q` is in the function's domain, a finite
result denotes `roundAt format` of the real function at `q`.
-/
theorem toReal_apply (function : Function) {value : Value} {q : ℚ}
    (hvalue : toRat? value = some q) (hdomain : function.Domain q)
    (hfinite : isFinite (apply function value).value = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (apply function value).value = Model.roundAt format (function.real q) := by
  unfold isFinite toReal at *
  have hmodel : toModel (apply function value).value = (function.apply (toModel value)).value :=
    congrArg Model.IEEEOutcome.value (toModel_apply function value .nearest)
  rw [hmodel] at hfinite ⊢
  exact Function.toReal_apply hformat function hvalue hdomain hfinite

/--
**The recommended functions of one argument are correctly rounded in every direction on
configured values.** For every format descriptor, a finite value whose exact value `q` is in
the function's domain with a real value that is not zero, and each rounding direction `mode`,
the decoded result meets the contract `Model.RoundsTo`: it is finite and denotes
`roundAt format (function.real q) mode` when that value is at most the largest finite magnitude,
it is the overflow result of the direction otherwise, and in a format with signed zeros it has
the sign of the real value.
-/
theorem apply_roundsTo (function : Function) {value : Value} {q : ℚ}
    (hvalue : toRat? value = some q) (hdomain : function.Domain q) (hne : function.real q ≠ 0)
    (mode : Model.IEEERoundingMode) :
    Model.RoundsTo format mode (function.real q) (decide (function.real q < 0))
      (toModel (apply function value mode).value) := by
  have hmodel : toModel (apply function value mode).value =
      (function.apply (toModel value) mode).value :=
    congrArg Model.IEEEOutcome.value (toModel_apply function value mode)
  rw [hmodel]
  exact Function.apply_roundsTo function hvalue hdomain hne

end FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded
