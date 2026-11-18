/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.CorrectlyRounded.Expm1x

/-!
# `exp x - 1 - x` for configured binary values

`ExecFloat.Binary.CorrectlyRounded.expm1x x` is `exp x - 1 - x` with one rounding, the function
`Model.Transcendentals.CorrectlyRounded.expm1x` on configured values. It takes the rounding
attribute as `(mode := .up)`, nearest-even by default, and always returns a value.

```lean
ExecFloat.Binary.CorrectlyRounded.expm1x x
ExecFloat.Binary.CorrectlyRounded.expm1x x (mode := .down)
```

For an IEEE descriptor and a finite input:

* `toReal_expm1x_eq_roundAt`, `isFinite_expm1x`: in the default attribute, a real value below
  `Certified.overflowThreshold` gives a finite result, the nearest-even rounding of
  `exp x - 1 - x`. These are the contract of the function for `roundoff`.
* `toReal_expm1x_eq_roundAt_mode`, `isFinite_expm1x_mode`: in every attribute, a real value at
  most the largest finite value gives a finite result, the rounding of `exp x - 1 - x` in that
  attribute. These are the contract for a call that names an attribute.
* `toReal_expm1x_of_isFinite`, `mixedError_toReal_expm1x`: in every attribute, a finite result
  whose real value is below the threshold is the rounding in that attribute, with the mixed error
  `Model.unitRoundoffIn format mode` and `Model.underflowErrorIn format mode`.
* `toReal_expm1x_nonneg`: the result is never negative.
* `toReal_expm1x_of_isZero`, `isFinite_expm1x_of_isZero`: a zero gives a zero.

Like `Configured.CorrectlyRounded`, this is a named import outside `import FloatLib`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
`exp x - 1 - x` with one rounding in the attribute `mode`, correctly rounded for an IEEE format
at every precision, with no cancellation near zero.
-/
@[inline] def expm1x (value : Value) (mode : Model.IEEERoundingMode := .nearest) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun input => Model.Transcendentals.CorrectlyRounded.expm1x input mode) value

/-- Decoding the configured `expm1x` gives the model function. -/
@[simp, grind =] theorem toModel_expm1x (value : Value) (mode : Model.IEEERoundingMode) :
    toModel (expm1x value mode) =
      Model.Transcendentals.CorrectlyRounded.expm1x (toModel value) mode := by
  simp [expm1x, toModel, Configured.Family.toModel]

/--
`expm1x` of a finite value is finite in the default attribute when its exact result is below the
overflow threshold.
-/
theorem isFinite_expm1x {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 - toReal value < Certified.overflowThreshold format)
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expm1x value) = true := by
  unfold isFinite toReal at *
  rw [toModel_expm1x]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expm1x hformat hvalue rfl hrange

/--
`expm1x` of a finite value is correctly rounded in the default attribute when its exact result is
below the overflow threshold.
-/
theorem toReal_expm1x_eq_roundAt {value : Value} (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 - toReal value < Certified.overflowThreshold format)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expm1x value) =
      Model.roundAt format (Real.exp (toReal value) - 1 - toReal value) := by
  unfold isFinite toReal at *
  rw [toModel_expm1x]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1x_eq_roundAt hformat hvalue rfl hrange

/-- `expm1x` of a finite value is finite in every attribute when its exact result is at most the
largest finite value. -/
theorem isFinite_expm1x_mode {value : Value} {mode : Model.IEEERoundingMode}
    (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 - toReal value ≤
      Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    isFinite (expm1x value mode) = true := by
  unfold isFinite toReal at *
  rw [toModel_expm1x]
  exact Model.Transcendentals.CorrectlyRounded.isFinite_expm1x_of_le_posMaxFinite hformat hvalue
    mode hrange

/-- `expm1x` of a finite value is correctly rounded in every attribute when its exact result is
at most the largest finite value. -/
theorem toReal_expm1x_eq_roundAt_mode {value : Value} {mode : Model.IEEERoundingMode}
    (hvalue : isFinite value = true)
    (hrange : Real.exp (toReal value) - 1 - toReal value ≤
      Model.toReal (Model.posMaxFinite format))
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expm1x value mode) =
      Model.roundAt format (Real.exp (toReal value) - 1 - toReal value) mode := by
  unfold isFinite toReal at *
  rw [toModel_expm1x]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1x_eq_roundAt_of_le_posMaxFinite hformat
    hvalue mode hrange

/--
A finite `expm1x` of a finite value whose exact result is below the overflow threshold is the
rounding of `exp x - 1 - x` in its attribute, in every one of the six attributes.
-/
theorem toReal_expm1x_of_isFinite {value : Value} (hvalue : isFinite value = true)
    (mode : Model.IEEERoundingMode) (hfinite : isFinite (expm1x value mode) = true)
    (hrange : Real.exp (toReal value) - 1 - toReal value < Certified.overflowThreshold format)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (expm1x value mode) =
      Model.roundAt format (Real.exp (toReal value) - 1 - toReal value) mode := by
  unfold isFinite toReal at *
  rw [toModel_expm1x] at hfinite ⊢
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1x_of_isFinite hformat hvalue mode
    hfinite (hrange.trans (Model.Transcendentals.CorrectlyRounded.overflowThreshold_lt_bpow format))

/--
A finite `expm1x` of a finite value whose exact result is below the overflow threshold has the
mixed error of one rounding in its attribute.
-/
theorem mixedError_toReal_expm1x {value : Value} (hvalue : isFinite value = true)
    (mode : Model.IEEERoundingMode) (hfinite : isFinite (expm1x value mode) = true)
    (hrange : Real.exp (toReal value) - 1 - toReal value < Certified.overflowThreshold format)
    (hformat : format.isIEEE = true := by ieee_format) :
    MixedError (toReal (expm1x value mode)) (Real.exp (toReal value) - 1 - toReal value)
      (Model.unitRoundoffIn format mode) (Model.underflowErrorIn format mode) :=
  Model.mixedError_toReal_of_eq_roundAt_mode
    (toReal_expm1x_of_isFinite hvalue mode hfinite hrange)

/-- `expm1x` never has a negative real value, for any input and in any attribute. -/
theorem toReal_expm1x_nonneg (value : Value) {mode : Model.IEEERoundingMode}
    (hformat : format.isIEEE = true := by ieee_format) : 0 ≤ toReal (expm1x value mode) := by
  unfold toReal
  rw [toModel_expm1x]
  exact Model.Transcendentals.CorrectlyRounded.toReal_expm1x_nonneg hformat _ mode

/-- `expm1x` of a zero is a zero, so its real value is zero. -/
theorem toReal_expm1x_of_isZero {value : Value} (hzero : isZero value = true)
    {mode : Model.IEEERoundingMode} : toReal (expm1x value mode) = 0 := by
  unfold toReal isZero at *
  rw [toModel_expm1x, Model.Transcendentals.CorrectlyRounded.expm1x_of_isZero hzero]
  exact Model.toReal_zero format false

/-- `expm1x` of a zero is finite. -/
theorem isFinite_expm1x_of_isZero {value : Value} (hzero : isZero value = true)
    {mode : Model.IEEERoundingMode} : isFinite (expm1x value mode) = true := by
  unfold isFinite isZero at *
  rw [toModel_expm1x, Model.Transcendentals.CorrectlyRounded.expm1x_of_isZero hzero]
  exact Model.isFinite_eq_true_of_isZero_eq_true _ (Model.isZero_zero format false)

end FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded
