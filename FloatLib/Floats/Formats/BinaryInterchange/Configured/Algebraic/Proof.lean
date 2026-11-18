/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.HypotProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.RootProof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

/-!
# Algebraic rounding contracts for configured binary values

The lossless codec preserves the full model result, including NaN payloads and signed zeros.
For conventional IEEE descriptors, finite results also satisfy the model's nearest-even real
rounding contracts, stated with the configured `toReal` like those of `Configured.Real`. These
statements do not depend on a particular carrier or width.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Decoding reciprocal square root recovers the complete model result. -/
@[simp, grind =] theorem toModel_rSqrt (value : Value) :
    toModel (rSqrt value) = Model.rSqrt (toModel value) := by
  simp [rSqrt, toModel, Configured.Family.toModel]

/-- Decoding the norm recovers the complete model result. -/
@[simp, grind =] theorem toModel_hypot (left right : Value) :
    toModel (hypot left right) = Model.hypot (toModel left) (toModel right) := by
  simp [hypot, toModel, Configured.Family.toModel]

/-- Decoding integer power recovers the complete model result. -/
@[simp, grind =] theorem toModel_pown (value : Value) (exponent : Int) :
    toModel (pown value exponent) = Model.pown (toModel value) exponent := by
  simp [pown, toModel, Configured.Family.toModel]

/-- Decoding integer root recovers the complete model result. -/
@[simp, grind =] theorem toModel_rootn (value : Value) (degree : Int) :
    toModel (rootn value degree) = Model.rootn (toModel value) degree := by
  simp [rootn, toModel, Configured.Family.toModel]

/-- A finite reciprocal square root rounds the exact real expression once. -/
theorem toReal_rSqrt_eq_roundAt (value : Value) (hvalue : isFinite value = true)
    (hresult : isFinite (rSqrt value) = true) (hformat : format.isIEEE = true := by ieee_format) :
    toReal (rSqrt value) = Model.roundAt format (Real.sqrt (toReal value))⁻¹ := by
  simpa only [toReal, toModel_rSqrt] using Model.toReal_rSqrt_eq_roundAt
    (toModel value) hformat hvalue
    (show Model.isFinite (Model.rSqrt (toModel value)) = true by
      simpa only [isFinite, toModel_rSqrt] using hresult)

/-- A finite norm rounds the exact sum of squares and square root once. -/
theorem toReal_hypot_eq_roundAt (left right : Value)
    (hresult : isFinite (hypot left right) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (hypot left right) =
      Model.roundAt format (Real.sqrt (toReal left ^ 2 + toReal right ^ 2)) := by
  simpa only [toReal, toModel_hypot] using Model.toReal_hypot_eq_roundAt
    (toModel left) (toModel right) hformat
    (show Model.isFinite (Model.hypot (toModel left) (toModel right)) = true by
      simpa only [isFinite, toModel_hypot] using hresult)

/-- A finite integer power of a finite base rounds the exact real power once. -/
theorem toReal_pown_eq_roundAt (value : Value) (exponent : Int)
    (hvalue : isFinite value = true) (hresult : isFinite (pown value exponent) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (pown value exponent) = Model.roundAt format (toReal value ^ exponent) := by
  simpa only [toReal, toModel_pown] using Model.toReal_pown_eq_roundAt
    (toModel value) exponent hformat hvalue
    (show Model.isFinite (Model.pown (toModel value) exponent) = true by
      simpa only [isFinite, toModel_pown] using hresult)

/-- A finite integer root rounds the chosen signed real branch once. -/
theorem toReal_rootn_eq_roundAt (value : Value) (degree : Int)
    (hvalue : isFinite value = true) (hresult : isFinite (rootn value degree) = true)
    (hformat : format.isIEEE = true := by ieee_format) :
    toReal (rootn value degree) =
      Model.roundAt format (if signBit value then -(|toReal value| ^ (degree : ℝ)⁻¹)
        else |toReal value| ^ (degree : ℝ)⁻¹) := by
  have hmodel := Model.toReal_rootn_eq_roundAt
    (toModel value) degree hformat hvalue
    (show Model.isFinite (Model.rootn (toModel value) degree) = true by
      simpa only [isFinite, toModel_rootn] using hresult)
  cases hsign : Model.signBit (toModel value) <;> simpa [toReal, signBit, hsign] using hmodel

end FloatLib.Floats.ExecFloat.Binary
