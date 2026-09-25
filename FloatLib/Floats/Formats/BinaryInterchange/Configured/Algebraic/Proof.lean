/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.RootProof
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.HypotProof
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Algebraic rounding contracts for configured binary values

The lossless codec preserves the full model result, including NaN payloads and signed zeros.
For conventional IEEE descriptors, finite results also satisfy the model's nearest-even real
rounding contracts. These statements do not depend on a particular carrier or width.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Decoding reciprocal square root recovers the complete model result. -/
@[simp, grind =] theorem toModel_rsqrt (value : Value) :
    toModel (rsqrt value) = Model.rsqrt (toModel value) := by
  simp [rsqrt, toModel, Configured.Family.toModel]

/-- Decoding the norm recovers the complete model result. -/
@[simp, grind =] theorem toModel_hypot (left right : Value) :
    toModel (hypot left right) = Model.hypot (toModel left) (toModel right) := by
  simp [hypot, toModel, Configured.Family.toModel]

/-- Decoding integer power recovers the complete model result. -/
@[simp, grind =] theorem toModel_powInt (value : Value) (exponent : Int) :
    toModel (powInt value exponent) = Model.powInt (toModel value) exponent := by
  simp [powInt, toModel, Configured.Family.toModel]

/-- Decoding integer root recovers the complete model result. -/
@[simp, grind =] theorem toModel_rootN (value : Value) (degree : Int) :
    toModel (rootN value degree) = Model.rootN (toModel value) degree := by
  simp [rootN, toModel, Configured.Family.toModel]

/-- A finite reciprocal square root rounds the exact real expression once. -/
theorem toReal_rsqrt_eq_roundAt (value : Value)
    (hfmt : format.isIEEE = true) (hvalue : isFinite value = true)
    (hzero : isZero value = false) (hsign : signBit value = false)
    (hfinite : isFinite (rsqrt value) = true) :
    Model.toReal (toModel (rsqrt value)) =
      Model.roundAt format (Real.sqrt (Model.toReal (toModel value)))⁻¹ := by
  simpa only [toModel_rsqrt] using Model.toReal_rsqrt_eq_roundAt
    (toModel value) hfmt hvalue hzero hsign
    (show Model.isFinite (Model.rsqrt (toModel value)) = true by
      simpa only [isFinite, toModel_rsqrt] using hfinite)

/-- A finite norm rounds the exact sum of squares and square root once. -/
theorem toReal_hypot_eq_roundAt (left right : Value)
    (hfmt : format.isIEEE = true)
    (hleft : isFinite left = true) (hright : isFinite right = true)
    (hfinite : isFinite (hypot left right) = true) :
    Model.toReal (toModel (hypot left right)) =
      Model.roundAt format (Real.sqrt
        (Model.toReal (toModel left) ^ 2 + Model.toReal (toModel right) ^ 2)) := by
  simpa only [toModel_hypot] using Model.toReal_hypot_eq_roundAt
    (toModel left) (toModel right) hfmt hleft hright
    (show Model.isFinite (Model.hypot (toModel left) (toModel right)) = true by
      simpa only [isFinite, toModel_hypot] using hfinite)

/-- A finite integer power of a finite nonzero base rounds the exact real power once. -/
theorem toReal_powInt_eq_roundAt (value : Value) (exponent : Int)
    (hfmt : format.isIEEE = true) (hvalue : isFinite value = true)
    (hzero : isZero value = false) (hfinite : isFinite (powInt value exponent) = true) :
    Model.toReal (toModel (powInt value exponent)) =
      Model.roundAt format (Model.toReal (toModel value) ^ exponent) := by
  simpa only [toModel_powInt] using Model.toReal_powInt_eq_roundAt
    (toModel value) exponent hfmt hvalue hzero
    (show Model.isFinite (Model.powInt (toModel value) exponent) = true by
      simpa only [isFinite, toModel_powInt] using hfinite)

/-- A finite integer root rounds the chosen signed real branch once. -/
theorem toReal_rootN_eq_roundAt (value : Value) (degree : Int)
    (hfmt : format.isIEEE = true) (hvalue : isFinite value = true)
    (hzero : isZero value = false) (hdegree : degree ≠ 0)
    (hdomain : signBit value = false ∨ degree % 2 ≠ 0)
    (hfinite : isFinite (rootN value degree) = true) :
    Model.toReal (toModel (rootN value degree)) =
      Model.roundAt format (if signBit value then
        -(|Model.toReal (toModel value)| ^ (degree : ℝ)⁻¹)
        else |Model.toReal (toModel value)| ^ (degree : ℝ)⁻¹) := by
  have hmodel := Model.toReal_rootN_eq_roundAt
    (toModel value) degree hfmt hvalue hzero hdegree hdomain
    (show Model.isFinite (Model.rootN (toModel value) degree) = true by
      simpa only [isFinite, toModel_rootN] using hfinite)
  cases hsign : Model.signBit (toModel value) <;> simpa [signBit, hsign] using hmodel

end FloatLib.Floats.ExecFloat.Binary
