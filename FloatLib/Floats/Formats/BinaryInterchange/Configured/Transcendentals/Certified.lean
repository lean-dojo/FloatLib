/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Proof

/-!
# Certified exponential and logarithmic functions for configured binary values

`Binary.Certified.exp`, `log`, `expMinus1`, and `logPlus1` decode the configured carrier, run the
rational enclosure kernel, and pack each accepted result. The codec laws preserve finiteness and
nearest-even real rounding. The model's options and `none` results pass through unchanged.

The guarantees are partial correctness: they hold whenever a call returns `some`, and no theorem
says which inputs succeed apart from the signed-zero passthrough of the model's `expMinus1` and
`logPlus1`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary.Certified

open FloatLib.Floats.Formats.BinaryInterchange

/-- The model kernel's enclosure-refinement options, shared by all configured carriers. -/
abbrev Options : Type := Model.Transcendentals.Certified.Options

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-- Certify a finite exponential and pack the accepted model result. -/
@[inline] def exp (value : Value) (options : Options := {}) : Option Value :=
  (Model.Transcendentals.Certified.exp (toModel value) options).map ofModel

/-- Certify a finite logarithm and pack the accepted model result. -/
@[inline] def log (value : Value) (options : Options := {}) : Option Value :=
  (Model.Transcendentals.Certified.log (toModel value) options).map ofModel

/-- Certify `exp x - 1` with one final rounding, preserving signed zero. -/
@[inline] def expMinus1 (value : Value) (options : Options := {}) : Option Value :=
  (Model.Transcendentals.Certified.expMinus1 (toModel value) options).map ofModel

/-- Certify `log (1 + x)` with one final rounding, preserving signed zero. -/
@[inline] def logPlus1 (value : Value) (options : Options := {}) : Option Value :=
  (Model.Transcendentals.Certified.logPlus1 (toModel value) options).map ofModel

/-- Decoding preserves the exponential kernel's accepted result or failure. -/
@[simp, grind =] theorem toModel_exp (value : Value) (options : Options) :
    (exp value options).map toModel =
      Model.Transcendentals.Certified.exp (toModel value) options := by
  simp [exp, Option.map_map, Function.comp_def]

/-- Decoding preserves the logarithm kernel's accepted result or failure. -/
@[simp, grind =] theorem toModel_log (value : Value) (options : Options) :
    (log value options).map toModel =
      Model.Transcendentals.Certified.log (toModel value) options := by
  simp [log, Option.map_map, Function.comp_def]

/-- Decoding preserves the stable exponential kernel's accepted result or failure. -/
@[simp, grind =] theorem toModel_expMinus1 (value : Value) (options : Options) :
    (expMinus1 value options).map toModel =
      Model.Transcendentals.Certified.expMinus1 (toModel value) options := by
  simp [expMinus1, Option.map_map, Function.comp_def]

/-- Decoding preserves the stable logarithm kernel's accepted result or failure. -/
@[simp, grind =] theorem toModel_logPlus1 (value : Value) (options : Options) :
    (logPlus1 value options).map toModel =
      Model.Transcendentals.Certified.logPlus1 (toModel value) options := by
  simp [logPlus1, Option.map_map, Function.comp_def]

/-- An accepted configured exponential is finite. -/
theorem isFinite_of_exp_eq_some {value result : Value} {options : Options}
    (hresult : exp value options = some result) : isFinite result = true := by
  apply Model.Transcendentals.Certified.isFinite_of_exp_eq_some
  simpa only [toModel_exp, Option.map_some] using congrArg (Option.map toModel) hresult

/-- An accepted configured exponential equals nearest-even rounding of the exact real value. -/
theorem toReal_of_exp_eq_some {value result : Value} {options : Options}
    (hresult : exp value options = some result) :
    Model.toReal (toModel result) =
      Model.roundAt format (Real.exp (Model.toReal (toModel value))) := by
  apply Model.Transcendentals.Certified.toReal_of_exp_eq_some
  simpa only [toModel_exp, Option.map_some] using congrArg (Option.map toModel) hresult

/-- An accepted configured logarithm is finite. -/
theorem isFinite_of_log_eq_some {value result : Value} {options : Options}
    (hresult : log value options = some result) : isFinite result = true := by
  apply Model.Transcendentals.Certified.isFinite_of_log_eq_some
  simpa only [toModel_log, Option.map_some] using congrArg (Option.map toModel) hresult

/-- An accepted configured logarithm equals nearest-even rounding of the exact real value. -/
theorem toReal_of_log_eq_some {value result : Value} {options : Options}
    (hresult : log value options = some result) :
    Model.toReal (toModel result) =
      Model.roundAt format (Real.log (Model.toReal (toModel value))) := by
  apply Model.Transcendentals.Certified.toReal_of_log_eq_some
  simpa only [toModel_log, Option.map_some] using congrArg (Option.map toModel) hresult

/-- An accepted configured `expMinus1` result is finite. -/
theorem isFinite_of_expMinus1_eq_some {value result : Value} {options : Options}
    (hresult : expMinus1 value options = some result) : isFinite result = true := by
  apply Model.Transcendentals.Certified.isFinite_of_expMinus1_eq_some
  simpa only [toModel_expMinus1, Option.map_some] using congrArg (Option.map toModel) hresult

/-- The configured stable exponential rounds the real expression once. -/
theorem toReal_of_expMinus1_eq_some {value result : Value} {options : Options}
    (hresult : expMinus1 value options = some result) :
    Model.toReal (toModel result) =
      Model.roundAt format (Real.exp (Model.toReal (toModel value)) - 1) := by
  apply Model.Transcendentals.Certified.toReal_of_expMinus1_eq_some
  simpa only [toModel_expMinus1, Option.map_some] using congrArg (Option.map toModel) hresult

/-- An accepted configured `logPlus1` result is finite. -/
theorem isFinite_of_logPlus1_eq_some {value result : Value} {options : Options}
    (hresult : logPlus1 value options = some result) : isFinite result = true := by
  apply Model.Transcendentals.Certified.isFinite_of_logPlus1_eq_some
  simpa only [toModel_logPlus1, Option.map_some] using congrArg (Option.map toModel) hresult

/-- The configured stable logarithm rounds the real expression once. -/
theorem toReal_of_logPlus1_eq_some {value result : Value} {options : Options}
    (hresult : logPlus1 value options = some result) :
    Model.toReal (toModel result) =
      Model.roundAt format (Real.log (1 + Model.toReal (toModel value))) := by
  apply Model.Transcendentals.Certified.toReal_of_logPlus1_eq_some
  simpa only [toModel_logPlus1, Option.map_some] using congrArg (Option.map toModel) hresult

end FloatLib.Floats.ExecFloat.Binary.Certified
