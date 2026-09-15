/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Elementary.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Elementary.Runtime

/-!
# Real correctness of configured natural posit functions

The configured operations inherit the model's real-rounding theorem at every supported width.
The `Minus1` and `Plus1` statements include the exact subtraction or addition in the value
being rounded.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured exponential refines the model operation. -/
@[simp] theorem toModel_exp (value : Value) :
    toModel (exp value) = Model.exp (toModel value) := by
  simp [exp, toModel, Configured.Family.toModel]

/-- Configured exponential minus one refines the model operation. -/
@[simp] theorem toModel_expMinus1 (value : Value) :
    toModel (expMinus1 value) = Model.expMinus1 (toModel value) := by
  simp [expMinus1, toModel, Configured.Family.toModel]

/-- Configured logarithm refines the model operation. -/
@[simp] theorem toModel_log (value : Value) :
    toModel (log value) = Model.log (toModel value) := by
  simp [log, toModel, Configured.Family.toModel]

/-- Configured logarithm of one plus the input refines the model operation. -/
@[simp] theorem toModel_logPlus1 (value : Value) :
    toModel (logPlus1 value) = Model.logPlus1 (toModel value) := by
  simp [logPlus1, toModel, Configured.Family.toModel]

/-- Natural exponential rounds its exact real value at the destination width. -/
theorem exp_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (exp value) = Model.RealRounding.round format (Real.exp (q : ℝ)) := by
  rw [toModel_exp]
  exact Model.exp_eq_real _ hvalue

/-- Exponential minus one has no intermediate posit rounding. -/
theorem expMinus1_eq_real (value : Value) {q : Rat} (hvalue : toRat? value = some q) :
    toModel (expMinus1 value) = Model.RealRounding.round format (Real.exp (q : ℝ) - 1) := by
  rw [toModel_expMinus1]
  exact Model.expMinus1_eq_real _ hvalue

/-- Natural logarithm rounds its exact real value on the positive domain. -/
theorem log_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : 0 < q) :
    toModel (log value) = Model.RealRounding.round format (Real.log (q : ℝ)) := by
  rw [toModel_log]
  exact Model.log_eq_real _ hvalue hq

/-- The input addition in `logPlus1` is exact before logarithm evaluation. -/
theorem logPlus1_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : -1 < q) :
    toModel (logPlus1 value) =
      Model.RealRounding.round format (Real.log (1 + (q : ℝ))) := by
  rw [toModel_logPlus1]
  exact Model.logPlus1_eq_real _ hvalue hq

end ExecFloat.Posit
end FloatLib.Floats
