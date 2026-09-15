/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Logarithm.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Logarithm.Runtime

/-!
# Real correctness of configured posit logarithms

Every supported carrier decodes to the same model operation. The finite-domain theorems state
the exact real logarithm being rounded, including the unrounded addition in `Plus1`.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Configured base-two logarithm refines the exact model operation. -/
@[simp] theorem toModel_log2 (value : Value) :
    toModel (log2 value) = Model.log2 (toModel value) := by
  simp [log2, toModel, Configured.Family.toModel]

/-- Configured base-ten logarithm refines the exact model operation. -/
@[simp] theorem toModel_log10 (value : Value) :
    toModel (log10 value) = Model.log10 (toModel value) := by
  simp [log10, toModel, Configured.Family.toModel]

/-- Configured base-two `Plus1` refines the exact model operation. -/
@[simp] theorem toModel_log2Plus1 (value : Value) :
    toModel (log2Plus1 value) = Model.log2Plus1 (toModel value) := by
  simp [log2Plus1, toModel, Configured.Family.toModel]

/-- Configured base-ten `Plus1` refines the exact model operation. -/
@[simp] theorem toModel_log10Plus1 (value : Value) :
    toModel (log10Plus1 value) = Model.log10Plus1 (toModel value) := by
  simp [log10Plus1, toModel, Configured.Family.toModel]

/-- Configured base-two logarithm rounds the exact signed real logarithm. -/
theorem log2_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : 0 < q) :
    toModel (log2 value) = Model.RealRounding.round format (Real.logb 2 (q : ℝ)) := by
  rw [toModel_log2]
  exact Model.log2_eq_real _ hvalue hq

/-- Configured base-ten logarithm rounds the exact signed real logarithm. -/
theorem log10_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : 0 < q) :
    toModel (log10 value) = Model.RealRounding.round format (Real.logb 10 (q : ℝ)) := by
  rw [toModel_log10]
  exact Model.log10_eq_real _ hvalue hq

/-- Configured base-two `Plus1` forms `1 + x` exactly before rounding the logarithm. -/
theorem log2Plus1_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : -1 < q) :
    toModel (log2Plus1 value) =
      Model.RealRounding.round format (Real.logb 2 (1 + (q : ℝ))) := by
  rw [toModel_log2Plus1]
  exact Model.log2Plus1_eq_real _ hvalue hq

/-- Configured base-ten `Plus1` forms `1 + x` exactly before rounding the logarithm. -/
theorem log10Plus1_eq_real (value : Value) {q : Rat}
    (hvalue : toRat? value = some q) (hq : -1 < q) :
    toModel (log10Plus1 value) =
      Model.RealRounding.round format (Real.logb 10 (1 + (q : ℝ))) := by
  rw [toModel_log10Plus1]
  exact Model.log10Plus1_eq_real _ hvalue hq

end ExecFloat.Posit
end FloatLib.Floats
