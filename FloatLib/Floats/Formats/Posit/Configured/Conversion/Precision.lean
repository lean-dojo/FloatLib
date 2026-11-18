/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Cast.Precision
public import FloatLib.Floats.Formats.Posit.Configured.Value.Proof

/-!
# Posit precision conversion through arbitrary carriers

Posit Standard (2022), §6.1. Source and destination widths and invertible
storage codecs are independent. The model's proved word-level widening
path remains available after the configured wrapper is unfolded.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Posit

open FloatLib.Floats.Formats.Posit

variable {source : Format} {sourcePlan : Configured.StoragePlan source} {sourceCode : Type}
  [ModelCodec sourcePlan (Model source) sourceCode]
  {target : Format} {targetPlan : Configured.StoragePlan target} {targetCode : Type}
  [ModelCodec targetPlan (Model target) targetCode]

/-- Posit Standard (2022), §6.1: one conversion family for every source and target precision. -/
def pₘToₙ
    (value : ExecFloat (Configured.Family source sourceCode sourcePlan)) :
    ExecFloat (Configured.Family target targetCode targetPlan) :=
  ofModel (Model.pₘToₙ target (toModel value))

/-- Section 6.1 conversion preserves the exact model result through both carrier codecs. -/
@[simp] theorem toModel_pₘToₙ
    (value : ExecFloat (Configured.Family source sourceCode sourcePlan)) :
    toModel (pₘToₙ (target := target) (targetPlan := targetPlan)
      (targetCode := targetCode) value) = Model.pₘToₙ target (toModel value) := by
  simp [pₘToₙ]

/-- Section 6.1 compiler certificate; the model conversion uses its proved direct widening path. -/
@[compiler_optimize baseline]
def precisionConversion : Backend.Certified (@pₘToₙ) :=
  .reference { name := "configured posit precision conversion", kind := .generic, steadyCost := 1 }
    (@pₘToₙ)

attribute [kernel_optimize] pₘToₙ.eq_def

end FloatLib.Floats.ExecFloat.Posit
