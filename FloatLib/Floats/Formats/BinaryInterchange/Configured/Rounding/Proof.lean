/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Packing correctness for explicitly rounded configured binary operations

The decoding bridge theorems `toModel_addWithRounding` through `toModel_sqrtWithRounding` and their
`IEEEOutcome.toModel_*WithStatus` companions state that decoding a configured result recovers the
single descriptor-model operation used to compute it. They let proofs transfer results from the
model without depending on the configured storage plan.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

namespace IEEEOutcome

/-- Repacking and then decoding a model outcome preserves both its value and status. -/
@[simp, grind =] theorem toModel_ofModel (outcome : Model.IEEEOutcome format) :
    toModel (ofModel (plan := plan) (code := code) outcome) = outcome := by
  cases outcome
  simp [toModel, ofModel]

end IEEEOutcome

/-- Decoding configured addition gives model addition with the same rounding mode. -/
@[simp, grind =] theorem toModel_addWithRounding
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    toModel (addWithRounding left right rounding) =
      Model.addWithRounding rounding (toModel left) (toModel right) := by
  simp [addWithRounding, toModel, Configured.Family.toModel]

/-- Decoding configured subtraction gives model subtraction with the same rounding mode. -/
@[simp, grind =] theorem toModel_subWithRounding
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    toModel (subWithRounding left right rounding) =
      Model.subWithRounding rounding (toModel left) (toModel right) := by
  simp [subWithRounding, toModel, Configured.Family.toModel]

/-- Decoding configured multiplication gives model multiplication with the same rounding mode. -/
@[simp, grind =] theorem toModel_mulWithRounding
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    toModel (mulWithRounding left right rounding) =
      Model.mulWithRounding rounding (toModel left) (toModel right) := by
  simp [mulWithRounding, toModel, Configured.Family.toModel]

/-- Decoding configured division gives model division with the same rounding mode. -/
@[simp, grind =] theorem toModel_divWithRounding
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    toModel (divWithRounding left right rounding) =
      Model.divWithRounding rounding (toModel left) (toModel right) := by
  simp [divWithRounding, toModel, Configured.Family.toModel]

/-- Decoding configured FMA gives model FMA with the same rounding mode. -/
@[simp, grind =] theorem toModel_fmaWithRounding
    (left right addend : Value) (rounding : Model.IEEERoundingMode) :
    toModel (fmaWithRounding left right addend rounding) =
      Model.fmaWithRounding rounding (toModel left) (toModel right) (toModel addend) := by
  simp [fmaWithRounding, toModel, Configured.Family.toModel]

/-- Decoding configured square root gives model square root with the same rounding mode. -/
@[simp, grind =] theorem toModel_sqrtWithRounding
    (value : Value) (rounding : Model.IEEERoundingMode) :
    toModel (sqrtWithRounding value rounding) =
      Model.sqrtWithRounding rounding (toModel value) := by
  simp [sqrtWithRounding, toModel, Configured.Family.toModel]

/-- Decoding configured addition preserves the model result and exception flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_addWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (addWithStatus left right rounding) =
      Model.addWithStatus
        (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding := by
  simp [addWithStatus]

/-- Decoding configured subtraction preserves the model result and exception flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_subWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (subWithStatus left right rounding) =
      Model.subWithStatus
        (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding := by
  simp [subWithStatus]

/-- Decoding configured multiplication preserves the model result and exception flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_mulWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (mulWithStatus left right rounding) =
      Model.mulWithStatus
        (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding := by
  simp [mulWithStatus]

/-- Decoding configured division preserves the model result and exception flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_divWithStatus
    (left right : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (divWithStatus left right rounding) =
      Model.divWithStatus
        (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right) rounding := by
  simp [divWithStatus]

/-- Decoding configured FMA preserves the model result and exception flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_fmaWithStatus
    (left right addend : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (fmaWithStatus left right addend rounding) =
      Model.fmaWithStatus
        (ExecFloat.Binary.toModel left) (ExecFloat.Binary.toModel right)
        (ExecFloat.Binary.toModel addend) rounding := by
  simp [fmaWithStatus]

/-- Decoding configured square root preserves the model result and exception flags. -/
@[simp, grind =] theorem IEEEOutcome.toModel_sqrtWithStatus
    (value : Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sqrtWithStatus value rounding) =
      Model.sqrtWithStatus (ExecFloat.Binary.toModel value) rounding := by
  simp [sqrtWithStatus]

end FloatLib.Floats.ExecFloat.Binary
