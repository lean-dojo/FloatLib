/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Correctness of configured binary reductions

The configured API is a lossless carrier adaptation of the descriptor-model reducer. These
theorems expose that connection directly, so proofs can reason about the one model definition
without depending on byte, word, or wide storage choices.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/--
Decoding a configured correctly rounded sum recovers the descriptor-model sum and all status
indicators exactly.
-/
theorem IEEEOutcome.toModel_sumWithStatus
    (values : Array Value) (rounding : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sumWithStatus values rounding) =
      Model.sumWithStatus format (values.map ExecFloat.Binary.toModel) rounding := by
  simpa only [sumWithStatus] using
    (IEEEOutcome.toModel_ofModel
      (plan := plan) (code := code)
      (Model.sumWithStatus format
        (values.map ExecFloat.Binary.toModel) rounding))

/--
Decoding the value-only configured sum gives the value component of the descriptor-model sum.
-/
@[simp, grind =] theorem toModel_sum
    (values : Array Value) (rounding : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (sum values rounding) =
      Model.sum format (values.map ExecFloat.Binary.toModel) rounding := by
  change
    (IEEEOutcome.toModel (sumWithStatus values rounding)).value =
      (Model.sumWithStatus format
        (values.map ExecFloat.Binary.toModel) rounding).value
  rw [IEEEOutcome.toModel_sumWithStatus]

/--
Configured dot-product execution is exactly the descriptor-model dot product, including a
length-mismatch error and every IEEE status indicator.
-/
theorem dotWithStatus_eq_model
    (left right : Array Value) (rounding : Model.IEEERoundingMode) :
    dotWithStatus left right rounding =
      (Model.dotWithStatus format
        (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel)
        rounding).map IEEEOutcome.ofModel := by
  rfl

/--
On a successful configured dot product, decoding the delivered value gives the descriptor-model
value exactly.
-/
theorem toModel_dot_of_eq_ok
    (left right : Array Value) (rounding : Model.IEEERoundingMode) (result : Value)
    (hresult : dot left right rounding = .ok result) :
    Model.dot format
        (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel)
        rounding =
      .ok (ExecFloat.Binary.toModel result) := by
  cases hmodel :
      Model.dotWithStatus format
        (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel)
        rounding with
  | error error =>
      have : False := by
        simp [dot, dotWithStatus, hmodel, Except.map] at hresult
      exact this.elim
  | ok outcome =>
      have hpacked : ExecFloat.Binary.ofModel outcome.value = result := by
        simpa [dot, dotWithStatus, hmodel, IEEEOutcome.ofModel, Except.map] using hresult
      have hdecoded : ExecFloat.Binary.toModel result = outcome.value := by
        rw [← hpacked]
        exact ExecFloat.Binary.toModel_ofModel outcome.value
      simp [Model.dot, hmodel, Except.map, hdecoded]

end FloatLib.Floats.ExecFloat.Binary
