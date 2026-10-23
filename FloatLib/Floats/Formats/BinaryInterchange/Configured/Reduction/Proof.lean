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
theorems state that connection, so proofs can reason about the one model definition without
depending on byte, word, or wide storage choices.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/--
Decoding a configured correctly rounded sum gives the descriptor-model sum, status indicators
included.
-/
theorem IEEEOutcome.toModel_sum
    (values : Array Value) (mode : Model.IEEERoundingMode) :
    IEEEOutcome.toModel (sum values mode (status := true)) =
      Model.sum format (values.map ExecFloat.Binary.toModel) mode (status := true) := by
  simpa only [sum] using
    (IEEEOutcome.toModel_ofModel
      (plan := plan) (code := code)
      (Model.sum format (values.map ExecFloat.Binary.toModel) mode (status := true)))

/--
Decoding the value-only configured sum gives the value component of the descriptor-model sum.
-/
@[simp, grind =] theorem toModel_sum
    (values : Array Value) (mode : Model.IEEERoundingMode) :
    ExecFloat.Binary.toModel (sum values mode) =
      Model.sum format (values.map ExecFloat.Binary.toModel) mode :=
  ExecFloat.Binary.toModel_ofModel _

/-- The configured sum with `status := true` delivers the value of the configured sum. -/
@[simp] theorem value_sum (values : Array Value) (mode : Model.IEEERoundingMode) :
    (sum values mode (status := true)).value = sum values mode :=
  rfl

/--
Configured dot-product execution with `status := true` is the descriptor-model dot product,
including a length-mismatch error and every IEEE status indicator.
-/
theorem dot_status_eq_model
    (left right : Array Value) (mode : Model.IEEERoundingMode) :
    dot left right mode (status := true) =
      (Model.dot format
        (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel)
        mode (status := true)).map IEEEOutcome.ofModel := by
  rfl

/--
On a successful configured dot product, decoding the delivered value gives the descriptor-model
value.
-/
theorem toModel_dot_of_eq_ok
    (left right : Array Value) (mode : Model.IEEERoundingMode) (result : Value)
    (hresult : dot left right mode = .ok result) :
    Model.dot format
        (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel)
        mode =
      .ok (ExecFloat.Binary.toModel result) := by
  cases hmodel :
      Model.dot format
        (left.map ExecFloat.Binary.toModel)
        (right.map ExecFloat.Binary.toModel)
        mode with
  | error error =>
      have : False := by
        simp [dot, hmodel, Except.map] at hresult
      exact this.elim
  | ok value =>
      have hpacked : ExecFloat.Binary.ofModel value = result := by
        simpa [dot, hmodel, Except.map] using hresult
      rw [← hpacked, ExecFloat.Binary.toModel_ofModel]

/--
The configured dot product with `status := true` has the value and the length check of the
value-only configured dot product.
-/
@[simp] theorem map_value_dot (left right : Array Value) (mode : Model.IEEERoundingMode) :
    (dot left right mode (status := true)).map (·.value) = dot left right mode := by
  unfold dot Model.dot Model.Internal.Status.dot Model.Internal.Value.dot
  by_cases hsize :
      (left.map ExecFloat.Binary.toModel).size = (right.map ExecFloat.Binary.toModel).size
  · simp only [dite_eq_left hsize]
    rfl
  · simp only [dite_eq_right hsize]
    rfl

end FloatLib.Floats.ExecFloat.Binary
