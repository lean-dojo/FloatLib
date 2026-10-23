/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Tree

/-!
# Configured reduction schedules

Decoding commutes with a reduction that rounds at every addition, independently of the storage
plan. Nearest-even finite executions inherit the model's half-ULP error budget. The round-once
collection API is separate.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]
    [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]
    [cap : ExecFloat.Add (Configured.Family format code plan)]
    [ExecFloat.Capability.HasSpec cap Configured.Spec.add]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
Decoding commutes with evaluating a schedule that rounds each addition in `mode`, for an addition
capability whose reference operation is the configured model addition, as `toModel_add` requires.
-/
theorem toModel_eval_tree (t : ReductionTree Value) (mode : Model.IEEERoundingMode) :
    toModel (t.eval (fun x y => add x y (mode := mode)) id) =
      (t.map toModel).eval (fun x y => Model.add x y (mode := mode)) id := by
  induction t with
  | leaf x => rfl
  | node a b ha hb =>
      simp only [ReductionTree.eval, ReductionTree.map, toModel_add, ha, hb]

/--
Configured nearest-even execution on an IEEE descriptor inherits the finite model's absolute
error enclosure, for an addition capability whose reference operation is the configured model
addition.
-/
theorem abs_toReal_eval_tree_sub_sum_le (t : ReductionTree Value)
    (hformat : format.isIEEE = true)
    (hfinite : Model.ReductionTree.FiniteEval (t.map toModel)) :
    |Model.toReal (toModel (t.eval (fun x y => add x y) id)) -
        (t.leaves.map (Model.toReal ∘ toModel)).sum| ≤
      Model.ReductionTree.errorBudget (t.map toModel) := by
  rw [toModel_eval_tree]
  simpa only [ReductionTree.leaves_map, List.map_map] using
    Model.ReductionTree.abs_toReal_eval_sub_sum_le (t.map toModel) hformat hfinite

end FloatLib.Floats.ExecFloat.Binary
