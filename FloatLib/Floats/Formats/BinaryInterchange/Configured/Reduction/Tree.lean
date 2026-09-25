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
plan. Nearest-even finite executions inherit the model's half-ULP error budget. These theorems
are separate from the configured round-once collection API.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-- Decoding preserves the entire schedule and its chosen rounding mode. -/
theorem toModel_eval_tree (t : ReductionTree Value) (rounding : Model.IEEERoundingMode) :
    toModel (t.eval (fun x y => addWithRounding x y rounding) id) =
      (t.map toModel).eval (Model.addWithRounding rounding) id := by
  induction t with
  | leaf x => rfl
  | node a b ha hb =>
      simp only [ReductionTree.eval, ReductionTree.map, toModel_addWithRounding, ha, hb]

/-- Configured nearest-even execution inherits the finite model's absolute error enclosure. -/
theorem abs_toReal_eval_tree_sub_sum_le (t : ReductionTree Value)
    (hformat : format.isIEEE = true)
    (hfinite : Model.ReductionTree.FiniteEval (t.map toModel)) :
    |Model.toReal (toModel (t.eval (fun x y => addWithRounding x y .nearestEven) id)) -
        (t.leaves.map (Model.toReal ∘ toModel)).sum| ≤
      Model.ReductionTree.errorBudget (t.map toModel) := by
  rw [toModel_eval_tree]
  have hadd : (Model.addWithRounding .nearestEven : Model format → Model format → Model format) =
      Model.add := by
    funext x y
    rfl
  rw [hadd]
  simpa only [ReductionTree.leaves_map, List.map_map] using
    Model.ReductionTree.abs_toReal_eval_sub_sum_le (t.map toModel) hformat hfinite

end FloatLib.Floats.ExecFloat.Binary
