/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Predicates.Proof

/-!
# Configured comparison semantics

Configured predicates preserve the complete model result, including flags. The numerical
theorems connect both quiet and signaling operations to exact extended-real order.
-/

public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Quiet comparison preserves the model's answer and all five flags. -/
theorem compareQuiet_eq_model (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Value) :
    compareQuiet predicate x y =
      Model.compareQuiet predicate (toModel x) (toModel y) := rfl

/-- Signaling comparison preserves the model's answer and all five flags. -/
theorem compareSignaling_eq_model (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Value) :
    compareSignaling predicate x y =
      Model.compareSignaling predicate (toModel x) (toModel y) := rfl

/-- Configured quiet predicates use exact extended-real order on non-NaN operands. -/
theorem compareQuiet_value_of_toEReal? (predicate : Numerics.IEEEComparison.Predicate)
    {x y : Value} {a b : EReal}
    (hx : Model.toEReal? (toModel x) = some a)
    (hy : Model.toEReal? (toModel y) = some b) :
    (compareQuiet predicate x y).value = predicate.accepts (some (compare a b)) :=
  Model.compareQuiet_value_of_toEReal? predicate hx hy

/-- Configured signaling predicates use the same exact numerical order. -/
theorem compareSignaling_value_of_toEReal? (predicate : Numerics.IEEEComparison.Predicate)
    {x y : Value} {a b : EReal}
    (hx : Model.toEReal? (toModel x) = some a)
    (hy : Model.toEReal? (toModel y) = some b) :
    (compareSignaling predicate x y).value = predicate.accepts (some (compare a b)) :=
  Model.compareSignaling_value_of_toEReal? predicate hx hy

/-- Quiet configured comparison raises invalid if and only if an operand is a signaling NaN. -/
theorem compareQuiet_invalid_iff (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Value) :
    (compareQuiet predicate x y).status.invalid = true ↔
      Model.isSNaN (toModel x) = true ∨ Model.isSNaN (toModel y) = true :=
  Model.compareQuiet_invalid_iff predicate _ _

/-- Signaling configured comparison raises invalid if and only if an operand is a NaN. -/
theorem compareSignaling_invalid_iff (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Value) :
    (compareSignaling predicate x y).status.invalid = true ↔
      Model.isNaN (toModel x) = true ∨ Model.isNaN (toModel y) = true :=
  Model.compareSignaling_invalid_iff predicate _ _

end FloatLib.Floats.ExecFloat.Binary
