/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Predicates.Runtime

/-!
# IEEE predicates on configured binary values

These operations decode the configured carrier and use the model's exact comparison.
The Boolean answer and exception flags pass through unchanged. Quiet and signaling
names follow IEEE 754-2019 Tables 5.1–5.2.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Quiet comparison under an explicit IEEE predicate, with its invalid flag. -/
@[inline] def compareQuiet (predicate : Model.Comparison.Predicate) (x y : Value) :
    Model.Comparison.Result :=
  Model.Comparison.quiet predicate (toModel x) (toModel y)

/-- Signaling comparison under an explicit IEEE predicate, with its invalid flag. -/
@[inline] def compareSignaling (predicate : Model.Comparison.Predicate) (x y : Value) :
    Model.Comparison.Result :=
  Model.Comparison.signaling predicate (toModel x) (toModel y)

/-- Quiet equality on configured values. -/
@[inline] def compareQuietEqual (x y : Value) : Model.Comparison.Result :=
  compareQuiet .equal x y

/-- Quiet inequality, including unordered operands on configured values. -/
@[inline] def compareQuietNotEqual (x y : Value) : Model.Comparison.Result :=
  compareQuiet .notEqual x y

/-- Quiet greater-than comparison on configured values. -/
@[inline] def compareQuietGreater (x y : Value) : Model.Comparison.Result :=
  compareQuiet .greater x y

/-- Quiet greater-than-or-equal comparison on configured values. -/
@[inline] def compareQuietGreaterEqual (x y : Value) : Model.Comparison.Result :=
  compareQuiet .greaterEqual x y

/-- Quiet less-than comparison on configured values. -/
@[inline] def compareQuietLess (x y : Value) : Model.Comparison.Result :=
  compareQuiet .less x y

/-- Quiet less-than-or-equal comparison on configured values. -/
@[inline] def compareQuietLessEqual (x y : Value) : Model.Comparison.Result :=
  compareQuiet .lessEqual x y

/-- Quiet test for unordered operands on configured values. -/
@[inline] def compareQuietUnordered (x y : Value) : Model.Comparison.Result :=
  compareQuiet .unordered x y

/-- Quiet test for ordered operands on configured values. -/
@[inline] def compareQuietOrdered (x y : Value) : Model.Comparison.Result :=
  compareQuiet .ordered x y

/-- Quiet less-than-or-unordered comparison on configured values. -/
@[inline] def compareQuietLessUnordered (x y : Value) : Model.Comparison.Result :=
  compareQuiet .lessUnordered x y

/-- Quiet complement of greater-than on configured values. -/
@[inline] def compareQuietNotGreater (x y : Value) : Model.Comparison.Result :=
  compareQuiet .notGreater x y

/-- Quiet complement of less-than on configured values. -/
@[inline] def compareQuietNotLess (x y : Value) : Model.Comparison.Result :=
  compareQuiet .notLess x y

/-- Quiet greater-than-or-unordered comparison on configured values. -/
@[inline] def compareQuietGreaterUnordered (x y : Value) : Model.Comparison.Result :=
  compareQuiet .greaterUnordered x y

/-- Signaling equality on configured values. -/
@[inline] def compareSignalingEqual (x y : Value) : Model.Comparison.Result :=
  compareSignaling .equal x y

/-- Signaling inequality, including unordered operands on configured values. -/
@[inline] def compareSignalingNotEqual (x y : Value) : Model.Comparison.Result :=
  compareSignaling .notEqual x y

/-- Signaling greater-than comparison on configured values. -/
@[inline] def compareSignalingGreater (x y : Value) : Model.Comparison.Result :=
  compareSignaling .greater x y

/-- Signaling greater-than-or-equal comparison on configured values. -/
@[inline] def compareSignalingGreaterEqual (x y : Value) : Model.Comparison.Result :=
  compareSignaling .greaterEqual x y

/-- Signaling less-than comparison on configured values. -/
@[inline] def compareSignalingLess (x y : Value) : Model.Comparison.Result :=
  compareSignaling .less x y

/-- Signaling less-than-or-equal comparison on configured values. -/
@[inline] def compareSignalingLessEqual (x y : Value) : Model.Comparison.Result :=
  compareSignaling .lessEqual x y

/-- Signaling less-than-or-unordered comparison on configured values. -/
@[inline] def compareSignalingLessUnordered (x y : Value) : Model.Comparison.Result :=
  compareSignaling .lessUnordered x y

/-- Signaling complement of greater-than on configured values. -/
@[inline] def compareSignalingNotGreater (x y : Value) : Model.Comparison.Result :=
  compareSignaling .notGreater x y

/-- Signaling complement of less-than on configured values. -/
@[inline] def compareSignalingNotLess (x y : Value) : Model.Comparison.Result :=
  compareSignaling .notLess x y

/-- Signaling greater-than-or-unordered comparison on configured values. -/
@[inline] def compareSignalingGreaterUnordered (x y : Value) : Model.Comparison.Result :=
  compareSignaling .greaterUnordered x y

end FloatLib.Floats.ExecFloat.Binary
