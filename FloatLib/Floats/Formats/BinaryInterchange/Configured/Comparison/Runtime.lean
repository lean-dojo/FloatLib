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

These operations decode the configured carrier and use the model's exact comparison. The Boolean
answer and exception flags pass through unchanged. The predicate argument selects one of the 22
IEEE 754-2019 §5.6.1 comparisons, so `x.compareQuiet .lessEqual y` is `compareQuietLessEqual`.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
An IEEE 754-2019 quiet comparison, with its invalid flag, raised only for a signaling NaN. The
predicate selects the operation: `.equal` is `compareQuietEqual`, `.notEqual`
`compareQuietNotEqual`, `.greater` `compareQuietGreater`, `.greaterEqual`
`compareQuietGreaterEqual`, `.less` `compareQuietLess`, `.lessEqual` `compareQuietLessEqual`,
`.unordered` `compareQuietUnordered`, `.ordered` `compareQuietOrdered`, `.lessUnordered`
`compareQuietLessUnordered`, `.notGreater` `compareQuietNotGreater`, `.notLess`
`compareQuietNotLess`, and `.greaterUnordered` `compareQuietGreaterUnordered`.
-/
@[inline] def compareQuiet (predicate : Numerics.IEEEComparison.Predicate) (x y : Value) :
    Numerics.IEEEComparison.Result :=
  Model.compareQuiet predicate (toModel x) (toModel y)

/--
An IEEE 754-2019 signaling comparison, with its invalid flag, raised for any NaN. The predicate
selects the operation: `.equal` is `compareSignalingEqual`, `.notEqual`
`compareSignalingNotEqual`, `.greater` `compareSignalingGreater`, `.greaterEqual`
`compareSignalingGreaterEqual`, `.less` `compareSignalingLess`, `.lessEqual`
`compareSignalingLessEqual`, `.notGreater` `compareSignalingNotGreater`, `.notLess`
`compareSignalingNotLess`, `.lessUnordered` `compareSignalingLessUnordered`, and
`.greaterUnordered` `compareSignalingGreaterUnordered`.
-/
@[inline] def compareSignaling (predicate : Numerics.IEEEComparison.Predicate) (x y : Value) :
    Numerics.IEEEComparison.Result :=
  Model.compareSignaling predicate (toModel x) (toModel y)

end FloatLib.Floats.ExecFloat.Binary
