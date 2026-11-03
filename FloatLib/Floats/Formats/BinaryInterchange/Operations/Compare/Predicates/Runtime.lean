/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Numerics.IEEEComparison

/-!
# Quiet and signaling binary comparisons

IEEE 754-2019 §5.6.1 specifies 22 comparison operations. Their truth values depend on exact
numerical comparison, with NaNs unordered and signed zeros equal. `compareQuiet` takes the twelve
quiet ones as a predicate argument and `compareSignaling` the ten signaling ones, so
`compareQuiet .lessEqual x y` is the standard's `compareQuietLessEqual`. Quiet operations raise
invalid for signaling NaNs, and signaling operations do so for any NaN. Neither family raises any
of the other four exceptions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/--
An IEEE 754-2019 quiet comparison, with its invalid flag. The predicate selects the operation:
`.equal` is `compareQuietEqual`, `.notEqual` `compareQuietNotEqual`, `.greater`
`compareQuietGreater`, `.greaterEqual` `compareQuietGreaterEqual`, `.less` `compareQuietLess`,
`.lessEqual` `compareQuietLessEqual`, `.unordered` `compareQuietUnordered`, `.ordered`
`compareQuietOrdered`, `.lessUnordered` `compareQuietLessUnordered`, `.notGreater`
`compareQuietNotGreater`, `.notLess` `compareQuietNotLess`, and `.greaterUnordered`
`compareQuietGreaterUnordered`. Only a signaling NaN operand raises invalid.
-/
def compareQuiet {fmt : FloatFormat} (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Model fmt) : Numerics.IEEEComparison.Result :=
  { value := predicate.accepts (compare x y)
    status := { invalid := isSNaN x || isSNaN y } }

/--
An IEEE 754-2019 signaling comparison, with its invalid flag. The predicate selects the operation:
`.equal` is `compareSignalingEqual`, `.notEqual` `compareSignalingNotEqual`, `.greater`
`compareSignalingGreater`, `.greaterEqual` `compareSignalingGreaterEqual`, `.less`
`compareSignalingLess`, `.lessEqual` `compareSignalingLessEqual`, `.notGreater`
`compareSignalingNotGreater`, `.notLess` `compareSignalingNotLess`, `.lessUnordered`
`compareSignalingLessUnordered`, and `.greaterUnordered` `compareSignalingGreaterUnordered`. Any NaN
operand raises invalid. The standard names no signaling form of `.unordered` and `.ordered`, which
evaluate here with the same truth table.
-/
def compareSignaling {fmt : FloatFormat} (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Model fmt) : Numerics.IEEEComparison.Result :=
  { value := predicate.accepts (compare x y)
    status := { invalid := isNaN x || isNaN y } }

end FloatLib.Floats.Formats.BinaryInterchange.Model
