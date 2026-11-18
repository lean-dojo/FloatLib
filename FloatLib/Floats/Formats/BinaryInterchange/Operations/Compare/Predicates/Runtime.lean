/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Numerics.IEEEComparison
public meta import FloatLib.Tactic.IEEENames

/-!
# Quiet and signaling binary comparisons

IEEE 754-2019 §5.11 specifies 22 comparison operations. Their truth values depend on exact
numerical comparison, with NaNs unordered and signed zeros equal. `compareQuiet` takes the twelve
quiet ones as a predicate argument and `compareSignaling` the ten signaling ones, so
`compareQuiet .lessEqual x y` is the standard's `compareQuietLessEqual`. Quiet operations raise
invalid for signaling NaNs, and signaling operations do so for any NaN. Neither family raises any
of the other four exceptions.

The 22 operations are also declared under their own names, `compareQuietEqual` to
`compareSignalingGreaterUnordered` (ISO/IEC 9899:2024 Annex F, Table F.2), each as its family at
one predicate, so the theorems of `compareQuiet` and `compareSignaling` apply to them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/--
An IEEE 754-2019 §5.11 quiet comparison, with its invalid flag. The predicate selects the
operation:
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
    status := { invalid := isSignaling x || isSignaling y } }

/--
An IEEE 754-2019 signaling comparison, with its invalid flag. The predicate selects the operation:
`.equal` is `compareSignalingEqual`, `.notEqual` `compareSignalingNotEqual`, `.greater`
`compareSignalingGreater`, `.greaterEqual` `compareSignalingGreaterEqual`, `.less`
`compareSignalingLess`, `.lessEqual` `compareSignalingLessEqual`, `.notGreater`
`compareSignalingNotGreater`, `.notLess` `compareSignalingNotLess`, `.lessUnordered`
`compareSignalingLessUnordered`, and `.greaterUnordered` `compareSignalingGreaterUnordered`. Any NaN
operand raises invalid. The standard names no signaling form of `.unordered` and `.ordered`, which
evaluate here with the same truth table.

Reference: IEEE 754-2019 §5.11.
-/
def compareSignaling {fmt : FloatFormat} (predicate : Numerics.IEEEComparison.Predicate)
    (x y : Model fmt) : Numerics.IEEEComparison.Result :=
  { value := predicate.accepts (compare x y)
    status := { invalid := isNaN x || isNaN y } }

/-! ## The 22 comparisons by their names in the standard -/

ieee_by_predicate "IEEE 754-2019 §5.11" compareQuiet {fmt : FloatFormat} (x y : Model fmt) :
    Numerics.IEEEComparison.Result := fun predicate => compareQuiet predicate x y

ieee_by_predicate "IEEE 754-2019 §5.11" compareSignaling {fmt : FloatFormat} (x y : Model fmt) :
    Numerics.IEEEComparison.Result := fun predicate => compareSignaling predicate x y
  without unordered ordered

end FloatLib.Floats.Formats.BinaryInterchange.Model
