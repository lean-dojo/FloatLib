/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Runtime
public import FloatLib.Numerics.IEEEComparison
public import Mathlib.Order.WithBot

/-!
# Exact decimal comparisons

IEEE 754-2019 §5.6.1 requires 22 comparison operations, and `Datum.compareQuiet` and
`Datum.compareSignaling` take them as a predicate argument, so `x.compareQuiet .lessEqual y` is
`compareQuietLessEqual`. Comparison uses exact rational values extended by two infinities. It
ignores finite cohorts and equates signed zeros. NaNs are unordered. Quiet comparisons raise
invalid only for signaling NaNs, and signaling comparisons raise invalid for either kind of NaN.
No other exception is raised.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Exact ordered values, with negative and positive infinity at the endpoints. -/
abbrev NumericValue := WithBot (WithTop ℚ)

/-- Ordered numerical meaning. NaN is absent, rather than assigned an ordered value. -/
def Datum.numericValue? : Datum → Option NumericValue
  | .finite s c q => some ↑(↑(Datum.finiteValue s c q) : WithTop ℚ)
  | .infinity s => some (if s then ⊥ else ⊤)
  | .nan _ _ _ => none

/-- The order of two data: `none` when either is a NaN, and otherwise `some` of less, equal or
greater. -/
def Datum.compare (x y : Datum) : Option Ordering := do
  let a ← x.numericValue?
  let b ← y.numericValue?
  some (Ord.compare a b)

/--
An IEEE 754-2019 quiet comparison, with its invalid flag, raised only for a signaling NaN. The
predicate selects the operation: `.equal` is `compareQuietEqual`, `.notEqual`
`compareQuietNotEqual`, `.greater` `compareQuietGreater`, `.greaterEqual`
`compareQuietGreaterEqual`, `.less` `compareQuietLess`, `.lessEqual` `compareQuietLessEqual`,
`.unordered` `compareQuietUnordered`, `.ordered` `compareQuietOrdered`, `.lessUnordered`
`compareQuietLessUnordered`, `.notGreater` `compareQuietNotGreater`, `.notLess`
`compareQuietNotLess`, and `.greaterUnordered` `compareQuietGreaterUnordered`. Equal-valued
cohorts and signed zeros compare equal.
-/
def Datum.compareQuiet (predicate : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    Numerics.IEEEComparison.Result :=
  { value := predicate.accepts (x.compare y)
    status := { invalid := x.isSNaN || y.isSNaN } }

/--
An IEEE 754-2019 signaling comparison, with its invalid flag, raised for any NaN. The predicate
selects the operation: `.equal` is `compareSignalingEqual`, `.notEqual`
`compareSignalingNotEqual`, `.greater` `compareSignalingGreater`, `.greaterEqual`
`compareSignalingGreaterEqual`, `.less` `compareSignalingLess`, `.lessEqual`
`compareSignalingLessEqual`, `.notGreater` `compareSignalingNotGreater`, `.notLess`
`compareSignalingNotLess`, `.lessUnordered` `compareSignalingLessUnordered`, and
`.greaterUnordered` `compareSignalingGreaterUnordered`.
-/
def Datum.compareSignaling (predicate : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    Numerics.IEEEComparison.Result :=
  { value := predicate.accepts (x.compare y)
    status := { invalid := x.isNaN || y.isNaN } }

end FloatLib.Floats.Formats.DecimalInterchange
