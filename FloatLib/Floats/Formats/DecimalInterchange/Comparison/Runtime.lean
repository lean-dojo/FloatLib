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

IEEE 754-2019 §5.6.1 requires the 22 predicates of Tables 5.1–5.2.
Comparison uses exact rational values extended by two infinities; it ignores
finite cohorts and equates signed zeros. NaNs are unordered.
Quiet comparisons raise invalid only for signaling NaNs; signaling comparisons
raise invalid for either kind of NaN. No other exception is raised.
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

namespace Comparison

/-- Four comparison relations: `none` is unordered, and `some` is less, equal or greater. -/
def relation (x y : Datum) : Option Ordering := do
  let a ← x.numericValue?
  let b ← y.numericValue?
  some (compare a b)

/-- Truth sets named in the IEEE comparison tables. -/
abbrev Predicate := Numerics.IEEEComparison.Predicate

/-- A predicate result and its default IEEE exception flags. -/
abbrev Result := Numerics.IEEEComparison.Result

/-- Evaluate a quiet predicate, signaling invalid only for an sNaN operand. -/
def quiet (predicate : Predicate) (x y : Datum) : Result :=
  { value := predicate.accepts (relation x y)
    status := { invalid := x.isSignaling || y.isSignaling } }

/-- Evaluate a signaling predicate, signaling invalid for any NaN operand. -/
def signaling (predicate : Predicate) (x y : Datum) : Result :=
  { value := predicate.accepts (relation x y)
    status := { invalid := x.isNaN || y.isNaN } }

end Comparison

namespace Arithmetic

/-- Quiet equality; signed zeros and equal-valued cohorts compare equal. -/
def compareQuietEqual (x y : Datum) : Comparison.Result :=
  Comparison.quiet .equal x y
/-- Quiet inequality, true on unordered operands. -/
def compareQuietNotEqual (x y : Datum) : Comparison.Result :=
  Comparison.quiet .notEqual x y
/-- Quiet greater-than comparison. -/
def compareQuietGreater (x y : Datum) : Comparison.Result :=
  Comparison.quiet .greater x y
/-- Quiet greater-than-or-equal comparison. -/
def compareQuietGreaterEqual (x y : Datum) : Comparison.Result :=
  Comparison.quiet .greaterEqual x y
/-- Quiet less-than comparison. -/
def compareQuietLess (x y : Datum) : Comparison.Result :=
  Comparison.quiet .less x y
/-- Quiet less-than-or-equal comparison. -/
def compareQuietLessEqual (x y : Datum) : Comparison.Result :=
  Comparison.quiet .lessEqual x y
/-- Quiet test for an unordered pair. -/
def compareQuietUnordered (x y : Datum) : Comparison.Result :=
  Comparison.quiet .unordered x y
/-- Quiet test for an ordered pair. -/
def compareQuietOrdered (x y : Datum) : Comparison.Result :=
  Comparison.quiet .ordered x y
/-- Quiet less-than-or-unordered comparison, the complement of greater-than-or-equal. -/
def compareQuietLessUnordered (x y : Datum) : Comparison.Result :=
  Comparison.quiet .lessUnordered x y
/-- Quiet complement of greater-than, including unordered pairs. -/
def compareQuietNotGreater (x y : Datum) : Comparison.Result :=
  Comparison.quiet .notGreater x y
/-- Quiet complement of less-than, including unordered pairs. -/
def compareQuietNotLess (x y : Datum) : Comparison.Result :=
  Comparison.quiet .notLess x y
/-- Quiet greater-than-or-unordered comparison, the complement of less-than-or-equal. -/
def compareQuietGreaterUnordered (x y : Datum) : Comparison.Result :=
  Comparison.quiet .greaterUnordered x y

/-- Signaling equality. -/
def compareSignalingEqual (x y : Datum) : Comparison.Result :=
  Comparison.signaling .equal x y
/-- Signaling inequality, true on unordered operands. -/
def compareSignalingNotEqual (x y : Datum) : Comparison.Result :=
  Comparison.signaling .notEqual x y
/-- Signaling greater-than comparison. -/
def compareSignalingGreater (x y : Datum) : Comparison.Result :=
  Comparison.signaling .greater x y
/-- Signaling greater-than-or-equal comparison. -/
def compareSignalingGreaterEqual (x y : Datum) : Comparison.Result :=
  Comparison.signaling .greaterEqual x y
/-- Signaling less-than comparison. -/
def compareSignalingLess (x y : Datum) : Comparison.Result :=
  Comparison.signaling .less x y
/-- Signaling less-than-or-equal comparison. -/
def compareSignalingLessEqual (x y : Datum) : Comparison.Result :=
  Comparison.signaling .lessEqual x y
/-- Signaling complement of greater-than. -/
def compareSignalingNotGreater (x y : Datum) : Comparison.Result :=
  Comparison.signaling .notGreater x y
/-- Signaling complement of less-than. -/
def compareSignalingNotLess (x y : Datum) : Comparison.Result :=
  Comparison.signaling .notLess x y
/-- Signaling less-than-or-unordered comparison. -/
def compareSignalingLessUnordered (x y : Datum) : Comparison.Result :=
  Comparison.signaling .lessUnordered x y
/-- Signaling greater-than-or-unordered comparison. -/
def compareSignalingGreaterUnordered (x y : Datum) : Comparison.Result :=
  Comparison.signaling .greaterUnordered x y

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
