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

IEEE 754-2019 Tables 5.1–5.2 specify 22 comparison operations. Their truth values depend
on exact numerical comparison, with NaNs unordered and signed zeros equal. Quiet
operations raise invalid for signaling NaNs; signaling operations do so for any NaN.
Neither family raises any of the other four exceptions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

namespace Comparison

/-- Shared IEEE truth sets, independent of the operand format. -/
abbrev Predicate := Numerics.IEEEComparison.Predicate

/-- A Boolean comparison result paired with its exception indicators. -/
abbrev Result := Numerics.IEEEComparison.Result

/-- Evaluate a quiet predicate; only signaling NaNs raise invalid. -/
def quiet {fmt : FloatFormat} (predicate : Predicate) (x y : Model fmt) : Result :=
  { value := predicate.accepts (compare x y)
    status := { invalid := isSNaN x || isSNaN y } }

/-- Evaluate a signaling predicate; either kind of NaN raises invalid. -/
def signaling {fmt : FloatFormat} (predicate : Predicate) (x y : Model fmt) : Result :=
  { value := predicate.accepts (compare x y)
    status := { invalid := isNaN x || isNaN y } }

end Comparison

/-- Quiet equality, equating signed zeros. -/
def compareQuietEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .equal x y
/-- Quiet inequality, including unordered operands. -/
def compareQuietNotEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .notEqual x y
/-- Quiet greater-than comparison. -/
def compareQuietGreater {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .greater x y
/-- Quiet greater-than-or-equal comparison. -/
def compareQuietGreaterEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .greaterEqual x y
/-- Quiet less-than comparison. -/
def compareQuietLess {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .less x y
/-- Quiet less-than-or-equal comparison. -/
def compareQuietLessEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .lessEqual x y
/-- Quiet test for unordered operands. -/
def compareQuietUnordered {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .unordered x y
/-- Quiet test for ordered operands. -/
def compareQuietOrdered {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .ordered x y
/-- Quiet less-than-or-unordered comparison. -/
def compareQuietLessUnordered {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .lessUnordered x y
/-- Quiet complement of greater-than. -/
def compareQuietNotGreater {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .notGreater x y
/-- Quiet complement of less-than. -/
def compareQuietNotLess {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .notLess x y
/-- Quiet greater-than-or-unordered comparison. -/
def compareQuietGreaterUnordered {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.quiet .greaterUnordered x y

/-- Signaling equality. -/
def compareSignalingEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .equal x y
/-- Signaling inequality, including unordered operands. -/
def compareSignalingNotEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .notEqual x y
/-- Signaling greater-than comparison. -/
def compareSignalingGreater {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .greater x y
/-- Signaling greater-than-or-equal comparison. -/
def compareSignalingGreaterEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .greaterEqual x y
/-- Signaling less-than comparison. -/
def compareSignalingLess {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .less x y
/-- Signaling less-than-or-equal comparison. -/
def compareSignalingLessEqual {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .lessEqual x y
/-- Signaling complement of greater-than. -/
def compareSignalingNotGreater {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .notGreater x y
/-- Signaling complement of less-than. -/
def compareSignalingNotLess {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .notLess x y
/-- Signaling less-than-or-unordered comparison. -/
def compareSignalingLessUnordered {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .lessUnordered x y
/-- Signaling greater-than-or-unordered comparison. -/
def compareSignalingGreaterUnordered {fmt : FloatFormat} (x y : Model fmt) : Comparison.Result :=
  Comparison.signaling .greaterUnordered x y

end FloatLib.Floats.Formats.BinaryInterchange.Model
