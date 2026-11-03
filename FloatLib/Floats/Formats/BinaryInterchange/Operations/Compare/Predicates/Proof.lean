/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Predicates.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof

/-!
# Binary predicate semantics

All predicates use exact extended-real order on non-NaN inputs and their specified
unordered truth value on NaNs. The exception theorems distinguish quiet and signaling
comparisons without changing their Boolean answers.
-/

public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Every quiet predicate agrees with its truth table on exact extended-real order. -/
theorem compareQuiet_value_of_toEReal? {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) :
    (compareQuiet predicate x y).value = predicate.accepts (some (Ord.compare a b)) := by
  simp [compareQuiet, compare_eq_of_toEReal? hx hy]

/-- Every signaling predicate has the same exact numerical truth table. -/
theorem compareSignaling_value_of_toEReal? {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) :
    (compareSignaling predicate x y).value = predicate.accepts (some (Ord.compare a b)) := by
  simp [compareSignaling, compare_eq_of_toEReal? hx hy]

/-- NaN operands select the predicate's unordered truth value. -/
theorem compareQuiet_value_of_nan {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt)
    (h : isNaN x = true ∨ isNaN y = true) :
    (compareQuiet predicate x y).value = predicate.accepts none := by
  simp [compareQuiet, (compare_eq_none_iff x y).2 h]

/-- Signaling comparison uses the same unordered truth value as quiet comparison. -/
theorem compareSignaling_value_of_nan {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt)
    (h : isNaN x = true ∨ isNaN y = true) :
    (compareSignaling predicate x y).value = predicate.accepts none := by
  simp [compareSignaling, (compare_eq_none_iff x y).2 h]

/-- Quiet and signaling comparisons differ only in their exception behavior. -/
theorem compareQuiet_value_eq_compareSignaling {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt) :
    (compareQuiet predicate x y).value = (compareSignaling predicate x y).value := rfl

/-- Quiet comparisons raise invalid exactly for signaling NaN operands. -/
theorem compareQuiet_invalid_iff {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt) :
    (compareQuiet predicate x y).status.invalid = true ↔
      isSNaN x = true ∨ isSNaN y = true := by
  simp [compareQuiet]

/-- Signaling comparisons raise invalid exactly for NaN operands. -/
theorem compareSignaling_invalid_iff {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt) :
    (compareSignaling predicate x y).status.invalid = true ↔
      isNaN x = true ∨ isNaN y = true := by
  simp [compareSignaling]

/-- Quiet comparison raises no range, division, or inexact exception. -/
theorem compareQuiet_status {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt) :
    (compareQuiet predicate x y).status = { invalid := isSNaN x || isSNaN y } := rfl

/-- Signaling comparison raises no range, division, or inexact exception. -/
theorem compareSignaling_status {fmt : FloatFormat}
    (predicate : Numerics.IEEEComparison.Predicate) (x y : Model fmt) :
    (compareSignaling predicate x y).status = { invalid := isNaN x || isNaN y } := rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model
