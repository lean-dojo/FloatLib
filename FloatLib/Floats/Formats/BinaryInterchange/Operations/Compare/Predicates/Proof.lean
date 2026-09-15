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

namespace Comparison

/-- Every quiet predicate agrees with its truth table on exact extended-real order. -/
theorem quiet_value_of_toEReal? {fmt : FloatFormat} (predicate : Predicate)
    {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) :
    (quiet predicate x y).value = predicate.accepts (some (Ord.compare a b)) := by
  simp [quiet, compare_eq_of_toEReal? hx hy]

/-- Every signaling predicate has the same exact numerical truth table. -/
theorem signaling_value_of_toEReal? {fmt : FloatFormat} (predicate : Predicate)
    {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) :
    (signaling predicate x y).value = predicate.accepts (some (Ord.compare a b)) := by
  simp [signaling, compare_eq_of_toEReal? hx hy]

/-- NaN operands select the predicate's unordered truth value. -/
theorem quiet_value_of_nan {fmt : FloatFormat} (predicate : Predicate)
    (x y : Model fmt) (h : isNaN x = true ∨ isNaN y = true) :
    (quiet predicate x y).value = predicate.accepts none := by
  simp [quiet, (compare_eq_none_iff x y).2 h]

/-- Signaling comparison uses the same unordered truth value as quiet comparison. -/
theorem signaling_value_of_nan {fmt : FloatFormat} (predicate : Predicate)
    (x y : Model fmt) (h : isNaN x = true ∨ isNaN y = true) :
    (signaling predicate x y).value = predicate.accepts none := by
  simp [signaling, (compare_eq_none_iff x y).2 h]

/-- Quiet and signaling comparisons differ only in their exception behavior. -/
theorem quiet_value_eq_signaling {fmt : FloatFormat} (predicate : Predicate)
    (x y : Model fmt) :
    (quiet predicate x y).value = (signaling predicate x y).value := rfl

/-- Quiet comparisons raise invalid exactly for signaling NaN operands. -/
theorem quiet_invalid_iff {fmt : FloatFormat} (predicate : Predicate) (x y : Model fmt) :
    (quiet predicate x y).status.invalid = true ↔
      isSNaN x = true ∨ isSNaN y = true := by
  simp [quiet]

/-- Signaling comparisons raise invalid exactly for NaN operands. -/
theorem signaling_invalid_iff {fmt : FloatFormat} (predicate : Predicate) (x y : Model fmt) :
    (signaling predicate x y).status.invalid = true ↔
      isNaN x = true ∨ isNaN y = true := by
  simp [signaling]

/-- Quiet comparison raises no range, division, or inexact exception. -/
theorem quiet_status {fmt : FloatFormat} (predicate : Predicate) (x y : Model fmt) :
    (quiet predicate x y).status = { invalid := isSNaN x || isSNaN y } := rfl

/-- Signaling comparison raises no range, division, or inexact exception. -/
theorem signaling_status {fmt : FloatFormat} (predicate : Predicate) (x y : Model fmt) :
    (signaling predicate x y).status = { invalid := isNaN x || isNaN y } := rfl

end Comparison
end FloatLib.Floats.Formats.BinaryInterchange.Model
