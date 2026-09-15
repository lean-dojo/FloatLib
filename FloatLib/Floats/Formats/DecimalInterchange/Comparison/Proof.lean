/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Comparison.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Proof

/-!
# Ordered numerical semantics and exception guarantees of decimal comparisons

Decimal comparison agrees with exact extended-rational order, treats either NaN as unordered,
and respects cohorts. Quiet predicates raise `invalid` exactly for signaling NaNs; signaling
predicates raise it for any NaN.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Datum

@[simp] theorem numericValue?_eq_none_iff (x : Datum) :
    x.numericValue? = none ↔ x.isNaN = true := by
  cases x <;> simp [numericValue?, isNaN]

theorem sameCohort_numericValue? {x y : Datum} (h : x.SameCohort y) :
    x.numericValue? = y.numericValue? := by
  cases x <;> cases y <;> simp only [SameCohort] at h
  · rcases h with ⟨rfl, h⟩
    simp only [numericValue?, finiteValue, mul_assoc, h]
  · rcases h with rfl
    rfl

end Datum

namespace Comparison

/-- Exactly the pairs containing a NaN are unordered. -/
theorem relation_eq_none_iff (x y : Datum) :
    relation x y = none ↔ x.isNaN = true ∨ y.isNaN = true := by
  simp only [relation, ← Datum.numericValue?_eq_none_iff]
  cases x.numericValue? <;> cases y.numericValue? <;> simp

/-- A less-than result means strict order in the exact extended rationals. -/
theorem relation_eq_lt_iff (x y : Datum) :
    relation x y = some .lt ↔
      ∃ a b : NumericValue, x.numericValue? = some a ∧
        y.numericValue? = some b ∧ a < b := by
  unfold relation
  cases x.numericValue? <;> cases y.numericValue? <;>
    simp [compare_lt_iff_lt]

/-- Equality compares exact numerical values, rather than stored cohorts. -/
theorem relation_eq_eq_iff (x y : Datum) :
    relation x y = some .eq ↔
      ∃ a : NumericValue, x.numericValue? = some a ∧ y.numericValue? = some a := by
  unfold relation
  cases x.numericValue? <;> cases y.numericValue? <;> simp
  exact eq_comm

theorem relation_eq_gt_iff (x y : Datum) :
    relation x y = some .gt ↔
      ∃ a b : NumericValue, x.numericValue? = some a ∧
        y.numericValue? = some b ∧ b < a := by
  unfold relation
  cases x.numericValue? <;> cases y.numericValue? <;>
    simp [compare_gt_iff_gt]

/-- Every finite comparison agrees with exact signed rational comparison. -/
theorem relation_finite_lt_iff (s t : Bool) (c d : Nat) (q r : Int) :
    relation (.finite s c q) (.finite t d r) = some .lt ↔
      Datum.finiteValue s c q < Datum.finiteValue t d r := by
  simp [relation_eq_lt_iff, Datum.numericValue?]

theorem relation_finite_eq_iff (s t : Bool) (c d : Nat) (q r : Int) :
    relation (.finite s c q) (.finite t d r) = some .eq ↔
      Datum.finiteValue s c q = Datum.finiteValue t d r := by
  rw [relation_eq_eq_iff]
  simp [Datum.numericValue?]
  exact eq_comm

theorem relation_zero_zero (s t : Bool) (q r : Int) :
    relation (.finite s 0 q) (.finite t 0 r) = some .eq :=
  (relation_finite_eq_iff s t 0 0 q r).2 (by simp [Datum.finiteValue])

/-- Replacing either operand by a member of its cohort preserves comparison. -/
theorem relation_sameCohort {x x' y y' : Datum}
    (hx : x.SameCohort x') (hy : y.SameCohort y') :
    relation x y = relation x' y' := by
  simp only [relation, Datum.sameCohort_numericValue? hx, Datum.sameCohort_numericValue? hy]

theorem quiet_invalid_iff (p : Predicate) (x y : Datum) :
    (quiet p x y).status.invalid = true ↔
      x.isSignaling = true ∨ y.isSignaling = true := by
  simp [quiet]

theorem signaling_invalid_iff (p : Predicate) (x y : Datum) :
    (signaling p x y).status.invalid = true ↔
      x.isNaN = true ∨ y.isNaN = true := by
  simp [signaling]

/-- Quiet and signaling variants have identical truth values, including on NaNs. -/
theorem quiet_value_eq_signaling (p : Predicate) (x y : Datum) :
    (quiet p x y).value = (signaling p x y).value := rfl

/-- Complete truth-set specification, stated in terms of exact ordered values
and unordered NaN operands. Together with the status theorems this covers all
22 named comparison entry points. -/
theorem quiet_value_iff (p : Predicate) (x y : Datum) :
    (quiet p x y).value = true ↔
      (p.accepts none = true ∧ (x.isNaN = true ∨ y.isNaN = true)) ∨
      (p.accepts (some .lt) = true ∧ ∃ a b : NumericValue,
        x.numericValue? = some a ∧ y.numericValue? = some b ∧ a < b) ∨
      (p.accepts (some .eq) = true ∧ ∃ a : NumericValue,
        x.numericValue? = some a ∧ y.numericValue? = some a) ∨
      (p.accepts (some .gt) = true ∧ ∃ a b : NumericValue,
        x.numericValue? = some a ∧ y.numericValue? = some b ∧ b < a) := by
  rw [← relation_eq_none_iff, ← relation_eq_lt_iff, ← relation_eq_eq_iff,
    ← relation_eq_gt_iff]
  cases h : relation x y with
  | none => simp [quiet, h]
  | some r => cases r <;> simp [quiet, h]

/-- Comparison never raises numerical range, division, or inexact exceptions. -/
theorem quiet_status (p : Predicate) (x y : Datum) :
    (quiet p x y).status = { invalid := x.isSignaling || y.isSignaling } := rfl

theorem signaling_status (p : Predicate) (x y : Datum) :
    (signaling p x y).status = { invalid := x.isNaN || y.isNaN } := rfl

end Comparison
end FloatLib.Floats.Formats.DecimalInterchange
