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

/-- A datum has no extended-rational value exactly when it is a NaN; infinities and both zeros have
one. -/
@[simp] theorem numericValue?_eq_none_iff (x : Datum) :
    x.numericValue? = none ↔ x.isNaN = true := by
  cases x <;> simp [numericValue?, isNaN]

/-- Members of one cohort have the same extended-rational value. -/
theorem sameCohort_numericValue? {x y : Datum} (h : x.SameCohort y) :
    x.numericValue? = y.numericValue? := by
  cases x <;> cases y <;> simp only [SameCohort] at h
  · rcases h with ⟨rfl, h⟩
    simp only [numericValue?, finiteValue, mul_assoc, h]
  · rcases h with rfl
    rfl

end Datum

namespace Datum

/-- Exactly the pairs containing a NaN are unordered. -/
theorem compare_eq_none_iff (x y : Datum) :
    Datum.compare x y = none ↔ x.isNaN = true ∨ y.isNaN = true := by
  simp only [Datum.compare, ← Datum.numericValue?_eq_none_iff]
  cases x.numericValue? <;> cases y.numericValue? <;> simp

/-- A less-than result means strict order in the exact extended rationals. -/
theorem compare_eq_lt_iff (x y : Datum) :
    Datum.compare x y = some .lt ↔
      ∃ a b : NumericValue, x.numericValue? = some a ∧
        y.numericValue? = some b ∧ a < b := by
  unfold Datum.compare
  cases x.numericValue? <;> cases y.numericValue? <;>
    simp [compare_lt_iff_lt]

/-- Equality compares exact numerical values, rather than stored cohorts. -/
theorem compare_eq_eq_iff (x y : Datum) :
    Datum.compare x y = some .eq ↔
      ∃ a : NumericValue, x.numericValue? = some a ∧ y.numericValue? = some a := by
  unfold Datum.compare
  cases x.numericValue? <;> cases y.numericValue? <;> simp
  exact eq_comm

/-- A greater-than result means the first operand is strictly greater in the exact extended
rationals. -/
theorem compare_eq_gt_iff (x y : Datum) :
    Datum.compare x y = some .gt ↔
      ∃ a b : NumericValue, x.numericValue? = some a ∧
        y.numericValue? = some b ∧ b < a := by
  unfold Datum.compare
  cases x.numericValue? <;> cases y.numericValue? <;>
    simp [compare_gt_iff_gt]

/-- Every finite comparison agrees with exact signed rational comparison. -/
theorem compare_finite_lt_iff (s t : Bool) (c d : Nat) (q r : Int) :
    Datum.compare (.finite s c q) (.finite t d r) = some .lt ↔
      Datum.finiteValue s c q < Datum.finiteValue t d r := by
  simp [compare_eq_lt_iff, Datum.numericValue?]

/-- Two finite datums compare equal exactly when their exact signed values are equal, whatever their
cohorts. -/
theorem compare_finite_eq_iff (s t : Bool) (c d : Nat) (q r : Int) :
    Datum.compare (.finite s c q) (.finite t d r) = some .eq ↔
      Datum.finiteValue s c q = Datum.finiteValue t d r := by
  rw [compare_eq_eq_iff]
  simp [Datum.numericValue?]
  exact eq_comm

/-- Any two zeros compare equal, whatever their signs and quanta. -/
theorem compare_zero_zero (s t : Bool) (q r : Int) :
    Datum.compare (.finite s 0 q) (.finite t 0 r) = some .eq :=
  (compare_finite_eq_iff s t 0 0 q r).2 (by simp [Datum.finiteValue])

/-- Replacing either operand by a member of its cohort preserves comparison. -/
theorem compare_sameCohort {x x' y y' : Datum}
    (hx : x.SameCohort x') (hy : y.SameCohort y') :
    Datum.compare x y = Datum.compare x' y' := by
  simp only [Datum.compare, Datum.sameCohort_numericValue? hx, Datum.sameCohort_numericValue? hy]

end Datum

namespace Datum

/-- A quiet comparison raises invalid exactly when an operand is a signaling NaN. -/
theorem compareQuiet_invalid_iff (p : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    (x.compareQuiet p y).status.invalid = true ↔
      x.isSNaN = true ∨ y.isSNaN = true := by
  simp [compareQuiet]

/-- A signaling comparison raises invalid exactly when an operand is a NaN, quiet or signaling. -/
theorem compareSignaling_invalid_iff (p : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    (x.compareSignaling p y).status.invalid = true ↔
      x.isNaN = true ∨ y.isNaN = true := by
  simp [compareSignaling]

/-- Quiet and signaling variants have identical truth values, including on NaNs. -/
theorem compareQuiet_value_eq_compareSignaling (p : Numerics.IEEEComparison.Predicate)
    (x y : Datum) :
    (x.compareQuiet p y).value = (x.compareSignaling p y).value := rfl

/-- Complete truth-set specification, stated in terms of exact ordered values
and unordered NaN operands. Together with the status theorems this covers all
22 IEEE comparison operations. -/
theorem compareQuiet_value_iff (p : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    (x.compareQuiet p y).value = true ↔
      (p.accepts none = true ∧ (x.isNaN = true ∨ y.isNaN = true)) ∨
      (p.accepts (some .lt) = true ∧ ∃ a b : NumericValue,
        x.numericValue? = some a ∧ y.numericValue? = some b ∧ a < b) ∨
      (p.accepts (some .eq) = true ∧ ∃ a : NumericValue,
        x.numericValue? = some a ∧ y.numericValue? = some a) ∨
      (p.accepts (some .gt) = true ∧ ∃ a b : NumericValue,
        x.numericValue? = some a ∧ y.numericValue? = some b ∧ b < a) := by
  rw [← compare_eq_none_iff, ← compare_eq_lt_iff, ← compare_eq_eq_iff,
    ← compare_eq_gt_iff]
  cases h : Datum.compare x y with
  | none => simp [compareQuiet, h]
  | some r => cases r <;> simp [compareQuiet, h]

/-- Comparison never raises numerical range, division, or inexact exceptions. -/
theorem compareQuiet_status (p : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    (x.compareQuiet p y).status = { invalid := x.isSNaN || y.isSNaN } := rfl

/-- A signaling comparison raises only invalid, and only on a NaN operand. -/
theorem compareSignaling_status (p : Numerics.IEEEComparison.Predicate) (x y : Datum) :
    (x.compareSignaling p y).status = { invalid := x.isNaN || y.isNaN } := rfl

end Datum
end FloatLib.Floats.Formats.DecimalInterchange
