/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Runtime
public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof

/-!
# Mathematical order and extrema for P3109

Finite extrema agree with the rational field's minimum and maximum. Comparisons agree with
rational order, while NaN remains unordered. Magnitude ties and the preference for finite values
are stated separately from rounding. The executable extrema use the same `binaryTo` refinement
as arithmetic, so these identities describe the expression at their single projection boundary.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

/-- Finite strict comparison is precisely rational strict order. -/
@[simp] theorem less_finite (left right : Rat) :
    less (.finite left) (.finite right) = true ↔ left < right := by
  simp [less]

/-- Finite non-strict comparison is precisely rational order. -/
@[simp] theorem lessEqual_finite (left right : Rat) :
    lessEqual (.finite left) (.finite right) = true ↔ left ≤ right := by
  simp only [lessEqual, less, equal, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨fun h => h.elim le_of_lt le_of_eq, lt_or_eq_of_le⟩

/-- Finite comparison equality is precisely equality of rational values. -/
@[simp] theorem equal_finite (left right : Rat) :
    equal (.finite left) (.finite right) = true ↔ left = right := by
  simp [equal]

/-- No datum is strictly less than itself, even NaN. -/
@[simp] theorem less_self (value : NumericalValue Rat) : less value value = false := by
  cases value with
  | finite value => simp [less]
  | infinity sign => cases sign <;> rfl
  | exceptional value => rfl

/-- Finite minimum is the ordinary rational minimum. -/
@[simp] theorem minimum_finite (left right : Rat) :
    minimum (.finite left) (.finite right) = .finite (min left right) := by
  by_cases h : left < right
  · simp [minimum, less, h, min_eq_left h.le]
  · simp [minimum, less, h, min_eq_right (le_of_not_gt h)]

/-- Finite maximum is the ordinary rational maximum. -/
@[simp] theorem maximum_finite (left right : Rat) :
    maximum (.finite left) (.finite right) = .finite (max left right) := by
  by_cases h : left < right
  · simp [maximum, less, h, max_eq_right h.le]
  · simp [maximum, less, h, max_eq_left (le_of_not_gt h)]

/-- Exact closed minimum is commutative, including NaN and infinity. -/
theorem minimum_comm (left right : NumericalValue Rat) :
    minimum left right = minimum right left := by
  cases left <;> cases right <;> (repeat' cases_type Bool) <;>
    first | simp only [minimum_finite, _root_.min_comm] | rfl

/-- Exact closed maximum is commutative, including NaN and infinity. -/
theorem maximum_comm (left right : NumericalValue Rat) :
    maximum left right = maximum right left := by
  cases left <;> cases right <;> (repeat' cases_type Bool) <;>
    first | simp only [maximum_finite, _root_.max_comm] | rfl

/-- A finite operand wins over either infinity in minimum-finite. -/
@[simp] theorem minimumFinite_finite_infinity (value : Rat) (negative : Bool) :
    minimumFinite (.finite value) (.infinity negative) = .finite value :=
  rfl

/-- A finite operand wins over either infinity in maximum-finite. -/
@[simp] theorem maximumFinite_finite_infinity (value : Rat) (negative : Bool) :
    maximumFinite (.finite value) (.infinity negative) = .finite value :=
  rfl

/-- The number variant ignores NaN in favor of a finite operand. -/
@[simp] theorem minimumNumber_nan_finite (value : Rat) :
    minimumNumber nan (.finite value) = .finite value :=
  rfl

/-- The number variant ignores NaN in favor of a finite operand. -/
@[simp] theorem maximumNumber_nan_finite (value : Rat) :
    maximumNumber nan (.finite value) = .finite value :=
  rfl

/-- Equal nonnegative magnitudes are resolved toward the negative datum by minimum. -/
theorem minimumMagnitude_neg_self (value : Rat) (hvalue : 0 ≤ value) :
    minimumMagnitude (.finite (-value)) (.finite value) = .finite (-value) := by
  have habs : abs (.finite (-value)) = abs (.finite value) := by
    simp only [abs]
    split_ifs <;> simp_all <;> linarith
  simp only [minimumMagnitude, habs, less_self, Bool.false_eq_true, ite_false]
  rw [minimum_finite, min_eq_left (by linarith)]

/-- Equal nonnegative magnitudes are resolved toward the positive datum by maximum. -/
theorem maximumMagnitude_neg_self (value : Rat) (hvalue : 0 ≤ value) :
    maximumMagnitude (.finite (-value)) (.finite value) = .finite value := by
  have habs : abs (.finite (-value)) = abs (.finite value) := by
    simp only [abs]
    split_ifs <;> simp_all <;> linarith
  simp only [maximumMagnitude, habs, less_self, Bool.false_eq_true, ite_false]
  rw [maximum_finite, max_eq_right (by linarith)]

end FloatLib.Floats.Formats.P3109.Arithmetic
