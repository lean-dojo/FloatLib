/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MagnitudeExtrema.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Selection
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.EReal
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Rational

/-!
# Contracts of the minimum and maximum by magnitude

The four operations of `Operations.MagnitudeExtrema.Runtime` are instances of one selection, and
the theorems are stated once for it, for every format descriptor:

* `magnitudeExtremum_of_compare_abs_lt` and `magnitudeExtremum_of_compare_abs_gt`: when the
  magnitudes differ, the operand of smaller (or larger) magnitude is delivered unchanged.
* `magnitudeExtremum_of_compare_abs_eq` and `magnitudeExtremum_of_isNaN`: equal magnitudes and
  NaN operands defer to the base operation, so the signed-zero rule and the NaN rule are those
  of `minimum`, `maximum`, `minimumNumber` and `maximumNumber`.
* `value_magnitudeExtremum` and `magnitudeExtremum_status`: asking for the status does not change
  the value, and the only flag is `invalid`, raised exactly for a signaling NaN operand.
* `abs_toReal_magnitudeExtremum`: on finite operands of a signed-zero format the magnitude of
  the result is the real `min` or `max` of the magnitudes, provided the base operation returns
  an operand's magnitude on a tie. `abs_toReal_minimumMagnitude` and its three siblings
  discharge that premise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

variable {fmt : FloatFormat}

/-- A magnitude that compares smaller selects the left operand of a minimum and the right
operand of a maximum, unchanged. -/
theorem magnitudeExtremum_of_compare_abs_lt (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) {x y : Model fmt}
    (h : compare (abs x) (abs y) = some .lt) :
    magnitudeExtremum larger base x y = if larger then y else x := by
  simp [magnitudeExtremum, Internal.Value.magnitudeExtremum, h]

/-- A magnitude that compares larger selects the right operand of a minimum and the left
operand of a maximum, unchanged. -/
theorem magnitudeExtremum_of_compare_abs_gt (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) {x y : Model fmt}
    (h : compare (abs x) (abs y) = some .gt) :
    magnitudeExtremum larger base x y = if larger then x else y := by
  simp [magnitudeExtremum, Internal.Value.magnitudeExtremum, h]

/-- Equal magnitudes defer to the base operation. -/
theorem magnitudeExtremum_of_compare_abs_eq (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) {x y : Model fmt}
    (h : compare (abs x) (abs y) = some .eq) :
    magnitudeExtremum larger base x y = base x y := by
  simp [magnitudeExtremum, Internal.Value.magnitudeExtremum, h]

/-- A NaN operand defers to the base operation, which holds the NaN rule. -/
theorem magnitudeExtremum_of_isNaN (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) {x y : Model fmt}
    (h : isNaN x = true ∨ isNaN y = true) :
    magnitudeExtremum larger base x y = base x y := by
  have hcompare : compare (abs x) (abs y) = none := by
    rw [compare_eq_none_iff, isNaN_abs, isNaN_abs]
    exact h
  simp [magnitudeExtremum, Internal.Value.magnitudeExtremum, hcompare]

/-- Asking for the status does not change the value. -/
@[simp] theorem value_magnitudeExtremum (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) (x y : Model fmt) :
    (magnitudeExtremum larger base x y (status := true)).value =
      magnitudeExtremum larger base x y :=
  rfl

/-- A selection by magnitude raises `invalid` exactly for a signaling NaN operand, and no other
flag. -/
theorem magnitudeExtremum_status (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) (x y : Model fmt) :
    (magnitudeExtremum larger base x y (status := true)).status =
      { invalid := isSignaling x || isSignaling y } := by
  cases h : isSignaling x || isSignaling y <;>
    simp [magnitudeExtremum, outcomeWithInvalid, Numerics.IEEEStatus.clear, h]

/--
On finite operands of a format with signed zero, the magnitude of a selection by magnitude is
the real `min` (for `larger := false`) or `max` (for `larger := true`) of the operands'
magnitudes, for every base operation that returns a value of the common magnitude on a tie.
-/
theorem abs_toReal_magnitudeExtremum (larger : Bool)
    (base : Model fmt → Model fmt → Model fmt) (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hbase : |toReal x| = |toReal y| → |toReal (base x y)| = |toReal x|) :
    |toReal (magnitudeExtremum larger base x y)| =
      if larger then max |toReal x| |toReal y| else min |toReal x| |toReal y| := by
  have hax : isFinite (abs x) = true := by rw [isFinite_abs]; exact hx
  have hay : isFinite (abs y) = true := by rw [isFinite_abs]; exact hy
  have hrx := toReal_abs_of_isFinite x hfmt hx
  have hry := toReal_abs_of_isFinite y hfmt hy
  have hnan : compare (abs x) (abs y) ≠ none := by
    rw [Ne, compare_eq_none_iff, isNaN_abs, isNaN_abs,
      isNaN_eq_false_of_isFinite_eq_true x hx, isNaN_eq_false_of_isFinite_eq_true y hy]
    simp
  cases hcompare : compare (abs x) (abs y) with
  | none => exact absurd hcompare hnan
  | some order =>
    cases order with
    | lt =>
        have hlt := (compare_eq_some_lt_iff_toReal_lt_of_isFinite _ _ hax hay).1 hcompare
        rw [hrx, hry] at hlt
        rw [magnitudeExtremum_of_compare_abs_lt larger base hcompare]
        cases larger
        · simp [min_eq_left hlt.le]
        · simp [max_eq_right hlt.le]
    | gt =>
        have hgt := (compare_eq_some_gt_iff_toReal_gt_of_isFinite _ _ hax hay).1 hcompare
        rw [hrx, hry] at hgt
        rw [magnitudeExtremum_of_compare_abs_gt larger base hcompare]
        cases larger
        · simp [min_eq_right hgt.le]
        · simp [max_eq_left hgt.le]
    | eq =>
        have heq := (compare_eq_some_eq_iff_toReal_eq_of_isFinite _ _ hax hay).1 hcompare
        rw [hrx, hry] at heq
        rw [magnitudeExtremum_of_compare_abs_eq larger base hcompare, hbase heq]
        cases larger <;> simp [heq]

/-- A real `min` of two reals of one magnitude has that magnitude. -/
private theorem abs_min_of_abs_eq {a b : ℝ} (h : |a| = |b|) : |min a b| = |a| := by
  rcases min_choice a b with hmin | hmin <;> rw [hmin]
  exact h.symm

/-- A real `max` of two reals of one magnitude has that magnitude. -/
private theorem abs_max_of_abs_eq {a b : ℝ} (h : |a| = |b|) : |max a b| = |a| := by
  rcases max_choice a b with hmax | hmax <;> rw [hmax]
  exact h.symm

/-- On finite operands of a signed-zero format, `minimumMagnitude` has the smaller magnitude. -/
theorem abs_toReal_minimumMagnitude (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (minimumMagnitude x y)| = min |toReal x| |toReal y| :=
  abs_toReal_magnitudeExtremum false _ x y hfmt hx hy fun h => by
    rw [toReal_minimum_eq_min_of_isFinite x y hx hy, abs_min_of_abs_eq h]

/-- On finite operands of a signed-zero format, `maximumMagnitude` has the larger magnitude. -/
theorem abs_toReal_maximumMagnitude (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (maximumMagnitude x y)| = max |toReal x| |toReal y| :=
  abs_toReal_magnitudeExtremum true _ x y hfmt hx hy fun h => by
    rw [toReal_maximum_eq_max_of_isFinite x y hx hy, abs_max_of_abs_eq h]

/-- On finite operands of a signed-zero format, `minimumMagnitudeNumber` has the smaller
magnitude. -/
theorem abs_toReal_minimumMagnitudeNumber (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (minimumMagnitudeNumber x y)| = min |toReal x| |toReal y| :=
  abs_toReal_magnitudeExtremum false _ x y hfmt hx hy fun h => by
    rw [minimumNumber_eq_minimum_of_not_isNaN x y (isNaN_eq_false_of_isFinite_eq_true x hx)
      (isNaN_eq_false_of_isFinite_eq_true y hy),
      toReal_minimum_eq_min_of_isFinite x y hx hy, abs_min_of_abs_eq h]

/-- On finite operands of a signed-zero format, `maximumMagnitudeNumber` has the larger
magnitude. -/
theorem abs_toReal_maximumMagnitudeNumber (x y : Model fmt)
    (hfmt : fmt.supportsSignedZero = true)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    |toReal (maximumMagnitudeNumber x y)| = max |toReal x| |toReal y| :=
  abs_toReal_magnitudeExtremum true _ x y hfmt hx hy fun h => by
    rw [maximumNumber_eq_maximum_of_not_isNaN x y (isNaN_eq_false_of_isFinite_eq_true x hx)
      (isNaN_eq_false_of_isFinite_eq_true y hy),
      toReal_maximum_eq_max_of_isFinite x y hx hy, abs_max_of_abs_eq h]

end Model
end FloatLib.Floats.Formats.BinaryInterchange
