/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime

/-!
# Classification of binary comparisons and extrema

Comparison is unordered exactly when an operand is NaN. The number variants of minimum and maximum
obey their specified signaling and quiet NaN priorities.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- NaN selection returns `none` when both inputs are known not to be NaNs. -/
theorem chooseNaN2_none_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    chooseNaN2 x y = none :=
  (chooseNaN2_eq_none_iff x y).2 ⟨hx, hy⟩

/-- Comparison is unordered if and only if an operand is a NaN. -/
theorem compare_eq_none_iff {fmt : FloatFormat} (x y : Model fmt) :
    compare x y = none ↔ isNaN x = true ∨ isNaN y = true := by
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp [compare, hx, hy]

/-- Without NaNs, `minNum` is the IEEE `minimum` operation. -/
theorem minNum_eq_minimum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    minNum x y = minimum x y := by
  have hxSNaN := isSignaling_eq_false_of_isNaN_eq_false x hx
  have hySNaN := isSignaling_eq_false_of_isNaN_eq_false y hy
  simp [minNum, hxSNaN, hySNaN, hx, hy]

/-- Without NaNs, `maxNum` is the IEEE `maximum` operation. -/
theorem maxNum_eq_maximum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    maxNum x y = maximum x y := by
  have hxSNaN := isSignaling_eq_false_of_isNaN_eq_false x hx
  have hySNaN := isSignaling_eq_false_of_isNaN_eq_false y hy
  simp [maxNum, hxSNaN, hySNaN, hx, hy]

/--
A signaling left operand has first priority in `minNum` and is returned after quieting.
-/
theorem minNum_of_isSignaling_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSignaling x = true) :
    minNum x y = quietNaN x := by
  simp [minNum, hx]

/--
When the left operand is not signaling, a signaling right operand has priority in `minNum`.
-/
theorem minNum_of_isSignaling_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSignaling x = false) (hy : isSignaling y = true) :
    minNum x y = quietNaN y := by
  simp [minNum, hx, hy]

/--
After signaling NaNs are excluded, `minNum` skips one quiet NaN on the left.
-/
theorem minNum_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSignaling x = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = false) :
    minNum x y = y := by
  have hySNaN := isSignaling_eq_false_of_isNaN_eq_false y hyNaN
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
After signaling NaNs are excluded, `minNum` skips one quiet NaN on the right.
-/
theorem minNum_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSignaling y = false) (hxNaN : isNaN x = false) (hyNaN : isNaN y = true) :
    minNum x y = x := by
  have hxSNaN := isSignaling_eq_false_of_isNaN_eq_false x hxNaN
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
When both operands are NaNs and the right one is quiet, `minNum` quiets and returns the left
operand.
-/
theorem minNum_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSignaling y = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = true) :
    minNum x y = quietNaN x := by
  cases hxSNaN : isSignaling x <;> simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
A signaling left operand has first priority in `maxNum` and is returned after quieting.
-/
theorem maxNum_of_isSignaling_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSignaling x = true) :
    maxNum x y = quietNaN x := by
  simp [maxNum, hx]

/--
When the left operand is not signaling, a signaling right operand has priority in `maxNum`.
-/
theorem maxNum_of_isSignaling_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSignaling x = false) (hy : isSignaling y = true) :
    maxNum x y = quietNaN y := by
  simp [maxNum, hx, hy]

/--
After signaling NaNs are excluded, `maxNum` skips one quiet NaN on the left.
-/
theorem maxNum_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSignaling x = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = false) :
    maxNum x y = y := by
  have hySNaN := isSignaling_eq_false_of_isNaN_eq_false y hyNaN
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
After signaling NaNs are excluded, `maxNum` skips one quiet NaN on the right.
-/
theorem maxNum_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSignaling y = false) (hxNaN : isNaN x = false) (hyNaN : isNaN y = true) :
    maxNum x y = x := by
  have hxSNaN := isSignaling_eq_false_of_isNaN_eq_false x hxNaN
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
When both operands are NaNs and the right one is quiet, `maxNum` quiets and returns the left
operand.
-/
theorem maxNum_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSignaling y = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = true) :
    maxNum x y = quietNaN x := by
  cases hxSNaN : isSignaling x <;> simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/-! ### IEEE 754-2019 §9.6 `minimumNumber` and `maximumNumber` -/

/-- Without NaNs, `minimumNumber` is the IEEE `minimum` operation. -/
theorem minimumNumber_eq_minimum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    minimumNumber x y = minimum x y := by
  simp [minimumNumber, Internal.Value.minimumNumber, hx, hy]

/-- Without NaNs, `maximumNumber` is the IEEE `maximum` operation. -/
theorem maximumNumber_eq_maximum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    maximumNumber x y = maximum x y := by
  simp [maximumNumber, Internal.Value.maximumNumber, hx, hy]

/--
`minimumNumber` returns the right operand whenever only the left operand is a NaN, even a
signaling one. This is the point where IEEE 754-2019 §9.6 departs from `minNum`.
-/
theorem minimumNumber_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = false) :
    minimumNumber x y = y := by
  simp [minimumNumber, Internal.Value.minimumNumber, hx, hy]

/-- `minimumNumber` returns the left operand whenever only the right operand is a NaN. -/
theorem minimumNumber_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = true) :
    minimumNumber x y = x := by
  simp [minimumNumber, Internal.Value.minimumNumber, hx, hy]

/-- When both operands are NaNs, `minimumNumber` delivers the quiet NaN chosen by
`bothNaNNumber`. -/
theorem minimumNumber_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = true) :
    minimumNumber x y = bothNaNNumber x y := by
  simp [minimumNumber, Internal.Value.minimumNumber, hx, hy]

/-- `maximumNumber` returns the right operand whenever only the left operand is a NaN. -/
theorem maximumNumber_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = false) :
    maximumNumber x y = y := by
  simp [maximumNumber, Internal.Value.maximumNumber, hx, hy]

/-- `maximumNumber` returns the left operand whenever only the right operand is a NaN. -/
theorem maximumNumber_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = true) :
    maximumNumber x y = x := by
  simp [maximumNumber, Internal.Value.maximumNumber, hx, hy]

/-- When both operands are NaNs, `maximumNumber` delivers the quiet NaN chosen by
`bothNaNNumber`. -/
theorem maximumNumber_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = true) (hy : isNaN y = true) :
    maximumNumber x y = bothNaNNumber x y := by
  simp [maximumNumber, Internal.Value.maximumNumber, hx, hy]

/-- The NaN chosen for two NaN operands is always one of them, quieted. -/
theorem bothNaNNumber_eq_or {fmt : FloatFormat} (x y : Model fmt) :
    bothNaNNumber x y = quietNaN x ∨ bothNaNNumber x y = quietNaN y := by
  unfold bothNaNNumber
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The NaN chosen for two NaN operands is a NaN. -/
theorem isNaN_bothNaNNumber {fmt : FloatFormat} {x y : Model fmt}
    (hx : isNaN x = true) (hy : isNaN y = true) :
    isNaN (bothNaNNumber x y) = true := by
  unfold bothNaNNumber
  split <;> simp [hx, hy]

/--
When neither operand is a signaling NaN, `minimumNumber` agrees with `minNum`, including when
one or both operands are quiet NaNs.
-/
theorem minimumNumber_eq_minNum_of_not_isSignaling {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSignaling x = false) (hy : isSignaling y = false) :
    minimumNumber x y = minNum x y := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y <;>
    simp [minimumNumber, Internal.Value.minimumNumber, minNum, bothNaNNumber, hx, hy, hxNaN, hyNaN]

/--
When neither operand is a signaling NaN, `maximumNumber` agrees with `maxNum`, including when
one or both operands are quiet NaNs.
-/
theorem maximumNumber_eq_maxNum_of_not_isSignaling {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSignaling x = false) (hy : isSignaling y = false) :
    maximumNumber x y = maxNum x y := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y <;>
    simp [maximumNumber, Internal.Value.maximumNumber, maxNum, bothNaNNumber, hx, hy, hxNaN, hyNaN]

/-- IEEE `minimum` is non-NaN when both operands are non-NaN. -/
theorem isNaN_minimum_eq_false_of_isNaN_eq_false
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    isNaN (minimum x y) = false := by
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  simp only [minimum, Internal.Value.minimum, withNaNSelection_of_none _ _ hchoose]
  cases compareNonNaN x y hxNaN hyNaN <;>
    simp [apply_ite, hxNaN, hyNaN]

/-- IEEE `maximum` is non-NaN when both operands are non-NaN. -/
theorem isNaN_maximum_eq_false_of_isNaN_eq_false
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    isNaN (maximum x y) = false := by
  have hchoose := chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN
  simp only [maximum, Internal.Value.maximum, withNaNSelection_of_none _ _ hchoose]
  cases compareNonNaN x y hxNaN hyNaN <;>
    simp [apply_ite, hxNaN, hyNaN]

/-- `minimumNumber` never returns a NaN unless both operands are NaNs. -/
theorem isNaN_minimumNumber_eq_false_of_not_both
    {fmt : FloatFormat} (x y : Model fmt)
    (h : isNaN x = false ∨ isNaN y = false) :
    isNaN (minimumNumber x y) = false := by
  cases hx : isNaN x <;> cases hy : isNaN y <;>
    simp_all [minimumNumber, Internal.Value.minimumNumber, isNaN_minimum_eq_false_of_isNaN_eq_false]

/-- `maximumNumber` never returns a NaN unless both operands are NaNs. -/
theorem isNaN_maximumNumber_eq_false_of_not_both
    {fmt : FloatFormat} (x y : Model fmt)
    (h : isNaN x = false ∨ isNaN y = false) :
    isNaN (maximumNumber x y) = false := by
  cases hx : isNaN x <;> cases hy : isNaN y <;>
    simp_all [maximumNumber, Internal.Value.maximumNumber, isNaN_maximum_eq_false_of_isNaN_eq_false]

/-- `minimumNumber` returns a NaN just when both operands are NaNs. -/
theorem isNaN_minimumNumber {fmt : FloatFormat} (x y : Model fmt) :
    isNaN (minimumNumber x y) = (isNaN x && isNaN y) := by
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp only [Bool.and_self, Bool.and_false,
      Bool.false_and]
  · exact isNaN_minimumNumber_eq_false_of_not_both x y (Or.inl hx)
  · exact isNaN_minimumNumber_eq_false_of_not_both x y (Or.inl hx)
  · exact isNaN_minimumNumber_eq_false_of_not_both x y (Or.inr hy)
  · rw [minimumNumber_of_isNaN_both x y hx hy]
    exact isNaN_bothNaNNumber hx hy

/-- `maximumNumber` returns a NaN just when both operands are NaNs. -/
theorem isNaN_maximumNumber {fmt : FloatFormat} (x y : Model fmt) :
    isNaN (maximumNumber x y) = (isNaN x && isNaN y) := by
  cases hx : isNaN x <;> cases hy : isNaN y <;> simp only [Bool.and_self, Bool.and_false,
      Bool.false_and]
  · exact isNaN_maximumNumber_eq_false_of_not_both x y (Or.inl hx)
  · exact isNaN_maximumNumber_eq_false_of_not_both x y (Or.inl hx)
  · exact isNaN_maximumNumber_eq_false_of_not_both x y (Or.inr hy)
  · rw [maximumNumber_of_isNaN_both x y hx hy]
    exact isNaN_bothNaNNumber hx hy

/--
Once both operands are known not to be NaNs, the public comparison is the total non-NaN
comparison.
-/
theorem compare_eq_some_compareNonNaN
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    compare x y = some (compareNonNaN x y hx hy) := by
  simp [compare, hx, hy]

/--
Any successful public comparison determines the result of the total non-NaN comparison.

The min/max semantics below use it, so runtime code needs no unreachable unordered branch once
NaNs are excluded.
-/
@[simp] theorem compareNonNaN_eq_of_compare_eq_some
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) {order : Ordering}
    (hcompare : compare x y = some order) :
    compareNonNaN x y hx hy = order := by
  simpa [compare, hx, hy] using hcompare

end Model
end FloatLib.Floats.Formats.BinaryInterchange
