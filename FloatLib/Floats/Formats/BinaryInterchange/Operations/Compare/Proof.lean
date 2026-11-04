/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Correctness of binary comparisons

We prove that the executable comparison, written once for every format, agrees with exact dyadic,
real and extended-real order. The selection theorems specify IEEE `minimum` and `maximum` as well,
infinities and signed-zero ties included. Given two zeros in either order, `minimum` returns the
zero whose sign is the disjunction of the operands' signs, so a negative zero wins, and `maximum`
returns the one whose sign is their conjunction (`minimum_of_isZero`, `maximum_of_isZero`, and
`minimum_zero_zero` for the policy zeros).

Every result is uniform in the binary format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

section

/-! ## Classification helpers -/

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
  have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hx
  have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hy
  simp [minNum, hxSNaN, hySNaN, hx, hy]

/-- Without NaNs, `maxNum` is the IEEE `maximum` operation. -/
theorem maxNum_eq_maximum_of_not_isNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    maxNum x y = maximum x y := by
  have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hx
  have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hy
  simp [maxNum, hxSNaN, hySNaN, hx, hy]

/--
A signaling left operand has first priority in `minNum` and is returned after quieting.
-/
theorem minNum_of_isSNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = true) :
    minNum x y = quietNaN x := by
  simp [minNum, hx]

/--
When the left operand is not signaling, a signaling right operand has priority in `minNum`.
-/
theorem minNum_of_isSNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = true) :
    minNum x y = quietNaN y := by
  simp [minNum, hx, hy]

/--
After signaling NaNs are excluded, `minNum` skips one quiet NaN on the left.
-/
theorem minNum_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = false) :
    minNum x y = y := by
  have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hyNaN
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
After signaling NaNs are excluded, `minNum` skips one quiet NaN on the right.
-/
theorem minNum_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSNaN y = false) (hxNaN : isNaN x = false) (hyNaN : isNaN y = true) :
    minNum x y = x := by
  have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hxNaN
  simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
When both operands are NaNs and the right one is quiet, `minNum` quiets and returns the left
operand.
-/
theorem minNum_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSNaN y = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = true) :
    minNum x y = quietNaN x := by
  cases hxSNaN : isSNaN x <;> simp [minNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
A signaling left operand has first priority in `maxNum` and is returned after quieting.
-/
theorem maxNum_of_isSNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = true) :
    maxNum x y = quietNaN x := by
  simp [maxNum, hx]

/--
When the left operand is not signaling, a signaling right operand has priority in `maxNum`.
-/
theorem maxNum_of_isSNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = true) :
    maxNum x y = quietNaN y := by
  simp [maxNum, hx, hy]

/--
After signaling NaNs are excluded, `maxNum` skips one quiet NaN on the left.
-/
theorem maxNum_of_isNaN_left {fmt : FloatFormat} (x y : Model fmt)
    (hxSNaN : isSNaN x = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = false) :
    maxNum x y = y := by
  have hySNaN := isSNaN_eq_false_of_isNaN_eq_false y hyNaN
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
After signaling NaNs are excluded, `maxNum` skips one quiet NaN on the right.
-/
theorem maxNum_of_isNaN_right {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSNaN y = false) (hxNaN : isNaN x = false) (hyNaN : isNaN y = true) :
    maxNum x y = x := by
  have hxSNaN := isSNaN_eq_false_of_isNaN_eq_false x hxNaN
  simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/--
When both operands are NaNs and the right one is quiet, `maxNum` quiets and returns the left
operand.
-/
theorem maxNum_of_isNaN_both {fmt : FloatFormat} (x y : Model fmt)
    (hySNaN : isSNaN y = false) (hxNaN : isNaN x = true) (hyNaN : isNaN y = true) :
    maxNum x y = quietNaN x := by
  cases hxSNaN : isSNaN x <;> simp [maxNum, hxSNaN, hySNaN, hxNaN, hyNaN]

/-! ### IEEE 754-2019 `minimumNumber` and `maximumNumber` -/

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
signaling one. This is the point where IEEE 754-2019 departs from `minNum`.
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

/-- When both operands are NaNs, `minimumNumber` delivers the quiet NaN chosen by `bothNaNNumber`. -/
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

/-- When both operands are NaNs, `maximumNumber` delivers the quiet NaN chosen by `bothNaNNumber`. -/
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
theorem minimumNumber_eq_minNum_of_not_isSNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = false) :
    minimumNumber x y = minNum x y := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y <;>
    simp [minimumNumber, Internal.Value.minimumNumber, minNum, bothNaNNumber, hx, hy, hxNaN, hyNaN]

/--
When neither operand is a signaling NaN, `maximumNumber` agrees with `maxNum`, including when
one or both operands are quiet NaNs.
-/
theorem maximumNumber_eq_maxNum_of_not_isSNaN {fmt : FloatFormat} (x y : Model fmt)
    (hx : isSNaN x = false) (hy : isSNaN y = false) :
    maximumNumber x y = maxNum x y := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y <;>
    simp [maximumNumber, Internal.Value.maximumNumber, maxNum, bothNaNNumber, hx, hy, hxNaN, hyNaN]

/-! ## Non-NaN minimum and maximum -/

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

/-! ## Finite comparison -/

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

/--
When both operands decode to dyadics, executable comparison returns their exact dyadic ordering.
-/
theorem compare_eq_some_cmpDyadic_of_toDyadic?
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    compare x y = some (cmpDyadic dx dy) := by
  have hxNaN := isNaN_eq_false_of_toDyadic?_some hx
  have hyNaN := isNaN_eq_false_of_toDyadic?_some hy
  have hxInf := isInf_eq_false_of_toDyadic?_some hx
  have hyInf := isInf_eq_false_of_toDyadic?_some hy
  simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hx, hy]

/-- Finite executable comparison returns `.lt` just when the decoded reals are ordered. -/
theorem compare_eq_some_lt_iff_toReal_lt
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    compare x y = some .lt ↔ toReal x < toReal y := by
  simpa [compare_eq_some_cmpDyadic_of_toDyadic? x y hx hy, toReal_eq, hx, hy] using
    cmpDyadic_lt_iff dx dy

/-- Finite executable comparison returns `.eq` just when the decoded reals are equal. -/
theorem compare_eq_some_eq_iff_toReal_eq
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    compare x y = some .eq ↔ toReal x = toReal y := by
  simpa [compare_eq_some_cmpDyadic_of_toDyadic? x y hx hy, toReal_eq, hx, hy] using
    cmpDyadic_eq_iff dx dy

/-- Finite executable comparison returns `.gt` just when the decoded reals are reversed. -/
theorem compare_eq_some_gt_iff_toReal_gt
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    compare x y = some .gt ↔ toReal y < toReal x := by
  simpa [compare_eq_some_cmpDyadic_of_toDyadic? x y hx hy, toReal_eq, hx, hy] using
    cmpDyadic_gt_iff dx dy

/-- On finite inputs, executable comparison agrees with strict real order. -/
theorem compare_eq_some_lt_iff_toReal_lt_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    compare x y = some .lt ↔ toReal x < toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  exact compare_eq_some_lt_iff_toReal_lt x y hdx hdy

/-- On finite inputs, executable comparison agrees with real equality. -/
theorem compare_eq_some_eq_iff_toReal_eq_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    compare x y = some .eq ↔ toReal x = toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  exact compare_eq_some_eq_iff_toReal_eq x y hdx hdy

/-- On finite inputs, executable comparison agrees with reversed strict real order. -/
theorem compare_eq_some_gt_iff_toReal_gt_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    compare x y = some .gt ↔ toReal y < toReal x := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  exact compare_eq_some_gt_iff_toReal_gt x y hdx hdy

/-! ## Signed-zero tie breaking -/

/-- Positive and policy-selected negative zero compare equal numerically. -/
@[simp] theorem compare_zero_false_true (fmt : FloatFormat) :
    compare (zero fmt false) (zero fmt true) = some .eq := by
  rw [compare_eq_some_cmpDyadic_of_toDyadic?
    (zero fmt false) (zero fmt true)
    (toDyadic?_zero fmt false) (toDyadic?_zero fmt true)]
  simp [cmpDyadic]

/--
`minimum` selects policy-negative zero from a positive-zero/negative-zero tie.

In a format without signed zero, both inputs and the result are the single positive zero.
-/
theorem minimum_zero_false_true (fmt : FloatFormat) :
    minimum (zero fmt false) (zero fmt true) = zero fmt true := by
  have hchoose :=
    chooseNaN2_none_of_not_isNaN
      (zero fmt false) (zero fmt true)
      (isNaN_zero fmt false) (isNaN_zero fmt true)
  simp [minimum, Internal.Value.minimum, hchoose, compare_zero_false_true, signBit_zero]
  cases hfmt : fmt.supportsSignedZero <;> simp [zero, hfmt]

/--
`maximum` selects positive zero from a positive-zero/negative-zero tie.

In a format without signed zero, both inputs already denote the single positive zero.
-/
theorem maximum_zero_false_true (fmt : FloatFormat) :
    maximum (zero fmt false) (zero fmt true) = zero fmt false := by
  have hchoose :=
    chooseNaN2_none_of_not_isNaN
      (zero fmt false) (zero fmt true)
      (isNaN_zero fmt false) (isNaN_zero fmt true)
  simp [maximum, Internal.Value.maximum, hchoose, compare_zero_false_true, signBit_zero]

/-- A zero is not a NaN, in every encoding. -/
private theorem isNaN_eq_false_of_isZero {fmt : FloatFormat} {x : Model fmt}
    (hx : isZero x = true) : isNaN x = false :=
  isNaN_eq_false_of_isFinite_eq_true x (isFinite_eq_true_of_isZero_eq_true x hx)

/-- Two zeros compare equal, whatever their signs and order. -/
theorem compare_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    compare x y = some .eq := by
  rw [compare_eq_some_cmpDyadic_of_toDyadic? x y (toDyadic?_eq_zero_of_isZero_eq_true x hx)
    (toDyadic?_eq_zero_of_isZero_eq_true y hy)]
  simp [cmpDyadic]

/--
On two zeros, `minimum` returns the zero whose sign is the disjunction of the operands' sign
bits: either order of `+0` and `-0` gives `-0`, and two zeros of one sign give that zero. A format
without signed zero has one zero, which both operands and the result are.
-/
theorem minimum_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    minimum x y = zero fmt (signBit x || signBit y) := by
  have hxNaN := isNaN_eq_false_of_isZero hx
  have hyNaN := isNaN_eq_false_of_isZero hy
  simp [minimum, Internal.Value.minimum, chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN,
    compareNonNaN_eq_of_compare_eq_some x y hxNaN hyNaN (compare_of_isZero hx hy), hx, hy]

/--
On two zeros, `maximum` returns the zero whose sign is the conjunction of the operands' sign
bits: either order of `+0` and `-0` gives `+0`, and two zeros of one sign give that zero.
-/
theorem maximum_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    maximum x y = zero fmt (signBit x && signBit y) := by
  have hxNaN := isNaN_eq_false_of_isZero hx
  have hyNaN := isNaN_eq_false_of_isZero hy
  simp [maximum, Internal.Value.maximum, chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN,
    compareNonNaN_eq_of_compare_eq_some x y hxNaN hyNaN (compare_of_isZero hx hy), hx, hy]

/--
`minimum` of the policy zeros of signs `s` and `t` is the policy zero of sign `s || t`, for both
argument orders and equal signs.
-/
@[simp] theorem minimum_zero_zero (fmt : FloatFormat) (s t : Bool) :
    minimum (zero fmt s) (zero fmt t) = zero fmt (s || t) := by
  rw [minimum_of_isZero (isZero_zero fmt s) (isZero_zero fmt t), signBit_zero, signBit_zero]
  cases s <;> cases t <;> cases hsigned : fmt.supportsSignedZero <;> simp [zero, hsigned]

/--
`maximum` of the policy zeros of signs `s` and `t` is the policy zero of sign `s && t`, for both
argument orders and equal signs.
-/
@[simp] theorem maximum_zero_zero (fmt : FloatFormat) (s t : Bool) :
    maximum (zero fmt s) (zero fmt t) = zero fmt (s && t) := by
  rw [maximum_of_isZero (isZero_zero fmt s) (isZero_zero fmt t), signBit_zero, signBit_zero]
  cases s <;> cases t <;> cases hsigned : fmt.supportsSignedZero <;> simp [zero, hsigned]

/-- On two zeros, `minNum` is `minimum`: the sign of the result is the disjunction of the signs. -/
theorem minNum_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    minNum x y = zero fmt (signBit x || signBit y) := by
  rw [minNum_eq_minimum_of_not_isNaN x y
    (isNaN_eq_false_of_isZero hx) (isNaN_eq_false_of_isZero hy),
    minimum_of_isZero hx hy]

/-- On two zeros, `maxNum` is `maximum`: the sign of the result is the conjunction of the signs. -/
theorem maxNum_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    maxNum x y = zero fmt (signBit x && signBit y) := by
  rw [maxNum_eq_maximum_of_not_isNaN x y
    (isNaN_eq_false_of_isZero hx) (isNaN_eq_false_of_isZero hy),
    maximum_of_isZero hx hy]

/--
On two zeros, `minimumNumber` is `minimum`: the sign of the result is the disjunction of the
signs.
-/
theorem minimumNumber_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    minimumNumber x y = zero fmt (signBit x || signBit y) := by
  rw [minimumNumber_eq_minimum_of_not_isNaN x y
    (isNaN_eq_false_of_isZero hx) (isNaN_eq_false_of_isZero hy),
    minimum_of_isZero hx hy]

/--
On two zeros, `maximumNumber` is `maximum`: the sign of the result is the conjunction of the
signs.
-/
theorem maximumNumber_of_isZero {fmt : FloatFormat} {x y : Model fmt}
    (hx : isZero x = true) (hy : isZero y = true) :
    maximumNumber x y = zero fmt (signBit x && signBit y) := by
  rw [maximumNumber_eq_maximum_of_not_isNaN x y
    (isNaN_eq_false_of_isZero hx) (isNaN_eq_false_of_isZero hy),
    maximum_of_isZero hx hy]

/--
For every encoding with signed zero, `minimum (+0, -0)` returns the negative zero encoding.
-/
@[simp] theorem minimum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    minimum (posZero fmt) (negZero fmt) = negZero fmt := by
  rw [← show zero fmt false = posZero fmt by simp [zero],
    ← show zero fmt true = negZero fmt by simp [zero, hfmt],
    minimum_zero_false_true]

/--
For every encoding with signed zero, `maximum (+0, -0)` returns the positive zero encoding.
-/
@[simp] theorem maximum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    maximum (posZero fmt) (negZero fmt) = posZero fmt := by
  rw [← show zero fmt false = posZero fmt by simp [zero],
    ← show zero fmt true = negZero fmt by simp [zero, hfmt],
    maximum_zero_false_true]

/--
For every encoding with signed zero, `minNum (+0, -0)` returns the negative zero encoding.
-/
@[simp] theorem minNum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    minNum (posZero fmt) (negZero fmt) = negZero fmt := by
  rw [minNum_eq_minimum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    minimum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/--
For every encoding with signed zero, `maxNum (+0, -0)` returns the positive zero encoding.
-/
@[simp] theorem maxNum_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    maxNum (posZero fmt) (negZero fmt) = posZero fmt := by
  rw [maxNum_eq_maximum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    maximum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/--
For every encoding with signed zero, `minimumNumber (+0, -0)` returns the negative zero encoding.
-/
@[simp] theorem minimumNumber_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    minimumNumber (posZero fmt) (negZero fmt) = negZero fmt := by
  rw [minimumNumber_eq_minimum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    minimum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/--
For every encoding with signed zero, `maximumNumber (+0, -0)` returns the positive zero encoding.
-/
@[simp] theorem maximumNumber_posZero_negZero_of_supportsSignedZero
    (fmt : FloatFormat) (hfmt : fmt.supportsSignedZero = true) :
    maximumNumber (posZero fmt) (negZero fmt) = posZero fmt := by
  rw [maximumNumber_eq_maximum_of_not_isNaN _ _ (isNaN_posZero fmt) (isNaN_negZero fmt hfmt),
    maximum_posZero_negZero_of_supportsSignedZero fmt hfmt]

/-! ## Finite minimum and maximum -/

/--
On non-NaN operands, a value map that respects the model comparison and gives every zero the same
value carries IEEE `minimum` to `min`. The signed-zero tie break is invisible to such a map.
-/
private theorem map_minimum_eq_min {α : Type*} [LinearOrder α] {fmt : FloatFormat}
    (f : Model fmt → α) {x y : Model fmt} (hx : isNaN x = false) (hy : isNaN y = false)
    (hzero : isZero x = true → isZero y = true → ∀ sign, f (zero fmt sign) = f x)
    (hlt : compare x y = some .lt → f x < f y)
    (heq : compare x y = some .eq → f x = f y)
    (hgt : compare x y = some .gt → f y < f x) :
    f (minimum x y) = min (f x) (f y) := by
  have hchoose := chooseNaN2_none_of_not_isNaN x y hx hy
  cases hcompare : compare x y with
  | none =>
      rcases (compare_eq_none_iff x y).1 hcompare with hnan | hnan <;> simp_all
  | some order =>
      cases order with
      | lt =>
          simp [minimum, Internal.Value.minimum, hchoose, hcompare, min_eq_left (hlt hcompare).le]
      | gt =>
          simp [minimum, Internal.Value.minimum, hchoose, hcompare, min_eq_right (hgt hcompare).le]
      | eq =>
          cases hzeros : isZero x && isZero y with
          | false =>
              simp [minimum, Internal.Value.minimum, hchoose, hcompare, hzeros,
                min_eq_left (heq hcompare).le]
          | true =>
              have hzeroParts : isZero x = true ∧ isZero y = true := by
                simpa [Bool.and_eq_true] using hzeros
              simp [minimum, Internal.Value.minimum, hchoose, hcompare, hzeros,
                hzero hzeroParts.1 hzeroParts.2, min_eq_left (heq hcompare).le]

/--
On non-NaN operands, a value map that respects the model comparison and gives every zero the same
value carries IEEE `maximum` to `max`.
-/
private theorem map_maximum_eq_max {α : Type*} [LinearOrder α] {fmt : FloatFormat}
    (f : Model fmt → α) {x y : Model fmt} (hx : isNaN x = false) (hy : isNaN y = false)
    (hzero : isZero x = true → isZero y = true → ∀ sign, f (zero fmt sign) = f x)
    (hlt : compare x y = some .lt → f x < f y)
    (heq : compare x y = some .eq → f x = f y)
    (hgt : compare x y = some .gt → f y < f x) :
    f (maximum x y) = max (f x) (f y) := by
  have hchoose := chooseNaN2_none_of_not_isNaN x y hx hy
  cases hcompare : compare x y with
  | none =>
      rcases (compare_eq_none_iff x y).1 hcompare with hnan | hnan <;> simp_all
  | some order =>
      cases order with
      | lt =>
          simp [maximum, Internal.Value.maximum, hchoose, hcompare, max_eq_right (hlt hcompare).le]
      | gt =>
          simp [maximum, Internal.Value.maximum, hchoose, hcompare, max_eq_left (hgt hcompare).le]
      | eq =>
          cases hzeros : isZero x && isZero y with
          | false =>
              simp [maximum, Internal.Value.maximum, hchoose, hcompare, hzeros,
                max_eq_left (heq hcompare).ge]
          | true =>
              have hzeroParts : isZero x = true ∧ isZero y = true := by
                simpa [Bool.and_eq_true] using hzeros
              simp [maximum, Internal.Value.maximum, hchoose, hcompare, hzeros,
                hzero hzeroParts.1 hzeroParts.2, max_eq_left (heq hcompare).ge]

/--
On finite inputs, IEEE `minimum` agrees with real `min`. Its signed-zero tie break,
`minimum(+0, -0) = -0`, is invisible here because both zeros denote `0`.
-/
theorem toReal_minimum_eq_min
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    toReal (minimum x y) = min (toReal x) (toReal y) := by
  exact map_minimum_eq_min toReal (isNaN_eq_false_of_toDyadic?_some hx)
    (isNaN_eq_false_of_toDyadic?_some hy)
    (fun hxz _ _ => by
      rw [toReal_eq_zero_of_isZero x hxz, toReal_eq_zero_of_isZero _ (isZero_zero _ _)])
    (compare_eq_some_lt_iff_toReal_lt x y hx hy).mp
    (compare_eq_some_eq_iff_toReal_eq x y hx hy).mp
    (compare_eq_some_gt_iff_toReal_gt x y hx hy).mp

/--
On finite inputs, IEEE `maximum` agrees with real `max`. Its signed-zero tie break,
`maximum(+0, -0) = +0`, is invisible here because both zeros denote `0`.
-/
theorem toReal_maximum_eq_max
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    toReal (maximum x y) = max (toReal x) (toReal y) := by
  exact map_maximum_eq_max toReal (isNaN_eq_false_of_toDyadic?_some hx)
    (isNaN_eq_false_of_toDyadic?_some hy)
    (fun hxz _ _ => by
      rw [toReal_eq_zero_of_isZero x hxz, toReal_eq_zero_of_isZero _ (isZero_zero _ _)])
    (compare_eq_some_lt_iff_toReal_lt x y hx hy).mp
    (compare_eq_some_eq_iff_toReal_eq x y hx hy).mp
    (compare_eq_some_gt_iff_toReal_gt x y hx hy).mp

/-- On finite inputs, IEEE `minimum` agrees with real `min`. -/
theorem toReal_minimum_eq_min_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toReal (minimum x y) = min (toReal x) (toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  exact toReal_minimum_eq_min x y hdx hdy

/-- On finite inputs, IEEE `maximum` agrees with real `max`. -/
theorem toReal_maximum_eq_max_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    toReal (maximum x y) = max (toReal x) (toReal y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite hx
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite hy
  exact toReal_maximum_eq_max x y hdx hdy

/--
IEEE `maximum` of finite values is finite in every format. Two equal zeros give the policy-aware
zero, which is positive zero when the format has a single zero.
-/
theorem isFinite_maximum {fmt : FloatFormat} (x y : Model fmt) (hx : isFinite x = true)
    (hy : isFinite y = true) : isFinite (maximum x y) = true := by
  have hxNaN := isNaN_eq_false_of_isFinite_eq_true x hx
  have hyNaN := isNaN_eq_false_of_isFinite_eq_true y hy
  have hzero (sign : Bool) : isFinite (zero fmt sign) = true :=
    isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign)
  have ordinary : maximum x y =
      match compareNonNaN x y hxNaN hyNaN with
      | .lt => y
      | .gt => x
      | .eq => if isZero x && isZero y then zero fmt (signBit x && signBit y) else x := by
    simp only [maximum, Internal.Value.maximum, chooseNaN2_none_of_not_isNaN x y hxNaN hyNaN,
      withNaNSelection, dite_eq_left True.intro]
    rfl
  rw [ordinary]
  cases comparison : compareNonNaN x y hxNaN hyNaN with
  | lt => simpa only [comparison] using hy
  | gt => simpa only [comparison] using hx
  | eq =>
      by_cases zeros : (isZero x && isZero y) = true
      · simpa only [comparison, ite_eq_left zeros] using hzero (signBit x && signBit y)
      · simpa only [comparison, ite_eq_right zeros] using hx

/-! ## Extended-real comparison -/

/-- Every non-NaN executable value has a partial extended-real interpretation. -/
theorem exists_toEReal?_of_isNaN_eq_false
    {fmt : FloatFormat} (x : Model fmt) (hx : isNaN x = false) :
    ∃ value, toEReal? x = some value := by
  cases hinf : isInf x <;> simp [toEReal?, hx, hinf]

/--
Every successful extended-real interpretation is either a signed infinity or a finite real value.
-/
theorem toEReal?_cases
    {fmt : FloatFormat} (x : Model fmt) {value : EReal}
    (hx : toEReal? x = some value) :
    (isInf x = true ∧
        value = if signBit x then (⊥ : EReal) else (⊤ : EReal)) ∨
      (isFinite x = true ∧ value = (toReal x : EReal)) := by
  by_cases hinf : isInf x = true
  · left
    refine ⟨hinf, ?_⟩
    have hnan := isNaN_eq_false_of_isInf_eq_true x hinf
    unfold toEReal? at hx
    rw [hnan, hinf] at hx
    simpa using hx.symm
  · right
    have hinfFalse : isInf x = false := by
      simpa using hinf
    have hnan : isNaN x = false := by
      by_contra h
      simp only [Bool.not_eq_false] at h
      unfold toEReal? at hx
      rw [h] at hx
      simp at hx
    have hfinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnan hinfFalse
    refine ⟨hfinite, ?_⟩
    unfold toEReal? at hx
    rw [hnan, hinfFalse] at hx
    simpa using hx.symm

/-- A non-NaN comparison returns the ordering of its exact extended-real values. -/
theorem compare_eq_of_toEReal? {fmt : FloatFormat} {x y : Model fmt} {a b : EReal}
    (hx : toEReal? x = some a) (hy : toEReal? y = some b) :
    compare x y = some (Ord.compare a b) := by
  classical
  symm
  rcases toEReal?_cases x hx with ⟨hxInf, rfl⟩ | ⟨hxFin, rfl⟩ <;>
    rcases toEReal?_cases y hy with ⟨hyInf, rfl⟩ | ⟨hyFin, rfl⟩
  · have hxNaN := isNaN_eq_false_of_isInf_eq_true x hxInf
    have hyNaN := isNaN_eq_false_of_isInf_eq_true y hyInf
    cases hxSign : signBit x <;> cases hySign : signBit y <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hxSign, hySign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · have hxNaN := isNaN_eq_false_of_isInf_eq_true x hxInf
    have hyNaN := isNaN_eq_false_of_isFinite_eq_true y hyFin
    have hyInf := isInf_eq_false_of_isFinite_eq_true y hyFin
    cases hxSign : signBit x <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hxSign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · have hxNaN := isNaN_eq_false_of_isFinite_eq_true x hxFin
    have hyNaN := isNaN_eq_false_of_isInf_eq_true y hyInf
    have hxInf := isInf_eq_false_of_isFinite_eq_true x hxFin
    cases hySign : signBit y <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hySign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · rcases lt_trichotomy (toReal x) (toReal y) with h | h | h
    · rw [(compare_eq_some_lt_iff_toReal_lt_of_isFinite x y hxFin hyFin).2 h]
      simp [compare_lt_iff_lt, h]
    · rw [(compare_eq_some_eq_iff_toReal_eq_of_isFinite x y hxFin hyFin).2 h, h]
      simp
    · rw [(compare_eq_some_gt_iff_toReal_gt_of_isFinite x y hxFin hyFin).2 h]
      simp [compare_gt_iff_gt, h]

/-- Non-NaN executable comparison agrees with strict extended-real order. -/
theorem compare_eq_some_lt_iff_toEReal_lt
    {fmt : FloatFormat} {x y : Model fmt} {ex ey : EReal}
    (hx : toEReal? x = some ex) (hy : toEReal? y = some ey) :
    compare x y = some .lt ↔ ex < ey := by
  rw [compare_eq_of_toEReal? hx hy, Option.some.injEq, compare_lt_iff_lt]

/-- Non-NaN executable comparison agrees with extended-real equality. -/
theorem compare_eq_some_eq_iff_toEReal_eq
    {fmt : FloatFormat} {x y : Model fmt} {ex ey : EReal}
    (hx : toEReal? x = some ex) (hy : toEReal? y = some ey) :
    compare x y = some .eq ↔ ex = ey := by
  rw [compare_eq_of_toEReal? hx hy, Option.some.injEq, compare_eq_iff_eq]

/-- Every non-NaN value compares equal to itself. -/
theorem compare_self_of_isNaN_eq_false {fmt : FloatFormat}
    (x : Model fmt) (h : isNaN x = false) :
    compare x x = some .eq := by
  obtain ⟨value, hx⟩ := exists_toEReal?_of_isNaN_eq_false x h
  exact (compare_eq_some_eq_iff_toEReal_eq hx hx).2 rfl

/-- Non-NaN executable comparison agrees with reversed strict extended-real order. -/
theorem compare_eq_some_gt_iff_toEReal_gt
    {fmt : FloatFormat} {x y : Model fmt} {ex ey : EReal}
    (hx : toEReal? x = some ex) (hy : toEReal? y = some ey) :
    compare x y = some .gt ↔ ey < ex := by
  rw [compare_eq_of_toEReal? hx hy, Option.some.injEq, compare_gt_iff_gt]

/-! ## Extended-real minimum and maximum -/

/-- The total extended-real interpretation erases the sign of an executable zero. -/
theorem toEReal_eq_zero_of_isZero
    {fmt : FloatFormat} (x : Model fmt) (hx : isZero x = true) :
    toEReal x = 0 := by
  have hfinite := isFinite_eq_true_of_isZero_eq_true x hx
  rw [toEReal_eq_coe_toReal_of_isFinite x hfinite,
    toReal_eq_zero_of_isZero x hx]
  simp

/-- On non-NaN operands, the total extended-real interpretation respects the model comparison. -/
private theorem toEReal_respects_compare {fmt : FloatFormat} {x y : Model fmt}
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    (compare x y = some .lt → toEReal x < toEReal y) ∧
      (compare x y = some .eq → toEReal x = toEReal y) ∧
      (compare x y = some .gt → toEReal y < toEReal x) := by
  obtain ⟨ex, hx⟩ := exists_toEReal?_of_isNaN_eq_false x hxNaN
  obtain ⟨ey, hy⟩ := exists_toEReal?_of_isNaN_eq_false y hyNaN
  rw [toEReal_of_toEReal? hx, toEReal_of_toEReal? hy]
  exact ⟨(compare_eq_some_lt_iff_toEReal_lt hx hy).mp,
    (compare_eq_some_eq_iff_toEReal_eq hx hy).mp,
    (compare_eq_some_gt_iff_toEReal_gt hx hy).mp⟩

/-- Every zero has the extended-real value of any other zero, whatever the signs. -/
private theorem toEReal_zero_eq_of_isZero {fmt : FloatFormat} {x : Model fmt}
    (hx : isZero x = true) (sign : Bool) :
    toEReal (zero fmt sign) = toEReal x := by
  rw [toEReal_eq_zero_of_isZero x hx, toEReal_eq_zero_of_isZero _ (isZero_zero _ _)]

/--
IEEE `minimum` agrees with `min` on every pair of non-NaN values in `EReal`, infinities included.
NaNs are excluded: `minimum` propagates them, while `toEReal` sends them to `0`.
-/
theorem toEReal_minimum_eq_min
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minimum x y) = min (toEReal x) (toEReal y) := by
  obtain ⟨hlt, heq, hgt⟩ := toEReal_respects_compare hxNaN hyNaN
  exact map_minimum_eq_min toEReal hxNaN hyNaN
    (fun hxz _ sign => toEReal_zero_eq_of_isZero hxz sign) hlt heq hgt

/--
IEEE `maximum` agrees with `max` on every pair of non-NaN values in `EReal`, infinities included.
NaNs are excluded: `maximum` propagates them, while `toEReal` sends them to `0`.
-/
theorem toEReal_maximum_eq_max
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maximum x y) = max (toEReal x) (toEReal y) := by
  obtain ⟨hlt, heq, hgt⟩ := toEReal_respects_compare hxNaN hyNaN
  exact map_maximum_eq_max toEReal hxNaN hyNaN
    (fun hxz _ sign => toEReal_zero_eq_of_isZero hxz sign) hlt heq hgt

/--
On non-NaN values, `minNum` has the extended-real semantics of mathematical minimum. The encoded
result keeps its signed-zero tie breaking, which `toEReal` does not see because it identifies the
two zeros.
-/
theorem toEReal_minNum_eq_min
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minNum x y) = min (toEReal x) (toEReal y) := by
  rw [minNum_eq_minimum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_minimum_eq_min x y hxNaN hyNaN

/--
On non-NaN values, `maxNum` has the extended-real semantics of mathematical maximum. The encoded
result keeps its signed-zero tie breaking, which `toEReal` does not see because it identifies the
two zeros.
-/
theorem toEReal_maxNum_eq_max
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maxNum x y) = max (toEReal x) (toEReal y) := by
  rw [maxNum_eq_maximum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_maximum_eq_max x y hxNaN hyNaN

/-- On non-NaN values, `minimumNumber` has the extended-real semantics of mathematical minimum. -/
theorem toEReal_minimumNumber_eq_min
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (minimumNumber x y) = min (toEReal x) (toEReal y) := by
  rw [minimumNumber_eq_minimum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_minimum_eq_min x y hxNaN hyNaN

/-- On non-NaN values, `maximumNumber` has the extended-real semantics of mathematical maximum. -/
theorem toEReal_maximumNumber_eq_max
    {fmt : FloatFormat} (x y : Model fmt)
    (hxNaN : isNaN x = false) (hyNaN : isNaN y = false) :
    toEReal (maximumNumber x y) = max (toEReal x) (toEReal y) := by
  rw [maximumNumber_eq_maximum_of_not_isNaN x y hxNaN hyNaN]
  exact toEReal_maximum_eq_max x y hxNaN hyNaN

/--
`minimumNumber` is commutative up to extended-real value, a reading that identifies the two signed
zeros and sends every NaN to zero. On the words themselves, two zeros give the same word in either
order (`minimumNumber_of_isZero`) and a single NaN operand is skipped in either order. Two NaN
operands give a NaN both ways (`isNaN_minimumNumber`), but `bothNaNNumber` quiets the left operand
unless only the right one is signaling, so sign and payload can depend on the order.
-/
theorem toEReal_minimumNumber_comm
    {fmt : FloatFormat} (x y : Model fmt) :
    toEReal (minimumNumber x y) = toEReal (minimumNumber y x) := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y
  · rw [toEReal_minimumNumber_eq_min x y hxNaN hyNaN,
      toEReal_minimumNumber_eq_min y x hyNaN hxNaN, min_comm]
  · rw [minimumNumber_of_isNaN_right x y hxNaN hyNaN, minimumNumber_of_isNaN_left y x hyNaN hxNaN]
  · rw [minimumNumber_of_isNaN_left x y hxNaN hyNaN, minimumNumber_of_isNaN_right y x hyNaN hxNaN]
  · rw [minimumNumber_of_isNaN_both x y hxNaN hyNaN, minimumNumber_of_isNaN_both y x hyNaN hxNaN,
      toEReal_eq_ite, toEReal_eq_ite, isNaN_bothNaNNumber hxNaN hyNaN,
      isNaN_bothNaNNumber hyNaN hxNaN]
    rfl

/--
The `maximumNumber` counterpart of `toEReal_minimumNumber_comm`, with the same scope: for two NaN
operands both orders deliver a NaN (`isNaN_maximumNumber`) whose sign and payload can depend on the
order.
-/
theorem toEReal_maximumNumber_comm
    {fmt : FloatFormat} (x y : Model fmt) :
    toEReal (maximumNumber x y) = toEReal (maximumNumber y x) := by
  cases hxNaN : isNaN x <;> cases hyNaN : isNaN y
  · rw [toEReal_maximumNumber_eq_max x y hxNaN hyNaN,
      toEReal_maximumNumber_eq_max y x hyNaN hxNaN, max_comm]
  · rw [maximumNumber_of_isNaN_right x y hxNaN hyNaN, maximumNumber_of_isNaN_left y x hyNaN hxNaN]
  · rw [maximumNumber_of_isNaN_left x y hxNaN hyNaN, maximumNumber_of_isNaN_right y x hyNaN hxNaN]
  · rw [maximumNumber_of_isNaN_both x y hxNaN hyNaN, maximumNumber_of_isNaN_both y x hyNaN hxNaN,
      toEReal_eq_ite, toEReal_eq_ite, isNaN_bothNaNNumber hxNaN hyNaN,
      isNaN_bothNaNNumber hyNaN hxNaN]
    rfl

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
