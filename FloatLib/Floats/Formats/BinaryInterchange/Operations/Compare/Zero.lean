/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Finite

/-!
# Signed-zero policies of binary extrema

Minimum combines zero signs by disjunction and maximum by conjunction. The results account for
formats with a single zero and for number variants.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

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
  simp only [minimum, Internal.Value.minimum, compare_zero_false_true, Option.some.injEq,
    compareNonNaN_eq_of_compare_eq_some, isZero_zero, Bool.and_self, ↓reduceIte, signBit_zero,
    Bool.false_and, Bool.true_and, Bool.false_or, hchoose, withNaNSelection_of_none]
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

end Model
end FloatLib.Floats.Formats.BinaryInterchange
