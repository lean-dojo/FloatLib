/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Classification

/-!
# Order-preserving interpretation of binary extrema

An order-preserving value map carries binary minimum and maximum to the corresponding extrema in
any linear order, when all zeros have the same value. Maximum also preserves finiteness.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
On non-NaN operands, a value map that respects the model comparison and gives every zero the same
value carries IEEE `minimum` to `min`. The signed-zero tie break is invisible to such a map.
-/
theorem map_minimum_eq_min {α : Type*} [LinearOrder α] {fmt : FloatFormat}
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
theorem map_maximum_eq_max {α : Type*} [LinearOrder α] {fmt : FloatFormat}
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

end Model
end FloatLib.Floats.Formats.BinaryInterchange
