/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Zero
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics

/-!
# Extended-real order of binary values

Non-NaN comparisons agree with extended-real order, including infinities. The same interpretation
carries binary extrema to extended-real extrema.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Every non-NaN executable value has a partial extended-real interpretation. -/
theorem exists_toEReal?_of_isNaN_eq_false
    {fmt : FloatFormat} (x : Model fmt) (hx : isNaN x = false) :
    ∃ value, toEReal? x = some value := by
  cases hinf : isInfinite x <;> simp [toEReal?, hx, hinf]

/--
Every successful extended-real interpretation is either a signed infinity or a finite real value.
-/
theorem toEReal?_cases
    {fmt : FloatFormat} (x : Model fmt) {value : EReal}
    (hx : toEReal? x = some value) :
    (isInfinite x = true ∧
        value = if signBit x then (⊥ : EReal) else (⊤ : EReal)) ∨
      (isFinite x = true ∧ value = (toReal x : EReal)) := by
  by_cases hinf : isInfinite x = true
  · left
    refine ⟨hinf, ?_⟩
    have hnan := isNaN_eq_false_of_isInfinite_eq_true x hinf
    unfold toEReal? at hx
    rw [hnan, hinf] at hx
    simpa using hx.symm
  · right
    have hinfFalse : isInfinite x = false := by
      simpa using hinf
    have hnan : isNaN x = false := by
      by_contra h
      simp only [Bool.not_eq_false] at h
      unfold toEReal? at hx
      rw [h] at hx
      simp at hx
    have hfinite :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInfinite_eq_false x hnan hinfFalse
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
  · have hxNaN := isNaN_eq_false_of_isInfinite_eq_true x hxInf
    have hyNaN := isNaN_eq_false_of_isInfinite_eq_true y hyInf
    cases hxSign : signBit x <;> cases hySign : signBit y <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hxSign, hySign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · have hxNaN := isNaN_eq_false_of_isInfinite_eq_true x hxInf
    have hyNaN := isNaN_eq_false_of_isFinite_eq_true y hyFin
    have hyInf := isInfinite_eq_false_of_isFinite_eq_true y hyFin
    cases hxSign : signBit x <;>
      simp [compare, compareNonNaN, hxNaN, hyNaN, hxInf, hyInf, hxSign,
        compare_lt_iff_lt, compare_gt_iff_gt]
  · have hxNaN := isNaN_eq_false_of_isFinite_eq_true x hxFin
    have hyNaN := isNaN_eq_false_of_isInfinite_eq_true y hyInf
    have hxInf := isInfinite_eq_false_of_isFinite_eq_true x hxFin
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
end Model
end FloatLib.Floats.Formats.BinaryInterchange
