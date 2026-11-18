/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Selection
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.DyadicOrder

/-!
# Real order of finite binary values

Finite executable comparisons agree with exact dyadic and real order. Consequently the real values
of minimum and maximum are the real extrema.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
When both operands decode to dyadics, executable comparison returns their exact dyadic ordering.
-/
theorem compare_eq_some_cmpDyadic_of_toDyadic?
    {fmt : FloatFormat} (x y : Model fmt) {dx dy : Numerics.Dyadic}
    (hx : toDyadic? x = some dx) (hy : toDyadic? y = some dy) :
    compare x y = some (cmpDyadic dx dy) := by
  have hxNaN := isNaN_eq_false_of_toDyadic?_some hx
  have hyNaN := isNaN_eq_false_of_toDyadic?_some hy
  have hxInf := isInfinite_eq_false_of_toDyadic?_some hx
  have hyInf := isInfinite_eq_false_of_toDyadic?_some hy
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

end Model
end FloatLib.Floats.Formats.BinaryInterchange
