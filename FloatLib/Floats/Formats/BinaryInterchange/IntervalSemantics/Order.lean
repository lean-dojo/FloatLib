/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Core

/-!
# Order of interval endpoints

Boolean endpoint comparisons agree with real order for finite values and with extended-real
order for non-NaN values, including infinities. The non-NaN hypotheses are needed because NaNs
are unordered.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

section

/-- The proposition-valued and Boolean executable non-strict orders agree. -/
theorem le_iff_leB_eq_true
    {fmt : FloatFormat} (x y : Model fmt) :
    Model.le x y ↔ leB x y = true := by
  unfold Model.le leB
  cases hcompare : compare x y with
  | none => simp
  | some order =>
      cases order <;> simp

/-- On non-NaN values, executable comparison agrees exactly with extended-real `≤`. -/
theorem le_iff_toEReal_le_of_isNaN_eq_false
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    Model.le x y ↔ toEReal x ≤ toEReal y := by
  obtain ⟨ex, hex⟩ := exists_toEReal?_of_isNaN_eq_false x hx
  obtain ⟨ey, hey⟩ := exists_toEReal?_of_isNaN_eq_false y hy
  have hxTotal : toEReal x = ex := toEReal_of_toEReal? hex
  have hyTotal : toEReal y = ey := toEReal_of_toEReal? hey
  rcases lt_trichotomy ex ey with hlt | heq | hgt
  · have hcompare := (compare_eq_some_lt_iff_toEReal_lt hex hey).2 hlt
    simp [Model.le, hcompare, hxTotal, hyTotal, hlt.le]
  · have hcompare := (compare_eq_some_eq_iff_toEReal_eq hex hey).2 heq
    simp [Model.le, hcompare, hxTotal, hyTotal, heq.le]
  · have hcompare := (compare_eq_some_gt_iff_toEReal_gt hex hey).2 hgt
    simp [Model.le, hcompare, hxTotal, hyTotal, not_le_of_gt hgt]

/-- Boolean endpoint comparison agrees with extended-real order on non-NaN values. -/
theorem leB_eq_true_iff_toEReal_le_of_isNaN_eq_false
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isNaN x = false) (hy : isNaN y = false) :
    leB x y = true ↔ toEReal x ≤ toEReal y :=
  (le_iff_leB_eq_true x y).symm.trans (le_iff_toEReal_le_of_isNaN_eq_false x y hx hy)

/-- On finite values, executable boolean comparison agrees exactly with real `≤`. -/
theorem leB_eq_true_iff_toReal_le_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    leB x y = true ↔ toReal x ≤ toReal y := by
  rw [leB_eq_true_iff_toEReal_le_of_isNaN_eq_false x y
      (isNaN_eq_false_of_isFinite_eq_true x hx) (isNaN_eq_false_of_isFinite_eq_true y hy),
    toEReal_eq_coe_toReal_of_isFinite x hx, toEReal_eq_coe_toReal_of_isFinite y hy,
    EReal.coe_le_coe_iff]

/-- On finite values, the proposition-valued executable order agrees exactly with real `≤`. -/
theorem le_iff_toReal_le_of_isFinite
    {fmt : FloatFormat} (x y : Model fmt)
    (hx : isFinite x = true) (hy : isFinite y = true) :
    Model.le x y ↔ toReal x ≤ toReal y := by
  rw [le_iff_leB_eq_true, leB_eq_true_iff_toReal_le_of_isFinite x y hx hy]

/-- Ordered, non-NaN extended-real endpoints define a valid interval. -/
theorem validExtended_of_toEReal_le
    {fmt : FloatFormat} {I : Interval fmt}
    (hlo : isNaN I.lo = false) (hhi : isNaN I.hi = false)
    (hordered : toEReal I.lo ≤ toEReal I.hi) : ValidExtended I :=
  ⟨hlo, hhi, (le_iff_toEReal_le_of_isNaN_eq_false I.lo I.hi hlo hhi).2 hordered⟩

/-- A valid interval's decoded lower endpoint does not exceed its decoded upper endpoint. -/
theorem Valid.toReal_ordered
    {fmt : FloatFormat} {I : Interval fmt} (hI : Valid I) :
    toReal I.lo ≤ toReal I.hi :=
  (le_iff_toReal_le_of_isFinite I.lo I.hi hI.1 hI.2.1).mp hI.2.2

/-- An extended-valid interval has ordered extended-real endpoints. -/
theorem ValidExtended.toEReal_ordered
    {fmt : FloatFormat} {I : Interval fmt} (hI : ValidExtended I) :
    toEReal I.lo ≤ toEReal I.hi :=
  (le_iff_toEReal_le_of_isNaN_eq_false I.lo I.hi
    hI.lo_isNaN_eq_false hI.hi_isNaN_eq_false).1 hI.ordered

/-- A finite executable value defines a valid degenerate interval. -/
theorem valid_point_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hx : isFinite x = true) :
    Valid (point x) := by
  refine ⟨hx, hx, ?_⟩
  exact (le_iff_toReal_le_of_isFinite x x hx hx).2 le_rfl

/-- Every non-NaN value defines an extended-valid degenerate interval. -/
theorem validExtended_point_of_isNaN_eq_false
    {fmt : FloatFormat} (x : Model fmt) (hx : isNaN x = false) :
    ValidExtended (point x) := by
  refine ⟨hx, hx, ?_⟩
  exact (le_iff_toEReal_le_of_isNaN_eq_false x x hx hx).2 le_rfl

/-- The full IEEE range, including infinities, is extended-valid. -/
theorem validExtended_whole (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    ValidExtended (whole fmt) := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hsupports : fmt.supportsInfinity = true := by
    simp [FloatFormat.supportsInfinity, hencoding]
  have hwhole : whole fmt = ⟨negInf fmt, posInf fmt⟩ := by
    simp [whole, Model.infinityOrMaxFinite, hencoding]
  rw [hwhole]
  refine ⟨isNaN_negInf fmt hsupports, isNaN_posInf fmt hsupports, ?_⟩
  apply (le_iff_toEReal_le_of_isNaN_eq_false
    (negInf fmt) (posInf fmt)
    (isNaN_negInf fmt hsupports) (isNaN_posInf fmt hsupports)).2
  rw [toEReal_negInf fmt hfmt, toEReal_posInf fmt hfmt]
  exact bot_le

/-- Every extended-real value belongs to the full IEEE range. -/
theorem eRealMem_whole (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x : EReal) :
    ERealMem (whole fmt) x := by
  have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
  simp [ERealMem, whole, Model.infinityOrMaxFinite, hencoding,
    toEReal_negInf fmt hfmt, toEReal_posInf fmt hfmt]

/-- Checking candidate endpoints can only lower the lower bound of an IEEE enclosure. -/
theorem ofBounds_lower_le {fmt : FloatFormat} (lo hi : Model fmt)
    (hfmt : fmt.isIEEE = true) : toEReal (ofBounds lo hi).lo ≤ toEReal lo := by
  unfold ofBounds
  split
  · exact le_rfl
  · exact (eRealMem_whole fmt hfmt _).1

/-- Checking candidate endpoints can only raise the upper bound of an IEEE enclosure. -/
theorem le_ofBounds_upper {fmt : FloatFormat} (lo hi : Model fmt)
    (hfmt : fmt.isIEEE = true) : toEReal hi ≤ toEReal (ofBounds lo hi).hi := by
  unfold ofBounds
  split
  · exact le_rfl
  · exact (eRealMem_whole fmt hfmt _).2

/-- Ordered finite bounds survive the enclosure check exactly. -/
theorem ofBounds_eq_of_isFinite {fmt : FloatFormat} (lo hi : Model fmt)
    (hlo : isFinite lo = true) (hhi : isFinite hi = true)
    (hordered : toReal lo ≤ toReal hi) : ofBounds lo hi = ⟨lo, hi⟩ := by
  simp [ofBounds, (leB_eq_true_iff_toReal_le_of_isFinite lo hi hlo hhi).2 hordered]

/-- A real enclosure with finite candidate endpoints survives the bounds check. -/
theorem realMem_ofBounds {fmt : FloatFormat} {lo hi : Model fmt} {x : ℝ}
    (hlo : isFinite lo = true) (hhi : isFinite hi = true)
    (hx : RealMem ⟨lo, hi⟩ x) : RealMem (ofBounds lo hi) x := by
  rw [ofBounds_eq_of_isFinite lo hi hlo hhi (hx.1.trans hx.2)]
  exact hx

/-- Checked IEEE bounds always define an ordered interval without NaN endpoints. -/
theorem validExtended_ofBounds {fmt : FloatFormat} (lo hi : Model fmt)
    (hfmt : fmt.isIEEE = true) : ValidExtended (ofBounds lo hi) := by
  unfold ofBounds
  split
  next hle =>
    have hnan : (isNaN lo || isNaN hi) = false := by
      by_contra h
      have htrue : (isNaN lo || isNaN hi) = true := Bool.eq_true_of_not_eq_false h
      simp [leB, compare, htrue] at hle
    exact ⟨(Bool.or_eq_false_iff.mp hnan).1, (Bool.or_eq_false_iff.mp hnan).2,
      (le_iff_leB_eq_true lo hi).2 hle⟩
  next => exact validExtended_whole fmt hfmt

end

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
