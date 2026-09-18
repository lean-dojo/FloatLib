/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.FiniteBounds
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Order
public import FloatLib.Floats.Interval.RealBounds

/-!
# Range-limited finite-only interval enclosures

Finite-only formats saturate instead of producing infinity. Their outward interval operations are
therefore sound only when the exact endpoint expressions remain inside the finite range. This
module states those range premises explicitly.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

section

/--
Finite-only interval addition encloses every selected sum when both exact endpoint sums fit in the
format's symmetric finite range.
-/
theorem add_sound_of_encoding_finite
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.encoding = .finite)
    (hloRange :
      |toReal A.lo + toReal B.lo| ≤ toReal (posMaxFinite fmt))
    (hhiRange :
      |toReal A.hi + toReal B.hi| ≤ toReal (posMaxFinite fmt))
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    RealMem (add A B) (x + y) := by
  apply realMem_ofBounds
    (isFinite_eq_true_of_encoding_finite hfmt _)
    (isFinite_eq_true_of_encoding_finite hfmt _)
  constructor
  · change toReal (Model.addDown A.lo B.lo) ≤ x + y
    exact (toReal_addDown_le_of_encoding_finite A.lo B.lo hfmt hloRange).trans
      (add_le_add hx.1 hy.1)
  · change x + y ≤ toReal (Model.addUp A.hi B.hi)
    exact (add_le_add hx.2 hy.2).trans
      (le_toReal_addUp_of_encoding_finite A.hi B.hi hfmt hhiRange)

/--
Finite-only interval subtraction is sound when its two exact endpoint differences fit in range.
-/
theorem sub_sound_of_encoding_finite
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.encoding = .finite)
    (hloRange :
      |toReal A.lo - toReal B.hi| ≤ toReal (posMaxFinite fmt))
    (hhiRange :
      |toReal A.hi - toReal B.lo| ≤ toReal (posMaxFinite fmt))
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    RealMem (sub A B) (x - y) := by
  apply realMem_ofBounds
    (isFinite_eq_true_of_encoding_finite hfmt _)
    (isFinite_eq_true_of_encoding_finite hfmt _)
  constructor
  · change toReal (Model.subDown A.lo B.hi) ≤ x - y
    exact (toReal_subDown_le_of_encoding_finite A.lo B.hi hfmt hloRange).trans
      (sub_le_sub hx.1 hy.2)
  · change x - y ≤ toReal (Model.subUp A.hi B.lo)
    exact (sub_le_sub hx.2 hy.1).trans
      (le_toReal_subUp_of_encoding_finite A.hi B.lo hfmt hhiRange)

/--
Finite-only interval multiplication is sound when all four exact corner products fit in range.
-/
theorem mul_sound_of_encoding_finite
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.encoding = .finite)
    (h00 : |toReal A.lo * toReal B.lo| ≤ toReal (posMaxFinite fmt))
    (h01 : |toReal A.lo * toReal B.hi| ≤ toReal (posMaxFinite fmt))
    (h10 : |toReal A.hi * toReal B.lo| ≤ toReal (posMaxFinite fmt))
    (h11 : |toReal A.hi * toReal B.hi| ≤ toReal (posMaxFinite fmt))
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    RealMem (mul A B) (x * y) := by
  have hfinite (z : Model fmt) : isFinite z = true :=
    isFinite_eq_true_of_encoding_finite hfmt z
  have hxy :=
    FloatLib.Floats.Interval.mul_bounds_Icc
      (toReal A.lo) (toReal A.hi) (toReal B.lo) (toReal B.hi) x y hx hy
  refine realMem_ofBounds (hfinite _) (hfinite _) ⟨le_trans ?_ hxy.1, hxy.2.trans ?_⟩
  · simp only [minOfFour, FloatLib.Floats.Interval.minOfFour,
      toReal_minimum_eq_min_of_isFinite _ _ (hfinite _) (hfinite _)]
    exact min_le_min
      (min_le_min
        (toReal_mulDown_le_of_encoding_finite A.lo B.lo hfmt h00)
        (toReal_mulDown_le_of_encoding_finite A.lo B.hi hfmt h01))
      (min_le_min
        (toReal_mulDown_le_of_encoding_finite A.hi B.lo hfmt h10)
        (toReal_mulDown_le_of_encoding_finite A.hi B.hi hfmt h11))
  · simp only [maxOfFour, FloatLib.Floats.Interval.maxOfFour,
      toReal_maximum_eq_max_of_isFinite _ _ (hfinite _) (hfinite _)]
    exact max_le_max
      (max_le_max
        (le_toReal_mulUp_of_encoding_finite A.lo B.lo hfmt h00)
        (le_toReal_mulUp_of_encoding_finite A.lo B.hi hfmt h01))
      (max_le_max
        (le_toReal_mulUp_of_encoding_finite A.hi B.lo hfmt h10)
        (le_toReal_mulUp_of_encoding_finite A.hi B.hi hfmt h11))

end

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
