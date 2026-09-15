/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Division
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.NonNaN
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Subtraction
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.MinMax
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Order
public import FloatLib.Floats.Formats.BinaryInterchange.Model.SignedERealSemantics
public import FloatLib.Floats.Interval.ERealCoercions
public import FloatLib.Floats.Interval.RealBounds

/-!
# Arithmetic enclosures for executable binary intervals

Read this module after `IntervalSemantics.Order` for the proofs behind negation, addition,
subtraction, multiplication, division, and reciprocal. The four-corner arguments for products and
quotients are kept with the operations that consume them. `IntervalSemantics.Finite` supplies the
separate range-checked results for all-words-finite encodings.

IEEE binary arithmetic starts with finite valid inputs and encloses exact real results in `EReal`,
allowing overflow at the output. Negation also accepts infinite input endpoints. The validity
theorems explain which results can be passed to later interval operations; division through zero
and indeterminate candidate bounds use the whole interval.

`Interval.Arithmetic` contains the executable definitions. `IntervalSemantics.Activations` builds
ReLU, absolute-value, and square-root enclosures on the results here.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

noncomputable section

/-! ## Exact negation -/

/-- The negated interval encloses each negated real member, including with infinite endpoints. -/
theorem neg_sound_extended
    {fmt : FloatFormat} (A : Interval fmt) (hA : ValidExtended A)
    {x : ℝ} (hx : ERealMem A (x : EReal)) :
    ERealMem (neg A) ((-x : ℝ) : EReal) := by
  simpa only [ERealMem, neg, toEReal_neg_of_isNaN_eq_false A.lo hA.lo_isNaN_eq_false,
    toEReal_neg_of_isNaN_eq_false A.hi hA.hi_isNaN_eq_false, EReal.coe_neg] using
    And.intro (EReal.neg_le_neg_iff.2 hx.2) (EReal.neg_le_neg_iff.2 hx.1)

/-- Negation preserves ordered, non-NaN endpoints in every format. -/
theorem neg_validExtended
    {fmt : FloatFormat} (A : Interval fmt) (hA : ValidExtended A) :
    ValidExtended (neg A) := by
  apply validExtended_of_toEReal_le
    (by simpa [neg] using hA.hi_isNaN_eq_false)
    (by simpa [neg] using hA.lo_isNaN_eq_false)
  simpa only [neg, toEReal_neg_of_isNaN_eq_false A.lo hA.lo_isNaN_eq_false,
    toEReal_neg_of_isNaN_eq_false A.hi hA.hi_isNaN_eq_false] using
    EReal.neg_le_neg_iff.2 hA.toEReal_ordered

/-- Interval negation encloses the negation of every represented real value. -/
theorem neg_sound
    {fmt : FloatFormat} (A : Interval fmt) (hA : Valid A)
    {x : ℝ} (hx : RealMem A x) :
    ERealMem (neg A) ((-x : ℝ) : EReal) :=
  neg_sound_extended A hA.validExtended ((eRealMem_coe_iff_of_valid hA x).2 hx)

/-! ## Addition -/

/-- Outward-rounded interval addition encloses every sum of represented real values. -/
theorem add_sound
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true)
    (hA : Valid A) (hB : Valid B)
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    ERealMem (add A B) ((x + y : ℝ) : EReal) := by
  constructor
  · apply (ofBounds_lower_le (Model.addDown A.lo B.lo) (Model.addUp A.hi B.hi) hfmt).trans
    exact
      (toEReal_addDown_le A.lo B.lo hfmt hA.lo_isFinite hB.lo_isFinite).trans
        ((EReal.coe_le_coe_iff).2 (add_le_add hx.1 hy.1))
  · apply le_trans ?_ (le_ofBounds_upper (Model.addDown A.lo B.lo) (Model.addUp A.hi B.hi) hfmt)
    exact
      ((EReal.coe_le_coe_iff).2 (add_le_add hx.2 hy.2)).trans
        (le_toEReal_addUp A.hi B.hi hfmt hA.hi_isFinite hB.hi_isFinite)

/-- Outward-rounded addition always returns ordered IEEE bounds without NaNs. -/
theorem add_validExtended
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true) :
    ValidExtended (add A B) := by
  exact validExtended_ofBounds _ _ hfmt

/-! ## Subtraction -/

/-- Outward-rounded interval subtraction encloses every represented real difference. -/
theorem sub_sound
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true)
    (hA : Valid A) (hB : Valid B)
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    ERealMem (sub A B) ((x - y : ℝ) : EReal) := by
  constructor
  · apply (ofBounds_lower_le (Model.subDown A.lo B.hi) (Model.subUp A.hi B.lo) hfmt).trans
    exact
      (toEReal_subDown_le A.lo B.hi hfmt hA.lo_isFinite hB.hi_isFinite).trans
        ((EReal.coe_le_coe_iff).2 (sub_le_sub hx.1 hy.2))
  · apply le_trans ?_ (le_ofBounds_upper (Model.subDown A.lo B.hi) (Model.subUp A.hi B.lo) hfmt)
    exact
      ((EReal.coe_le_coe_iff).2 (sub_le_sub hx.2 hy.1)).trans
        (le_toEReal_subUp A.hi B.lo hfmt hA.hi_isFinite hB.lo_isFinite)

/-- Outward-rounded subtraction always returns ordered IEEE bounds without NaNs. -/
theorem sub_validExtended
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true) :
    ValidExtended (sub A B) := by
  exact validExtended_ofBounds _ _ hfmt

/-! ## Four-corner enclosures -/

/--
The checked four-corner enclosure contains every real bracketed by the exact corner values.

The corner operations `down` and `up` are applied to the endpoints of `A` and `B`. Each downward
corner must lie below, and each upward corner above, the exact value `f` of the corresponding
decoded endpoints, and neither may be a NaN. The bound hypotheses receive finiteness of both
arguments and the identity of the right endpoint, so operations with a side condition on the right
operand, such as a nonzero divisor, can discharge it per endpoint.
-/
theorem eRealMem_ofBounds_corners
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true)
    (hA : Valid A) (hB : Valid B)
    (down up : Model fmt → Model fmt → Model fmt) (f : ℝ → ℝ → ℝ) {z : ℝ}
    (hdown : ∀ a b, isFinite a = true → isFinite b = true → (b = B.lo ∨ b = B.hi) →
      isNaN (down a b) = false ∧
        toEReal (down a b) ≤ ((f (toReal a) (toReal b) : ℝ) : EReal))
    (hup : ∀ a b, isFinite a = true → isFinite b = true → (b = B.lo ∨ b = B.hi) →
      isNaN (up a b) = false ∧
        ((f (toReal a) (toReal b) : ℝ) : EReal) ≤ toEReal (up a b))
    (hz : z ∈ Set.Icc
      (FloatLib.Floats.Interval.minOfFour
        (f (toReal A.lo) (toReal B.lo)) (f (toReal A.lo) (toReal B.hi))
        (f (toReal A.hi) (toReal B.lo)) (f (toReal A.hi) (toReal B.hi)))
      (FloatLib.Floats.Interval.maxOfFour
        (f (toReal A.lo) (toReal B.lo)) (f (toReal A.lo) (toReal B.hi))
        (f (toReal A.hi) (toReal B.lo)) (f (toReal A.hi) (toReal B.hi)))) :
    ERealMem
      (ofBounds
        (minOfFour (down A.lo B.lo) (down A.lo B.hi) (down A.hi B.lo) (down A.hi B.hi))
        (maxOfFour (up A.lo B.lo) (up A.lo B.hi) (up A.hi B.lo) (up A.hi B.hi)))
      (z : EReal) := by
  have hp00 := hdown A.lo B.lo hA.lo_isFinite hB.lo_isFinite (Or.inl rfl)
  have hp01 := hdown A.lo B.hi hA.lo_isFinite hB.hi_isFinite (Or.inr rfl)
  have hp10 := hdown A.hi B.lo hA.hi_isFinite hB.lo_isFinite (Or.inl rfl)
  have hp11 := hdown A.hi B.hi hA.hi_isFinite hB.hi_isFinite (Or.inr rfl)
  have hq00 := hup A.lo B.lo hA.lo_isFinite hB.lo_isFinite (Or.inl rfl)
  have hq01 := hup A.lo B.hi hA.lo_isFinite hB.hi_isFinite (Or.inr rfl)
  have hq10 := hup A.hi B.lo hA.hi_isFinite hB.lo_isFinite (Or.inl rfl)
  have hq11 := hup A.hi B.hi hA.hi_isFinite hB.hi_isFinite (Or.inr rfl)
  constructor
  · apply (ofBounds_lower_le _ _ hfmt).trans
    apply (toEReal_minOfFour_le_of_le _ _ _ _ hp00.1 hp01.1 hp10.1 hp11.1
      hp00.2 hp01.2 hp10.2 hp11.2).trans
    simpa [FloatLib.Floats.Interval.minOfFour, FloatLib.Floats.Interval.coe_min] using
      EReal.coe_le_coe_iff.2 hz.1
  · apply le_trans ?_ (le_ofBounds_upper _ _ hfmt)
    apply le_trans ?_ (le_toEReal_maxOfFour_of_le _ _ _ _ hq00.1 hq01.1 hq10.1 hq11.1
      hq00.2 hq01.2 hq10.2 hq11.2)
    simpa [FloatLib.Floats.Interval.maxOfFour, FloatLib.Floats.Interval.coe_max] using
      EReal.coe_le_coe_iff.2 hz.2

/-! ## Four-corner multiplication -/

/-- Outward-rounded interval multiplication encloses every represented real product. -/
theorem mul_sound
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true)
    (hA : Valid A) (hB : Valid B)
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    ERealMem (mul A B) ((x * y : ℝ) : EReal) :=
  eRealMem_ofBounds_corners A B hfmt hA hB mulDown mulUp (· * ·)
    (fun a b ha hb _ =>
      ⟨isNaN_mulDown_eq_false_of_isFinite a b hfmt ha hb, toEReal_mulDown_le a b hfmt ha hb⟩)
    (fun a b ha hb _ =>
      ⟨isNaN_mulUp_eq_false_of_isFinite a b hfmt ha hb, le_toEReal_mulUp a b hfmt ha hb⟩)
    (FloatLib.Floats.Interval.mul_bounds_Icc _ _ _ _ x y hx hy)

/-- Outward-rounded multiplication always returns ordered IEEE bounds without NaNs. -/
theorem mul_validExtended
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true) :
    ValidExtended (mul A B) := by
  exact validExtended_ofBounds _ _ hfmt

/-! ## Division and reciprocal -/

/-- A valid denominator interval that excludes zero lies strictly on one side of zero. -/
private theorem denominator_sign_stable
    {fmt : FloatFormat} (B : Interval fmt) (hB : Valid B)
    (hzero : containsZero B = false) :
    toReal B.hi < 0 ∨ 0 < toReal B.lo := by
  have hlo := leB_eq_true_iff_toEReal_le_of_isNaN_eq_false B.lo (zero fmt false)
    (isNaN_eq_false_of_isFinite_eq_true _ hB.lo_isFinite) (isNaN_zero fmt false)
  have hhi := leB_eq_true_iff_toEReal_le_of_isNaN_eq_false (zero fmt true) B.hi
    (isNaN_zero fmt true) (isNaN_eq_false_of_isFinite_eq_true _ hB.hi_isFinite)
  rw [toEReal_zero, toEReal_eq_coe_toReal_of_isFinite _ hB.lo_isFinite, EReal.coe_nonpos] at hlo
  rw [toEReal_zero, toEReal_eq_coe_toReal_of_isFinite _ hB.hi_isFinite, EReal.coe_nonneg] at hhi
  simp only [containsZero, Bool.and_eq_false_iff] at hzero
  rcases hzero with h | h
  · exact Or.inr (lt_of_not_ge fun hle => by simp [hlo.2 hle] at h)
  · exact Or.inl (lt_of_not_ge fun hle => by simp [hhi.2 hle] at h)

/-- No value between the endpoints of a sign-stable interval is a zero. -/
private theorem isZero_eq_false_of_sign_stable
    {fmt : FloatFormat} (B : Interval fmt)
    (hsign : toReal B.hi < 0 ∨ 0 < toReal B.lo)
    {b : Model fmt} (hlo : toReal B.lo ≤ toReal b) (hhi : toReal b ≤ toReal B.hi) :
    isZero b = false := by
  refine Bool.eq_false_iff.mpr fun hzero => ?_
  have hreal := toReal_eq_zero_of_isZero b hzero
  rcases hsign with h | h <;> linarith

/--
Outward-rounded interval division encloses every represented real quotient.

The theorem is total in the denominator: when `B` contains zero the result is `whole fmt`, which
encloses every real, and otherwise the four directed corner quotients bracket `x / y`. Both
intervals must be `Valid` (finite ordered endpoints) because the directed division kernels are
specified only on finite operands; an extended version with infinite endpoints would need
directed-division semantics for infinite arguments, which the library does not provide.
-/
theorem div_sound
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true)
    (hA : Valid A) (hB : Valid B)
    {x y : ℝ} (hx : RealMem A x) (hy : RealMem B y) :
    ERealMem (div A B) ((x / y : ℝ) : EReal) := by
  by_cases hcontains : containsZero B = true
  · rw [div, if_pos hcontains]
    exact eRealMem_whole fmt hfmt _
  · have hsign := denominator_sign_stable B hB (Bool.eq_false_iff.mpr hcontains)
    have hzero : ∀ b, b = B.lo ∨ b = B.hi → isZero b = false := by
      rintro b (rfl | rfl)
      · exact isZero_eq_false_of_sign_stable B hsign le_rfl hB.toReal_ordered
      · exact isZero_eq_false_of_sign_stable B hsign hB.toReal_ordered le_rfl
    rw [div, if_neg hcontains]
    exact eRealMem_ofBounds_corners A B hfmt hA hB divDown divUp (· / ·)
      (fun a b ha hb hb' =>
        ⟨isNaN_divDown_eq_false_of_isFinite a b hfmt ha hb (hzero b hb'),
          toEReal_divDown_le a b hfmt ha hb (hzero b hb')⟩)
      (fun a b ha hb hb' =>
        ⟨isNaN_divUp_eq_false_of_isFinite a b hfmt ha hb (hzero b hb'),
          le_toEReal_divUp a b hfmt ha hb (hzero b hb')⟩)
      (FloatLib.Floats.Interval.div_bounds_Icc _ _ _ _ x y hx hy hsign)

/-- Outward-rounded division always returns ordered IEEE bounds without NaNs. -/
theorem div_validExtended
    {fmt : FloatFormat} (A B : Interval fmt) (hfmt : fmt.isIEEE = true) :
    ValidExtended (div A B) := by
  unfold div
  split
  · exact validExtended_whole fmt hfmt
  · exact validExtended_ofBounds _ _ hfmt

/-- Outward-rounded interval reciprocal encloses every represented real reciprocal. -/
theorem inv_sound
    {fmt : FloatFormat} (B : Interval fmt) (hfmt : fmt.isIEEE = true) (hB : Valid B)
    {y : ℝ} (hy : RealMem B y) :
    ERealMem (inv B) ((1 / y : ℝ) : EReal) := by
  have hOne : Valid (point (posOne fmt)) :=
    valid_point_of_isFinite (posOne fmt) (isFinite_posOne fmt)
  have hmemOne : RealMem (point (posOne fmt)) 1 := by
    simp [RealMem, point]
  simpa [inv] using
    div_sound (point (posOne fmt)) B hfmt hOne hB hmemOne hy

end

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
