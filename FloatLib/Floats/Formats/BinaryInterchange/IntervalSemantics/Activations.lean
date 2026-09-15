/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.SquareRoot
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Activations
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Arithmetic
public import FloatLib.Floats.Interval.ERealCoercions

/-!
# Activation enclosures for executable binary intervals

ReLU, absolute value, and square root have enclosure and interval-validity theorems with
operation-specific hypotheses. The executable definitions live in `Interval.Activations`; shared
endpoint order and negation facts come from `IntervalSemantics.Arithmetic`.

ReLU and absolute value work for every descriptor and accept ordered non-NaN endpoints, including
infinities from an earlier operation. Their finite-input theorems specialize the same proofs.
Square root uses directed IEEE rounding and requires finite valid input bounds with a nonnegative
lower endpoint. These differences appear in the theorem statements rather than in a second
interval carrier or an implicit execution mode.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

noncomputable section

/-! ## ReLU -/

/-- The ReLU interval encloses each member's ReLU, including with infinite endpoints. -/
theorem relu_sound_extended
    {fmt : FloatFormat} (A : Interval fmt) (hA : ValidExtended A)
    {x : ℝ} (hx : ERealMem A (x : EReal)) :
    ERealMem (relu A) ((max x 0 : ℝ) : EReal) := by
  simpa only [ERealMem, relu,
    toEReal_maximum_eq_max _ _ hA.lo_isNaN_eq_false (isNaN_zero fmt false),
    toEReal_maximum_eq_max _ _ hA.hi_isNaN_eq_false (isNaN_zero fmt false),
    toEReal_zero, FloatLib.Floats.Interval.coe_max, EReal.coe_zero] using
    And.intro (max_le_max hx.1 (le_refl (0 : EReal))) (max_le_max hx.2 le_rfl)

/-- ReLU preserves ordered, non-NaN endpoints in every format. -/
theorem relu_validExtended
    {fmt : FloatFormat} (A : Interval fmt) (hA : ValidExtended A) :
    ValidExtended (relu A) := by
  apply validExtended_of_toEReal_le (I := relu A)
    (isNaN_maximum_eq_false_of_isNaN_eq_false _ _ hA.lo_isNaN_eq_false (isNaN_zero fmt false))
    (isNaN_maximum_eq_false_of_isNaN_eq_false _ _ hA.hi_isNaN_eq_false (isNaN_zero fmt false))
  simpa only [relu,
    toEReal_maximum_eq_max _ _ hA.lo_isNaN_eq_false (isNaN_zero fmt false),
    toEReal_maximum_eq_max _ _ hA.hi_isNaN_eq_false (isNaN_zero fmt false)] using
    max_le_max hA.toEReal_ordered (le_refl (toEReal (zero fmt false)))

/-- Executable interval ReLU encloses the ReLU of every represented real value. -/
theorem relu_sound
    {fmt : FloatFormat} (A : Interval fmt) (hA : Valid A)
    {x : ℝ} (hx : RealMem A x) :
    ERealMem (relu A) ((max x 0 : ℝ) : EReal) :=
  relu_sound_extended A hA.validExtended ((eRealMem_coe_iff_of_valid hA x).2 hx)

/-! ## Absolute value -/

/-- Absolute value encloses every represented real magnitude, including with infinite endpoints. -/
theorem abs_sound_extended
    {fmt : FloatFormat} (A : Interval fmt) (hA : ValidExtended A)
    {x : ℝ} (hx : ERealMem A (x : EReal)) :
    ERealMem (abs A) ((|x| : ℝ) : EReal) := by
  by_cases hneg : leB A.hi (zero fmt true) = true
  · have hhiNonpos : toEReal A.hi ≤ 0 := by
      simpa using (leB_eq_true_iff_toEReal_le_of_isNaN_eq_false
        A.hi (zero fmt true) hA.hi_isNaN_eq_false (isNaN_zero fmt true)).1 hneg
    have hxNonpos : x ≤ 0 := EReal.coe_nonpos.1 (hx.2.trans hhiNonpos)
    rw [abs, if_pos hneg]
    simpa [abs_of_nonpos hxNonpos] using neg_sound_extended A hA hx
  · by_cases hpos : leB (zero fmt false) A.lo = true
    · have hloNonneg : 0 ≤ toEReal A.lo := by
        simpa using (leB_eq_true_iff_toEReal_le_of_isNaN_eq_false
          (zero fmt false) A.lo (isNaN_zero fmt false) hA.lo_isNaN_eq_false).1 hpos
      have hxNonneg : 0 ≤ x := EReal.coe_nonneg.1 (hloNonneg.trans hx.1)
      rw [abs, if_neg hneg, if_pos hpos]
      simpa [abs_of_nonneg hxNonneg] using hx
    · have hloNaN := hA.lo_isNaN_eq_false
      have hhiNaN := hA.hi_isNaN_eq_false
      have hnegLoNaN : isNaN (Model.neg A.lo) = false := by
        simpa using hloNaN
      have hxAbs :
          ((|x| : ℝ) : EReal) ≤ max (-toEReal A.lo) (toEReal A.hi) := by
        by_cases hxNonpos : x ≤ 0
        · rw [abs_of_nonpos hxNonpos, EReal.coe_neg]
          exact (EReal.neg_le_neg_iff.2 hx.1).trans (le_max_left _ _)
        · rw [abs_of_nonneg (le_of_not_ge hxNonpos)]
          exact hx.2.trans (le_max_right _ _)
      rw [abs, if_neg hneg, if_neg hpos]
      constructor
      · change toEReal (zero fmt false) ≤ ((|x| : ℝ) : EReal)
        rw [toEReal_zero]
        exact EReal.coe_le_coe_iff.2 (abs_nonneg x)
      · change
          ((|x| : ℝ) : EReal) ≤
            toEReal (maximum (Model.neg A.lo) A.hi)
        rw [toEReal_maximum_eq_max (Model.neg A.lo) A.hi hnegLoNaN hhiNaN,
          toEReal_neg_of_isNaN_eq_false A.lo hloNaN]
        exact hxAbs

/-- Absolute value preserves ordered, non-NaN endpoints in every format. -/
theorem abs_validExtended
    {fmt : FloatFormat} (A : Interval fmt) (hA : ValidExtended A) :
    ValidExtended (abs A) := by
  unfold abs
  split
  · exact neg_validExtended A hA
  · split
    · exact hA
    next hneg _ =>
      have hhiNonneg : 0 ≤ toEReal A.hi := by
        have h := (leB_eq_true_iff_toEReal_le_of_isNaN_eq_false
          A.hi (zero fmt true) hA.hi_isNaN_eq_false (isNaN_zero fmt true)).not.mp hneg
        simpa only [toEReal_zero] using le_of_not_ge h
      have hnegLoNaN : isNaN (Model.neg A.lo) = false := by
        simpa using hA.lo_isNaN_eq_false
      refine validExtended_of_toEReal_le ?_ ?_ ?_
      · exact isNaN_zero fmt false
      · exact isNaN_maximum_eq_false_of_isNaN_eq_false _ _ hnegLoNaN hA.hi_isNaN_eq_false
      · simpa only [toEReal_zero,
          toEReal_maximum_eq_max _ _ hnegLoNaN hA.hi_isNaN_eq_false] using
          hhiNonneg.trans (le_max_right (toEReal (Model.neg A.lo)) (toEReal A.hi))

/-- Executable interval absolute value encloses the absolute value of every represented real. -/
theorem abs_sound
    {fmt : FloatFormat} (A : Interval fmt) (hA : Valid A)
    {x : ℝ} (hx : RealMem A x) :
    ERealMem (abs A) ((|x| : ℝ) : EReal) :=
  abs_sound_extended A hA.validExtended ((eRealMem_coe_iff_of_valid hA x).2 hx)

/-! ## Directed square root -/

/--
Executable interval square root encloses the square root of every represented real value.

The lower endpoint's decoded value must be nonnegative. Validity and endpoint order then imply
that the upper endpoint is nonnegative as well.
-/
theorem sqrt_sound
    {fmt : FloatFormat} (A : Interval fmt) (hfmt : fmt.isIEEE = true) (hA : Valid A)
    (hnonnegative : 0 ≤ toReal A.lo)
    {x : ℝ} (hx : RealMem A x) :
    ERealMem (sqrt A) ((Real.sqrt x : ℝ) : EReal) := by
  have hhiNonnegative : 0 ≤ toReal A.hi :=
    hnonnegative.trans hA.toReal_ordered
  constructor
  · change
      toEReal (sqrtDown A.lo) ≤ ((Real.sqrt x : ℝ) : EReal)
    calc
      toEReal (sqrtDown A.lo) ≤
          ((Real.sqrt (toReal A.lo) : ℝ) : EReal) :=
        toEReal_sqrtDown_le_of_nonnegative A.lo hfmt hA.lo_isFinite hnonnegative
      _ ≤ ((Real.sqrt x : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 (Real.sqrt_le_sqrt hx.1)
  · change
      ((Real.sqrt x : ℝ) : EReal) ≤ toEReal (sqrtUp A.hi)
    calc
      ((Real.sqrt x : ℝ) : EReal) ≤
          ((Real.sqrt (toReal A.hi) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 (Real.sqrt_le_sqrt hx.2)
      _ ≤ toEReal (sqrtUp A.hi) :=
        le_toEReal_sqrtUp_of_nonnegative A.hi hfmt hA.hi_isFinite hhiNonnegative

/--
Square root maps a finite valid nonnegative interval to an ordered interval with non-NaN
endpoints. The extended-valid conclusion avoids requiring a separate output-finiteness premise.
-/
theorem sqrt_validExtended
    {fmt : FloatFormat} (A : Interval fmt) (hfmt : fmt.isIEEE = true) (hA : Valid A)
    (hnonnegative : 0 ≤ toReal A.lo) :
    ValidExtended (sqrt A) := by
  have hhiNonnegative : 0 ≤ toReal A.hi :=
    hnonnegative.trans hA.toReal_ordered
  have hloNaN : isNaN (sqrtDown A.lo) = false :=
    isNaN_sqrtDown_eq_false_of_isFinite_of_nonnegative
      A.lo hfmt hA.lo_isFinite hnonnegative
  have hhiNaN : isNaN (sqrtUp A.hi) = false :=
    isNaN_sqrtUp_eq_false_of_isFinite_of_nonnegative
      A.hi hfmt hA.hi_isFinite hhiNonnegative
  refine ⟨hloNaN, hhiNaN, ?_⟩
  apply (le_iff_toEReal_le_of_isNaN_eq_false _ _ hloNaN hhiNaN).2
  have hmem : RealMem A (toReal A.lo) :=
    ⟨le_rfl, hA.toReal_ordered⟩
  have henclosure := sqrt_sound A hfmt hA hnonnegative hmem
  exact henclosure.1.trans henclosure.2

end

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
