/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Sterbenz
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Addition
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Multiplication

/-!
# Sterbenz's Lemma for Gradual Underflow

Sterbenz exact subtraction carries over from the unbounded-exponent family `FLX` to the
gradual-underflow family `FLT`, which is the format behind the rounded-real binary32 model.

The proof splits on the size of the exact difference. Every `FLT` operand lies on the
minimum-exponent grid, and that grid is closed under subtraction, so a small enough difference is
representable. A larger one follows from the `FLX` Sterbenz theorem and the inclusion of the
normal range of `FLX` in `FLT`.

## Reference

- P. H. Sterbenz, *Floating-Point Computation*, Prentice-Hall, 1974.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
An `FLX` value in the normal range is representable in the corresponding `FLT` format.

This is the normal-range converse of `genericRepresentable_flt_to_flx`.
-/
theorem genericRepresentable_flx_to_flt_of_normal (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hxFLX : @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) x)
    (hnorm : bpow β (emin + prec - 1) ≤ abs x) :
    @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) x := by
  let : ValidExp (flxExp prec) := validExp_flx prec hprec
  let : ValidExp (fltExp emin prec) := validExp_flt emin prec hprec
  obtain ⟨_, f, hxf, hmant⟩ := (genericRepresentable_flx_iff (β := β) prec hprec x).mp hxFLX
  refine (genericRepresentable_flt_iff (β := β) emin prec hprec x).mpr ⟨hprec, f, hxf, hmant, ?_⟩
  have habsx : abs x < bpow β (f.exponent + prec) := by
    rw [hxf]
    exact f.abs_toReal_lt_bpow prec hmant
  have hlt : bpow β (emin + prec - 1) < bpow β (f.exponent + prec) :=
    lt_of_le_of_lt hnorm habsx
  have hexp : emin + prec - 1 < f.exponent + prec :=
    (bpow_lt_bpow_iff β _ _).mp hlt
  omega

/--
Directed Sterbenz lemma for `FLT`: if `y ≤ x ≤ 2y` and both operands are representable, then
their exact difference is representable. The bounds force `0 ≤ y`.
-/
theorem genericRepresentable_flt_sub_of_le_two_mul (emin prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hyx : y ≤ x) (hx2y : x ≤ 2 * y)
    (hxFmt : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) x)
    (hyFmt : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) y) :
    @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) (x - y) := by
  let : ValidExp (fltExp emin prec) := validExp_flt emin prec hprec
  let : ValidExp (flxExp prec) := validExp_flx prec hprec
  by_cases hsmall : abs (x - y) ≤ bpow β (emin + prec - 1)
  · have hxFix := genericRepresentable_flt_to_fix (β := β) emin prec hprec hxFmt
    have hyFix := genericRepresentable_flt_to_fix (β := β) emin prec hprec hyFmt
    have hdFix := genericRepresentable_fix_sub (β := β) emin hxFix hyFix
    apply genericRepresentable_fix_to_flt_of_abs_le (β := β) emin prec hprec hdFix
    exact hsmall.trans ((bpow_le_bpow_iff β _ _).2 (by omega))
  · rw [not_le] at hsmall
    have hxFLX := genericRepresentable_flt_to_flx (β := β) emin prec hprec hxFmt
    have hyFLX := genericRepresentable_flt_to_flx (β := β) emin prec hprec hyFmt
    have hdFLX := genericRepresentable_flx_sub_of_le_two_mul (β := β) prec hprec
      hyx hx2y hxFLX hyFLX
    exact genericRepresentable_flx_to_flt_of_normal (β := β) emin prec hprec
      hdFLX (le_of_lt hsmall)

/--
Sterbenz's lemma for `FLT`: if two representable values are within a factor of two of each other,
then their exact difference is representable, including across the subnormal boundary. The two
bounds force both values to be nonnegative.
-/
theorem genericRepresentable_flt_sterbenz (emin prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hx2y : x ≤ 2 * y) (hy2x : y ≤ 2 * x)
    (hxFmt : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) x)
    (hyFmt : @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) y) :
    @GenericRepresentable β (fltExp emin prec) (validExp_flt emin prec hprec) (x - y) := by
  let : ValidExp (fltExp emin prec) := validExp_flt emin prec hprec
  rcases le_total y x with hyx | hxy
  · exact genericRepresentable_flt_sub_of_le_two_mul emin prec hprec hyx hx2y hxFmt hyFmt
  · have hdiff :=
      genericRepresentable_flt_sub_of_le_two_mul emin prec hprec hxy hy2x hyFmt hxFmt
    have hneg := genericRepresentable_neg (β := β) (fexp := fltExp emin prec) (y - x) hdiff
    simpa only [neg_sub] using hneg

end FloatLib.Floats.Formats.Flocq
