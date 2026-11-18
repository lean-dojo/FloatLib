/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems

/-!
# Exact Subtraction

Sterbenz's lemma says that if `y ≤ x ≤ 2y`, then `x - y` is representable, so the subtraction
doesn't round. On a fixed-point grid you don't even need the ratio condition, because the grid is
an additive lattice (`genericRepresentable_fix_sub` in `Format.Theorems`). That fixed-grid fact
is the
foundation here. For floating point, the ratio hypotheses are what align the operands' effective
exponents.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
Sterbenz's lemma for the unbounded-exponent format: if two representable values satisfy
`y ≤ x ≤ 2 * y`, then their difference is exactly representable at the same precision. The bounds
force `0 ≤ y`, and `y = 0` forces `x = 0`.

The proof never mentions rounding. Both operands lie on the grid of the smaller canonical
exponent, which is `y`'s, and `x - y ≤ y` keeps the canonical exponent of the difference at most
that of `y`, so the integer difference on that common grid is representable.
-/
theorem genericRepresentable_flx_sub_of_le_two_mul (prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hyx : y ≤ x) (hx2y : x ≤ 2 * y)
    (hxFmt : @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) x)
    (hyFmt : @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) y) :
    @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) (x - y) := by
  let : ValidExp (flxExp prec) := validExp_flx prec hprec
  by_cases hxy : x = y
  · rw [hxy, sub_self]
    exact genericRepresentable_zero
  have hdpos : 0 < x - y := sub_pos.mpr (lt_of_le_of_ne hyx (Ne.symm hxy))
  have hy : 0 < y := by linarith
  let ex := magnitude β x
  let ey := magnitude β y
  let e0 := ey - prec
  have heyex : ey ≤ ex := magnitude_mono_pos β hy hyx
  -- Both operands lie on the grid of the smaller canonical exponent `e0`.
  obtain ⟨mx, hxAligned⟩ := exists_int_mul_bpow_of_le_cexp hxFmt (e := e0)
    (by simp only [cexp, flxExp, tsub_le_iff_right, sub_add_cancel, e0, ey]; linarith)
  obtain ⟨my, hyAligned⟩ := exists_int_mul_bpow_of_le_cexp hyFmt (e := e0)
    (by simp [cexp, flxExp, ey, e0])
  have hdUpper : x - y < bpow β ey := by
    calc
      x - y ≤ y := by linarith
      _ < bpow β ey := by simpa [ey, abs_of_pos hy] using
        (abs_lt_bpow_magnitude β y)
  have hmagd : magnitude β (x - y) ≤ ey :=
    magnitude_le_of_abs_lt_bpow β (x - y) ey hdpos.ne'
      (by simpa [abs_of_pos hdpos] using hdUpper)
  apply genericRepresentable_of_toReal_of_cexp_le
    ({ mantissa := mx - my, exponent := e0 } : FloatRep β)
  · rw [hxAligned, hyAligned, toReal]
    push_cast
    ring
  · simp only [cexp, flxExp, tsub_le_iff_right, sub_add_cancel, e0]
    linarith

/--
Symmetric Sterbenz lemma for FLX.  If two representable values are within a factor of two of each
other, their exact difference is representable, whichever operand is larger. The two bounds force
both values to be nonnegative.
-/
theorem genericRepresentable_flx_sterbenz (prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hx2y : x ≤ 2 * y) (hy2x : y ≤ 2 * x)
    (hxFmt : @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) x)
    (hyFmt : @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) y) :
    @GenericRepresentable β (flxExp prec) (validExp_flx prec hprec) (x - y) := by
  let : ValidExp (flxExp prec) := validExp_flx prec hprec
  rcases le_total y x with hyx | hxy
  · exact genericRepresentable_flx_sub_of_le_two_mul
      prec hprec hyx hx2y hxFmt hyFmt
  · have hdiff := genericRepresentable_flx_sub_of_le_two_mul
      prec hprec hxy hy2x hyFmt hxFmt
    have hneg := genericRepresentable_neg (β := β) (fexp := flxExp prec) (y - x) hdiff
    simpa only [neg_sub] using hneg

end FloatLib.Floats.Formats.Flocq
