/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems

/-!
# Exact Subtraction

The fixed-point family is an additive lattice, so subtraction is exact without a ratio
restriction (`generic_format_FIX_sub` in `Format.Theorems`). This is the fixed-grid foundation for
the floating-point Sterbenz theorem, where the ratio hypotheses are needed to align the operands'
effective exponents.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
Sterbenz's lemma for the unbounded-exponent format: if two representable values satisfy
`y ≤ x ≤ 2 * y`, then their subtraction is exactly representable at the same precision. The bounds
force `0 ≤ y`, and `y = 0` forces `x = 0`.

The proof does not appeal to rounding.  Both operands lie on the grid of the smaller canonical
exponent, the one of `y`.  The ratio bound gives `x - y ≤ y`, so the difference has magnitude at
most that of `y`, its canonical exponent is at most that of `y`, and the integer difference on the
common grid is representable.
-/
theorem generic_format_FLX_sub_of_le_two_mul (prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hyx : y ≤ x) (hx2y : x ≤ 2 * y)
    (hxFmt : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (hyFmt : @genericFormat β (flxExp prec) (flxValidExp prec hprec) y) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec) (x - y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  by_cases hxy : x = y
  · rw [hxy, sub_self]
    exact generic_format_zero
  have hdpos : 0 < x - y := sub_pos.mpr (lt_of_le_of_ne hyx (Ne.symm hxy))
  have hy : 0 < y := by linarith
  let ex := magnitude β x
  let ey := magnitude β y
  let e0 := ey - prec
  have heyex : ey ≤ ex := magnitude_mono_pos β hy hyx
  -- Both operands lie on the grid of the smaller canonical exponent `e0`.
  obtain ⟨mx, hxAligned⟩ := exists_int_mul_bpow_of_le_cexp hxFmt (e := e0)
    (by simp [cexp, flxExp, ey, e0]; linarith)
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
  apply generic_format_of_toReal_of_cexp_le
    ({ mantissa := mx - my, exponent := e0 } : FloatRep β)
  · rw [hxAligned, hyAligned, toReal]
    push_cast
    ring
  · simp [cexp, flxExp, e0]
    linarith

/--
Symmetric Sterbenz lemma for FLX.  If two representable values are within a factor of two of each
other, their exact difference is representable, whichever operand is larger. The two bounds force
both values to be nonnegative.
-/
theorem generic_format_FLX_sterbenz (prec : ℤ) (hprec : 0 < prec)
    {x y : ℝ} (hx2y : x ≤ 2 * y) (hy2x : y ≤ 2 * x)
    (hxFmt : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (hyFmt : @genericFormat β (flxExp prec) (flxValidExp prec hprec) y) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec) (x - y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  rcases le_total y x with hyx | hxy
  · exact generic_format_FLX_sub_of_le_two_mul
      prec hprec hyx hx2y hxFmt hyFmt
  · have hdiff := generic_format_FLX_sub_of_le_two_mul
      prec hprec hxy hy2x hyFmt hxFmt
    have hneg := generic_format_neg (β := β) (fexp := flxExp prec) (y - x) hdiff
    simpa only [neg_sub] using hneg

end FloatLib.Floats.Formats.Flocq
