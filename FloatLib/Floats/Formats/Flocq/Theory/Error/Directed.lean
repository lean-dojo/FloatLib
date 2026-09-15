/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Error.Relative
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Generic

/-!
# Error Bounds for General Rounding Modes

A valid rounding mode selects one of the two adjacent representable values.  Consequently its
absolute error is at most one ULP.  Nearest rounding sharpens this to half an ULP; this file records
the one-ULP result needed for directed and toward-zero modes.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/-- Every valid generic rounding mode has absolute error at most one ULP. -/
theorem round_abs_error_le_ulp (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    abs (round (β := β) (fexp := fexp) rnd x - x) ≤ ulp β fexp x := by
  by_cases hx : genericFormat β fexp x
  · rw [round_preserves_generic rnd x hx, sub_self, abs_zero]
    exact ulp.nonneg (β := β) (fexp := fexp) x
  · let d := round (β := β) (fexp := fexp) floorRound x
    let u := round (β := β) (fexp := fexp) ceilRound x
    let r := round (β := β) (fexp := fexp) rnd x
    have hd : d ≤ x := round_floor_le x
    have hu : x ≤ u := le_round_ceil x
    have hdr : d ≤ r := round_floor_le_round rnd x
    have hru : r ≤ u := round_le_ceil rnd x
    have hgap : u = d + ulp β fexp x :=
      round_ceil_eq_floor_add_ulp hx
    rcases le_total r x with hrx | hxr
    · rw [abs_of_nonpos (sub_nonpos.mpr hrx)]
      simp only [neg_sub]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hxr)]
      linarith

/-- A non-exact valid rounding has error strictly smaller than one ULP. -/
theorem round_abs_error_lt_ulp_of_inexact (rnd : ℝ → ℤ) [ValidRnd rnd]
    {x : ℝ} (hinexact : round (β := β) (fexp := fexp) rnd x ≠ x) :
    abs (round (β := β) (fexp := fexp) rnd x - x) < ulp β fexp x := by
  have hx : ¬genericFormat β fexp x := by
    intro hx
    exact hinexact (round_preserves_generic rnd x hx)
  let d := round (β := β) (fexp := fexp) floorRound x
  let u := round (β := β) (fexp := fexp) ceilRound x
  let r := round (β := β) (fexp := fexp) rnd x
  have hdle : d ≤ x := round_floor_le x
  have hxleu : x ≤ u := le_round_ceil x
  have hdlt : d < x := lt_of_le_of_ne hdle (by
    intro h
    apply hx
    rw [← h]
    exact generic_format_round floorRound x)
  have hxlt : x < u := lt_of_le_of_ne hxleu (by
    intro h
    apply hx
    rw [h]
    exact generic_format_round ceilRound x)
  have hgap : u = d + ulp β fexp x := round_ceil_eq_floor_add_ulp hx
  rcases round_eq_floor_or_ceil (β := β) (fexp := fexp) rnd x with hr | hr
  · change abs (r - x) < ulp β fexp x
    have hr' : r = d := hr
    rw [hr']
    rw [abs_of_nonpos (sub_nonpos.mpr hdle), neg_sub]
    linarith
  · change abs (r - x) < ulp β fexp x
    have hr' : r = u := hr
    rw [hr']
    rw [abs_of_nonneg (sub_nonneg.mpr hxleu)]
    linarith

/-- Every valid FLX rounding mode has relative error at most `β^(1-prec)`. -/
theorem relative_error_round_FLX_of_valid (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) (hx : x ≠ 0) :
    ErrorBounds.relativeError x
        (@round β (flxExp prec) (flxValidExp prec hprec) rnd x) hx ≤
      bpow β (1 - prec) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  unfold ErrorBounds.relativeError
  calc
    abs (round (β := β) (fexp := flxExp prec) rnd x - x) / abs x ≤
        ulp β (flxExp prec) x / abs x :=
      div_le_div_of_nonneg_right (round_abs_error_le_ulp rnd x) (abs_nonneg x)
    _ ≤ bpow β (1 - prec) := ulp_div_abs_le_FLX prec hprec x hx

/-- General FLX rounding admits a multiplicative error model with a one-ULP relative bound. -/
theorem round_relative_error_FLX_of_valid (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) (hx : x ≠ 0) :
    ∃ δ : ℝ,
      abs δ ≤ bpow β (1 - prec) ∧
      @round β (flxExp prec) (flxValidExp prec hprec) rnd x = x * (1 + δ) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let rounded := round (β := β) (fexp := flxExp prec) rnd x
  refine ⟨(rounded - x) / x, ?_, ?_⟩
  · rw [abs_div]
    exact relative_error_round_FLX_of_valid prec hprec rnd x hx
  · dsimp [rounded]
    field_simp [hx]
    ring

end FloatLib.Floats.Formats.Flocq
