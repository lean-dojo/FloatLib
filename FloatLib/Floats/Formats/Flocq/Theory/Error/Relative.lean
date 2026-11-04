/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Error.Bounds
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Formats
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Magnitude

/-!
# Relative Error in the FLX Format

In the unbounded-exponent `flxExp prec` format one relative-error bound holds everywhere, and the
argument is short. For a nonzero input the ULP is `β^(magnitude x - prec)`, and the magnitude lower
bound gives `β^(magnitude x - 1) ≤ |x|`, so their ratio is at most `β^(1 - prec)`. For the 24
bits of binary32 that's `2^-23`.

Nearest rounding halves it, which gives the unit-roundoff bound `u = β^(1 - prec) / 2`. The same
bound holds for FLT inputs in the normal range. We don't prove the sharper classical bound
`u / (1 + u)` for nearest rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
When the canonical exponent of a nonzero `x` is `magnitude x - prec`, one ULP has relative size at
most `β^(1-prec)`, because `β^(magnitude x - 1) ≤ |x|`.
-/
private theorem ulp_div_abs_le_of_cexp_eq {fexp : ℤ → ℤ} [ValidExp fexp] (prec : ℤ)
    {x : ℝ} (hx : x ≠ 0) (hcexp : cexp β fexp x = magnitude β x - prec) :
    ulp β fexp x / abs x ≤ bpow β (1 - prec) := by
  rw [div_le_iff₀ (abs_pos.mpr hx), ulp.of_ne_zero β fexp x hx]
  calc
    bpow β (cexp β fexp x) =
        bpow β (1 - prec) * bpow β (magnitude β x - 1) := by
      rw [← bpow.add_exp, hcexp]
      congr 1
      ring
    _ ≤ bpow β (1 - prec) * abs x :=
      mul_le_mul_of_nonneg_left (bpow_magnitude_sub_one_le β x hx) (bpow.nonneg β _)

/-- Under nearest rounding, a bound `B` on the relative size of one ULP halves to an error bound. -/
private theorem relativeError_round_le_half {fexp : ℤ → ℤ} [ValidExp fexp]
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] {x : ℝ} (hx : x ≠ 0) {B : ℝ}
    (hB : ulp β fexp x / abs x ≤ B) :
    ErrorBounds.relativeError x (round (β := β) (fexp := fexp) rnd x) hx ≤ B / 2 :=
  calc
    ErrorBounds.relativeError x (round (β := β) (fexp := fexp) rnd x) hx ≤
        ulp β fexp x / (2 * abs x) :=
      ErrorBounds.relative_error_round_ulp rnd x hx
    _ = (ulp β fexp x / abs x) / 2 := by
      field_simp [abs_ne_zero.mpr hx]
    _ ≤ B / 2 := div_le_div_of_nonneg_right hB (by norm_num)

/-- The relative size of one FLX ULP is at most `β^(1-prec)`. -/
theorem ulp_div_abs_le_FLX (prec : ℤ) (hprec : 0 < prec) (x : ℝ) (hx : x ≠ 0) :
    @ulp β (flxExp prec) (flxValidExp prec hprec) x / abs x ≤
      bpow β (1 - prec) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  exact ulp_div_abs_le_of_cexp_eq prec hx (by simp [cexp, flxExp])

/-- Nearest FLX rounding has relative error at most the unit roundoff `u = β^(1 - prec) / 2`. -/
theorem relative_error_round_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0) :
    ErrorBounds.relativeError x
        (@round β (flxExp prec) (flxValidExp prec hprec) rnd x) hx ≤
      bpow β (1 - prec) / 2 := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  exact relativeError_round_le_half rnd hx (ulp_div_abs_le_FLX prec hprec x hx)

/--
Nearest FLX rounding admits the usual multiplicative model
`round x = x * (1 + δ)` with `|δ| ≤ u`, where `u = β^(1 - prec) / 2` is the unit roundoff. Zero
rounds to itself, with `δ = 0`.
-/
theorem round_relative_error_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    ∃ δ : ℝ,
      abs δ ≤ bpow β (1 - prec) / 2 ∧
      @round β (flxExp prec) (flxValidExp prec hprec) rnd x = x * (1 + δ) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by simpa using div_nonneg (bpow.nonneg β (1 - prec)) zero_le_two,
      by simp [round_zero]⟩
  · exact ErrorBounds.exists_delta_of_relativeError_le hx
      (relative_error_round_FLX prec hprec rnd x hx)

/-- In the normal range, one FLT ULP has relative size at most `β^(1-prec)`. -/
theorem ulp_div_abs_le_FLT_normal (emin prec : ℤ) (hprec : 0 < prec)
    (x : ℝ) (hnormal : bpow β (emin + prec - 1) ≤ abs x) :
    @ulp β (fltExp emin prec) (fltValidExp emin prec hprec) x / abs x ≤
      bpow β (1 - prec) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  have hx : x ≠ 0 := abs_pos.mp ((bpow.pos β _).trans_le hnormal)
  have hpowLt : bpow β (emin + prec - 1) < bpow β (magnitude β x) :=
    hnormal.trans_lt (abs_lt_bpow_magnitude β x)
  have hnormalExp : emin ≤ magnitude β x - prec := by
    have := (bpow_lt_bpow_iff β _ _).mp hpowLt
    linarith
  exact ulp_div_abs_le_of_cexp_eq prec hx (by simp [cexp, fltExp, max_eq_left hnormalExp])

/-- Nearest FLT rounding has relative error at most `u = β^(1 - prec) / 2` in the normal range. -/
theorem relative_error_round_FLT_normal (emin prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0)
    (hnormal : bpow β (emin + prec - 1) ≤ abs x) :
    ErrorBounds.relativeError x
        (@round β (fltExp emin prec) (fltValidExp emin prec hprec) rnd x) hx ≤
      bpow β (1 - prec) / 2 := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  exact relativeError_round_le_half rnd hx
    (ulp_div_abs_le_FLT_normal emin prec hprec x hnormal)

end FloatLib.Floats.Formats.Flocq
