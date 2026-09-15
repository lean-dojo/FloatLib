/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Error.Exactness
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Directed

/-!
# Division and Square-Root Residuals

Division and square-root residuals in FLX are exactly representable under the stated precision
and operand hypotheses.  A division residual is controlled both relative to the dividend and
relative to the product of the rounded quotient with the divisor; the two bounds place it on
their common exponent grid.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/-- Positive FLX rounding cannot move a nonzero result into a lower magnitude bin. -/
private theorem magnitude_le_round_FLX_of_pos (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x : ℝ} (hx : 0 < x) :
    magnitude β x ≤
      magnitude β
        (@round β (flxExp prec) (flxValidExp prec hprec) rnd x) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  have hlarge : flxExp prec (magnitude β x) < magnitude β x := by
    simp [flxExp]
    linarith
  have hb := (round_pos_large_bounds_and_generic
    (β := β) (fexp := flxExp prec) rnd x hx hlarge).1.1
  let q := round (β := β) (fexp := flxExp prec) rnd x
  have hqpos : 0 < q := (bpow.pos β _).trans_le hb
  have hqUpper := abs_lt_bpow_magnitude β q hqpos.ne'
  have hpowers : bpow β (magnitude β x - 1) <
      bpow β (magnitude β q) := by
    exact lt_of_le_of_lt hb (by simpa [abs_of_pos hqpos] using hqUpper)
  have hexp : magnitude β x - 1 < magnitude β q :=
    (bpow_lt_bpow_iff β _ _).mp hpowers
  linarith

/-- A nonzero FLX rounded result has magnitude at least that of its exact input. -/
theorem magnitude_le_round_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x : ℝ}
    (hround : @round β (flxExp prec) (flxValidExp prec hprec) rnd x ≠ 0) :
    magnitude β x ≤
      magnitude β
        (@round β (flxExp prec) (flxValidExp prec hprec) rnd x) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  rcases lt_trichotomy x 0 with hx | hx | hx
  · let nrnd := negRound rnd
    have hpos : 0 < -x := neg_pos.mpr hx
    have hmag := magnitude_le_round_FLX_of_pos
      (β := β) prec hprec nrnd hpos
    have hneg := round_neg (β := β) (fexp := flxExp prec) rnd (-x)
    simp only [neg_neg] at hneg
    simpa [hneg] using hmag
  · subst x
    simp [magnitude]
  · exact magnitude_le_round_FLX_of_pos (β := β) prec hprec rnd hx

/--
Common grid argument for arithmetic residuals in FLX.

If `x`, `a` and `b` are representable and the residual `x - a * b` is smaller than `|x|` and than
the radix power at exponent `cexp a + magnitude b`, then the residual lies on the exponent grid
shared by `x` and by the product representation of `a * b`, so it is itself representable.
-/
theorem generic_format_FLX_sub_mul_of_bounds (prec : ℤ) (hprec : 0 < prec) {x a b : ℝ}
    (hx : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (ha : @genericFormat β (flxExp prec) (flxValidExp prec hprec) a)
    (hb : @genericFormat β (flxExp prec) (flxValidExp prec hprec) b)
    (hlt : abs (x - a * b) < abs x)
    (hbound : abs (x - a * b) <
      bpow β (@cexp β (flxExp prec) (flxValidExp prec hprec) a + magnitude β b)) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec) (x - a * b) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [abs_zero] at hlt
    exact absurd hlt (not_lt.mpr (abs_nonneg _))
  obtain ⟨fx, hfx, cfx⟩ := canonical_exists_of_generic hx
  obtain ⟨fa, hfa, cfa⟩ := canonical_exists_of_generic ha
  obtain ⟨fb, hfb, cfb⟩ := canonical_exists_of_generic hb
  let negProduct : FloatRep β :=
    { mantissa := -(fa.mantissa * fb.mantissa)
      exponent := fa.exponent + fb.exponent }
  have hnegProduct : -(a * b) = toReal negProduct := by
    rw [hfa, hfb]
    unfold negProduct toReal
    rw [bpow.add_exp]
    push_cast
    ring
  have hfxexp : fx.exponent = cexp β (flxExp prec) x := by rw [hfx]; exact cfx
  have hfaexp : fa.exponent = cexp β (flxExp prec) a := by rw [hfa]; exact cfa
  have hfbexp : fb.exponent = cexp β (flxExp prec) b := by rw [hfb]; exact cfb
  rw [sub_eq_add_neg]
  apply generic_format_FLX_add_of_repr_bounds prec hprec fx negProduct x (-(a * b)) hfx hnegProduct
  · rw [← sub_eq_add_neg, hfxexp]
    refine lt_trans hlt ?_
    simpa [cexp, flxExp] using abs_lt_bpow_magnitude β x hx0
  · rw [← sub_eq_add_neg]
    refine hbound.trans_le ((bpow_le_bpow_iff β _ _).2 ?_)
    simp only [negProduct, hfaexp, hfbexp, cexp, flxExp]
    linarith

/-- The residual `x - round(x / y) * y` is exactly FLX-representable. -/
theorem div_round_residual_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (hy : @genericFormat β (flxExp prec) (flxValidExp prec hprec) y) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec)
      (x - @round β (flxExp prec) (flxValidExp prec hprec) rnd (x / y) * y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let z := x / y
  let q := round (β := β) (fexp := flxExp prec) rnd z
  change genericFormat β (flxExp prec) (x - q * y)
  by_cases hy0 : y = 0
  · simpa [hy0] using hx
  by_cases hq0 : q = 0
  · simpa [hq0] using hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hq0 (by simp [q, z])
  have hz0 : z ≠ 0 := div_ne_zero hx0 hy0
  by_cases hinexact : q = z
  · rw [hinexact, div_mul_cancel₀ x hy0, sub_self]
    exact generic_format_zero
  have herrorStrict : abs (q - z) < ulp β (flxExp prec) z :=
    round_abs_error_lt_ulp_of_inexact rnd hinexact
  have hresAbs : abs (x - q * y) = abs y * abs (q - z) := by
    rw [← abs_neg, ← abs_mul]
    congr 1
    simp only [z]
    field_simp
    ring
  have hlt : abs (x - q * y) < abs x := by
    have hrelativeUlp : ulp β (flxExp prec) z ≤ bpow β (1 - prec) * abs z := by
      have h := ulp_div_abs_le_FLX (β := β) prec hprec z hz0
      rw [div_le_iff₀ (abs_pos.mpr hz0)] at h
      linarith
    have heps : bpow β (1 - prec) ≤ 1 := by
      simpa [bpow] using (bpow_le_bpow_iff β (1 - prec) 0).2 (by linarith)
    have hxy : abs y * abs z = abs x := by
      rw [← abs_mul, mul_div_cancel₀ x hy0]
    rw [hresAbs, ← hxy]
    calc
      abs y * abs (q - z) < abs y * (bpow β (1 - prec) * abs z) :=
        mul_lt_mul_of_pos_left (herrorStrict.trans_le hrelativeUlp) (abs_pos.mpr hy0)
      _ ≤ abs y * (1 * abs z) := by gcongr
      _ = abs y * abs z := by rw [one_mul]
  have hbound : abs (x - q * y) <
      bpow β (cexp β (flxExp prec) q + magnitude β y) := by
    have hcexpZQ : cexp β (flxExp prec) z ≤ cexp β (flxExp prec) q := by
      simp only [cexp, flxExp]
      exact sub_le_sub_right (magnitude_le_round_FLX (β := β) prec hprec rnd hq0) prec
    have herrBpowQ : abs (q - z) < bpow β (cexp β (flxExp prec) q) := by
      have herrBpow : abs (q - z) < bpow β (cexp β (flxExp prec) z) := by
        simpa [ulp, hz0] using herrorStrict
      exact herrBpow.trans_le ((bpow_le_bpow_iff β _ _).2 hcexpZQ)
    rw [hresAbs, bpow.add_exp, mul_comm (bpow β _)]
    exact mul_lt_mul (abs_lt_bpow_magnitude β y hy0) herrBpowQ.le
      (abs_pos.mpr (sub_ne_zero.mpr hinexact)) (bpow.nonneg β _)
  exact generic_format_FLX_sub_mul_of_bounds prec hprec hx (generic_format_round rnd z) hy hlt
    hbound

/--
For precision greater than one, the nearest-rounded square-root residual `x - q^2` is
FLX-representable, where `q` is the nearest-even rounding of `√x`.

The hypothesis `1 < prec` makes the unit roundoff `u = β^(1 - prec) / 2` at most `1/4`.  The proof
uses that bound to show `|x - q^2| < x`, which places the residual on the grid of `x`; with
`prec = 1` the relative error of `q` can reach `1/2` and the argument does not apply.
-/
theorem sqrt_round_residual_FLX (prec : ℤ) (hprec : 1 < prec) {x : ℝ}
    (hxFmt : @genericFormat β (flxExp prec) (flxValidExp prec (by linarith)) x) :
    @genericFormat β (flxExp prec) (flxValidExp prec (by linarith))
      (x - (@round β (flxExp prec) (flxValidExp prec (by linarith))
        nearestEven (Real.sqrt x)) ^ 2) := by
  have hp0 : 0 < prec := by linarith
  let : ValidExp (flxExp prec) := flxValidExp prec hp0
  let s := Real.sqrt x
  let q := round (β := β) (fexp := flxExp prec) nearestEven s
  change genericFormat β (flxExp prec) (x - q ^ 2)
  rcases lt_or_ge x 0 with hx | hx
  · have hq0 : q = 0 := by simp [q, s, Real.sqrt_eq_zero_of_nonpos hx.le]
    simpa [hq0] using hxFmt
  rcases hx.eq_or_lt with hx | hx
  · subst hx
    simp [q, s]
  have hspos : 0 < s := Real.sqrt_pos.2 hx
  have hsSq : s ^ 2 = x := Real.sq_sqrt hx.le
  have hlarge : flxExp prec (magnitude β s) < magnitude β s := by
    simp only [flxExp]
    linarith
  have hqBounds := (round_pos_large_bounds_and_generic
    (β := β) (fexp := flxExp prec) nearestEven s hspos hlarge).1
  have hqpos : 0 < q := (bpow.pos β _).trans_le hqBounds.1
  by_cases hqs : q = s
  · rw [hqs, hsSq, sub_self]
    exact generic_format_zero
  have hresAbs : abs (x - q ^ 2) = abs (q - s) * (q + s) := by
    rw [← hsSq, show s ^ 2 - q ^ 2 = -((q - s) * (q + s)) by ring, abs_neg, abs_mul,
      abs_of_pos (add_pos hqpos hspos)]
  have hlt : abs (x - q ^ 2) < abs x := by
    let u := bpow β (1 - prec) / 2
    have hrelative : abs (q - s) ≤ u * s := by
      have h := relative_error_round_FLX (β := β) prec hp0 nearestEven s hspos.ne'
      unfold ErrorBounds.relativeError at h
      rw [div_le_iff₀ (abs_pos.mpr hspos.ne')] at h
      simpa [u, abs_of_pos hspos, mul_comm] using h
    have huQuarter : u ≤ (1 : ℝ) / 4 := by
      have hbHalf : bpow β (-1) ≤ (1 : ℝ) / 2 := by
        have hb : (2 : ℝ) ≤ β.toReal := by
          change (2 : ℝ) ≤ (β.base : ℝ)
          exact_mod_cast β.base_valid
        rw [bpow, zpow_neg_one, one_div]
        exact inv_anti₀ (by norm_num) hb
      have hepsHalf : bpow β (1 - prec) ≤ bpow β (-1) :=
        (bpow_le_bpow_iff β _ _).2 (by linarith)
      simp only [u]
      linarith
    have huNonneg : 0 ≤ u := div_nonneg (bpow.nonneg β _) (by norm_num)
    have hqLe : q - s ≤ u * s := (le_abs_self _).trans hrelative
    rw [hresAbs, abs_of_pos hx, ← hsSq]
    nlinarith [mul_le_mul_of_nonneg_right hrelative (add_pos hqpos hspos).le,
      mul_nonneg huNonneg hspos.le, mul_le_mul_of_nonneg_right huQuarter (sq_nonneg s)]
  have hbound : abs (x - q ^ 2) <
      bpow β (cexp β (flxExp prec) q + magnitude β q) := by
    have hmagSQ : magnitude β s ≤ magnitude β q :=
      magnitude_le_round_FLX (β := β) prec hp0 nearestEven hqpos.ne'
    have herrorBpow : abs (q - s) ≤ bpow β (cexp β (flxExp prec) s) / 2 := by
      simpa [ulp, hspos.ne'] using error_bound_ulp (β := β) (fexp := flxExp prec) nearestEven s
    have hsumStrict : q + s < 2 * bpow β (magnitude β s) := by
      have hsUpper := abs_lt_bpow_magnitude β s hspos.ne'
      rw [abs_of_pos hspos] at hsUpper
      linarith [hqBounds.2]
    have hcexpSQ : cexp β (flxExp prec) s ≤ cexp β (flxExp prec) q := by
      simp only [cexp, flxExp]
      linarith
    calc
      abs (x - q ^ 2) = abs (q - s) * (q + s) := hresAbs
      _ < (bpow β (cexp β (flxExp prec) s) / 2) * (2 * bpow β (magnitude β s)) := by
        have hb : 0 < bpow β (cexp β (flxExp prec) s) / 2 := div_pos (bpow.pos β _) two_pos
        nlinarith [abs_nonneg (q - s), add_pos hqpos hspos]
      _ = bpow β (cexp β (flxExp prec) s + magnitude β s) := by
        rw [bpow.add_exp]
        ring
      _ ≤ bpow β (cexp β (flxExp prec) q + magnitude β q) :=
        (bpow_le_bpow_iff β _ _).2 (by linarith)
  have hqFmt : genericFormat β (flxExp prec) q := generic_format_round nearestEven s
  rw [sq] at hlt hbound ⊢
  exact generic_format_FLX_sub_mul_of_bounds prec hp0 hxFmt hqFmt hqFmt hlt hbound

end FloatLib.Floats.Formats.Flocq
