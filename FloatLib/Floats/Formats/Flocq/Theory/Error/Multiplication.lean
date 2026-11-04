/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Error.Exactness
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Directed

/-!
# Exactness of Multiplication Errors

Multiply two representable values in the unbounded-exponent FLX format, round with any valid
monotone integer rounding, and the residual of the product is itself representable.

We work in FLX so that the precision argument stays clear of overflow and underflow. A
bounded-format error theorem can then combine this residual fact with its own range hypotheses,
with no need to redo the algebra of rounded multiplication for each exponent policy.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/--
Scaling a generic-format value by `β^e` keeps it representable when its canonical exponent grows
by at most `e`.
-/
private theorem generic_format_mul_bpow_of_cexp_le {fexp : ℤ → ℤ} [ValidExp fexp] {x : ℝ}
    (hx : genericFormat β fexp x) (e : ℤ)
    (hcexp : x ≠ 0 → cexp β fexp (x * bpow β e) ≤ cexp β fexp x + e) :
    genericFormat β fexp (x * bpow β e) := by
  by_cases hx0 : x = 0
  · subst x
    simp
  obtain ⟨n, hxn⟩ := exists_int_mul_bpow_cexp_of_generic hx
  apply generic_format_of_toReal_of_cexp_le
    ({ mantissa := n, exponent := cexp β fexp x + e } : FloatRep β) _ ?_ (hcexp hx0)
  change x * bpow β e = (n : ℝ) * bpow β (cexp β fexp x + e)
  rw [bpow.add_exp, ← mul_assoc, ← hxn]

/-- Multiplication by a radix power preserves FLX representability. -/
theorem generic_format_FLX_mul_bpow (prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (e : ℤ) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec)
      (x * bpow β e) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  refine generic_format_mul_bpow_of_cexp_le hx e fun hx0 => ?_
  simp only [cexp, flxExp, magnitude_mul_bpow β x e hx0]
  linarith

/--
A nonzero rounded-product residual has a representation at the sum of the operand canonical
exponents. This is the exponent-carrying form needed by FLT underflow proofs.
-/
theorem mul_round_error_FLX_exists_repr (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (hy : @genericFormat β (flxExp prec) (flxValidExp prec hprec) y)
    (herr0 : @round β (flxExp prec) (flxValidExp prec hprec) rnd (x * y) - x * y ≠ 0) :
    ∃ f : FloatRep β,
      @round β (flxExp prec) (flxValidExp prec hprec) rnd (x * y) - x * y =
        toReal f ∧
      @cexp β (flxExp prec) (flxValidExp prec hprec)
          (@round β (flxExp prec) (flxValidExp prec hprec) rnd (x * y) - x * y) ≤
        f.exponent ∧
      f.exponent = @cexp β (flxExp prec) (flxValidExp prec hprec) x +
        @cexp β (flxExp prec) (flxValidExp prec hprec) y := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let product := x * y
  let rounded := round (β := β) (fexp := flxExp prec) rnd product
  let err := rounded - product
  have herr0' : err ≠ 0 := herr0
  have hp0 : product ≠ 0 := by
    intro hp0
    have hr0 : rounded = 0 := by
      unfold rounded
      rw [hp0]
      exact round_preserves_generic rnd 0 generic_format_zero
    exact herr0' (by simp [err, hr0, hp0])
  have hx0 : x ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  have hy0 : y ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  let ex := cexp β (flxExp prec) x
  let ey := cexp β (flxExp prec) y
  obtain ⟨mx, hxrepr⟩ := exists_int_mul_bpow_cexp_of_generic hx
  obtain ⟨my, hyrepr⟩ := exists_int_mul_bpow_cexp_of_generic hy
  let exactProduct : FloatRep β := { mantissa := mx * my, exponent := ex + ey }
  have hproduct : product = toReal exactProduct := by
    unfold product exactProduct toReal
    rw [hxrepr, hyrepr, bpow.add_exp]
    push_cast
    ring
  obtain ⟨mr, hrounded⟩ :=
    round_toReal_exists_same_exponent
      (β := β) (fexp := flxExp prec) rnd exactProduct
  let errorFloat : FloatRep β :=
    { mantissa := mr - exactProduct.mantissa, exponent := ex + ey }
  have herr : err = toReal errorFloat := by
    unfold err rounded errorFloat toReal
    rw [hproduct, hrounded]
    simp only [exactProduct]
    simp only [toReal]
    push_cast
    ring
  have hinexact : rounded ≠ product := sub_ne_zero.mp herr0'
  have herrUlp : abs err < ulp β (flxExp prec) product := by
    exact round_abs_error_lt_ulp_of_inexact rnd hinexact
  have herrBpow : abs err < bpow β (cexp β (flxExp prec) product) := by
    simpa [ulp, hp0] using herrUlp
  have hmagErr : magnitude β err ≤ cexp β (flxExp prec) product :=
    magnitude_le_of_abs_lt_bpow β err _ herr0' herrBpow
  have hmagProduct : magnitude β product ≤
      magnitude β x + magnitude β y := by
    simpa [product] using magnitude_mul_le_add β hx0 hy0
  have hcexp : cexp β (flxExp prec) err ≤ ex + ey := by
    change magnitude β err - prec ≤
      (magnitude β x - prec) + (magnitude β y - prec)
    simp [cexp, flxExp] at hmagErr
    linarith
  exact ⟨errorFloat, herr, hcexp, rfl⟩

/-- The residual of a valid rounded FLX product is FLX-representable. -/
theorem mul_round_error_FLX (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : @genericFormat β (flxExp prec) (flxValidExp prec hprec) x)
    (hy : @genericFormat β (flxExp prec) (flxValidExp prec hprec) y) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec)
      (@round β (flxExp prec) (flxValidExp prec hprec) rnd (x * y) - x * y) := by
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let err := round (β := β) (fexp := flxExp prec) rnd (x * y) - x * y
  by_cases herr0 : err = 0
  · change genericFormat β (flxExp prec) err
    rw [herr0]
    exact generic_format_zero
  obtain ⟨f, herr, hcexp, _⟩ :=
    mul_round_error_FLX_exists_repr (β := β) prec hprec rnd hx hy herr0
  apply generic_format_of_toReal_of_cexp_le f err herr
  exact hcexp

/-- Every FLT value is representable in the corresponding unbounded FLX format. -/
theorem generic_format_FLT_to_FLX (emin prec : ℤ) (hprec : 0 < prec) {x : ℝ}
    (hx : @genericFormat β (fltExp emin prec) (fltValidExp emin prec hprec) x) :
    @genericFormat β (flxExp prec) (flxValidExp prec hprec) x := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  apply generic_inclusion (fexp₁ := fltExp emin prec) (fexp₂ := flxExp prec)
  · intro e
    simp [fltExp, flxExp]
  · exact hx

/--
The residual of an FLT rounded product is FLT-representable when the exact product is zero or
has magnitude at least `β^(emin + 2*prec - 1)`. This sufficient bound keeps the residual
representation's exponent at or above `emin`.
-/
theorem mul_round_error_FLT (emin prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ}
    (hx : @genericFormat β (fltExp emin prec) (fltValidExp emin prec hprec) x)
    (hy : @genericFormat β (fltExp emin prec) (fltValidExp emin prec hprec) y)
    (hproduct : x * y ≠ 0 →
      bpow β (emin + 2 * prec - 1) ≤ abs (x * y)) :
    @genericFormat β (fltExp emin prec) (fltValidExp emin prec hprec)
      (@round β (fltExp emin prec) (fltValidExp emin prec hprec) rnd (x * y) - x * y) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  let product := x * y
  let roundFLT := round (β := β) (fexp := fltExp emin prec) rnd product
  let roundFLX := round (β := β) (fexp := flxExp prec) rnd product
  let err := roundFLT - product
  by_cases hp0 : product = 0
  · have hr0 : roundFLT = 0 := by
      unfold roundFLT
      rw [hp0]
      exact round_preserves_generic rnd 0 generic_format_zero
    change genericFormat β (fltExp emin prec) err
    simp [err, hr0, hp0]
  have hx0 : x ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  have hy0 : y ≠ 0 := by
    intro h
    exact hp0 (by simp [product, h])
  have hmagProduct : emin + 2 * prec ≤ magnitude β product := by
    have hlower := hproduct hp0
    have hupper := abs_lt_bpow_magnitude β product
    have hpowers : bpow β (emin + 2 * prec - 1) <
        bpow β (magnitude β product) := hlower.trans_lt hupper
    have hexp := (bpow_lt_bpow_iff β _ _).mp hpowers
    linarith
  have hcexpEq : cexp β (fltExp emin prec) product =
      cexp β (flxExp prec) product := by
    simp [cexp, fltExp, flxExp, max_eq_left (by linarith :
      emin ≤ magnitude β product - prec)]
  have hroundEq : roundFLT = roundFLX := by
    unfold roundFLT roundFLX round scaledMantissa
    rw [hcexpEq]
  have hxFLX := generic_format_FLT_to_FLX (β := β) emin prec hprec hx
  have hyFLX := generic_format_FLT_to_FLX (β := β) emin prec hprec hy
  by_cases herr0 : err = 0
  · change genericFormat β (fltExp emin prec) err
    rw [herr0]
    exact generic_format_zero
  have herrFLX0 : roundFLX - product ≠ 0 := by simpa [err, hroundEq] using herr0
  obtain ⟨f, herr, hcexpFLX, hfexp⟩ :=
    mul_round_error_FLX_exists_repr
      (β := β) prec hprec rnd hxFLX hyFLX herrFLX0
  have hmagMul := magnitude_mul_le_add β hx0 hy0
  have hemin : emin ≤ f.exponent := by
    rw [hfexp]
    simp [cexp, flxExp]
    have : emin + 2 * prec ≤ magnitude β x + magnitude β y := by
      exact hmagProduct.trans (by simpa [product] using hmagMul)
    linarith
  have hcexpFLT : cexp β (fltExp emin prec) err ≤ f.exponent := by
    have herrEq : err = roundFLX - product := by simp [err, hroundEq]
    have hflx : cexp β (flxExp prec) err ≤ f.exponent := by
      simpa [herrEq] using hcexpFLX
    change max (magnitude β err - prec) emin ≤ f.exponent
    apply max_le
    · simpa [cexp, flxExp] using hflx
    · exact hemin
  apply generic_format_of_toReal_of_cexp_le f err
  · simpa [err, hroundEq] using herr
  · exact hcexpFLT

/--
Multiplying an FLT-representable value by a radix power preserves representability when
`emin + prec - magnitude β x ≤ e`.
-/
theorem generic_format_FLT_mul_bpow (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : @genericFormat β (fltExp emin prec)
      (fltValidExp emin prec hprec) x) (e : ℤ)
    (hshift : emin + prec - magnitude β x ≤ e) :
    @genericFormat β (fltExp emin prec) (fltValidExp emin prec hprec)
      (x * bpow β e) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  refine generic_format_mul_bpow_of_cexp_le hx e fun hx0 => ?_
  simp only [cexp, fltExp, magnitude_mul_bpow β x e hx0]
  apply max_le
  · have hleft := add_le_add_right
      (le_max_left (magnitude β x - prec) emin) e
    linarith
  · have hbase : magnitude β x - prec ≤
        max (magnitude β x - prec) emin := le_max_left _ _
    linarith

/-- Nonnegative radix shifts preserve every FLT-representable value. -/
theorem generic_format_FLT_mul_bpow_of_nonneg (emin prec : ℤ) (hprec : 0 < prec)
    {x : ℝ} (hx : @genericFormat β (fltExp emin prec)
      (fltValidExp emin prec hprec) x) (e : ℤ) (he : 0 ≤ e) :
    @genericFormat β (fltExp emin prec) (fltValidExp emin prec hprec)
      (x * bpow β e) := by
  let : ValidExp (fltExp emin prec) := fltValidExp emin prec hprec
  refine generic_format_mul_bpow_of_cexp_le hx e fun hx0 => ?_
  simp only [cexp, fltExp, magnitude_mul_bpow β x e hx0]
  apply max_le
  · have hleft := add_le_add_right
      (le_max_left (magnitude β x - prec) emin) e
    linarith
  · exact (le_max_right _ _).trans (le_add_of_nonneg_right he)

end FloatLib.Floats.Formats.Flocq
