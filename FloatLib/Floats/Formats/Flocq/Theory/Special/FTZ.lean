/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Format.Generic
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems
public import FloatLib.Floats.Formats.Flocq.Theory.Analysis.Ulp

/-!
# Abrupt Underflow

`ftzExp emin prec` is the Flocq abrupt-underflow exponent selector.  Below the smallest normal
magnitude it selects the normal threshold `emin + prec - 1`; above that threshold it agrees with
the unbounded precision-`prec` selector.  A matching rounding mode can therefore flush values below
the normal range directly to zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

variable {β : Numerics.Radix}

/-- Exponent selection with precision `prec` and smallest normal value `β^(emin + prec - 1)`. -/
def ftzExp (emin prec : ℤ) (e : ℤ) : ℤ :=
  if e - prec < emin then emin + prec - 1 else e - prec

/-- The radix exponent of the smallest normal value in the abrupt-underflow format. -/
def ftzThreshold (emin prec : ℤ) : ℤ := emin + prec - 1

/-- Below the threshold, `ftzExp` selects the threshold itself. -/
theorem ftzExp_eq_threshold {emin prec e : ℤ} (h : e ≤ ftzThreshold emin prec) :
    ftzExp emin prec e = ftzThreshold emin prec := by
  rw [ftzExp, if_pos]
  · rfl
  · simp [ftzThreshold] at h ⊢
    linarith

/-- Above the threshold, `ftzExp` agrees with `e - prec`. -/
theorem ftzExp_eq_sub {emin prec e : ℤ} (h : ftzThreshold emin prec < e) :
    ftzExp emin prec e = e - prec := by
  rw [ftzExp, if_neg]
  simp [ftzThreshold] at h ⊢
  linarith

/-- Positive-precision abrupt-underflow exponent selection satisfies Flocq validity. -/
abbrev ftzValidExp (emin prec : ℤ) (hprec : 0 < prec) :
    ValidExp (ftzExp emin prec) where
  flocq_valid := by
    intro k
    constructor
    · intro hk
      have hlarge : ftzThreshold emin prec < k := by
        by_contra hnot
        have hsmall : k ≤ ftzThreshold emin prec := le_of_not_gt hnot
        rw [ftzExp_eq_threshold hsmall] at hk
        exact (not_lt_of_ge hsmall) hk
      rw [ftzExp_eq_sub hlarge] at hk
      by_cases hnext : k + 1 ≤ ftzThreshold emin prec
      · rw [ftzExp_eq_threshold hnext]
        linarith
      · rw [ftzExp_eq_sub (lt_of_not_ge hnext)]
        linarith
    · intro hk
      have hsmall : k ≤ ftzThreshold emin prec := by
        by_contra hnot
        have hlarge := lt_of_not_ge hnot
        rw [ftzExp_eq_sub hlarge] at hk
        linarith
      have hkEq := ftzExp_eq_threshold hsmall
      rw [hkEq] at hk ⊢
      constructor
      · have hnext : ftzThreshold emin prec < ftzThreshold emin prec + 1 := by linarith
        rw [ftzExp_eq_sub hnext]
        simp [ftzThreshold]
        linarith
      · intro l hl
        rw [ftzExp_eq_threshold hl]

/-- `ftzExp emin prec` satisfies the exponent axioms exactly for positive precision. -/
theorem validExp_FTZ_iff (emin prec : ℤ) : ValidExp (ftzExp emin prec) ↔ 0 < prec := by
  constructor
  · intro hvalid
    by_contra hprec
    have hnonpos : prec ≤ 0 := le_of_not_gt hprec
    have hlarge : ftzThreshold emin prec < emin + 1 := by
      simp [ftzThreshold]
      linarith
    have hexp : ftzExp emin prec (emin + 1) = emin + 1 - prec :=
      ftzExp_eq_sub hlarge
    have hk : emin + 1 ≤ ftzExp emin prec (emin + 1) := by
      rw [hexp]
      linarith
    have hnext := ((hvalid.flocq_valid (emin + 1)).2 hk).1
    have hnextLarge :
        ftzThreshold emin prec < ftzExp emin prec (emin + 1) + 1 := by
      rw [hexp]
      simp [ftzThreshold]
      linarith
    rw [ftzExp_eq_sub hnextLarge, hexp] at hnext
    linarith
  · exact ftzValidExp emin prec

namespace FormatPrecision

/-- The abrupt-underflow exponent selector associated with a checked precision. -/
def ftzExp (precision : FormatPrecision) (emin : ℤ) : ℤ → ℤ :=
  Flocq.ftzExp emin precision.toInt

/-- A checked precision automatically discharges the abrupt-underflow validity obligation. -/
instance ftzExpValid (precision : FormatPrecision) (emin : ℤ) :
    ValidExp (precision.ftzExp emin) :=
  ftzValidExp emin precision.toInt precision.toInt_pos

end FormatPrecision

/-- The threshold is a negligible exponent for the abrupt-underflow format. -/
theorem ftzThreshold_negligible (emin prec : ℤ) :
    IsNegligibleExp (ftzExp emin prec) (ftzThreshold emin prec) := by
  unfold IsNegligibleExp
  rw [ftzExp_eq_threshold le_rfl]

/-- The ULP at zero in the abrupt-underflow format is the smallest normal magnitude. -/
theorem ulp_zero_FTZ (emin prec : ℤ) (hprec : 0 < prec) :
    @ulp β (ftzExp emin prec) (ftzValidExp emin prec hprec) 0 =
      bpow β (ftzThreshold emin prec) := by
  let : ValidExp (ftzExp emin prec) := ftzValidExp emin prec hprec
  rw [ulp.zero]
  cases hopt : negligibleExp (ftzExp emin prec) with
  | none =>
      have hnone := (negligibleExp_eq_none_iff (ftzExp emin prec)).mp hopt
      exact (hnone ⟨ftzThreshold emin prec, ftzThreshold_negligible emin prec⟩).elim
  | some n =>
      have hn := negligibleExp_spec hopt
      have heq := negligibleExp_value_unique hn
        (ftzThreshold_negligible emin prec)
      change bpow β (ftzExp emin prec n) = bpow β (ftzThreshold emin prec)
      rw [heq, ftzExp_eq_threshold le_rfl]

/-- Flush an inexact scaled mantissa to zero when its magnitude is below one. -/
noncomputable def fTZRound (rnd : ℝ → ℤ) (x : ℝ) : ℤ :=
  if 1 ≤ abs x then rnd x else 0

/-- Flushing around `(-1,1)` preserves monotonicity and exact integer values. -/
instance fTZRoundValid (rnd : ℝ → ℤ) [ValidRnd rnd] :
    ValidRnd (fTZRound rnd) where
  id := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [fTZRound]
    · have habs : (1 : ℝ) ≤ abs (n : ℝ) := by
        exact_mod_cast (Int.one_le_abs hn0)
      simp [fTZRound, habs, ValidRnd.id (rnd := rnd)]
  monotone := by
    intro x y hxy
    by_cases hx : 1 ≤ abs x
    · by_cases hy : 1 ≤ abs y
      · simp [fTZRound, hx, hy, ValidRnd.monotone (rnd := rnd) x y hxy]
      · have hyAbs : abs y < 1 := lt_of_not_ge hy
        have hx0 : x ≤ 0 := by
          by_contra hnot
          have hxpos : 0 < x := lt_of_not_ge hnot
          have hypos : 0 < y := hxpos.trans_le hxy
          rw [abs_of_pos hxpos] at hx
          rw [abs_of_pos hypos] at hyAbs
          linarith
        have hrx : rnd x ≤ 0 := by
          have hmono := ValidRnd.monotone (rnd := rnd) x 0 hx0
          have hr0 : rnd 0 = 0 := by
            simpa using ValidRnd.id (rnd := rnd) (0 : ℤ)
          rwa [hr0] at hmono
        simp [fTZRound, hx, hy, hrx]
    · by_cases hy : 1 ≤ abs y
      · have hxAbs : abs x < 1 := lt_of_not_ge hx
        have hy0 : 0 ≤ y := by
          by_contra hnot
          have hyneg : y < 0 := lt_of_not_ge hnot
          have hxneg : x < 0 := lt_of_le_of_lt hxy hyneg
          rw [abs_of_neg hxneg] at hxAbs
          rw [abs_of_neg hyneg] at hy
          linarith
        have hry : 0 ≤ rnd y := by
          have hmono := ValidRnd.monotone (rnd := rnd) 0 y hy0
          have hr0 : rnd 0 = 0 := by
            simpa using ValidRnd.id (rnd := rnd) (0 : ℤ)
          rwa [hr0] at hmono
        simp [fTZRound, hx, hy, hry]
      · simp [fTZRound, hx, hy]

/-- Values below the smallest-normal threshold flush exactly to zero. -/
theorem round_FTZ_small (emin prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) (x : ℝ)
    (hsmall : abs x < bpow β (ftzThreshold emin prec)) :
    @round β (ftzExp emin prec) (ftzValidExp emin prec hprec)
      (fTZRound rnd) x = 0 := by
  let : ValidExp (ftzExp emin prec) := ftzValidExp emin prec hprec
  by_cases hx : x = 0
  · subst x
    simp [round, scaledMantissa, fTZRound, toReal]
  have hmag : magnitude β x ≤ ftzThreshold emin prec :=
    magnitude_le_of_abs_lt_bpow β x (ftzThreshold emin prec) hx hsmall
  have hcexp : cexp β (ftzExp emin prec) x = ftzThreshold emin prec := by
    simp [cexp, ftzExp_eq_threshold hmag]
  have hb : 0 < bpow β (ftzThreshold emin prec) := bpow.pos β _
  have hscaled : abs (scaledMantissa β (ftzExp emin prec) x) < 1 := by
    rw [scaledMantissa_eq_div, hcexp, abs_div, abs_of_pos hb, div_lt_one hb]
    exact hsmall
  unfold round toReal
  rw [show fTZRound rnd (scaledMantissa β (ftzExp emin prec) x) = 0 by
    simp [fTZRound, not_le.mpr hscaled]]
  simp

/-- At normal magnitudes, abrupt-underflow rounding agrees with FLX rounding. -/
theorem round_FTZ_eq_FLX_of_normal (emin prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) (x : ℝ)
    (hnormal : bpow β (ftzThreshold emin prec) ≤ abs x) :
    @round β (ftzExp emin prec) (ftzValidExp emin prec hprec)
        (fTZRound rnd) x =
      @round β (flxExp prec) (flxValidExp prec hprec) rnd x := by
  let : ValidExp (ftzExp emin prec) := ftzValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  have hx : x ≠ 0 := by
    intro hx0
    rw [hx0, abs_zero] at hnormal
    exact (not_le_of_gt (bpow.pos β _)) hnormal
  have hupper := abs_lt_bpow_magnitude β x hx
  have hmag : ftzThreshold emin prec < magnitude β x :=
    (bpow_lt_bpow_iff β _ _).mp (hnormal.trans_lt hupper)
  have hcexp : cexp β (ftzExp emin prec) x =
      cexp β (flxExp prec) x := by
    simp [cexp, ftzExp_eq_sub hmag, flxExp]
  have hscaled : scaledMantissa β (ftzExp emin prec) x =
      scaledMantissa β (flxExp prec) x := by
    simp [scaledMantissa, hcexp]
  have hb : 0 < bpow β (magnitude β x - prec) := bpow.pos β _
  have hlower := bpow_magnitude_sub_one_le β x hx
  have hp : 0 ≤ prec - 1 := by linarith
  have hone : (1 : ℝ) ≤ bpow β (prec - 1) := by
    change (1 : ℝ) ≤ β.toReal ^ (prec - 1)
    exact one_le_zpow₀ (Numerics.Radix.gt_one β).le hp
  have hsone : 1 ≤ abs (scaledMantissa β (ftzExp emin prec) x) := by
    rw [scaledMantissa_eq_div, hcexp]
    simp only [cexp, flxExp]
    rw [abs_div, abs_of_pos hb]
    calc
      1 ≤ bpow β (prec - 1) := hone
      _ = bpow β ((magnitude β x - 1) -
          (magnitude β x - prec)) := by
        congr 1
        linarith
      _ = bpow β (magnitude β x - 1) /
          bpow β (magnitude β x - prec) :=
        bpow.sub_exp β _ _
      _ ≤ abs x / bpow β (magnitude β x - prec) :=
        div_le_div_of_nonneg_right hlower hb.le
  have hsoneFLX : 1 ≤ abs (scaledMantissa β (flxExp prec) x) := by
    simpa [hscaled] using hsone
  unfold round toReal
  rw [hcexp, hscaled]
  simp [fTZRound, hsoneFLX]

/-- Exact abrupt-underflow values are zero or normal-range FLX values. -/
def FTZFormat (emin prec : ℤ) (x : ℝ) : Prop :=
  FLXFormat (β := β) prec x ∧
    (x = 0 ∨ bpow β (ftzThreshold emin prec) ≤ abs x)

/-- Nonpositive precision is rejected by the explicit abrupt-underflow format predicate. -/
theorem not_ftzFormat_of_nonpos (emin prec : ℤ) (hprec : prec ≤ 0) (x : ℝ) :
    ¬FTZFormat (β := β) emin prec x := by
  intro h
  exact not_flxFormat_of_nonpos prec hprec x h.1

/-- The generic format generated by `ftzExp` satisfies the explicit abrupt-underflow predicate. -/
theorem ftzFormat_of_generic (emin prec : ℤ) (hprec : 0 < prec) {x : ℝ}
    (hx : @genericFormat β (ftzExp emin prec) (ftzValidExp emin prec hprec) x) :
    FTZFormat (β := β) emin prec x := by
  let : ValidExp (ftzExp emin prec) := ftzValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  constructor
  · rw [← generic_format_FLX_iff prec hprec]
    apply generic_inclusion (fexp₁ := ftzExp emin prec) (fexp₂ := flxExp prec)
    · intro e
      by_cases he : e ≤ ftzThreshold emin prec
      · rw [ftzExp_eq_threshold he]
        change e - prec ≤ ftzThreshold emin prec
        linarith
      · rw [ftzExp_eq_sub (lt_of_not_ge he)]
        rfl
    · exact hx
  · by_cases hx0 : x = 0
    · exact Or.inl hx0
    · right
      by_cases hmag : magnitude β x ≤ ftzThreshold emin prec
      · obtain ⟨n, hn⟩ := scaled_mantissa_int_of_generic
          (β := β) (fexp := ftzExp emin prec) x hx
        have hn0 : n ≠ 0 := by
          intro hnzero
          have hrepr := scaled_mantissa_mul_bpow
            (β := β) (fexp := ftzExp emin prec) x
          rw [hn, hnzero, Int.cast_zero, zero_mul] at hrepr
          exact hx0 hrepr.symm
        have habsn : (1 : ℝ) ≤ abs (n : ℝ) := by
          exact_mod_cast (Int.one_le_abs hn0)
        have hcexp : cexp β (ftzExp emin prec) x = ftzThreshold emin prec := by
          simp [cexp, ftzExp_eq_threshold hmag]
        have hrepr := scaled_mantissa_mul_bpow
          (β := β) (fexp := ftzExp emin prec) x
        rw [hn, hcexp] at hrepr
        have hb := bpow.nonneg β (ftzThreshold emin prec)
        calc
          bpow β (ftzThreshold emin prec) =
              1 * bpow β (ftzThreshold emin prec) := by ring
          _ ≤ abs (n : ℝ) * bpow β (ftzThreshold emin prec) :=
            mul_le_mul_of_nonneg_right habsn hb
          _ = abs ((n : ℝ) * bpow β (ftzThreshold emin prec)) := by
            rw [abs_mul, abs_of_nonneg hb]
          _ = abs x := by rw [hrepr]
      · have hmagLt : ftzThreshold emin prec < magnitude β x := lt_of_not_ge hmag
        have hlower := bpow_magnitude_sub_one_le β x hx0
        exact ((bpow_le_bpow_iff β _ _).2 (by linarith)).trans hlower

/-- Every explicit abrupt-underflow value belongs to the generic `ftzExp` format. -/
theorem generic_of_ftzFormat (emin prec : ℤ) (hprec : 0 < prec) {x : ℝ}
    (hx : FTZFormat (β := β) emin prec x) :
    @genericFormat β (ftzExp emin prec) (ftzValidExp emin prec hprec) x := by
  let : ValidExp (ftzExp emin prec) := ftzValidExp emin prec hprec
  let : ValidExp (flxExp prec) := flxValidExp prec hprec
  rcases hx with ⟨hxFLX, hxRange⟩
  rcases hxRange with rfl | hnormal
  · exact generic_format_zero
  · have hx0 : x ≠ 0 := by
      intro hxzero
      rw [hxzero, abs_zero] at hnormal
      exact (not_le_of_gt (bpow.pos β _)) hnormal
    have hupper := abs_lt_bpow_magnitude β x hx0
    have hmag : ftzThreshold emin prec < magnitude β x :=
      (bpow_lt_bpow_iff β _ _).mp (hnormal.trans_lt hupper)
    apply generic_inclusion_mag (fexp₁ := flxExp prec) (fexp₂ := ftzExp emin prec)
    · intro _
      rw [ftzExp_eq_sub hmag]
      rfl
    · exact (generic_format_FLX_iff prec hprec x).2 hxFLX

/-- `FTZFormat` is exactly the generic format generated by `ftzExp`. -/
theorem generic_format_FTZ_iff (emin prec : ℤ) (hprec : 0 < prec) (x : ℝ) :
    @genericFormat β (ftzExp emin prec) (ftzValidExp emin prec hprec) x ↔
      FTZFormat (β := β) emin prec x :=
  ⟨ftzFormat_of_generic emin prec hprec, generic_of_ftzFormat emin prec hprec⟩

end FloatLib.Floats.Formats.Flocq
