/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticGrid
public import FloatLib.Numerics.Quantization.Stochastic.Rounder
public import FloatLib.Numerics.Quantization.Stochastic.Word

/-!
# Exact rational observations of executable stochastic rounding

`stochasticRound` calls the existing binary policy runtime. `stochasticValue`
decodes its actual result to a rational. `StochasticSafe` checks the two possible
encodings, the entropy denominator and the unclipped finite range using rational
arithmetic. Under that check, the observation is unbiased with the cell-width
Hoeffding proxy. Zero is included without a nonzero-input premise.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

open FloatLib.Floats FloatLib.Numerics MeasureTheory ProbabilityTheory
open FloatLib.Numerics.Quantization.Stochastic
open scoped NNReal

/-- The rational grid spacing used to check the runtime's finite range. -/
def stochasticUnit (fmt : FloatFormat) (x : ℚ) : ℚ :=
  (2 : ℚ) ^ (if RationalBinary.floorLog2 x.num.natAbs x.den < fmt.minNormalExponent then
    fmt.minSubnormalExponent else RationalBinary.floorLog2 x.num.natAbs x.den - fmt.fracWidth)

/-- Actual encoded stochastic rounding of an exact rational, with positive zero. -/
def stochasticRound (fmt : FloatFormat) (entropy : ℕ) (x : ℚ) : Model fmt :=
  roundRatGeneralOfDenNeZero fmt { rounding := .stochastic }
    entropy (decide (x < 0)) x.num.natAbs x.den x.den_nz

/-- Exact rational observation of the encoded result; numerical rules prove it finite. -/
def stochasticValue (fmt : FloatFormat) (entropy : ℕ) (x : ℚ) : ℚ :=
  (toRat? (stochasticRound fmt entropy x)).getD 0

/-- A decidable sufficient condition for an unbiased, unclipped local rounding.
The upper quotient and both possible output encodings are checked, not a sample. -/
def StochasticSafe (fmt : FloatFormat) (M : ℕ) (x : ℚ) : Prop :=
  x = 0 ∨
    RationalBinary.floorLog2 x.num.natAbs x.den ≤ fmt.maxNormalExponent ∧
    (alignedRatio fmt x.num.natAbs x.den).2 ∣ M ∧
    isFinite (stochasticRound fmt 0 x) = true ∧
    isFinite (stochasticRound fmt ((alignedRatio fmt x.num.natAbs x.den).2 - 1) x) = true ∧
    (roundQuot .stochastic (decide (x < 0)) 0 (alignedRatio fmt x.num.natAbs x.den).1
      (alignedRatio fmt x.num.natAbs x.den).2 : ℚ) * stochasticUnit fmt x ≤
        (toRat? (posMaxFinite fmt)).getD 0

instance (fmt : FloatFormat) (M : ℕ) (x : ℚ) : Decidable (StochasticSafe fmt M x) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Exact rational and real spacing agree, including below the normal range. -/
theorem cast_stochasticUnit (fmt : FloatFormat) (x : ℚ) :
    (stochasticUnit fmt x : ℝ) = stochasticSpacing fmt x.num.natAbs x.den := by
  unfold stochasticUnit stochasticSpacing
  split_ifs <;> simp [bpow,
    FloatLib.Floats.Formats.Flocq.bpow, binaryRadix, Radix.toReal]

/-- Rational decoding with the exceptional zero convention agrees with `toReal`. -/
theorem cast_toRat_getD {fmt : FloatFormat} (v : Model fmt) :
    ((toRat? v).getD 0 : ℝ) = toReal v := by
  cases hd : toDyadic? v with
  | none => simp [toRat?, toReal_eq, hd]
  | some d => simp [toRat?, toReal_eq, hd, Numerics.Dyadic.cast_toRat]

/-- The sign and magnitude supplied to the runtime denote the input rational. -/
theorem signedRat_magnitude (x : ℚ) :
    (if decide (x < 0) then (-1 : ℝ) else 1) *
      ((x.num.natAbs : ℝ) / x.den) = (x : ℝ) := by
  have hm : (x.num.natAbs : ℝ) / x.den = |(x : ℝ)| := by
    simp [Rat.cast_def, abs_div]
  rw [hm]
  by_cases hx : x < 0
  · have hr : (x : ℝ) < 0 := by exact_mod_cast hx
    simp [hx, abs_of_neg hr]
  · have hr : (0 : ℝ) ≤ x := by exact_mod_cast le_of_not_gt hx
    simp [hx, abs_of_nonneg hr]

/-- Exact zero stays zero for every entropy value. -/
@[simp] theorem stochasticRound_zero (fmt : FloatFormat) (e : ℕ) :
    stochasticRound fmt e 0 = zero fmt false := by
  simp [stochasticRound, roundRatGeneralOfDenNeZero, applyUnderflow]

/-- The rational observation also preserves zero exactly. -/
@[simp] theorem stochasticValue_zero (fmt : FloatFormat) (e : ℕ) :
    stochasticValue fmt e 0 = 0 := by
  simp [stochasticValue, toRat?]

/-- A safe input gives finite output for every entropy value. -/
theorem StochasticSafe.finite {fmt : FloatFormat} {M : ℕ} {x : ℚ}
    (h : StochasticSafe fmt M x) (e : ℕ) :
    isFinite (stochasticRound fmt e x) = true := by
  rcases h with rfl | ⟨_, _, hu, hl, _⟩
  · rw [stochasticRound_zero]
    exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt false)
  · exact roundRat_stochastic_finite fmt _ rfl _ _ _ x.den_nz hu hl e

/-- The single rational upper-bound check covers every entropy value. -/
theorem StochasticSafe.bounded {fmt : FloatFormat} {M : ℕ} {x : ℚ}
    (h : StochasticSafe fmt M x) (hx : x ≠ 0) (e : ℕ) :
    (roundQuot .stochastic (decide (x < 0)) e (alignedRatio fmt x.num.natAbs x.den).1
      (alignedRatio fmt x.num.natAbs x.den).2 : ℝ) *
        stochasticSpacing fmt x.num.natAbs x.den ≤ toReal (posMaxFinite fmt) := by
  obtain ⟨_, _, _, _, hb⟩ := h.resolve_left hx
  have hb' := (Rat.cast_le (K := ℝ)).mpr hb
  simp only [Rat.cast_mul, Rat.cast_natCast, cast_stochasticUnit, cast_toRat_getD] at hb'
  apply le_trans ?_ hb'
  apply mul_le_mul_of_nonneg_right
    (Nat.cast_le.mpr (roundQuot_stochastic_upper _ _ _ _))
  rw [← cast_stochasticUnit]
  exact_mod_cast le_of_lt (zpow_pos (by norm_num : (0 : ℚ) < 2) _)

/-- The actual rational-valued runtime is unbiased under its local safety check. -/
theorem mean_stochasticValue (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x : ℚ)
    (h : StochasticSafe fmt M x) :
    (∫ e, (stochasticValue fmt e x : ℝ) ∂entropyLaw M) = x := by
  by_cases hx : x = 0
  · subst x
    simp
  · have hn : x.num.natAbs ≠ 0 := by simpa using hx
    have hs := h.resolve_left hx
    simpa only [stochasticValue, cast_toRat_getD, stochasticRound, signedRat_magnitude] using
      mean_roundRat_stochastic fmt (decide (x < 0)) M x.num.natAbs x.den hM hn x.den_nz
        hs.1 hs.2.1 (fun e ↦ h.finite e) (h.bounded hx)

/-- The local error of the actual rational-valued runtime has a squared half-gap proxy. -/
theorem subgaussian_stochasticValue (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x : ℚ)
    (h : StochasticSafe fmt M x) :
    HasSubgaussianMGF (fun e ↦ (stochasticValue fmt e x : ℝ) - x)
      ((‖(stochasticUnit fmt x : ℝ)‖₊ / 2) ^ 2) (entropyLaw M) := by
  let := entropyLaw_probability M hM
  by_cases hx : x = 0
  · subst x
    simpa only [stochasticValue_zero, Rat.cast_zero, sub_self] using
      (subgaussian_mono (HasSubgaussianMGF.fun_zero (μ := entropyLaw M))
        (show (0 : ℝ≥0) ≤ (‖(stochasticUnit fmt 0 : ℝ)‖₊ / 2) ^ 2 from bot_le))
  · have hn : x.num.natAbs ≠ 0 := by simpa using hx
    have hs := h.resolve_left hx
    simpa only [stochasticValue, cast_toRat_getD, stochasticRound, signedRat_magnitude,
      cast_stochasticUnit] using
      subgaussian_roundRat_stochastic fmt (decide (x < 0)) M x.num.natAbs x.den hM hn
        x.den_nz hs.1 hs.2.1 (fun e ↦ h.finite e) (h.bounded hx)

/-- The local second moment has the same squared half-gap budget. -/
theorem second_moment_stochasticValue (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) (x : ℚ)
    (h : StochasticSafe fmt M x) :
    (∫ e, ((stochasticValue fmt e x : ℝ) - x) ^ 2 ∂entropyLaw M) ≤
      (stochasticUnit fmt x : ℝ) ^ 2 / 4 := by
  by_cases hx : x = 0
  · subst x
    simp only [stochasticValue_zero, Rat.cast_zero, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero]
    positivity
  · have hn : x.num.natAbs ≠ 0 := by simpa using hx
    have hs := h.resolve_left hx
    simpa only [stochasticValue, cast_toRat_getD, stochasticRound, signedRat_magnitude,
      cast_stochasticUnit] using
      second_moment_roundRat_stochastic fmt (decide (x < 0)) M x.num.natAbs x.den hM hn
        x.den_nz hs.1 hs.2.1 (fun e ↦ h.finite e) (h.bounded hx)

/-- The rational observation has the same two possible outputs as the complete runtime. -/
theorem stochasticValue_choice (fmt : FloatFormat) (x : ℚ) (e : ℕ) :
    stochasticValue fmt e x =
      if e % (alignedRatio fmt x.num.natAbs x.den).2 <
          (alignedRatio fmt x.num.natAbs x.den).1 %
            (alignedRatio fmt x.num.natAbs x.den).2
      then stochasticValue fmt 0 x
      else stochasticValue fmt ((alignedRatio fmt x.num.natAbs x.den).2 - 1) x := by
  unfold stochasticValue stochasticRound
  have h := roundRat_stochastic_choice fmt { rounding := .stochastic } rfl e
    (decide (x < 0)) x.num.natAbs x.den x.den_nz
  dsimp only at h
  rw [h]
  split_ifs <;> rfl

/-- A finite endpoint check recognizes an exact operation without enumerating entropy. -/
def StochasticExact (fmt : FloatFormat) (x : ℚ) : Prop :=
  stochasticValue fmt 0 x = x ∧
    stochasticValue fmt ((alignedRatio fmt x.num.natAbs x.den).2 - 1) x = x

instance (fmt : FloatFormat) (x : ℚ) : Decidable (StochasticExact fmt x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- If both possible endpoints equal the input, every word gives zero error. -/
theorem stochasticValue_of_exact (fmt : FloatFormat) (x : ℚ)
    (h : StochasticExact fmt x) (e : ℕ) : stochasticValue fmt e x = x := by
  rw [stochasticValue_choice]
  simp only [h.1, h.2, ite_self]

/-- Exact operations have zero error width; all others use the runtime's cell spacing. -/
def stochasticWidth (fmt : FloatFormat) (x : ℚ) : ℚ :=
  if StochasticExact fmt x then 0 else stochasticUnit fmt x

/-- One executable arithmetic rule for every binary descriptor and entropy word width. -/
def binaryRounder (fmt : FloatFormat) (M : ℕ) : Rounder (Fin M) where
  round e x := stochasticValue fmt e.val x
  Admissible := StochasticSafe fmt M
  width := stochasticWidth fmt

/-- Admissibility for the binary rule is the decidable check `StochasticSafe`, so a finite list
of inputs can be checked by evaluation. -/
instance (fmt : FloatFormat) (M : ℕ) (x : ℚ) : Decidable ((binaryRounder fmt M).Admissible x) :=
  inferInstanceAs (Decidable (StochasticSafe fmt M x))

/-- The binary rule's local contract follows from actual runtime and exact decoding. -/
theorem binaryRounder_law (fmt : FloatFormat) (M : ℕ) (hM : 0 < M) :
    (binaryRounder fmt M).Law (wordLaw M hM) where
  mean x h := by
    change (∫ e, (stochasticValue fmt e.val x : ℝ) ∂wordLaw M hM) = x
    rw [integral_wordLaw M hM (fun e ↦ (stochasticValue fmt e x : ℝ))]
    exact mean_stochasticValue fmt M hM x h
  second x h := by
    change (∫ e, ((stochasticValue fmt e.val x : ℝ) - x) ^ 2 ∂wordLaw M hM) ≤ _
    rw [integral_wordLaw M hM (fun e ↦ ((stochasticValue fmt e x : ℝ) - x) ^ 2),
      Rounder.coe_proxy]
    by_cases he : StochasticExact fmt x
    · simp only [stochasticValue_of_exact fmt x he, sub_self, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, integral_zero]
      positivity
    · simpa only [binaryRounder, stochasticWidth, ite_eq_right he] using
        second_moment_stochasticValue fmt M hM x h
  mgf x h := by
    by_cases he : StochasticExact fmt x
    · simpa only [binaryRounder, Rounder.proxy, stochasticWidth, ite_eq_left he,
        stochasticValue_of_exact fmt x he, sub_self, Rat.cast_zero, nnNorm_zero,
        zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
        (HasSubgaussianMGF.fun_zero (μ := wordLaw M hM))
    · have hg := subgaussian_stochasticValue fmt M hM x h
      have hw := hasLaw_word_val M hM
      rw [← hw.map_eq] at hg
      simpa only [binaryRounder, Rounder.proxy, stochasticWidth, ite_eq_right he,
        Function.comp_def] using
        hg.of_map hw.aemeasurable

end FloatLib.Floats.Formats.BinaryInterchange.Model.Policy
