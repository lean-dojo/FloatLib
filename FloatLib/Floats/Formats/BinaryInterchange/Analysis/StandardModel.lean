/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Positive
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Directed

/-!
# The standard model of floating-point arithmetic with gradual underflow

Rounding a real `x` onto the gradual-underflow grid of `fmt` satisfies

`round x = x * (1 + δ) + η`, with `|δ| ≤ u`, `|η| ≤ η₀`, and `δ * η = 0`.

For nearest rounding, `u = 2^(-p)` with `p = fracWidth + 1`, and `η₀ = 2^(emin - 1)` is half
the subnormal spacing, where `emin = minSubnormalExponent`. For binary32 these are `2^(-24)` and
`2^(-150)`. Any valid rounding function, including the directed ones, satisfies the same model
with `2 * u` and `2 * η₀`. At most one of the two error terms is nonzero: `η = 0` in the normal
range and `δ = 0` below it. The real grid has no overflow, so the grid theorems need no range
hypothesis. The executable corollaries use IEEE descriptors and require the stated domain and
finiteness hypotheses.

Addition and subtraction are sharper. Below the normal range, the exact sum of two grid points is
itself a grid point, so the underflow term vanishes and `fl(x + y) = (x + y) * (1 + δ)`.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002,
  Section 2.1, equations (2.8) and (2.9).
- J. W. Demmel, "Underflow and the Reliability of Numerical Software," SIAM J. Sci. Stat.
  Comput. 5(4), 1984. https://doi.org/10.1137/0905062
- J. R. Hauser, "Handling Floating-Point Exceptions in Numeric Programs," ACM TOPLAS 18(2),
  1996. https://doi.org/10.1145/227699.227701
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

/-- The unit roundoff `2^(-precision)` of nearest rounding to `fmt`. -/
noncomputable abbrev unitRoundoffAt (fmt : FloatFormat) : ℝ :=
  FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (-Int.ofNat (fmt.fracWidth + 1))

/--
Half the subnormal spacing of `fmt`, `2^(minSubnormalExponent - 1)`. This bounds the absolute
error of nearest rounding below the normal range.
-/
noncomputable abbrev underflowErrorAt (fmt : FloatFormat) : ℝ :=
  FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
    (FloatFormat.minSubnormalExponent fmt - 1)

/-- The unit roundoff as an explicit power of two. -/
theorem unitRoundoffAt_eq (fmt : FloatFormat) :
    unitRoundoffAt fmt = (2 : ℝ) ^ (-((fmt.fracWidth : ℤ) + 1)) := by
  simp [unitRoundoffAt, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal]

/-- The underflow allowance as an explicit power of two. -/
theorem underflowErrorAt_eq (fmt : FloatFormat) :
    underflowErrorAt fmt = (2 : ℝ) ^ (FloatFormat.minSubnormalExponent fmt - 1) := by
  simp [underflowErrorAt, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal]

private theorem bpow_binary_sub_one (e : ℤ) :
    FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (e - 1) =
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix e / 2 := by
  simp only [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
  rw [zpow_sub₀ (by norm_num), zpow_one]
  push_cast
  ring

/-- Twice the unit roundoff is the relative spacing `2^(1 - precision)` of the normal grid. -/
theorem two_mul_unitRoundoffAt (fmt : FloatFormat) :
    2 * unitRoundoffAt fmt =
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (1 - Int.ofNat (fmt.fracWidth + 1)) := by
  have h := bpow_binary_sub_one (1 - Int.ofNat (fmt.fracWidth + 1))
  rw [show 1 - Int.ofNat (fmt.fracWidth + 1) - 1 = -Int.ofNat (fmt.fracWidth + 1) by ring] at h
  rw [unitRoundoffAt, h]
  ring

/-- Twice the underflow allowance is the subnormal spacing `2^minSubnormalExponent`. -/
theorem two_mul_underflowErrorAt (fmt : FloatFormat) :
    2 * underflowErrorAt fmt =
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (FloatFormat.minSubnormalExponent fmt) := by
  rw [underflowErrorAt, bpow_binary_sub_one]
  ring

private theorem minNormalExponent_eq (fmt : FloatFormat) :
    FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1 =
      FloatFormat.minNormalExponent fmt := by
  simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
    Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
  ring

/-- Below the normal range, one ULP is the fixed subnormal spacing. -/
theorem ulpAt_eq_of_abs_lt_minNormalAt (fmt : FloatFormat) {x : ℝ}
    (hx : |x| < minNormalAt fmt) :
    ulpAt fmt x =
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (FloatFormat.minSubnormalExponent fmt) := by
  have hprec : (0 : ℤ) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  by_cases h0 : x = 0
  · subst h0
    exact ulp_zero_FLT (β := Numerics.binaryRadix)
      (FloatFormat.minSubnormalExponent fmt) (Int.ofNat (fmt.fracWidth + 1)) hprec
  · rw [ulpAt, ulp.of_ne_zero _ _ x h0]
    congr 1
    have hmag := magnitude_le_of_abs_lt_bpow Numerics.binaryRadix x _ h0 hx
    have hexp := minNormalExponent_eq fmt
    simp only [cexp, fexpOf, fltExp]
    apply max_eq_right
    simp only [Int.ofNat_eq_natCast] at hexp ⊢
    omega

/-- In the normal range, one ULP is at most `2^(1 - precision)` times the magnitude. -/
theorem ulpAt_le_of_minNormalAt_le (fmt : FloatFormat) {x : ℝ}
    (hx : minNormalAt fmt ≤ |x|) :
    ulpAt fmt x ≤
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (1 - Int.ofNat (fmt.fracWidth + 1)) * |x| := by
  have hprec : (0 : ℤ) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix
      (FloatFormat.minNormalExponent fmt)
    simp only [abs_zero] at hx
    linarith
  have hnormal :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1) ≤
        |x| := by
    rw [minNormalExponent_eq]
    exact hx
  have h := ulp_div_abs_le_FLT_normal (β := Numerics.binaryRadix)
    (FloatFormat.minSubnormalExponent fmt) (Int.ofNat (fmt.fracWidth + 1)) hprec x hx0 hnormal
  exact (div_le_iff₀ (abs_pos.mpr hx0)).mp h

/--
An absolute error of at most `c` ULPs splits into a relative term in the normal range and an
absolute term below it.
-/
private theorem exists_standardModel_of_abs_sub_le (fmt : FloatFormat) {x r c : ℝ}
    (hc : 0 ≤ c) (herr : |r - x| ≤ c * ulpAt fmt x) :
    ∃ δ η : ℝ, r = x * (1 + δ) + η ∧
      |δ| ≤ c * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (1 - Int.ofNat (fmt.fracWidth + 1)) ∧
      |η| ≤ c * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (FloatFormat.minSubnormalExponent fmt) ∧
      δ * η = 0 := by
  by_cases hnormal : minNormalAt fmt ≤ |x|
  · have hx0 : x ≠ 0 := by
      rintro rfl
      have := FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix
        (FloatFormat.minNormalExponent fmt)
      simp only [abs_zero] at hnormal
      linarith
    have hulp := ulpAt_le_of_minNormalAt_le fmt hnormal
    refine ⟨(r - x) / x, 0, ?_, ?_, ?_, by simp⟩
    · field_simp
      ring
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr hx0)]
      calc
        |r - x| ≤ c * ulpAt fmt x := herr
        _ ≤ c * (FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (1 - Int.ofNat (fmt.fracWidth + 1)) * |x|) :=
          mul_le_mul_of_nonneg_left hulp hc
        _ = _ := by ring
    · simpa using mul_nonneg hc
        (FloatLib.Floats.Formats.Flocq.bpow.nonneg Numerics.binaryRadix _)
  · replace hnormal := not_le.mp hnormal
    refine ⟨0, r - x, by ring, ?_, ?_, by simp⟩
    · simpa using mul_nonneg hc
        (FloatLib.Floats.Formats.Flocq.bpow.nonneg Numerics.binaryRadix _)
    · rw [← ulpAt_eq_of_abs_lt_minNormalAt fmt hnormal]
      exact herr

/--
Standard model with gradual underflow for any nearest rounding onto the grid of `fmt`, with
either tie-breaking rule: `round x = x * (1 + δ) + η`, `|δ| ≤ 2^(-precision)`,
`|η| ≤ 2^(minSubnormalExponent - 1)`, and `δ * η = 0`.
-/
theorem round_standardModel_of_nearest (fmt : FloatFormat)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    ∃ δ η : ℝ,
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd x = x * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  have herr : |round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd x - x| ≤
      (1 / 2) * ulpAt fmt x := by
    have := error_bound_ulp (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd x
    rw [ulpAt]
    linarith
  obtain ⟨δ, η, hr, hδ, hη, hδη⟩ :=
    exists_standardModel_of_abs_sub_le fmt (by norm_num) herr
  refine ⟨δ, η, hr, ?_, ?_, hδη⟩
  · rw [← two_mul_unitRoundoffAt] at hδ
    linarith
  · rw [← two_mul_underflowErrorAt] at hη
    linarith

/--
Standard model with gradual underflow for any valid rounding onto the grid of `fmt`, including
the directed roundings: `round x = x * (1 + δ) + η`, `|δ| ≤ 2^(1 - precision)`,
`|η| ≤ 2^minSubnormalExponent`, and `δ * η = 0`.
-/
theorem round_standardModel (fmt : FloatFormat) (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    ∃ δ η : ℝ,
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd x = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 := by
  have herr : |round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) rnd x - x| ≤
      1 * ulpAt fmt x := by
    rw [one_mul, ulpAt]
    exact round_abs_error_le_ulp rnd x
  obtain ⟨δ, η, hr, hδ, hη, hδη⟩ :=
    exists_standardModel_of_abs_sub_le fmt zero_le_one herr
  refine ⟨δ, η, hr, ?_, ?_, hδη⟩
  · rwa [one_mul, ← two_mul_unitRoundoffAt] at hδ
  · rwa [one_mul, ← two_mul_underflowErrorAt] at hη

/--
Standard model with gradual underflow for nearest-even rounding onto the grid of `fmt`:
`roundAt fmt x = x * (1 + δ) + η`, `|δ| ≤ 2^(-precision)`,
`|η| ≤ 2^(minSubnormalExponent - 1)`, and `δ * η = 0`. For binary32 the bounds are `2^(-24)` and
`2^(-150)`.
-/
theorem roundAt_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ, roundAt fmt x = x * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel_of_nearest fmt nearestEven x

/-- Standard model with gradual underflow for downward rounding onto the grid of `fmt`. -/
theorem roundAtDown_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ, roundAtDown fmt x = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel fmt floorRound x

/-- Standard model with gradual underflow for upward rounding onto the grid of `fmt`. -/
theorem roundAtUp_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ, roundAtUp fmt x = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel fmt ceilRound x

/-- Standard model with gradual underflow for rounding toward zero onto the grid of `fmt`. -/
theorem round_truncRound_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ,
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) truncRound x = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel fmt truncRound x

/-! ## Exact addition below the normal range -/

/--
Nearest-even rounding of a sum of two grid points has a relative error of at most
`2^(-precision)` and no underflow term. Below the normal range the sum is itself a grid point.
-/
theorem roundAt_add_eq_mul_one_add (fmt : FloatFormat) {x y : ℝ}
    (hx : genericFormat Numerics.binaryRadix (fexpOf fmt) x)
    (hy : genericFormat Numerics.binaryRadix (fexpOf fmt) y) :
    ∃ δ : ℝ, roundAt fmt (x + y) = (x + y) * (1 + δ) ∧ |δ| ≤ unitRoundoffAt fmt := by
  have hprec : (0 : ℤ) < Int.ofNat (fmt.fracWidth + 1) :=
    Int.natCast_pos.mpr (Nat.succ_pos fmt.fracWidth)
  by_cases hnormal : minNormalAt fmt ≤ |x + y|
  · have hs0 : x + y ≠ 0 := by
      intro h
      rw [h] at hnormal
      have := FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix
        (FloatFormat.minNormalExponent fmt)
      simp only [abs_zero] at hnormal
      linarith
    have hrel := relativeError_roundAt_le_of_normal fmt (x + y) hs0 hnormal
    rw [← two_mul_unitRoundoffAt] at hrel
    refine ⟨(roundAt fmt (x + y) - (x + y)) / (x + y), ?_, ?_⟩
    · field_simp
      ring
    · rw [abs_div]
      simp only [ErrorBounds.relativeError] at hrel
      linarith
  · replace hnormal := not_le.mp hnormal
    have hbound : |x + y| ≤
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (fmt.fracWidth + 1) + FloatFormat.minSubnormalExponent fmt) := by
      refine hnormal.le.trans ?_
      rw [minNormalAt, ← minNormalExponent_eq]
      exact (FloatLib.Floats.Formats.Flocq.bpow_le_bpow_iff Numerics.binaryRadix _ _).mpr
        (by linarith)
    have hsum : genericFormat Numerics.binaryRadix (fexpOf fmt) (x + y) :=
      generic_format_FLT_add_small (β := Numerics.binaryRadix)
        (FloatFormat.minSubnormalExponent fmt) (Int.ofNat (fmt.fracWidth + 1)) hprec
        hx hy hbound
    refine ⟨0, ?_, by simp [unitRoundoffAt, FloatLib.Floats.Formats.Flocq.bpow.nonneg]⟩
    rw [add_zero, mul_one]
    exact round_preserves_generic nearestEven (x + y) hsum

/--
For an IEEE descriptor, addition with finite operands and result has relative error at most
`2^(-precision)`, with no underflow term:
`toReal (add x y) = (toReal x + toReal y) * (1 + δ)`.
-/
theorem toReal_add_eq_mul_one_add {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    ∃ δ : ℝ, toReal (add x y) = (toReal x + toReal y) * (1 + δ) ∧
      |δ| ≤ unitRoundoffAt fmt := by
  rw [toReal_add_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_add_eq_mul_one_add fmt
    (toReal_genericFormat_of_isFinite x hx) (toReal_genericFormat_of_isFinite y hy)

/--
For an IEEE descriptor, subtraction with finite operands and result has relative error at most
`2^(-precision)`, with no underflow term:
`toReal (sub x y) = (toReal x - toReal y) * (1 + δ)`.
-/
theorem toReal_sub_eq_mul_one_add {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (sub x y) = true) :
    ∃ δ : ℝ, toReal (sub x y) = (toReal x - toReal y) * (1 + δ) ∧
      |δ| ≤ unitRoundoffAt fmt := by
  rw [toReal_sub_eq_roundAt x y hfmt hx hy hout, sub_eq_add_neg]
  exact roundAt_add_eq_mul_one_add fmt (toReal_genericFormat_of_isFinite x hx)
    (generic_format_neg _ (toReal_genericFormat_of_isFinite y hy))

/--
For an IEEE descriptor, addition with finite operands and result has absolute error at most
`2^(-precision) * |x + y|`.
-/
theorem abs_toReal_add_sub_le_unitRoundoffAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (add x y) = true) :
    |toReal (add x y) - (toReal x + toReal y)| ≤
      unitRoundoffAt fmt * |toReal x + toReal y| := by
  obtain ⟨δ, hδ, hbound⟩ := toReal_add_eq_mul_one_add x y hfmt hx hy hout
  rw [hδ, show (toReal x + toReal y) * (1 + δ) - (toReal x + toReal y) =
    δ * (toReal x + toReal y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

/--
For an IEEE descriptor, subtraction with finite operands and result has absolute error at most
`2^(-precision) * |x - y|`.
-/
theorem abs_toReal_sub_sub_le_unitRoundoffAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (sub x y) = true) :
    |toReal (sub x y) - (toReal x - toReal y)| ≤
      unitRoundoffAt fmt * |toReal x - toReal y| := by
  obtain ⟨δ, hδ, hbound⟩ := toReal_sub_eq_mul_one_add x y hfmt hx hy hout
  rw [hδ, show (toReal x - toReal y) * (1 + δ) - (toReal x - toReal y) =
    δ * (toReal x - toReal y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

/-! ## Standard model for finite IEEE executable operations -/

/--
Standard model with gradual underflow for IEEE multiplication with finite operands and result.
-/
theorem toReal_mul_standardModel {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hout : isFinite (mul x y) = true) :
    ∃ δ η : ℝ, toReal (mul x y) = toReal x * toReal y * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_mul_eq_roundAt x y hfmt hx hy hout]
  exact roundAt_standardModel fmt _

/--
Standard model with gradual underflow for IEEE division with finite operands and result and a
nonzero divisor.
-/
theorem toReal_div_standardModel {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true)
    (hy0 : isZero y = false) (hout : isFinite (div x y) = true) :
    ∃ δ η : ℝ, toReal (div x y) = toReal x / toReal y * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_div_eq_roundAt x y hfmt hx hy hy0 hout]
  exact roundAt_standardModel fmt _

/--
Standard model with gradual underflow for IEEE square root on a finite nonnegative input,
including either signed zero.
-/
theorem toReal_sqrt_standardModel {fmt : FloatFormat} (x : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    ∃ δ η : ℝ, toReal (sqrt x) = Real.sqrt (toReal x) * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_sqrt_eq_roundAt x hfmt hx hdomain]
  exact roundAt_standardModel fmt _

/--
Standard model with gradual underflow for IEEE fused multiply-add with finite operands and result.
-/
theorem toReal_fma_standardModel {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : isFinite x = true) (hy : isFinite y = true) (hz : isFinite z = true)
    (hout : isFinite (fma x y z) = true) :
    ∃ δ η : ℝ, toReal (fma x y z) = (toReal x * toReal y + toReal z) * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_fma_eq_roundAt x y z hfmt hx hy hz hout]
  exact roundAt_standardModel fmt _

/--
Standard model with gradual underflow for a cast between IEEE descriptors with finite input and
result, using the constants of the destination format.
-/
theorem toReal_cast_standardModel {src dst : FloatFormat} (x : Model src)
    (hsrc : src.isIEEE = true) (hdst : dst.isIEEE = true)
    (hx : isFinite x = true) (hout : isFinite (cast src dst x) = true) :
    ∃ δ η : ℝ, toReal (cast src dst x) = toReal x * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt dst ∧ |η| ≤ underflowErrorAt dst ∧ δ * η = 0 := by
  rw [cast_eq_roundAt hsrc hdst x hx hout]
  exact roundAt_standardModel dst _

end Model
end FloatLib.Floats.Formats.BinaryInterchange
