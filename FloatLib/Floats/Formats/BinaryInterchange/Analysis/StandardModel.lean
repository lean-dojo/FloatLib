/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Positive
public import FloatLib.Floats.Formats.Flocq.Theory.Error.Directed
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants

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

A real that rounds to zero under nearest rounding is at most `η₀` in magnitude, so a real beyond
`η₀` keeps its sign.

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

/-- The unit roundoff as a power of two. -/
theorem unitRoundoffAt_eq (fmt : FloatFormat) :
    unitRoundoffAt fmt = (2 : ℝ) ^ (-((fmt.fracWidth : ℤ) + 1)) := by
  simp [unitRoundoffAt, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal]

/-- The underflow allowance as a power of two. -/
theorem underflowErrorAt_eq (fmt : FloatFormat) :
    underflowErrorAt fmt = (2 : ℝ) ^ (FloatFormat.minSubnormalExponent fmt - 1) := by
  simp [underflowErrorAt, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal]

/-- The underflow allowance is at most `2^e` once `minSubnormalExponent - 1 ≤ e`. -/
theorem underflowErrorAt_le_zpow (fmt : FloatFormat) {e : ℤ}
    (he : FloatFormat.minSubnormalExponent fmt - 1 ≤ e) : underflowErrorAt fmt ≤ (2 : ℝ) ^ e := by
  rw [underflowErrorAt_eq]
  exact zpow_le_zpow_right₀ one_le_two he

/-- The unit roundoff is positive. -/
theorem unitRoundoffAt_pos (fmt : FloatFormat) : 0 < unitRoundoffAt fmt :=
  FloatLib.Floats.Formats.Flocq.bpow.pos _ _

/-- The underflow allowance is positive. -/
theorem underflowErrorAt_pos (fmt : FloatFormat) : 0 < underflowErrorAt fmt :=
  FloatLib.Floats.Formats.Flocq.bpow.pos _ _

/-- The unit roundoff is below one. -/
theorem unitRoundoffAt_lt_one (fmt : FloatFormat) : unitRoundoffAt fmt < 1 := by
  rw [unitRoundoffAt_eq]
  exact zpow_lt_one_of_neg₀ (by norm_num) (by omega)

/-- Every format represents one, so its largest finite value is at least one. -/
theorem one_le_toReal_posMaxFinite (fmt : FloatFormat) : 1 ≤ toReal (posMaxFinite fmt) := by
  simpa using abs_toReal_le_posMaxFinite_of_isFinite (posOne fmt) (isFinite_posOne fmt)

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

/-- The least positive normal magnitude is at most one. -/
theorem minNormalAt_le_one (fmt : FloatFormat) : minNormalAt fmt ≤ 1 := by
  rw [minNormalAt, Flocq.bpow_binaryRadix]
  apply zpow_le_one_of_nonpos₀ one_le_two
  have := fmt.exponentBias_pos
  simp only [FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
  omega

open Flocq in
/-- An integer of magnitude at most `2 ^ p`, with `p = fracWidth + 1`, lies on the grid that
`roundAt` rounds to, so every rounding direction keeps it. That grid has no largest exponent, so the
integer need not be a finite value of `fmt`: in `FloatFormat.ieee 2 3` the integer `4` is on it, but
the largest finite value is `3.75`. -/
theorem roundAt_intCast_of_abs_le (fmt : FloatFormat) {n : ℤ}
    (hn : |(n : ℝ)| ≤ 2 ^ (fmt.fracWidth + 1)) (mode : IEEERoundingMode := .nearest) :
    roundAt fmt (n : ℝ) mode = n := by
  apply roundAt_of_genericFormat
  have hemin : fmt.minSubnormalExponent ≤ 0 := by
    have := fmt.exponentBias_pos
    simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have hprec : (0 : ℤ) < ((fmt.fracWidth + 1 : ℕ) : ℤ) := by positivity
  change @genericFormat Numerics.binaryRadix
    (fltExp fmt.minSubnormalExponent ((fmt.fracWidth + 1 : ℕ) : ℤ)) (fltValidExp _ _ hprec) (n : ℝ)
  refine (generic_format_FLT_iff _ _ hprec _).mpr ⟨hprec, ?_⟩
  have hbase : Numerics.binaryRadix.base ^ (((fmt.fracWidth + 1 : ℕ) : ℤ)).toNat =
      2 ^ (fmt.fracWidth + 1) := by
    rw [Int.toNat_natCast]; rfl
  have habs : |n| ≤ 2 ^ (fmt.fracWidth + 1) := by exact_mod_cast hn
  rcases lt_or_eq_of_le habs with hlt | heq
  · -- Below `2 ^ p` the integer is its own mantissa.
    refine ⟨⟨n, 0⟩, by simp [Flocq.toReal], ?_, hemin⟩
    rw [hbase]
    have : ((n.natAbs : ℕ) : ℤ) < ((2 ^ (fmt.fracWidth + 1) : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]; exact_mod_cast hlt
    exact_mod_cast this
  · -- At `2 ^ p` it is twice the mantissa `± 2 ^ (p - 1)`.
    have hdvd : (2 : ℤ) ∣ n := by
      rw [← dvd_abs, heq]
      exact dvd_pow_self 2 (Nat.succ_ne_zero _)
    obtain ⟨m, rfl⟩ := hdvd
    refine ⟨⟨m, 1⟩, ?_, ?_, by dsimp only; omega⟩
    · simp [Flocq.toReal, bpow_binaryRadix]; ring
    · rw [hbase]
      have hm : (2 * m).natAbs = 2 ^ (fmt.fracWidth + 1) := by
        have : ((2 * m).natAbs : ℤ) = 2 ^ (fmt.fracWidth + 1) := by rw [Int.natCast_natAbs, heq]
        exact_mod_cast this
      rw [Int.natAbs_mul, pow_succ] at hm
      have := Nat.one_le_two_pow (n := fmt.fracWidth)
      dsimp only
      rw [pow_succ]
      change 2 * m.natAbs = 2 ^ fmt.fracWidth * 2 at hm
      omega

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
    have hexp := minSubnormalExponent_add_precision_sub_one fmt
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
  have hx0 : x ≠ 0 := abs_pos.mp ((bpow.pos _ _).trans_le hx)
  have hnormal :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (FloatFormat.minSubnormalExponent fmt + Int.ofNat (fmt.fracWidth + 1) - 1) ≤
        |x| := by
    rw [minSubnormalExponent_add_precision_sub_one]
    exact hx
  have h := ulp_div_abs_le_FLT_normal (β := Numerics.binaryRadix)
    (FloatFormat.minSubnormalExponent fmt) (Int.ofNat (fmt.fracWidth + 1)) hprec x hnormal
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
  · have hx0 : x ≠ 0 := abs_pos.mp ((bpow.pos _ _).trans_le hnormal)
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
theorem roundAt_down_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ, roundAt fmt x .down = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel fmt floorRound x

/-- Standard model with gradual underflow for upward rounding onto the grid of `fmt`. -/
theorem roundAt_up_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ, roundAt fmt x .up = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel fmt ceilRound x

/-- Standard model with gradual underflow for rounding toward zero onto the grid of `fmt`. -/
theorem round_truncRound_standardModel (fmt : FloatFormat) (x : ℝ) :
    ∃ δ η : ℝ,
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) truncRound x = x * (1 + δ) + η ∧
      |δ| ≤ 2 * unitRoundoffAt fmt ∧ |η| ≤ 2 * underflowErrorAt fmt ∧ δ * η = 0 :=
  round_standardModel fmt truncRound x

/-! ## Error and sign of nearest-even rounding -/

/--
Nearest-even rounding onto the grid of `fmt` has absolute error at most
`unitRoundoffAt fmt * |x| + underflowErrorAt fmt`.
-/
theorem abs_roundAt_sub_le_unitRoundoffAt (fmt : FloatFormat) (x : ℝ) :
    |roundAt fmt x - x| ≤ unitRoundoffAt fmt * |x| + underflowErrorAt fmt := by
  obtain ⟨δ, η, hround, hδ, hη, -⟩ := roundAt_standardModel fmt x
  rw [hround, show x * (1 + δ) + η - x = x * δ + η by ring]
  calc |x * δ + η| ≤ |x| * |δ| + |η| := (abs_add_le _ _).trans_eq (by rw [abs_mul])
    _ ≤ |x| * unitRoundoffAt fmt + underflowErrorAt fmt := by gcongr
    _ = unitRoundoffAt fmt * |x| + underflowErrorAt fmt := by ring

/-- A real that rounds to zero is at most `underflowErrorAt fmt`, half the least subnormal. -/
theorem abs_le_underflowErrorAt_of_roundAt_eq_zero (fmt : FloatFormat) {x : ℝ}
    (hx : roundAt fmt x = 0) : |x| ≤ underflowErrorAt fmt := by
  have herror := abs_roundAt_sub_le fmt x
  rw [hx, zero_sub, abs_neg, halfUlpAt] at herror
  by_cases hnormal : minNormalAt fmt ≤ |x|
  · have hulp := ulpAt_le_of_minNormalAt_le fmt hnormal
    have hpositive : 0 < |x| := (FloatLib.Floats.Formats.Flocq.bpow.pos _ _).trans_le hnormal
    have hspacing : FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (1 - Int.ofNat (fmt.fracWidth + 1)) ≤ 1 / 2 := by
      rw [bpow_binaryRadix, show (1 / 2 : ℝ) = 2 ^ (-1 : ℤ) by norm_num]
      exact zpow_le_zpow_right₀ (by norm_num)
        (by have := fmt.fracWidth_pos; simp only [Int.ofNat_eq_natCast]; push_cast; omega)
    nlinarith
  · rw [ulpAt_eq_of_abs_lt_minNormalAt fmt (not_le.mp hnormal), ← two_mul_underflowErrorAt]
      at herror
    linarith

/-- A nonnegative real rounds to a nonnegative value. -/
theorem roundAt_nonneg (fmt : FloatFormat) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ roundAt fmt x := by
  simpa using roundAt_mono fmt hx

/-- A nonpositive real rounds to a nonpositive value. -/
theorem roundAt_nonpos (fmt : FloatFormat) {x : ℝ} (hx : x ≤ 0) : roundAt fmt x ≤ 0 := by
  simpa using roundAt_mono fmt hx

/-- Rounding maps the unit interval into itself. -/
theorem roundAt_mem_Icc_zero_one (fmt : FloatFormat) {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    roundAt fmt x ∈ Set.Icc 0 1 := by
  exact ⟨roundAt_nonneg fmt hx.1, roundAt_one fmt ▸ roundAt_mono fmt hx.2⟩

/-- A real above `underflowErrorAt fmt` rounds to a positive value. -/
theorem roundAt_pos (fmt : FloatFormat) {x : ℝ} (hx : underflowErrorAt fmt < x) :
    0 < roundAt fmt x := by
  have hx₀ : 0 ≤ x := (underflowErrorAt_pos fmt).le.trans hx.le
  refine (by simpa using roundAt_mono fmt hx₀ : 0 ≤ roundAt fmt x).lt_of_ne' fun hzero => ?_
  have := abs_le_underflowErrorAt_of_roundAt_eq_zero fmt hzero
  rw [abs_of_nonneg hx₀] at this
  linarith

/-- A real below `-underflowErrorAt fmt` rounds to a negative value. -/
theorem roundAt_lt_zero (fmt : FloatFormat) {x : ℝ} (hx : x < -underflowErrorAt fmt) :
    roundAt fmt x < 0 := by
  have h := roundAt_pos fmt (lt_neg_of_lt_neg hx)
  rw [roundAt_neg, IEEERoundingMode.negate_nearest] at h
  linarith

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
  · have hs0 : x + y ≠ 0 := abs_pos.mp ((bpow.pos _ _).trans_le hnormal)
    have hrel := relativeError_roundAt_le_of_normal fmt (x + y) hs0 hnormal
    rw [← two_mul_unitRoundoffAt, mul_div_cancel_left₀ _ two_ne_zero] at hrel
    obtain ⟨δ, hδ, hround⟩ := ErrorBounds.exists_delta_of_relativeError_le hs0 hrel
    exact ⟨δ, hround, hδ⟩
  · replace hnormal := not_le.mp hnormal
    have hbound : |x + y| ≤
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (fmt.fracWidth + 1) + FloatFormat.minSubnormalExponent fmt) := by
      refine hnormal.le.trans ?_
      rw [minNormalAt, ← minSubnormalExponent_add_precision_sub_one]
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
For an IEEE descriptor, addition with a finite result, which forces finite operands, has relative
error at most `2^(-precision)`, with no underflow term:
`toReal (add x y) = (toReal x + toReal y) * (1 + δ)`.
-/
theorem toReal_add_eq_mul_one_add {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (add x y) = true) :
    ∃ δ : ℝ, toReal (add x y) = (toReal x + toReal y) * (1 + δ) ∧
      |δ| ≤ unitRoundoffAt fmt := by
  obtain ⟨hx, hy⟩ := isFinite_of_isFinite_add hfmt hout
  rw [toReal_add_eq_roundAt x y hfmt hout]
  exact roundAt_add_eq_mul_one_add fmt
    (toReal_genericFormat_of_isFinite x hx) (toReal_genericFormat_of_isFinite y hy)

/--
For an IEEE descriptor, subtraction with a finite result, which forces finite operands, has
relative error at most `2^(-precision)`, with no underflow term:
`toReal (sub x y) = (toReal x - toReal y) * (1 + δ)`.
-/
theorem toReal_sub_eq_mul_one_add {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (sub x y) = true) :
    ∃ δ : ℝ, toReal (sub x y) = (toReal x - toReal y) * (1 + δ) ∧
      |δ| ≤ unitRoundoffAt fmt := by
  obtain ⟨hx, hy⟩ := isFinite_of_isFinite_sub hfmt hout
  rw [toReal_sub_eq_roundAt x y hfmt hout, sub_eq_add_neg]
  exact roundAt_add_eq_mul_one_add fmt (toReal_genericFormat_of_isFinite x hx)
    (generic_format_neg _ (toReal_genericFormat_of_isFinite y hy))

/--
For an IEEE descriptor, addition with a finite result, which forces finite operands, has absolute
error at most `2^(-precision) * |x + y|`.
-/
theorem abs_toReal_add_sub_le_unitRoundoffAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (add x y) = true) :
    |toReal (add x y) - (toReal x + toReal y)| ≤
      unitRoundoffAt fmt * |toReal x + toReal y| := by
  obtain ⟨δ, hδ, hbound⟩ := toReal_add_eq_mul_one_add x y hfmt hout
  rw [hδ, show (toReal x + toReal y) * (1 + δ) - (toReal x + toReal y) =
    δ * (toReal x + toReal y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

/--
For an IEEE descriptor, subtraction with a finite result, which forces finite operands, has
absolute error at most `2^(-precision) * |x - y|`.
-/
theorem abs_toReal_sub_sub_le_unitRoundoffAt {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true) (hout : isFinite (sub x y) = true) :
    |toReal (sub x y) - (toReal x - toReal y)| ≤
      unitRoundoffAt fmt * |toReal x - toReal y| := by
  obtain ⟨δ, hδ, hbound⟩ := toReal_sub_eq_mul_one_add x y hfmt hout
  rw [hδ, show (toReal x - toReal y) * (1 + δ) - (toReal x - toReal y) =
    δ * (toReal x - toReal y) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right hbound (abs_nonneg _)

/-! ## Standard model for finite IEEE executable operations -/

/--
Standard model with gradual underflow for IEEE multiplication with a finite result, which forces
finite operands.
-/
theorem toReal_mul_standardModel {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (mul x y) = true) :
    ∃ δ η : ℝ, toReal (mul x y) = toReal x * toReal y * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_mul_eq_roundAt x y hfmt hout]
  exact roundAt_standardModel fmt _

/--
Standard model with gradual underflow for IEEE division by a finite divisor with a finite result,
which forces a finite dividend and a nonzero divisor.
-/
theorem toReal_div_standardModel {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hy : isFinite y = true) (hout : isFinite (div x y) = true) :
    ∃ δ η : ℝ, toReal (div x y) = toReal x / toReal y * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_div_eq_roundAt x y hfmt hy hout]
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
Standard model with gradual underflow for IEEE fused multiply-add with a finite result, which
forces finite operands.
-/
theorem toReal_fma_standardModel {fmt : FloatFormat} (x y z : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : isFinite (fma x y z) = true) :
    ∃ δ η : ℝ, toReal (fma x y z) = (toReal x * toReal y + toReal z) * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt fmt ∧ |η| ≤ underflowErrorAt fmt ∧ δ * η = 0 := by
  rw [toReal_fma_eq_roundAt x y z hfmt hout]
  exact roundAt_standardModel fmt _

/--
Standard model with gradual underflow for a finite cast to an IEEE destination, using the
constants of the destination format. The source may be any binary descriptor.
-/
theorem toReal_cast_standardModel {src dst : FloatFormat} (x : Model src)
    (hdst : dst.isIEEE = true) (hout : isFinite (cast src dst x) = true) :
    ∃ δ η : ℝ, toReal (cast src dst x) = toReal x * (1 + δ) + η ∧
      |δ| ≤ unitRoundoffAt dst ∧ |η| ≤ underflowErrorAt dst ∧ δ * η = 0 := by
  rw [cast_eq_roundAt hdst x hout]
  exact roundAt_standardModel dst _

end Model
end FloatLib.Floats.Formats.BinaryInterchange
