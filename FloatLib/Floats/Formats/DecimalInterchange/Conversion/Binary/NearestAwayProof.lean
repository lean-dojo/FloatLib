/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm

/-!
# Nearest-away conversion to binary

The rational is rounded to an integer on the destination binary grid. The rounded
significand fits the precision, allowing one carry, so the binary encoder preserves
its exact value whenever the delivered result is finite. This proves a single
rounding, including ties away from zero, rather than assuming that two successive
roundings agree.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats.Formats BinaryInterchange

/-- A nonnegative rational is its unsigned numerator divided by its denominator. -/
theorem rat_eq_unsigned_div {x : ℚ} (hx : 0 ≤ x) :
    x = (x.num.natAbs : ℚ) / x.den := by
  rw [Nat.cast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hx), Rat.num_div_den]

/-- The binary grid exponent is never below the subnormal quantum. -/
theorem minSubnormalExponent_le_binaryQuantum (fmt : FloatFormat) (x : ℚ) :
    fmt.minSubnormalExponent ≤ binaryQuantum fmt x :=
  le_max_left _ _

/-- A positive magnitude scaled to its binary grid is below one full precision carry. -/
theorem div_binaryQuantum_lt (fmt : FloatFormat) {x : ℚ} (hx : 0 < x) :
    x / (2 : ℚ) ^ binaryQuantum fmt x < 2 ^ (fmt.fracWidth + 1) := by
  have hn : x.num.natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr (ne_of_gt (Rat.num_pos.mpr hx))
  have hlog := (Model.floorLog2_bounds x.num.natAbs x.den hn x.den_nz).2
  have hcast : (x : ℝ) = (x.num.natAbs : ℝ) / x.den := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using
      congrArg (fun q : ℚ => (q : ℝ)) (rat_eq_unsigned_div hx.le)
  rw [← hcast] at hlog
  change (x : ℝ) < (2 : ℝ) ^
    (Numerics.RationalBinary.floorLog2 x.num.natAbs x.den + 1) at hlog
  have hexp : Numerics.RationalBinary.floorLog2 x.num.natAbs x.den + 1 ≤
      (fmt.fracWidth + 1 : ℕ) + binaryQuantum fmt x := by
    have := le_max_right fmt.minSubnormalExponent
      (Numerics.RationalBinary.floorLog2 x.num.natAbs x.den - fmt.fracWidth)
    dsimp [binaryQuantum]
    omega
  have hpow := (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp)
  have hupper : (x : ℝ) < (2 : ℝ) ^ (fmt.fracWidth + 1) *
      (2 : ℝ) ^ binaryQuantum fmt x := by
    simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast] using
      hlog.trans_le hpow
  have hresult := (div_lt_iff₀ (by positivity :
    (0 : ℝ) < (2 : ℝ) ^ binaryQuantum fmt x)).mpr hupper
  apply (Rat.cast_lt (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_pow] using hresult

/-- The nearest-away significand fits the precision, with equality allowed for a carry. -/
theorem binaryNearestAwayDyadic_significand_le (fmt : FloatFormat) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    (binaryNearestAwayDyadic fmt s x).significand ≤ 2 ^ (fmt.fracWidth + 1) := by
  by_cases hz : x = 0
  · subst x
    norm_num [binaryNearestAwayDyadic, RoundingMode.roundMagnitude, RoundingMode.increment]
  have hfloor : ⌊x / (2 : ℚ) ^ binaryQuantum fmt x⌋₊ < 2 ^ (fmt.fracWidth + 1) := by
    apply (Nat.floor_lt (by positivity)).mpr
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      div_binaryQuantum_lt fmt (lt_of_le_of_ne hx (Ne.symm hz))
  exact (RoundingMode.roundMagnitude_le_floor_add_one .nearestAway s _).trans
    (Nat.succ_le_of_lt hfloor)

/-- The nearest-away dyadic lies on the destination grid before imposing its upper
exponent bound. A carry is an exact change of exponent, not another rounding. -/
theorem binaryNearestAwayDyadic_genericFormat (fmt : FloatFormat) (s : Bool)
    {x : ℚ} (hx : 0 ≤ x) :
    Flocq.genericFormat Numerics.binaryRadix (Model.fexpOf fmt)
      (binaryNearestAwayDyadic fmt s x).toReal := by
  have hm := binaryNearestAwayDyadic_significand_le fmt s hx
  have he := minSubnormalExponent_le_binaryQuantum fmt x
  rcases lt_or_eq_of_le hm with hlt | heq
  · exact Model.Dyadic.genericFormat_of_significand_lt fmt _ hlt he
  · apply Model.Dyadic.genericFormat_of_eq_mul_pow2 fmt _ (2 ^ fmt.fracWidth) 1
    · simpa [pow_succ] using heq
    · exact Nat.pow_lt_pow_right (by decide) (by omega)
    · exact he

/-- Encoding the nearest-away dyadic preserves its exact real value on a finite result. -/
theorem roundBinaryMagnitude_nearestAway_eq (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (s : Bool) {x : ℚ} (hx : 0 ≤ x)
    (hfinite : Model.isFinite (roundBinaryMagnitude fmt .nearestAway s x) = true) :
    Model.toReal (roundBinaryMagnitude fmt .nearestAway s x) =
      (binaryNearestAwayDyadic fmt s x).toReal := by
  rw [roundBinaryMagnitude, Model.toReal_roundDyadic_eq_roundAt fmt hfmt _ hfinite]
  exact Flocq.round_preserves_generic Flocq.nearestEven _
    (binaryNearestAwayDyadic_genericFormat fmt s hx)

/-- A finite nearest-away conversion is within half a binary grid unit of the input.
The grid is clamped at the subnormal quantum. -/
theorem roundBinaryMagnitude_nearestAway_error_le_half (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (s : Bool) {x : ℚ} (hx : 0 ≤ x)
    (hfinite : Model.isFinite (roundBinaryMagnitude fmt .nearestAway s x) = true) :
    |Model.toReal (roundBinaryMagnitude fmt .nearestAway s x) -
      (if s then -(x : ℝ) else x)| ≤
        (2 : ℝ) ^ binaryQuantum fmt x / 2 := by
  rw [roundBinaryMagnitude_nearestAway_eq fmt hfmt s hx hfinite]
  have hu : (0 : ℚ) < (2 : ℚ) ^ binaryQuantum fmt x := by positivity
  have herr := RoundingMode.roundMagnitude_error_le_half .nearestAway (Or.inr rfl) s
    (div_nonneg hx hu.le)
  have hscaled := mul_le_mul_of_nonneg_right herr hu.le
  have habs : |(RoundingMode.nearestAway.roundMagnitude s
      (x / (2 : ℚ) ^ binaryQuantum fmt x) : ℚ) - x / (2 : ℚ) ^ binaryQuantum fmt x| *
      (2 : ℚ) ^ binaryQuantum fmt x =
      |((RoundingMode.nearestAway.roundMagnitude s
        (x / (2 : ℚ) ^ binaryQuantum fmt x) : ℚ) - x / (2 : ℚ) ^ binaryQuantum fmt x) *
        (2 : ℚ) ^ binaryQuantum fmt x| := by rw [abs_mul, abs_of_pos hu]
  rw [habs] at hscaled
  have hmul : ((RoundingMode.nearestAway.roundMagnitude s
      (x / (2 : ℚ) ^ binaryQuantum fmt x) : ℚ) - x / (2 : ℚ) ^ binaryQuantum fmt x) *
      (2 : ℚ) ^ binaryQuantum fmt x =
      (RoundingMode.nearestAway.roundMagnitude s
        (x / (2 : ℚ) ^ binaryQuantum fmt x) : ℚ) *
        (2 : ℚ) ^ binaryQuantum fmt x - x := by
    field_simp
  rw [hmul] at hscaled
  have hreal : |(RoundingMode.nearestAway.roundMagnitude s
      (x / (2 : ℚ) ^ binaryQuantum fmt x) : ℝ) *
      (2 : ℝ) ^ binaryQuantum fmt x - x| ≤
      (2 : ℝ) ^ binaryQuantum fmt x / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hscaled
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one, one_div, inv_mul_eq_div] using h
  cases s
  · simpa [binaryNearestAwayDyadic, Numerics.Dyadic.toReal,
      Numerics.Dyadic.signedSignificand, Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal] using hreal
  · simpa [binaryNearestAwayDyadic, Numerics.Dyadic.toReal,
      Numerics.Dyadic.signedSignificand, Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal, neg_mul, neg_add_eq_sub, abs_sub_comm] using hreal

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
