/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Rational.Selection
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
public import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact rational meaning of report precision rounding

The executable scale, quotient, and remainder represent the report's scaled magnitude, floor,
and fractional part exactly. The resulting formula is uniform in the rounding mode, including
each supplied stochastic word. Binary exponent bounds characterize the selected logarithm
without approximating it by a real-valued computation.

Reference: P3109 unapproved interim report 4.0.3, revision `34f5964`, §4.7.4.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.RationalRounding

/-- At the precision quantum, the exact quotient is below `2^precision`.
Clamping the leading exponent to the minimum normal exponent can only decrease the quotient.
The bound depends on these two parameters, not on an encoding or saturation policy. -/
theorem quotientFloor_lt_precision (precision : Nat) (minimumNormalExponent : Int)
    (numerator denominator : Nat) (hnumerator : numerator ≠ 0)
    (hdenominator : denominator ≠ 0) :
    let leading := RationalBinary.floorLog2 numerator denominator
    let quantum := max leading minimumNormalExponent - Int.ofNat precision + 1
    let scaled := RationalBinary.scaleByPowerOfTwo numerator denominator (-quantum)
    scaled.1 / scaled.2 < 2 ^ precision := by
  let leading := RationalBinary.floorLog2 numerator denominator
  let quantum := max leading minimumNormalExponent - Int.ofNat precision + 1
  let scaled := RationalBinary.scaleByPowerOfTwo numerator denominator (-quantum)
  have hden := RationalBinary.scaleByPowerOfTwo_snd_ne_zero
    numerator denominator (-quantum) hdenominator
  have hbounds := BinaryInterchange.Model.scaleByPowerOfTwo_floorLog2_bounds
    numerator denominator (-quantum) hnumerator hdenominator
  have hpower : leading + -quantum + 1 ≤ Int.ofNat precision := by
    dsimp only [quantum]
    omega
  have hratio : (scaled.1 : Real) / scaled.2 < (2 ^ precision : Nat) := by
    calc
      (scaled.1 : Real) / scaled.2 <
          BinaryInterchange.Model.bpow (leading + -quantum + 1) := hbounds.2
      _ ≤ BinaryInterchange.Model.bpow (Int.ofNat precision) :=
        (Flocq.bpow_le_bpow_iff binaryRadix _ _).2 hpower
      _ = (2 ^ precision : Nat) := by
        simpa [BinaryInterchange.Model.pow2_eq_two_pow] using
          BinaryInterchange.Model.bpow_ofNat precision
  have hdenReal : (0 : Real) < scaled.2 := by exact_mod_cast Nat.pos_of_ne_zero hden
  have hmul : scaled.1 < 2 ^ precision * scaled.2 := by
    exact_mod_cast (div_lt_iff₀ hdenReal).mp hratio
  exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hden)).2 hmul

/-- Apply the sign of the input to a nonnegative candidate. -/
def signed (negative : Bool) (magnitude : Rat) : Rat :=
  if negative then -magnitude else magnitude

/-- The report's real-valued significand, which is rational for a rational input. -/
def scaledMagnitude (value : Rat) (quantum : Int) : Rat :=
  |value| * (2 : Rat) ^ (-quantum)

/-- Report parity of the lower code, including its exceptional precision-one rule. -/
def codeEven (precision bias : Nat) (quantum : Int) (lower : Nat) : Bool :=
  if 1 < precision then decide (lower % 2 = 0)
  else decide (lower = 0 ∨ (quantum + (bias : Int)) % 2 = 0)

/-- Report selection between the two adjacent integer significands. -/
def roundedInteger (mode : RoundingMode) (negative : Bool) (parity : Nat → Bool)
    (scaled : Rat) : Nat :=
  let lower := ⌊scaled⌋₊
  if roundAway mode negative (parity lower) (scaled - lower) then lower + 1 else lower

/-- Precision rounding at a specified quantum, expressed by mathematical floor and fraction. -/
def roundAt (mode : RoundingMode) (quantum : Int) (parity : Nat → Bool) (value : Rat) : Rat :=
  signed (value.num < 0)
    ((roundedInteger mode (value.num < 0) parity (scaledMagnitude value quantum) : Rat) *
      (2 : Rat) ^ quantum)

/-- The report quantum uses the actual precision and exponent bias. -/
def quantum (precision bias : Nat) (value : Rat) : Int :=
  max (RationalBinary.floorLog2 value.num.natAbs value.den) (1 - (bias : Int)) -
    (precision : Int) + 1

/-- Mathematical report precision rounding of a finite rational. -/
def round (precision bias : Nat) (mode : RoundingMode) (value : Rat) : Rat :=
  roundAt mode (quantum precision bias value)
    (codeEven precision bias (quantum precision bias value)) value

/-- The absolute numerator and positive denominator represent the magnitude exactly. -/
theorem magnitude_eq_ratio (value : Rat) :
    |value| = (value.num.natAbs : Rat) / value.den := by
  calc
    |value| = |(value.num : Rat) / value.den| :=
      congrArg abs (Rat.num_div_den value).symm
    _ = _ := by
      rw [abs_div, ← Int.cast_abs, ← Int.natCast_natAbs,
        abs_of_nonneg (Nat.cast_nonneg _)]
      rfl

/-- The stored numerator sign is exactly the sign of the rational input. -/
theorem signed_abs (value : Rat) : signed (value.num < 0) |value| = value := by
  by_cases hn : value.num < 0
  · have hv : value < 0 := Rat.num_neg.mp hn
    simp [signed, hn, abs_of_neg hv]
  · have hv : 0 ≤ value := Rat.num_nonneg.mp (by omega)
    simp [signed, hn, abs_of_nonneg hv]

/-- Moving a binary exponent into an integer quotient preserves its exact rational value. -/
theorem scaleByPowerOfTwo_rat (numerator denominator : Nat) (exponent : Int) :
    ((RationalBinary.scaleByPowerOfTwo numerator denominator exponent).1 : Rat) /
        (RationalBinary.scaleByPowerOfTwo numerator denominator exponent).2 =
      (numerator : Rat) / denominator * (2 : Rat) ^ exponent := by
  cases exponent with
  | ofNat shift =>
      simp [RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
        div_mul_eq_mul_div]
  | negSucc shift =>
      simp [RationalBinary.scaleByPowerOfTwo, Nat.shiftLeft_eq', Nat.shiftLeft_eq,
        zpow_negSucc, div_mul_eq_div_mul_one_div]

/-- The executable scaled quotient is the report's scaled magnitude. -/
theorem scaledMagnitude_eq (value : Rat) (quantum : Int) :
    scaledMagnitude value quantum =
      ((RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).1 : Rat) /
        (RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).2 := by
  rw [scaleByPowerOfTwo_rat, scaledMagnitude, magnitude_eq_ratio]

/-- The quotient is exactly the lower adjacent integer in the report. -/
theorem floor_scaledMagnitude (value : Rat) (quantum : Int) :
    ⌊scaledMagnitude value quantum⌋₊ =
      (RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).1 /
        (RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).2 := by
  rw [scaledMagnitude_eq, Rat.natFloor_natCast_div_natCast]

/-- The remainder ratio is exactly the fractional part, not an approximation to it. -/
theorem fraction_scaledMagnitude (value : Rat) (quantum : Int) :
    scaledMagnitude value quantum - ⌊scaledMagnitude value quantum⌋₊ =
      (((RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).1 %
          (RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).2 : Nat) : Rat) /
        (RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)).2 := by
  have hd := RationalBinary.scaleByPowerOfTwo_snd_ne_zero
    value.num.natAbs value.den (-quantum) value.den_ne_zero
  rw [floor_scaledMagnitude, scaledMagnitude_eq,
    div_eq_quotient_add_fraction _ _ (Nat.pos_of_ne_zero hd)]
  ring

/-- All runtime rounding modes select the report's integer candidate at the given quantum. -/
theorem select_eq_roundedInteger (mode : RoundingMode) (value : Rat) (quantum : Int)
    (parity : Nat → Bool) :
    let scaled := RationalBinary.scaleByPowerOfTwo value.num.natAbs value.den (-quantum)
    let lower := scaled.1 / scaled.2
    (if Format.Internal.roundRationalAwayWithParity mode (value.num < 0)
        (parity lower) (scaled.1 % scaled.2) scaled.2 then lower + 1 else lower) =
      roundedInteger mode (value.num < 0) parity (scaledMagnitude value quantum) := by
  have hd := RationalBinary.scaleByPowerOfTwo_snd_ne_zero
    value.num.natAbs value.den (-quantum) value.den_ne_zero
  dsimp only
  rw [roundRationalAwayWithParity_eq _ _ _ _ _ (Nat.pos_of_ne_zero hd)]
  dsimp only [roundedInteger]
  rw [fraction_scaledMagnitude, floor_scaledMagnitude]

/-- Canonicalizing a zero significand does not change the mathematical rounded value. -/
theorem normalized_toRat (negative : Bool) (significand : Nat) (exponent : Int) :
    (if significand = 0 then Numerics.Dyadic.zero
      else ⟨negative, significand, exponent⟩).toRat =
      signed negative ((significand : Rat) * (2 : Rat) ^ exponent) := by
  cases negative <;> by_cases hz : significand = 0 <;>
    simp [hz, signed, Numerics.Dyadic.toRat, Numerics.Dyadic.signedSignificand,
      Numerics.Dyadic.zero]

/-- Zero is preserved by every mode and every supplied random word. -/
@[simp] theorem roundAt_zero (mode : RoundingMode) (quantum : Int) (parity : Nat → Bool) :
    roundAt mode quantum parity 0 = 0 := by
  simp [roundAt, roundedInteger, scaledMagnitude, signed]

/-- The executable logarithm is characterized by the two consecutive enclosing powers of two. -/
theorem leadingExponent_bounds (value : Rat) (hvalue : value ≠ 0) :
    let leading := RationalBinary.floorLog2 value.num.natAbs value.den
    (2 : Rat) ^ leading ≤ |value| ∧ |value| < (2 : Rat) ^ (leading + 1) := by
  have hn : value.num.natAbs ≠ 0 := by
    simpa only [Int.natAbs_ne_zero] using Rat.num_ne_zero.mpr hvalue
  have h := BinaryInterchange.Model.floorLog2_bounds
    value.num.natAbs value.den hn value.den_ne_zero
  simp only [BinaryInterchange.Model.bpow, Flocq.bpow, binaryRadix,
    Radix.toReal] at h
  dsimp only
  rw [magnitude_eq_ratio]
  constructor
  · apply (Rat.cast_le (K := Real)).mp
    push_cast
    exact h.1
  · apply (Rat.cast_lt (K := Real)).mp
    push_cast
    exact h.2

end RationalRounding

namespace Format

/-- Executable code parity agrees with the report, including precision one and the zero code. -/
theorem lowerCodeIsEven_eq (format : Format) (quantum : Int) (lower : Nat) :
    format.lowerCodeIsEven quantum lower =
      RationalRounding.codeEven format.precision format.exponentBias quantum lower := by
  unfold lowerCodeIsEven RationalRounding.codeEven
  by_cases hp : 1 < format.precision
  · simp only [hp, if_pos]
    rfl
  · simp only [hp]
    by_cases hz : lower = 0 <;> simp [hz]

/-- Every finite rational runtime result is the report's exact precision-rounding formula. -/
theorem roundFiniteRatToPrecision_toRat (format : Format) (mode : RoundingMode) (value : Rat) :
    (format.roundFiniteRatToPrecision mode value).toRat =
      RationalRounding.round format.precision format.exponentBias mode value := by
  by_cases hz : value = 0
  · simp [hz, roundFiniteRatToPrecision, RationalRounding.round]
  have hn : value.num.natAbs ≠ 0 := by
    simpa only [Int.natAbs_ne_zero] using Rat.num_ne_zero.mpr hz
  simp only [roundFiniteRatToPrecision, beq_iff_eq, hn, if_false]
  rw [RationalRounding.normalized_toRat]
  simp only [Internal.roundRationalAway, lowerCodeIsEven_eq]
  rw [RationalRounding.select_eq_roundedInteger]
  rfl

end Format
end FloatLib.Floats.Formats.P3109
