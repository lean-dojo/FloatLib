/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Real
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient
import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Predicates
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic

/-!
# Agreement between the policy engine and nearest-away dyadic rounding

`Policy.roundDyadic` sends a nearest-away policy with native overflow and gradual underflow to
the dyadic rounder `roundDyadicNearestAway` through `Internal.Directed.roundDyadic .nearestAway`.
This file proves the general rational engine `roundDyadicGeneral` equal to that rounder on every
descriptor, so the two implementations agree and the dispatch changes no result. The packed
results agree, including signed zero, subnormal carry, ties at the overflow midpoint, and
finite-only overflow words. `Rounding.Policy.Agreement` uses the theorem for its nearest-away
case.

The proof compares the engine with itself under two other rounding modes.
`roundRatGeneralOfDenNeZero_congr_rounding` says that the engine depends on its rounding mode only
through the overflow direction, the decision for values below half the least subnormal, and the
one quotient that the input's leading exponent selects. Off a grid tie that quotient is not a tie
either, so nearest-away and nearest-even choose the same integer and the nearest-even agreement of
`Rounding.Policy.ScaledDyadic` applies. At a grid tie the value is never below half the least
subnormal, nearest-away takes the ceiling of the tied quotient, and the engine agrees with the
directed policy that rounds the magnitude up, whose packed result is `roundDyadicMagnitudeUp`.

For status, `rationalNearestAwayOverflowsScaled_eq_true_iff` and
`rationalIsTinyAfterRoundingScaled_nearest_eq` give the classifiers their real meaning, and
`isTinyAfterRounding_roundRatGeneralOfDenNeZero_nearestAway_eq_false` shows that the engine, which
`Policy.roundRat` uses for nearest-away conversions, never delivers a tiny result at or above
`underflowMidpoint`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

/-! ## Grid ties of exact dyadics -/

/-- A grid tie has a nonzero significand. -/
theorem significand_ne_zero_of_dyadicIsGridTie {fmt : FloatFormat} {value : Numerics.Dyadic}
    (htie : dyadicIsGridTie fmt value = true) : value.significand ≠ 0 := by
  rcases value with ⟨sign, mantissa, exponent⟩
  rintro (rfl : mantissa = 0)
  simp at htie

/-- A dyadic below half the least subnormal is never a grid tie: its guard bit is clear. -/
theorem dyadicIsGridTie_eq_false_of_far_below (fmt : FloatFormat) (value : Numerics.Dyadic)
    (hfar : (value.significand.log2 : Int) + value.exponent + 1 < fmt.minSubnormalExponent) :
    dyadicIsGridTie fmt value = false := by
  have hgrid :
      max fmt.minSubnormalExponent
          ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth) =
        fmt.minSubnormalExponent := by
    apply max_eq_left
    omega
  unfold dyadicIsGridTie
  rw [hgrid]
  split
  · rfl
  · rename_i shift hshift
    rw [Int.negSucc_eq] at hshift
    have hlog : value.significand.log2 + 1 ≤ shift := by
      omega
    have hbits : value.significand < 2 ^ shift :=
      (Nat.lt_log2_self (n := value.significand)).trans_le
        (Nat.pow_le_pow_right (by decide) hlog)
    simp [shiftRightIsTie, Nat.testBit_eq_false_of_lt hbits]

/--
A dyadic scaled to a target exponent gives an exact quotient tie exactly when the bits below that
exponent are one half of its unit.
-/
private theorem two_mul_mod_scaleByPowerOfTwo_dyadic_iff (mantissa : Nat)
    (exponent targetExponent : Int) :
    2 * ((Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 (exponent - targetExponent)).1 %
        (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 (exponent - targetExponent)).2) =
        (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 (exponent - targetExponent)).2 ↔
      match exponent - targetExponent with
      | .ofNat _ => False
      | .negSucc shift => shiftRightIsTie mantissa (shift + 1) = true := by
  cases exponent - targetExponent with
  | ofNat shift =>
      simp [Numerics.RationalBinary.scaleByPowerOfTwo]
  | negSucc shift =>
      simp only [Numerics.RationalBinary.scaleByPowerOfTwo_negSucc, Nat.shiftLeft_eq',
        Nat.one_shiftLeft, shiftRightIsTie_eq_true_iff, Nat.add_sub_cancel]
      have hpow : 2 ^ (shift + 1) = 2 * 2 ^ shift := by
        rw [pow_succ, Nat.mul_comm]
      rw [hpow]
      omega

/-- A dyadic is a grid tie exactly when it is a quotient tie scaled to its grid exponent. -/
theorem dyadicIsGridTie_eq_true_iff (fmt : FloatFormat) (value : Numerics.Dyadic) :
    dyadicIsGridTie fmt value = true ↔
      2 * ((Numerics.RationalBinary.scaleByPowerOfTwo value.significand 1
            (value.exponent - max fmt.minSubnormalExponent
              ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth))).1 %
          (Numerics.RationalBinary.scaleByPowerOfTwo value.significand 1
            (value.exponent - max fmt.minSubnormalExponent
              ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth))).2) =
        (Numerics.RationalBinary.scaleByPowerOfTwo value.significand 1
          (value.exponent - max fmt.minSubnormalExponent
            ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth))).2 := by
  rw [two_mul_mod_scaleByPowerOfTwo_dyadic_iff]
  unfold dyadicIsGridTie
  generalize value.exponent - max fmt.minSubnormalExponent
    ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth) = difference
  cases difference <;> simp

namespace Policy

/-! ## Quotient rounding -/

/-- Policy nearest-away quotient rounding is `roundQuotient .nearestAway` for a nonzero divisor. -/
theorem roundQuot_nearestAway_eq_roundQuotient (sign : Bool)
    (entropy numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    roundQuot .nearestAway sign entropy numerator denominator =
      roundQuotient .nearestAway numerator denominator := by
  rw [roundQuotient_nearestAway_eq_div_add numerator denominator hdenominator]
  have hpos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
  unfold roundQuot
  simp only
  by_cases hremainder : numerator % denominator = 0
  · simp [hremainder, Nat.not_le.mpr hpos]
  · by_cases hbelow : 2 * (numerator % denominator) < denominator
    · simp [hremainder, hbelow, Nat.not_le.mpr hbelow]
    · simp [hremainder, hbelow, Nat.le_of_not_lt hbelow]

/-- Off an exact tie, policy nearest-away and nearest-even quotient rounding agree. -/
theorem roundQuot_nearestAway_eq_nearest_of_ne (sign : Bool)
    (entropy entropy' numerator denominator : Nat)
    (htie : 2 * (numerator % denominator) ≠ denominator) :
    roundQuot .nearestAway sign entropy numerator denominator =
      roundQuot .nearest sign entropy' numerator denominator := by
  unfold roundQuot
  simp only
  by_cases hremainder : numerator % denominator = 0
  · simp [hremainder]
  · by_cases hbelow : 2 * (numerator % denominator) < denominator
    · simp [hremainder, hbelow]
    · have habove : denominator < 2 * (numerator % denominator) := by
        omega
      simp [hremainder, hbelow, habove]

/-- At an exact tie, policy nearest-away quotient rounding takes the ceiling. -/
theorem roundQuot_nearestAway_eq_roundQuotDirected_of_tie (sign : Bool)
    (entropy numerator denominator : Nat) (hdenominator : denominator ≠ 0)
    (htie : 2 * (numerator % denominator) = denominator) :
    roundQuot .nearestAway sign entropy numerator denominator =
      roundQuotDirected true numerator denominator := by
  have hremainder : numerator % denominator ≠ 0 := by
    omega
  have hbelow : ¬2 * (numerator % denominator) < denominator := by
    omega
  simp [roundQuot, roundQuotDirected, roundQuotient_up_eq, hdenominator, hremainder, hbelow]

/-! ## Rounding-mode congruence of the general engine -/

/--
The general engine depends on its rounding mode only through the overflow direction, the decision
below half the least subnormal, and the one quotient that it rounds.

For a fixed input, two rounding modes give the same packed result when they agree on
`overflowRoundsMagnitudeUp`, on `tinyRoundsMagnitudeUp?` for a value below half the least
subnormal, and on `roundQuot` at the quotient that the leading exponent selects: the subnormal
alignment below the normal range and the significand quotient within it. The entropy may differ
as well.
-/
theorem roundRatGeneralOfDenNeZero_congr_rounding (fmt : FloatFormat)
    (overflow : OverflowMode) (underflow : UnderflowMode) (rounding rounding' : RoundingMode)
    (entropy entropy' : Nat) (sign : Bool) (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0)
    (hoverflow :
      overflowRoundsMagnitudeUp rounding sign = overflowRoundsMagnitudeUp rounding' sign)
    (htiny : numerator ≠ 0 →
      Numerics.RationalBinary.floorLog2 numerator denominator + 1 <
        fmt.minSubnormalExponent →
      tinyRoundsMagnitudeUp? rounding sign = tinyRoundsMagnitudeUp? rounding' sign)
    (hsubnormal : numerator ≠ 0 →
      Numerics.RationalBinary.floorLog2 numerator denominator < fmt.minNormalExponent →
      roundQuot rounding sign entropy
          (Nat.shiftLeft numerator (fmt.exponentBias + fmt.fracWidth - 1)) denominator =
        roundQuot rounding' sign entropy'
          (Nat.shiftLeft numerator (fmt.exponentBias + fmt.fracWidth - 1)) denominator)
    (hnormal : numerator ≠ 0 →
      fmt.minNormalExponent ≤ Numerics.RationalBinary.floorLog2 numerator denominator →
      Numerics.RationalBinary.floorLog2 numerator denominator ≤ fmt.maxNormalExponent →
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)
      roundQuot rounding sign entropy scaled.1 scaled.2 =
        roundQuot rounding' sign entropy' scaled.1 scaled.2) :
    roundRatGeneralOfDenNeZero fmt
        { rounding := rounding, overflow := overflow, underflow := underflow }
        entropy sign numerator denominator hdenominator =
      roundRatGeneralOfDenNeZero fmt
        { rounding := rounding', overflow := overflow, underflow := underflow }
        entropy' sign numerator denominator hdenominator := by
  have hresult :
      overflowResult fmt overflow rounding sign = overflowResult fmt overflow rounding' sign := by
    cases overflow <;> simp [overflowResult, hoverflow]
  unfold roundRatGeneralOfDenNeZero
  dsimp only
  rw [hresult]
  congr 1
  by_cases hnumerator : numerator = 0
  · simp [hnumerator]
  simp only [beq_iff_eq, hnumerator, ite_false]
  by_cases hover : Numerics.RationalBinary.floorLog2 numerator denominator > fmt.maxNormalExponent
  · simp only [hover, ite_true]
  simp only [hover, ite_false]
  by_cases hsub : Numerics.RationalBinary.floorLog2 numerator denominator < fmt.minNormalExponent
  · simp only [hsub, ite_true]
    rw [hsubnormal hnumerator hsub]
    by_cases hfar :
        Numerics.RationalBinary.floorLog2 numerator denominator + 1 < fmt.minSubnormalExponent
    · simp only [hfar, ite_true, htiny hnumerator hfar]
    · simp only [hfar, ite_false]
  · simp only [hsub, ite_false]
    exact congrArg
      (packRoundedNormal fmt sign (overflowResult fmt overflow rounding' sign)
        (Numerics.RationalBinary.floorLog2 numerator denominator))
      (hnormal hnumerator (by omega) (by omega))

/-! ## The quotient sites of an exact dyadic -/

/--
At the engine's subnormal quotient, an exact dyadic below the normal range is a quotient tie
exactly when it is a grid tie.
-/
private theorem subnormalQuotient_tie_iff (fmt : FloatFormat) (sign : Bool) (mantissa : Nat)
    (exponent : Int)
    (hsubnormal : (mantissa.log2 : Int) + exponent < fmt.minNormalExponent) :
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
    2 * (Nat.shiftLeft scaled.1 (fmt.exponentBias + fmt.fracWidth - 1) % scaled.2) =
        scaled.2 ↔
      dyadicIsGridTie fmt { negative := sign, significand := mantissa, exponent := exponent } =
        true := by
  dsimp only
  rw [dyadicIsGridTie_eq_true_iff]
  dsimp only
  have hgrid :
      max fmt.minSubnormalExponent ((mantissa.log2 : Int) + exponent - fmt.fracWidth) =
        fmt.minSubnormalExponent := by
    apply max_eq_left
    simp only [FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast] at hsubnormal ⊢
    omega
  rw [hgrid]
  have hcombine :=
    two_mul_mod_scaleByPowerOfTwo_add_iff mantissa 1 exponent
      (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)) (by decide)
  dsimp only at hcombine
  rw [exponent_add_subnormalAlign] at hcombine
  exact hcombine

/--
At the engine's normal quotient, an exact dyadic in the normal range is a quotient tie exactly
when it is a grid tie.
-/
private theorem normalQuotient_tie_iff (fmt : FloatFormat) (sign : Bool) (mantissa : Nat)
    (exponent : Int) (hmantissa : mantissa ≠ 0)
    (hnormal : fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent) :
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
    let shifted :=
      Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
        (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 scaled.1 scaled.2)
    2 * (shifted.1 % shifted.2) = shifted.2 ↔
      dyadicIsGridTie fmt { negative := sign, significand := mantissa, exponent := exponent } =
        true := by
  dsimp only
  have hlog :
      Numerics.RationalBinary.floorLog2
          (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
          (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 =
        Int.ofNat mantissa.log2 + exponent :=
    floorLog2_scaleByPowerOfTwo_den_one mantissa exponent hmantissa
  rw [hlog, dyadicIsGridTie_eq_true_iff]
  dsimp only
  have hgrid :
      max fmt.minSubnormalExponent ((mantissa.log2 : Int) + exponent - fmt.fracWidth) =
        (mantissa.log2 : Int) + exponent - fmt.fracWidth := by
    apply max_eq_right
    simp only [FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast] at hnormal ⊢
    omega
  rw [hgrid]
  have hcombine :=
    two_mul_mod_scaleByPowerOfTwo_add_iff mantissa 1 exponent
      (Int.ofNat fmt.fracWidth - (Int.ofNat mantissa.log2 + exponent)) (by decide)
  dsimp only at hcombine
  rw [show exponent + (Int.ofNat fmt.fracWidth - (Int.ofNat mantissa.log2 + exponent)) =
      exponent - ((mantissa.log2 : Int) + exponent - fmt.fracWidth) by
    simp only [Int.ofNat_eq_natCast]
    omega] at hcombine
  exact hcombine

/-! ## Nearest-away agreement -/

/--
General policy rounding with nearest-away rounding, native overflow, and gradual underflow is the
dyadic nearest-away rounder's complete packed result, on every descriptor.

The entropy argument is irrelevant because nearest-away rounding is deterministic.
-/
theorem roundDyadicGeneral_nearestAway_eq_roundDyadicNearestAway (fmt : FloatFormat)
    (entropy : Nat) (value : Numerics.Dyadic) :
    roundDyadicGeneral fmt
        { rounding := .nearestAway, overflow := .native, underflow := .gradual }
        entropy value =
      roundDyadicNearestAway fmt value := by
  rcases value with ⟨sign, mantissa, exponent⟩
  rw [roundDyadicGeneral_eq_roundRatGeneralOfDenNeZero]
  dsimp only
  have hdenominator :
      (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero mantissa 1 exponent (by decide)
  by_cases htie :
      dyadicIsGridTie fmt { negative := sign, significand := mantissa, exponent := exponent } =
        true
  · have hmantissa : mantissa ≠ 0 := significand_ne_zero_of_dyadicIsGridTie htie
    have hlog :
        Numerics.RationalBinary.floorLog2
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 =
          Int.ofNat mantissa.log2 + exponent :=
      floorLog2_scaleByPowerOfTwo_den_one mantissa exponent hmantissa
    have hnotFar : ¬(Int.ofNat mantissa.log2 + exponent + 1 < fmt.minSubnormalExponent) := by
      intro hfar
      have hfalse := dyadicIsGridTie_eq_false_of_far_below fmt
        { negative := sign, significand := mantissa, exponent := exponent } hfar
      rw [htie] at hfalse
      exact Bool.noConfusion hfalse
    have hsubTie :
        (mantissa.log2 : Int) + exponent < fmt.minNormalExponent →
          2 * (Nat.shiftLeft (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
              (fmt.exponentBias + fmt.fracWidth - 1) %
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2) =
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 :=
      fun hsub => (subnormalQuotient_tie_iff fmt sign mantissa exponent hsub).mpr htie
    have hnormalTie :
        fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent →
          let scaled := Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
          let shifted :=
            Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 scaled.1 scaled.2)
          2 * (shifted.1 % shifted.2) = shifted.2 :=
      fun hnormal => (normalQuotient_tie_iff fmt sign mantissa exponent hmantissa hnormal).mpr htie
    have haway :
        roundRatGeneralOfDenNeZero fmt
            { rounding := .nearestAway, overflow := .native, underflow := .gradual }
            entropy sign
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 hdenominator =
          roundRatGeneralOfDenNeZero fmt
            { rounding := if sign then .down else .up,
              overflow := .native, underflow := .gradual }
            entropy sign
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 hdenominator := by
      apply roundRatGeneralOfDenNeZero_congr_rounding
      · cases sign <;> rfl
      · intro _ hfar
        rw [hlog] at hfar
        exact absurd hfar hnotFar
      · intro _ hsub
        rw [hlog] at hsub
        rw [roundQuot_nearestAway_eq_roundQuotDirected_of_tie _ _ _ _ hdenominator
          (hsubTie hsub)]
        cases sign
        · exact (roundQuot_up_eq_roundQuotDirected false entropy _ _
            hdenominator).symm
        · exact (roundQuot_down_eq_roundQuotDirected true entropy _ _
            hdenominator).symm
      · intro _ hnormal _
        rw [hlog] at hnormal
        have hshiftedDenominator :
            (Numerics.RationalBinary.scaleByPowerOfTwo
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2
              (Int.ofNat fmt.fracWidth -
                Numerics.RationalBinary.floorLog2
                  (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
                  (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2)).2 ≠ 0 :=
          Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero _ _ _ hdenominator
        dsimp only
        rw [roundQuot_nearestAway_eq_roundQuotDirected_of_tie _ _ _ _ hshiftedDenominator
          (hnormalTie hnormal)]
        cases sign
        · exact (roundQuot_up_eq_roundQuotDirected false entropy _ _
            hshiftedDenominator).symm
        · exact (roundQuot_down_eq_roundQuotDirected true entropy _ _
            hshiftedDenominator).symm
    rw [haway]
    have hdirected :=
      roundRatGeneralOfDenNeZero_directed_dyadic_eq fmt
        (if sign then .down else .up) true sign entropy mantissa exponent
        (by
          intro numerator denominator hden
          cases sign
          · exact roundQuot_up_eq_roundQuotDirected _ _ _ _ hden
          · exact roundQuot_down_eq_roundQuotDirected _ _ _ _ hden)
        (by cases sign <;> rfl) (by cases sign <;> rfl)
    dsimp only at hdirected
    rw [hdirected, roundRatMagnitudeDirectedScaled_dyadic_eq]
    simp [roundDyadicNearestAway, htie, roundDyadicAway, hmantissa]
  · have hnotTie :
        dyadicIsGridTie fmt { negative := sign, significand := mantissa, exponent := exponent } =
          false :=
      Bool.eq_false_of_not_eq_true htie
    have heven :
        roundRatGeneralOfDenNeZero fmt
            { rounding := .nearestAway, overflow := .native, underflow := .gradual }
            entropy sign
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 hdenominator =
          roundRatGeneralOfDenNeZero fmt
            { rounding := .nearest, overflow := .native, underflow := .gradual }
            entropy sign
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent).2 hdenominator := by
      apply roundRatGeneralOfDenNeZero_congr_rounding
      · rfl
      · intro _ _
        rfl
      · intro hnumerator hsub
        have hmantissa : mantissa ≠ 0 := by
          intro hzero
          subst hzero
          exact hnumerator (by simp [Numerics.RationalBinary.scaleByPowerOfTwo]; split <;> rfl)
        rw [floorLog2_scaleByPowerOfTwo_den_one mantissa exponent hmantissa] at hsub
        apply roundQuot_nearestAway_eq_nearest_of_ne
        intro hsiteTie
        exact htie ((subnormalQuotient_tie_iff fmt sign mantissa exponent hsub).mp hsiteTie)
      · intro hnumerator hnormal _
        have hmantissa : mantissa ≠ 0 := by
          intro hzero
          subst hzero
          exact hnumerator (by simp [Numerics.RationalBinary.scaleByPowerOfTwo]; split <;> rfl)
        rw [floorLog2_scaleByPowerOfTwo_den_one mantissa exponent hmantissa] at hnormal
        dsimp only
        apply roundQuot_nearestAway_eq_nearest_of_ne
        intro hsiteTie
        exact htie ((normalQuotient_tie_iff fmt sign mantissa exponent hmantissa hnormal).mp
          hsiteTie)
    rw [heven]
    rw [roundDyadicNearestAway, ite_eq_right htie]
    exact (roundRatGeneralOfDenNeZero_nearest_dyadic_eq fmt sign entropy mantissa
      exponent).trans (roundDyadicGeneral_eq_roundDyadic fmt _)

end Policy

/-! ## Status classifiers -/

/-- The nonnegative scaled-rational comparison with a positive dyadic is the real comparison. -/
private theorem compareDyadicScaled?_false_eq_some_compare (numerator denominator : Nat)
    (value : Numerics.Dyadic) (hdenominator : denominator ≠ 0) (hsign : value.negative = false)
    (hsignificand : value.significand ≠ 0) :
    Numerics.RationalBinary.compareDyadicScaled? false numerator denominator 0 value =
      some (compare ((numerator : ℝ) / denominator) value.toReal) := by
  rw [compareDyadicScaled?_false_eq_compare numerator denominator 0 value hdenominator hsign
    hsignificand]
  simp [scaledRatToReal]

/--
Nearest-away overflow of a nonnegative scaled rational is reaching the top finite midpoint: the
midpoint itself overflows.
-/
theorem rationalNearestAwayOverflowsScaled_eq_true_iff (fmt : FloatFormat)
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    rationalNearestAwayOverflowsScaled fmt numerator denominator 0 = true ↔
      (overflowMidpoint fmt).toReal ≤ (numerator : ℝ) / denominator := by
  unfold rationalNearestAwayOverflowsScaled
  rw [compareDyadicScaled?_false_eq_some_compare numerator denominator _ hdenominator rfl
    (by simp [overflowMidpoint])]
  cases hcompare : compare ((numerator : ℝ) / denominator) (overflowMidpoint fmt).toReal
  · simp only [Bool.false_eq_true, false_iff, not_le]
    exact compare_lt_iff_lt.mp hcompare
  · simp only [true_iff]
    exact (compare_eq_iff_eq.mp hcompare).symm.le
  · simp only [true_iff]
    exact (compare_gt_iff_gt.mp hcompare).le

/--
With the nearest-even boundary, the tininess classifier for a nonnegative rational is a tiny
delivered result or a magnitude strictly below `underflowMidpoint`. The midpoint itself is not
tiny because nearest rounding takes it up to the smallest normal value.
-/
theorem rationalIsTinyAfterRoundingScaled_nearest_eq {fmt : FloatFormat} (sign : Bool)
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) (rounded : Model fmt) :
    rationalIsTinyAfterRoundingScaled fmt .nearest sign numerator denominator 0 rounded =
      (isTinyAfterRounding rounded ||
        decide ((numerator : ℝ) / denominator < (underflowMidpoint fmt).toReal)) := by
  have hsignificand : (underflowMidpoint fmt).significand ≠ 0 := by
    have := Nat.two_pow_pos fmt.fracWidth
    simp only [underflowMidpoint, pow2_eq_two_pow]
    omega
  simp only [rationalIsTinyAfterRoundingScaled]
  rw [compareDyadicScaled?_false_eq_some_compare numerator denominator _ hdenominator rfl
    hsignificand]
  cases isTinyAfterRounding rounded
  · cases hcompare : compare ((numerator : ℝ) / denominator) (underflowMidpoint fmt).toReal
    · simp [compare_lt_iff_lt.mp hcompare]
    · simp [IEEERoundingMode.roundsAwayFromZero, (compare_eq_iff_eq.mp hcompare).ge]
    · simp [(compare_gt_iff_gt.mp hcompare).le]
  · simp

/-! ## Tininess of the nearest-away engine result -/

/-- A packed field tuple with a nonzero in-range exponent field is not tiny. -/
private theorem isTinyAfterRounding_ofFields_eq_false (fmt : FloatFormat) (sign : Bool)
    (exponent fraction : Nat) (hpos : 0 < exponent) (hlt : exponent < 2 ^ fmt.expWidth) :
    isTinyAfterRounding (ofFields fmt sign exponent fraction) = false := by
  simp [isTinyAfterRounding, expField_ofFields_of_lt fmt sign exponent fraction hlt,
    Nat.ne_of_gt hpos]

/-- The largest finite value is not tiny. -/
private theorem isTinyAfterRounding_maxFinite (fmt : FloatFormat) (sign : Bool) :
    isTinyAfterRounding (maxFinite fmt sign) = false :=
  isTinyAfterRounding_ofFields_eq_false fmt sign _ _ fmt.maxFiniteExpField_pos
    fmt.maxFiniteExpField_lt_two_pow

/-- The native overflow value is infinite, a NaN, or the largest finite value, never tiny. -/
private theorem isTinyAfterRounding_nativeOverflow (fmt : FloatFormat) (sign : Bool) :
    isTinyAfterRounding (nativeOverflow fmt sign) = false := by
  cases hencoding : fmt.encoding with
  | ieee =>
      have hinfinity : fmt.supportsInfinity = true := by
        simp [FloatFormat.supportsInfinity, hencoding]
      cases sign <;>
        simp [isTinyAfterRounding, nativeOverflow, hencoding, isFinite_posInf fmt hinfinity,
          isFinite_negInf fmt hinfinity]
  | finiteMaxNaN =>
      have hpos := fmt.expAllOnesNat_pos
      have hlt : fmt.expAllOnesNat < 2 ^ fmt.expWidth := by
        have := Nat.two_pow_pos fmt.expWidth
        simp only [FloatFormat.expAllOnesNat]
        omega
      simp only [nativeOverflow, hencoding, propagatedNaN]
      exact isTinyAfterRounding_ofFields_eq_false fmt sign _ _ hpos hlt
  | finiteUnsignedZero =>
      simp [isTinyAfterRounding, nativeOverflow, hencoding, invalidResult, isFinite, isNaN,
        negZero, ofBits]
  | finite =>
      simp only [nativeOverflow, hencoding]
      exact isTinyAfterRounding_maxFinite fmt sign

/-- Nearest-away overflow, saturating or native, is never tiny. -/
private theorem isTinyAfterRounding_overflowResult_nearestAway (fmt : FloatFormat)
    (overflow : OverflowMode) (sign : Bool) :
    isTinyAfterRounding (Policy.overflowResult fmt overflow .nearestAway sign) = false := by
  cases overflow
  · exact isTinyAfterRounding_nativeOverflow fmt sign
  · exact isTinyAfterRounding_maxFinite fmt sign

/-- Packing a significand at or above the normal range never gives a tiny result. -/
private theorem isTinyAfterRounding_packRoundedNormal (fmt : FloatFormat) (sign : Bool)
    (overflow : Model fmt) (totalExponent : Int) (roundedMantissa : Nat)
    (hexponent : fmt.minNormalExponent ≤ totalExponent)
    (hoverflow : isTinyAfterRounding overflow = false) :
    isTinyAfterRounding (packRoundedNormal fmt sign overflow totalExponent roundedMantissa) =
      false := by
  have hlt := fmt.maxFiniteExpField_lt_two_pow
  have hmaximum : fmt.maxNormalExponent =
      Int.ofNat fmt.maxFiniteExpField - Int.ofNat fmt.exponentBias := rfl
  simp only [FloatFormat.minNormalExponent] at hexponent
  unfold packRoundedNormal
  dsimp only
  split_ifs <;> first
    | exact hoverflow
    | apply isTinyAfterRounding_ofFields_eq_false <;>
        simp only [Int.ofNat_eq_natCast] at * <;> omega

/-- A subnormal significand that reaches `2^fracWidth` packs the smallest normal value. -/
private theorem isTinyAfterRounding_packRoundedSubnormal_of_le (fmt : FloatFormat)
    (sign : Bool) (zeroResult : Model fmt) (fraction : Nat)
    (hfraction : pow2 fmt.fracWidth ≤ fraction) :
    isTinyAfterRounding (packRoundedSubnormal fmt sign zeroResult fraction) = false := by
  have hpos : 0 < pow2 fmt.fracWidth := by
    simp [pow2_eq_two_pow]
  have hne : fraction ≠ 0 := by
    omega
  have hone : 1 < 2 ^ fmt.expWidth := Nat.one_lt_two_pow (by have := fmt.expWidth_ge_two; omega)
  simp only [packRoundedSubnormal, beq_iff_eq, hne, ite_false, ge_iff_le, hfraction, ite_true]
  exact isTinyAfterRounding_ofFields_eq_false fmt sign 1 0 (by decide) hone

/-- Flush-to-zero leaves a result that is not tiny unchanged. -/
private theorem isTinyAfterRounding_applyUnderflow (fmt : FloatFormat) (mode : UnderflowMode)
    (x : Model fmt) (hx : isTinyAfterRounding x = false) :
    isTinyAfterRounding (Policy.applyUnderflow fmt mode x) = false := by
  cases mode with
  | gradual => exact hx
  | flushToZero =>
      have hsubnormal : isSubnormal x = false := by
        cases hcase : isSubnormal x
        · rfl
        · have hfinite := isFinite_of_isSubnormal hcase
          have hexponent : expField x = 0 := by
            simp only [isSubnormal, Bool.and_eq_true, beq_iff_eq] at hcase
            exact hcase.1
          simp [isTinyAfterRounding, hfinite, hexponent] at hx
      simp [Policy.applyUnderflow, hsubnormal, hx]

/-- The underflow midpoint is the real number `(4 * 2^fracWidth - 1) * 2^(minSubnormal - 2)`. -/
private theorem toReal_underflowMidpoint (fmt : FloatFormat) :
    (underflowMidpoint fmt).toReal =
      (4 * (2 : ℝ) ^ fmt.fracWidth - 1) * (2 : ℝ) ^ (fmt.minSubnormalExponent - 2) := by
  have hpow : 1 ≤ 4 * 2 ^ fmt.fracWidth := by
    have := Nat.two_pow_pos fmt.fracWidth
    omega
  simp [underflowMidpoint, pow2_eq_two_pow, Nat.cast_sub hpow]

namespace Policy

/--
Nearest-away rounding in the general engine never delivers a tiny result for an exact quotient at
or above `underflowMidpoint`, under every overflow and underflow policy.

At that magnitude the unbounded-exponent rounding already reaches the smallest normal value. The
engine then delivers the smallest normal value, a larger normal value, or an overflow value, and
flush-to-zero leaves each of them unchanged.
-/
theorem isTinyAfterRounding_roundRatGeneralOfDenNeZero_nearestAway_eq_false (fmt : FloatFormat)
    (overflow : OverflowMode) (underflow : UnderflowMode) (entropy : Nat) (sign : Bool)
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0)
    (hbound : (underflowMidpoint fmt).toReal ≤ (numerator : ℝ) / denominator) :
    isTinyAfterRounding
        (roundRatGeneralOfDenNeZero fmt
          { rounding := .nearestAway, overflow := overflow, underflow := underflow }
          entropy sign numerator denominator hdenominator) = false := by
  have hdenominatorReal : (0 : ℝ) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hmidpointPos : (0 : ℝ) < (underflowMidpoint fmt).toReal := by
    rw [toReal_underflowMidpoint]
    have hfrac : (1 : ℝ) ≤ (2 : ℝ) ^ fmt.fracWidth := one_le_pow₀ (by norm_num)
    exact mul_pos (by linarith) (zpow_pos (by norm_num) _)
  have hnumerator : numerator ≠ 0 := by
    rintro rfl
    simp at hbound
    linarith
  have hbounds := floorLog2_bounds numerator denominator hnumerator hdenominator
  dsimp only at hbounds
  simp only [bpow, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal] at hbounds
  have hminSubnormal : fmt.minSubnormalExponent =
      fmt.minNormalExponent - (fmt.fracWidth : Int) := by
    simp [FloatFormat.minSubnormalExponent]
  have hlower :
      fmt.minNormalExponent - 1 ≤ Numerics.RationalBinary.floorLog2 numerator denominator := by
    by_contra hsmall
    have hexponent :
        Numerics.RationalBinary.floorLog2 numerator denominator + 1 ≤
          fmt.minNormalExponent - 1 := by
      omega
    have hpowLe : (2 : ℝ) ^ (Numerics.RationalBinary.floorLog2 numerator denominator + 1) ≤
        (2 : ℝ) ^ (fmt.minNormalExponent - 1) :=
      zpow_le_zpow_right₀ (by norm_num) hexponent
    have hmidpointGe : (2 : ℝ) ^ (fmt.minNormalExponent - 1) ≤ (underflowMidpoint fmt).toReal := by
      rw [toReal_underflowMidpoint, hminSubnormal]
      have hsplit : (2 : ℝ) ^ (fmt.minNormalExponent - 1) =
          2 * (2 : ℝ) ^ fmt.fracWidth *
            (2 : ℝ) ^ (fmt.minNormalExponent - (fmt.fracWidth : Int) - 2) := by
        rw [show fmt.minNormalExponent - 1 =
            1 + (fmt.fracWidth : Int) + (fmt.minNormalExponent - (fmt.fracWidth : Int) - 2) by
          ring]
        rw [zpow_add₀ (by norm_num), zpow_add₀ (by norm_num), zpow_one, zpow_natCast]
      rw [hsplit]
      have hfrac : (1 : ℝ) ≤ (2 : ℝ) ^ fmt.fracWidth := one_le_pow₀ (by norm_num)
      have hscale : (0 : ℝ) < (2 : ℝ) ^ (fmt.minNormalExponent - (fmt.fracWidth : Int) - 2) :=
        zpow_pos (by norm_num) _
      nlinarith
    linarith [hbounds.2]
  unfold roundRatGeneralOfDenNeZero
  dsimp only
  apply isTinyAfterRounding_applyUnderflow
  simp only [beq_iff_eq, hnumerator, ite_false]
  by_cases hover :
      Numerics.RationalBinary.floorLog2 numerator denominator > fmt.maxNormalExponent
  · simp only [hover, ite_true]
    exact isTinyAfterRounding_overflowResult_nearestAway fmt overflow sign
  simp only [hover, ite_false]
  by_cases hsub :
      Numerics.RationalBinary.floorLog2 numerator denominator < fmt.minNormalExponent
  · have hnotFar :
        ¬(Numerics.RationalBinary.floorLog2 numerator denominator + 1 <
          fmt.minSubnormalExponent) := by
      have := fmt.fracWidth_pos
      omega
    simp only [hsub, ite_true, hnotFar, ite_false]
    apply isTinyAfterRounding_packRoundedSubnormal_of_le
    have hshiftedDenominator : denominator ≠ 0 := hdenominator
    rw [roundQuot_nearestAway_eq_roundQuotient _ _ _ _ hshiftedDenominator,
      Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow2_eq_two_pow]
    have hfracPos : 1 ≤ 2 ^ fmt.fracWidth := Nat.one_le_two_pow
    have hcarry := (lt_roundQuotient_nearestAway_iff (2 ^ fmt.fracWidth - 1)
      (numerator * 2 ^ (fmt.exponentBias + fmt.fracWidth - 1)) denominator hdenominator).mpr
    suffices hneeded :
        (2 * (2 ^ fmt.fracWidth - 1) + 1) * denominator ≤
          2 * (numerator * 2 ^ (fmt.exponentBias + fmt.fracWidth - 1)) by
      have := hcarry hneeded
      omega
    have halign : ((fmt.exponentBias + fmt.fracWidth - 1 : Nat) : Int) =
        -fmt.minSubnormalExponent := by
      have := fmt.exponentBias_pos
      simp only [FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
        Int.ofNat_eq_natCast]
      omega
    have hscaled : (4 * (2 : ℝ) ^ fmt.fracWidth - 1) * denominator ≤
        4 * (numerator * (2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1)) := by
      rw [toReal_underflowMidpoint, le_div_iff₀ hdenominatorReal] at hbound
      have hpowPos : (0 : ℝ) < (2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1) := by
        positivity
      have hcancel : (2 : ℝ) ^ (fmt.minSubnormalExponent - 2) *
          (2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1) * 4 = 1 := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num), halign]
        rw [show fmt.minSubnormalExponent - 2 + -fmt.minSubnormalExponent = -2 by ring]
        norm_num
      have hmul := mul_le_mul_of_nonneg_right hbound
        (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1) * 4)
      calc (4 * (2 : ℝ) ^ fmt.fracWidth - 1) * denominator =
            (4 * (2 : ℝ) ^ fmt.fracWidth - 1) * denominator * 1 := by
            ring
        _ = (4 * (2 : ℝ) ^ fmt.fracWidth - 1) * denominator *
              ((2 : ℝ) ^ (fmt.minSubnormalExponent - 2) *
                (2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1) * 4) := by
            rw [hcancel]
        _ = (4 * (2 : ℝ) ^ fmt.fracWidth - 1) * (2 : ℝ) ^ (fmt.minSubnormalExponent - 2) *
              denominator * ((2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1) * 4) := by
            ring
        _ ≤ numerator * ((2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1) * 4) := hmul
        _ = 4 * (numerator * (2 : ℝ) ^ (fmt.exponentBias + fmt.fracWidth - 1)) := by
            ring
    have hneededReal : ((2 * (2 ^ fmt.fracWidth - 1) + 1 : Nat) : ℝ) * denominator ≤
        ((2 * (numerator * 2 ^ (fmt.exponentBias + fmt.fracWidth - 1)) : Nat) : ℝ) := by
      have hcast : ((2 * (2 ^ fmt.fracWidth - 1) + 1 : Nat) : ℝ) =
          2 * (2 : ℝ) ^ fmt.fracWidth - 1 := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hfracPos]
        push_cast
        ring
      rw [hcast]
      push_cast
      nlinarith
    exact_mod_cast hneededReal
  · simp only [hsub, ite_false]
    exact isTinyAfterRounding_packRoundedNormal fmt sign _ _ _ (by omega)
      (isTinyAfterRounding_overflowResult_nearestAway fmt overflow sign)

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
