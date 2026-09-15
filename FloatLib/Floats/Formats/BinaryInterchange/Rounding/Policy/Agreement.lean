/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Dyadic.Core.Proof
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.NearestEven
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Quotient
import FloatLib.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime

/-!
# Agreement between policy and directed dyadic rounding

`roundDyadicGeneral` and `roundDyadicWithRounding` are independent executable algorithms. The
first embeds a dyadic into the rational policy engine; the second uses dedicated shift-based
dyadic packers. This file proves that their complete packed results agree for each
`IEEERoundingMode` when overflow is native and underflow is gradual. The proof includes signed zero,
subnormal carry, custom exponent bias, finite-only encodings, and native overflow words; it is not
merely an equality of real denotations.

The ordinary `roundDyadic` entry point dispatches recognized IEEE policies to the directed engine.
Nearest-away, stochastic, saturating, and flush-to-zero policies remain specified by the general
policy implementation.

-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

namespace Policy

/-- The policy nearest-even quotient is the shared nearest-even quotient primitive. -/
private theorem roundQuot_nearestEven_eq_roundQuotientEven
    (sign : Bool) (entropy numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    roundQuot .nearestEven sign entropy numerator denominator =
      roundQuotientEven numerator denominator := by
  unfold roundQuot roundQuotientEven
  simp only
  by_cases hremainder : numerator % denominator = 0
  · have hdenominatorPos : 0 < denominator :=
      Nat.pos_of_ne_zero hdenominator
    simp [hremainder, hdenominatorPos]
  · have htwicePos : 0 < 2 * (numerator % denominator) := by
      omega
    simp [hremainder]

/-- Policy truncation is the lower directed quotient primitive. -/
private theorem roundQuot_towardZero_eq_roundQuotDirected
    (sign : Bool) (entropy numerator denominator : Nat) :
    roundQuot .towardZero sign entropy numerator denominator =
      roundQuotDirected false numerator denominator := by
  simp [roundQuot, roundQuotDirected]

/-- Positive-direction policy rounding selects floor or ceiling from the encoded sign. -/
private theorem roundQuot_towardPositive_eq_roundQuotDirected
    (sign : Bool) (entropy numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    roundQuot .towardPositive sign entropy numerator denominator =
      roundQuotDirected (!sign) numerator denominator := by
  cases sign <;>
    simp [roundQuot, roundQuotDirected, quotCeil, hdenominator]

/-- Negative-direction policy rounding selects floor or ceiling from the encoded sign. -/
private theorem roundQuot_towardNegative_eq_roundQuotDirected
    (sign : Bool) (entropy numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    roundQuot .towardNegative sign entropy numerator denominator =
      roundQuotDirected sign numerator denominator := by
  cases sign <;>
    simp [roundQuot, roundQuotDirected, quotCeil, hdenominator]

/-- A positive natural number has the expected floor logarithm when viewed as a quotient by one. -/
private theorem floorLog2_den_one (mantissa : Nat) (hmantissa : mantissa ≠ 0) :
    Numerics.RationalBinary.floorLog2 mantissa 1 =
      Int.ofNat mantissa.log2 := by
  apply floorLog2_eq_of_bounds mantissa 1 (Int.ofNat mantissa.log2)
    hmantissa (by decide)
  · rw [bpow_ofNat]
    norm_num
    exact_mod_cast pow2_log2_le hmantissa
  · rw [show Int.ofNat mantissa.log2 + 1 =
        Int.ofNat (mantissa.log2 + 1) by simp, bpow_ofNat]
    norm_num
    exact_mod_cast lt_pow2_log2_add_one hmantissa

/-- Absorbing a dyadic exponent into a quotient adds that exponent to its leading bit. -/
private theorem floorLog2_dyadicScale
    (mantissa : Nat) (exponent : Int) (hmantissa : mantissa ≠ 0) :
    let scaled := Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
    Numerics.RationalBinary.floorLog2 scaled.1 scaled.2 =
      Int.ofNat mantissa.log2 + exponent := by
  dsimp only
  rw [floorLog2_scaleByPowerOfTwo mantissa 1 exponent hmantissa (by decide)]
  rw [floorLog2_den_one mantissa hmantissa]

/--
Nearest-even quotient rounding of an exact dyadic on a target grid is the shared dyadic shift
primitive.
-/
private theorem roundQuotientEven_scaledDyadic_eq
    (mantissa : Nat) (exponent targetExponent : Int) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        mantissa 1 (exponent - targetExponent)
    roundQuotientEven scaled.1 scaled.2 =
      roundMantissaAtExponentEven mantissa exponent targetExponent := by
  dsimp only
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo
      mantissa 1 (exponent - targetExponent)
  have hdenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      mantissa 1 (exponent - targetExponent) (by decide)
  have hvalue :
      (scaled.1 : Real) / (scaled.2 : Real) =
        (mantissa : Real) * bpow (exponent - targetExponent) := by
    rw [scaleByPowerOfTwo_real]
    simp [scaledRatToReal]
  apply Int.ofNat_inj.mp
  calc
    Int.ofNat (roundQuotientEven scaled.1 scaled.2) =
        FloatLib.Floats.Formats.Flocq.nearestEven
          ((scaled.1 : Real) / (scaled.2 : Real)) :=
      (nearestEven_div_eq_roundQuotientEven scaled.1 scaled.2 hdenominator).symm
    _ = FloatLib.Floats.Formats.Flocq.nearestEven
          ((mantissa : Real) * bpow (exponent - targetExponent)) :=
      congrArg FloatLib.Floats.Formats.Flocq.nearestEven hvalue
    _ = Int.ofNat
          (roundMantissaAtExponentEven mantissa exponent targetExponent) :=
      nearestEven_scaledMagnitude mantissa exponent targetExponent

/--
Floor or ceiling quotient rounding of an exact dyadic on a target grid is the corresponding
directed dyadic shift primitive.
-/
private theorem roundQuotDirected_scaledDyadic_eq
    (roundUp : Bool) (mantissa : Nat) (exponent targetExponent : Int) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo
        mantissa 1 (exponent - targetExponent)
    roundQuotDirected roundUp scaled.1 scaled.2 =
      if roundUp then
        roundMantissaAtExponentUp mantissa exponent targetExponent
      else
        roundMantissaAtExponentDown mantissa exponent targetExponent := by
  dsimp only
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo
      mantissa 1 (exponent - targetExponent)
  have hdenominator : scaled.2 ≠ 0 :=
    Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
      mantissa 1 (exponent - targetExponent) (by decide)
  have hvalue :
      (scaled.1 : Real) / (scaled.2 : Real) =
        (mantissa : Real) * bpow (exponent - targetExponent) := by
    rw [scaleByPowerOfTwo_real]
    simp [scaledRatToReal]
  cases roundUp
  · simp only [roundQuotDirected, Bool.false_eq_true, ite_false]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (scaled.1 / scaled.2) =
          ⌊(scaled.1 : Real) / (scaled.2 : Real)⌋ :=
        (floor_real_nat_div scaled.1 scaled.2).symm
      _ = ⌊(mantissa : Real) * bpow (exponent - targetExponent)⌋ :=
        congrArg Int.floor hvalue
      _ = Int.ofNat
          (roundMantissaAtExponentDown mantissa exponent targetExponent) := by
        simpa [FloatLib.Floats.Formats.Flocq.floorRound] using
          floor_scaledMagnitude mantissa exponent targetExponent
  · simp only [roundQuotDirected, ite_true]
    apply Int.ofNat_inj.mp
    calc
      Int.ofNat (quotCeil scaled.1 scaled.2) =
          ⌈(scaled.1 : Real) / (scaled.2 : Real)⌉ :=
        (ceil_real_nat_div_eq_quotCeil scaled.1 scaled.2 hdenominator).symm
      _ = ⌈(mantissa : Real) * bpow (exponent - targetExponent)⌉ :=
        congrArg Int.ceil hvalue
      _ = Int.ofNat
          (roundMantissaAtExponentUp mantissa exponent targetExponent) := by
        simpa [FloatLib.Floats.Formats.Flocq.ceilRound] using
          ceil_scaledMagnitude mantissa exponent targetExponent

/-- The policy engine's subnormal shift is the distance to the least-subnormal exponent. -/
private theorem exponent_add_subnormalAlign
    (fmt : FloatFormat) (exponent : Int) :
    exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
      exponent - fmt.minSubnormalExponent := by
  have hone : 1 ≤ fmt.exponentBias + fmt.fracWidth := by
    have hbias := fmt.exponentBias_pos
    omega
  have hcast :
      Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
        Int.ofNat (fmt.exponentBias + fmt.fracWidth) - 1 := by
    simpa only [Int.ofNat_eq_natCast, Int.natCast_one] using
      (Int.ofNat_sub hone)
  unfold FloatFormat.minSubnormalExponent FloatFormat.minNormalExponent
  rw [hcast]
  simp only [Int.ofNat_eq_natCast, Int.natCast_add]
  ring

/-- Exponent alignment by nearest-even rounding has the branch form used by the dyadic rounder. -/
private theorem roundMantissaAtExponentEven_eq_match
    (mantissa : Nat) (exponent targetExponent : Int) :
    roundMantissaAtExponentEven mantissa exponent targetExponent =
      match exponent - targetExponent with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => roundShiftRightEven mantissa (shift + 1) := by
  cases hdiff : exponent - targetExponent with
  | ofNat shift =>
      cases shift with
      | zero =>
          have heq : exponent = targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentEven, Numerics.roundShiftRightEven_def, heq]
      | succ shift =>
          have hnot : ¬exponent ≤ targetExponent := by
            norm_num at hdiff
            omega
          simp [roundMantissaAtExponentEven, hnot, hdiff]
  | negSucc shift =>
      have hle : exponent ≤ targetExponent := by
        omega
      have htoNat : (targetExponent - exponent).toNat = shift + 1 := by
        have hpos : targetExponent - exponent = Int.ofNat (shift + 1) := by
          norm_num at hdiff ⊢
          omega
        rw [hpos]
        rfl
      simp [roundMantissaAtExponentEven, hle, htoNat]

/-- A dyadic strictly below half the target unit rounds to zero under nearest-even. -/
private theorem roundMantissaAtExponentEven_eq_zero_of_far_below
    (mantissa : Nat) (exponent targetExponent : Int)
    (hfar : Int.ofNat mantissa.log2 + exponent + 1 < targetExponent) :
    roundMantissaAtExponentEven mantissa exponent targetExponent = 0 := by
  have hlogNonnegative : 0 ≤ Int.ofNat mantissa.log2 :=
    Int.natCast_nonneg mantissa.log2
  have hexponent : exponent < targetExponent := by
    omega
  let shift := (targetExponent - exponent).toNat
  have hshiftInt : (shift : Int) = targetExponent - exponent := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hexponent.le)
  have hshiftPos : 0 < shift := by
    exact Int.pos_iff_toNat_pos.mp (sub_pos.mpr hexponent)
  have hlogShift : mantissa.log2 + 1 ≤ shift - 1 := by
    have hlogShiftInt :
        Int.ofNat (mantissa.log2 + 1) < Int.ofNat shift := by
      change Int.ofNat mantissa.log2 + 1 < (shift : Int)
      rw [hshiftInt]
      omega
    have hlogShiftNat : mantissa.log2 + 1 < shift := by
      exact Int.ofNat_lt.mp hlogShiftInt
    omega
  have hmantissa :
      mantissa < pow2 (shift - 1) := by
    have hpow :
        2 ^ (mantissa.log2 + 1) ≤ 2 ^ (shift - 1) :=
      Nat.pow_le_pow_right (by decide) hlogShift
    simpa [pow2_eq_two_pow] using
      (Nat.lt_log2_self (n := mantissa)).trans_le hpow
  unfold roundMantissaAtExponentEven
  rw [ite_eq_left hexponent.le]
  exact roundShiftRightEven_eq_zero_of_lt_half
    mantissa shift hshiftPos hmantissa

/--
The independent rational policy core and descriptor-general dyadic rounder agree under
nearest-even rounding.
-/
private theorem roundRatGeneralOfDenNeZero_nearestEven_dyadic_eq
    (fmt : FloatFormat) (sign : Bool) (entropy mantissa : Nat) (exponent : Int) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
    roundRatGeneralOfDenNeZero fmt QuantizationPolicy.nearestEven
        entropy sign scaled.1 scaled.2
        (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
          mantissa 1 exponent (by decide)) =
      Model.roundDyadicGeneral fmt
        { negative := sign, significand := mantissa, exponent := exponent } := by
  dsimp only
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
  by_cases hmantissa : mantissa = 0
  · subst mantissa
    cases exponent <;>
      simp [roundRatGeneralOfDenNeZero, Model.roundDyadicGeneral,
        applyUnderflow, Numerics.RationalBinary.scaleByPowerOfTwo,
        QuantizationPolicy.nearestEven]
  · have hscaledNumerator : scaled.1 ≠ 0 :=
      Numerics.RationalBinary.scaleByPowerOfTwo_fst_ne_zero
        mantissa 1 exponent hmantissa
    have hscaledDenominator : scaled.2 ≠ 0 :=
      Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
        mantissa 1 exponent (by decide)
    have hlog :
        Numerics.RationalBinary.floorLog2 scaled.1 scaled.2 =
          Int.ofNat mantissa.log2 + exponent := by
      simpa [scaled] using floorLog2_dyadicScale mantissa exponent hmantissa
    have hsubnormalQuot :
        roundQuot .nearestEven sign entropy
            (Nat.shiftLeft scaled.1 (fmt.exponentBias + fmt.fracWidth - 1))
            scaled.2 =
          roundMantissaAtExponentEven
            mantissa exponent fmt.minSubnormalExponent := by
      calc
        roundQuot .nearestEven sign entropy
            (Nat.shiftLeft scaled.1 (fmt.exponentBias + fmt.fracWidth - 1))
            scaled.2 =
            roundQuotientEven
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 := by
          rw [roundQuot_nearestEven_eq_roundQuotientEven
            sign entropy _ _ hscaledDenominator]
          rfl
        _ = roundQuotientEven
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 := by
          simpa [scaled] using
            roundQuotientEven_scaleByPowerOfTwo_add
              mantissa 1 exponent
                (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))
              (by decide)
        _ = roundMantissaAtExponentEven
              mantissa exponent fmt.minSubnormalExponent := by
          rw [exponent_add_subnormalAlign]
          simpa using
            roundQuotientEven_scaledDyadic_eq
              mantissa exponent fmt.minSubnormalExponent
    have hnormalQuot :
        let shift :=
          Int.ofNat fmt.fracWidth -
            Numerics.RationalBinary.floorLog2 scaled.1 scaled.2
        let shifted :=
          match shift with
          | .ofNat amount => (Nat.shiftLeft scaled.1 amount, scaled.2)
          | .negSucc amount => (scaled.1, Nat.shiftLeft scaled.2 (amount + 1))
        roundQuot .nearestEven sign entropy shifted.1 shifted.2 =
          roundMantissaToLeadingBitEven mantissa fmt.fracWidth := by
      dsimp only
      rw [hlog]
      have hshift :
          exponent +
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent)) =
            Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 := by
        ring
      calc
        roundQuot .nearestEven sign entropy
            (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent))).2 =
            roundQuotientEven
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat fmt.fracWidth -
                  (Int.ofNat mantissa.log2 + exponent))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat fmt.fracWidth -
                  (Int.ofNat mantissa.log2 + exponent))).2 := by
          apply roundQuot_nearestEven_eq_roundQuotientEven
          exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
            scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent))
            hscaledDenominator
        _ = roundQuotientEven
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  (Int.ofNat fmt.fracWidth -
                    (Int.ofNat mantissa.log2 + exponent)))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  (Int.ofNat fmt.fracWidth -
                    (Int.ofNat mantissa.log2 + exponent)))).2 := by
          simpa [scaled] using
            roundQuotientEven_scaleByPowerOfTwo_add
              mantissa 1 exponent
                (Int.ofNat fmt.fracWidth -
                  (Int.ofNat mantissa.log2 + exponent))
              (by decide)
        _ = roundQuotientEven
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 := by
          rw [hshift]
        _ = roundMantissaAtExponentEven mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) := by
          rw [show Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 =
              exponent -
                (Int.ofNat mantissa.log2 + exponent -
                  Int.ofNat fmt.fracWidth) by ring]
          simpa using
            roundQuotientEven_scaledDyadic_eq mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth)
        _ = roundMantissaToLeadingBitEven mantissa fmt.fracWidth :=
            roundMantissaAtExponentEven_eq_roundMantissaToLeadingBitEven
            mantissa fmt.fracWidth exponent
    simp only [scaled] at hscaledNumerator hlog hsubnormalQuot hnormalQuot
    rw [hlog] at hnormalQuot
    simp only [Int.ofNat_eq_natCast] at hnormalQuot
    unfold roundRatGeneralOfDenNeZero Model.roundDyadicGeneral
    simp only [applyUnderflow, QuantizationPolicy.nearestEven,
      beq_iff_eq, hmantissa, hscaledNumerator, ite_false]
    rw [hlog]
    simp only [overflowResult, overflowRoundsMagnitudeUp,
      directedOverflow, ite_true, Int.ofNat_eq_natCast]
    by_cases hoverflow :
        fmt.maxNormalExponent < (mantissa.log2 : Int) + exponent
    · simp only [ite_eq_left hoverflow]
    · simp only [ite_eq_right hoverflow]
      by_cases hsubnormal :
          (mantissa.log2 : Int) + exponent < fmt.minNormalExponent
      · by_cases htiny :
            (mantissa.log2 : Int) + exponent + 1 <
              fmt.minSubnormalExponent
        · have hrounded :=
            roundMantissaAtExponentEven_eq_zero_of_far_below
              mantissa exponent fmt.minSubnormalExponent (by
                simpa only [Int.ofNat_eq_natCast] using htiny)
          have hmatchZero :
              (match exponent - fmt.minSubnormalExponent with
                | .ofNat shift => Nat.shiftLeft mantissa shift
                | .negSucc shift =>
                    roundShiftRightEven mantissa (shift + 1)) = 0 := by
            rw [← roundMantissaAtExponentEven_eq_match]
            exact hrounded
          have hmatchZero' :
              (match exponent - fmt.minSubnormalExponent with
                | .ofNat shift => mantissa <<< shift
                | .negSucc shift =>
                    roundShiftRightEven mantissa (shift + 1)) = 0 :=
            hmatchZero
          simp only [ite_eq_left hsubnormal, ite_eq_left htiny,
            tinyRoundsMagnitudeUp?]
          cases hdiff : exponent - fmt.minSubnormalExponent <;>
            simp_all [packRoundedSubnormal]
        · have hmatch :
              (match exponent - fmt.minSubnormalExponent with
                | .ofNat shift => Nat.shiftLeft mantissa shift
                | .negSucc shift =>
                    roundShiftRightEven mantissa (shift + 1)) =
                roundMantissaAtExponentEven
                  mantissa exponent fmt.minSubnormalExponent :=
            (roundMantissaAtExponentEven_eq_match
              mantissa exponent fmt.minSubnormalExponent).symm
          have hmatch' :
              (match exponent - fmt.minSubnormalExponent with
                | .ofNat shift => mantissa <<< shift
                | .negSucc shift =>
                    roundShiftRightEven mantissa (shift + 1)) =
                roundMantissaAtExponentEven
                  mantissa exponent fmt.minSubnormalExponent :=
            hmatch
          simp only [ite_eq_left hsubnormal, ite_eq_right htiny, hsubnormalQuot]
          exact congrArg (packRoundedSubnormal fmt sign (zero fmt sign)) hmatch'.symm
      · simp only [ite_eq_right hsubnormal]
        exact congrArg
          (packRoundedNormal fmt sign (nativeOverflow fmt sign)
            ((mantissa.log2 : Int) + exponent)) hnormalQuot

/--
For a directed mode, the rational policy core applied to an exact dyadic is the shared directed
rational packer. The two sides retain separate quotient and packing implementations; the proof
identifies their exact binary scalings before comparing branches.
-/
private theorem roundRatGeneralOfDenNeZero_directed_dyadic_eq
    (fmt : FloatFormat) (rounding : RoundingMode) (roundUp sign : Bool)
    (entropy mantissa : Nat) (exponent : Int)
    (hquot :
      ∀ numerator denominator, denominator ≠ 0 →
        roundQuot rounding sign entropy numerator denominator =
          roundQuotDirected roundUp numerator denominator)
    (hoverflow : overflowRoundsMagnitudeUp rounding sign = roundUp)
    (htiny : tinyRoundsMagnitudeUp? rounding sign = some roundUp) :
    let scaled :=
      Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
    roundRatGeneralOfDenNeZero fmt
        { rounding := rounding, overflow := .native, underflow := .gradual }
        entropy sign scaled.1 scaled.2
        (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
          mantissa 1 exponent (by decide)) =
      roundRatMagnitudeDirectedScaled fmt roundUp sign mantissa 1 exponent := by
  dsimp only
  let scaled :=
    Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1 exponent
  by_cases hmantissa : mantissa = 0
  · subst mantissa
    cases exponent <;>
      simp [roundRatGeneralOfDenNeZero, roundRatMagnitudeDirectedScaled,
        applyUnderflow, Numerics.RationalBinary.scaleByPowerOfTwo]
  · have hscaledNumerator : scaled.1 ≠ 0 :=
      Numerics.RationalBinary.scaleByPowerOfTwo_fst_ne_zero
        mantissa 1 exponent hmantissa
    have hscaledDenominator : scaled.2 ≠ 0 :=
      Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
        mantissa 1 exponent (by decide)
    have hlog :
        Numerics.RationalBinary.floorLog2 scaled.1 scaled.2 =
          Int.ofNat mantissa.log2 + exponent := by
      simpa [scaled] using floorLog2_dyadicScale mantissa exponent hmantissa
    have hsubnormalQuot :
        roundQuot rounding sign entropy
            (Nat.shiftLeft scaled.1 (fmt.exponentBias + fmt.fracWidth - 1))
            scaled.2 =
          roundQuotDirected roundUp
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent +
                Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent +
                Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 := by
      calc
        roundQuot rounding sign entropy
            (Nat.shiftLeft scaled.1 (fmt.exponentBias + fmt.fracWidth - 1))
            scaled.2 =
            roundQuotDirected roundUp
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 := by
          rw [hquot _ _ hscaledDenominator]
          rfl
        _ = roundQuotDirected roundUp
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 := by
          simpa [scaled] using
            roundQuotDirected_scaleByPowerOfTwo_add roundUp mantissa 1 exponent
              (Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)) (by decide)
    have hnormalQuot :
        let shift :=
          Int.ofNat fmt.fracWidth -
            Numerics.RationalBinary.floorLog2 scaled.1 scaled.2
        let shifted :=
          match shift with
          | .ofNat amount => (Nat.shiftLeft scaled.1 amount, scaled.2)
          | .negSucc amount => (scaled.1, Nat.shiftLeft scaled.2 (amount + 1))
        roundQuot rounding sign entropy shifted.1 shifted.2 =
          roundQuotDirected roundUp
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 := by
      dsimp only
      rw [hlog]
      have hshift :
          exponent +
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent)) =
            Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 := by
        ring
      calc
        roundQuot rounding sign entropy
            (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent))).2 =
            roundQuotDirected roundUp
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat fmt.fracWidth -
                  (Int.ofNat mantissa.log2 + exponent))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo scaled.1 scaled.2
                (Int.ofNat fmt.fracWidth -
                  (Int.ofNat mantissa.log2 + exponent))).2 := by
          apply hquot
          exact Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
            scaled.1 scaled.2
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent))
            hscaledDenominator
        _ = roundQuotDirected roundUp
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  (Int.ofNat fmt.fracWidth -
                    (Int.ofNat mantissa.log2 + exponent)))).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (exponent +
                  (Int.ofNat fmt.fracWidth -
                    (Int.ofNat mantissa.log2 + exponent)))).2 := by
          simpa [scaled] using
            roundQuotDirected_scaleByPowerOfTwo_add roundUp mantissa 1 exponent
              (Int.ofNat fmt.fracWidth -
                (Int.ofNat mantissa.log2 + exponent)) (by decide)
        _ = roundQuotDirected roundUp
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
                (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
              (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 := by
          rw [hshift]
    simp only [scaled] at hscaledNumerator hlog hsubnormalQuot hnormalQuot
    unfold roundRatGeneralOfDenNeZero roundRatMagnitudeDirectedScaled
    simp only [applyUnderflow, Nat.one_ne_zero, beq_iff_eq, hmantissa,
      hscaledNumerator, ite_false]
    rw [hlog, floorLog2_den_one mantissa hmantissa]
    simp only [overflowResult, hoverflow]
    by_cases hover :
        fmt.maxNormalExponent < Int.ofNat mantissa.log2 + exponent
    · simp only [ite_eq_left hover]
    · simp only [ite_eq_right hover]
      by_cases hunderflow :
          Int.ofNat mantissa.log2 + exponent < fmt.minSubnormalExponent
      · have hsubnormal :
            Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent :=
          hunderflow.trans (minSubnormalExponent_lt_minNormalExponent fmt)
        by_cases htinyExponent :
            Int.ofNat mantissa.log2 + exponent + 1 <
              fmt.minSubnormalExponent
        · cases roundUp
          · rw [ite_eq_left hsubnormal, ite_eq_left htinyExponent, htiny]
            rw [ite_eq_left hunderflow]
            rfl
          · rw [ite_eq_left hsubnormal, ite_eq_left htinyExponent, htiny]
            rw [ite_eq_left hunderflow]
            cases sign <;>
              simp only [ite_true, Bool.false_eq_true, ite_false,
                posMinSubnormal_eq_ofFields,
                negMinSubnormal_eq_ofFields]
        · have halign :=
            exponent_add_subnormalAlign fmt exponent
          have hquotient :
              roundQuot rounding sign entropy
                  (Nat.shiftLeft scaled.1
                    (fmt.exponentBias + fmt.fracWidth - 1))
                  scaled.2 =
                if roundUp then
                  roundMantissaAtExponentUp
                    mantissa exponent fmt.minSubnormalExponent
                else
                  roundMantissaAtExponentDown
                    mantissa exponent fmt.minSubnormalExponent := by
            rw [hsubnormalQuot, halign]
            simpa using
              roundQuotDirected_scaledDyadic_eq
                roundUp mantissa exponent fmt.minSubnormalExponent
          cases roundUp
          · have hrounded :=
              roundMantissaAtExponentDown_eq_zero_of_lt_minSubnormal
                fmt mantissa exponent hmantissa hunderflow
            rw [ite_eq_left hsubnormal, ite_eq_right htinyExponent, hquotient]
            simp only [Bool.false_eq_true, ite_false, hrounded]
            rw [ite_eq_left hunderflow]
            rfl
          · have hrounded :=
              roundMantissaAtExponentUp_eq_one_of_lt_minSubnormal
                fmt mantissa exponent hmantissa hunderflow
            have honeLt : 1 < pow2 fmt.fracWidth := by
              simpa [pow2_eq_two_pow] using
                Nat.one_lt_two_pow (Nat.ne_of_gt fmt.fracWidth_pos)
            rw [ite_eq_left hsubnormal, ite_eq_right htinyExponent, hquotient]
            simp only [packRoundedSubnormal, beq_iff_eq, ite_true, hrounded,
              Nat.one_ne_zero, ite_false, not_le_of_gt honeLt]
            rw [ite_eq_left hunderflow]
            cases sign <;>
              simp only [ite_true, Bool.false_eq_true, ite_false,
                posMinSubnormal_eq_ofFields,
                negMinSubnormal_eq_ofFields]
      · have htinyExponent :
            ¬Int.ofNat mantissa.log2 + exponent + 1 <
              fmt.minSubnormalExponent := by
          omega
        by_cases hsubnormal :
            Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent
        · rw [ite_eq_left hsubnormal, ite_eq_right htinyExponent, hsubnormalQuot]
          rw [ite_eq_right hunderflow, ite_eq_left hsubnormal]
        · rw [hlog] at hnormalQuot
          rw [ite_eq_right hsubnormal]
          rw [ite_eq_right hunderflow, ite_eq_right hsubnormal]
          exact congrArg
            (packRoundedNormal fmt sign (directedOverflow fmt sign roundUp)
              (Int.ofNat mantissa.log2 + exponent))
            hnormalQuot

/--
The rational directed packer specializes to the corresponding dyadic magnitude packer when the
denominator is one.
-/
private theorem roundRatMagnitudeDirectedScaled_dyadic_eq
    (fmt : FloatFormat) (roundUp sign : Bool) (mantissa : Nat) (exponent : Int) :
    roundRatMagnitudeDirectedScaled fmt roundUp sign mantissa 1 exponent =
      if mantissa = 0 then
        zero fmt sign
      else if roundUp then
        roundDyadicMagnitudeUp fmt sign mantissa exponent
      else
        roundDyadicMagnitudeDown fmt sign mantissa exponent := by
  by_cases hmantissa : mantissa = 0
  · simp [roundRatMagnitudeDirectedScaled, hmantissa]
  · rw [ite_eq_right hmantissa]
    have halign :
        exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1) =
          exponent - fmt.minSubnormalExponent :=
      exponent_add_subnormalAlign fmt exponent
    have hsubnormalDown :
        roundQuotDirected false
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 =
          roundMantissaAtExponentDown
            mantissa exponent fmt.minSubnormalExponent := by
      rw [halign]
      simpa using
        roundQuotDirected_scaledDyadic_eq
          false mantissa exponent fmt.minSubnormalExponent
    have hsubnormalUp :
        roundQuotDirected true
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1))).2 =
          roundMantissaAtExponentUp
            mantissa exponent fmt.minSubnormalExponent := by
      rw [halign]
      simpa using
        roundQuotDirected_scaledDyadic_eq
          true mantissa exponent fmt.minSubnormalExponent
    have hnormalDown :
        roundQuotDirected false
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
          roundMantissaToLeadingBitDown mantissa fmt.fracWidth := by
      calc
        roundQuotDirected false
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
            roundMantissaAtExponentDown mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) := by
          rw [show Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 =
              exponent -
                (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) by
            ring]
          simpa using
            roundQuotDirected_scaledDyadic_eq false mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth)
        _ = roundMantissaToLeadingBitDown mantissa fmt.fracWidth :=
          roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown
            mantissa fmt.fracWidth exponent
    have hnormalUp :
        roundQuotDirected true
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
          roundMantissaToLeadingBitUp mantissa fmt.fracWidth := by
      calc
        roundQuotDirected true
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).1
            (Numerics.RationalBinary.scaleByPowerOfTwo mantissa 1
              (Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2)).2 =
            roundMantissaAtExponentUp mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) := by
          rw [show Int.ofNat fmt.fracWidth - Int.ofNat mantissa.log2 =
              exponent -
                (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth) by
            ring]
          simpa using
            roundQuotDirected_scaledDyadic_eq true mantissa exponent
              (Int.ofNat mantissa.log2 + exponent - Int.ofNat fmt.fracWidth)
        _ = roundMantissaToLeadingBitUp mantissa fmt.fracWidth :=
          roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp
            mantissa fmt.fracWidth exponent
    cases roundUp
    · simp only [Bool.false_eq_true, ite_false]
      unfold roundRatMagnitudeDirectedScaled roundDyadicMagnitudeDown
      simp only [Nat.one_ne_zero, beq_iff_eq, hmantissa, ite_false,
        floorLog2_den_one mantissa hmantissa]
      by_cases hoverflow :
          fmt.maxNormalExponent < Int.ofNat mantissa.log2 + exponent
      · simp only [ite_eq_left hoverflow, directedOverflow, Bool.false_eq_true,
          ite_false]
      · simp only [ite_eq_right hoverflow]
        by_cases hunderflow :
            Int.ofNat mantissa.log2 + exponent < fmt.minSubnormalExponent
        · simp only [ite_eq_left hunderflow, Bool.false_eq_true, ite_false]
        · simp only [ite_eq_right hunderflow]
          by_cases hsubnormal :
              Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent
          · have hlt :=
              roundMantissaAtExponentDown_minSubnormal_lt_pow2
                fmt mantissa exponent hsubnormal
            rw [roundMantissaAtExponentDown_eq_match] at hlt
            rw [ite_eq_left hsubnormal, hsubnormalDown,
              roundMantissaAtExponentDown_eq_match]
            simp only [packRoundedSubnormal, beq_iff_eq, not_le_of_gt hlt,
              ite_false, ite_eq_left hsubnormal]
            rfl
          · have hcarry :
                roundMantissaToLeadingBitDown mantissa fmt.fracWidth ≠
                  pow2 (fmt.fracWidth + 1) :=
              ne_of_lt
                (roundMantissaToLeadingBitDown_lt_pow2_succ
                  mantissa fmt.fracWidth)
            rw [ite_eq_right hsubnormal, hnormalDown]
            rw [ite_eq_right hsubnormal]
            unfold packRoundedNormal
            simp only [beq_iff_eq, hcarry, ite_false]
            rw [ite_eq_right hoverflow]
            simp only [roundMantissaToLeadingBitDown, directedOverflow,
              Bool.false_eq_true, ite_false]
            by_cases hleading : fmt.fracWidth ≤ mantissa.log2 <;>
              simp [hleading]
    · simp only [ite_true]
      unfold roundRatMagnitudeDirectedScaled roundDyadicMagnitudeUp
      simp only [Nat.one_ne_zero, beq_iff_eq, hmantissa, ite_false,
        floorLog2_den_one mantissa hmantissa]
      by_cases hoverflow :
          fmt.maxNormalExponent < Int.ofNat mantissa.log2 + exponent
      · simp only [ite_eq_left hoverflow, directedOverflow, ite_true]
      · simp only [ite_eq_right hoverflow]
        by_cases hunderflow :
            Int.ofNat mantissa.log2 + exponent < fmt.minSubnormalExponent
        · simp only [ite_eq_left hunderflow]
          cases sign <;>
            simp only [Bool.false_eq_true, ite_false, ite_true,
              posMinSubnormal_eq_ofFields, negMinSubnormal_eq_ofFields]
        · simp only [ite_eq_right hunderflow]
          by_cases hsubnormal :
              Int.ofNat mantissa.log2 + exponent < fmt.minNormalExponent
          · have hrounded :
                roundMantissaAtExponentUp
                    mantissa exponent fmt.minSubnormalExponent ≠ 0 :=
              roundMantissaAtExponentUp_ne_zero
                mantissa exponent fmt.minSubnormalExponent hmantissa
            have hmatchNe :
                (match exponent - fmt.minSubnormalExponent with
                  | .ofNat shift => Nat.shiftLeft mantissa shift
                  | .negSucc shift => shiftRightCeilPow2 mantissa (shift + 1)) ≠ 0 := by
              intro hzero
              apply hrounded
              rw [roundMantissaAtExponentUp_eq_match]
              exact hzero
            rw [ite_eq_left hsubnormal, hsubnormalUp,
              roundMantissaAtExponentUp_eq_match]
            simp only [packRoundedSubnormal, beq_iff_eq, ite_eq_left hsubnormal]
            cases hdiff : exponent - fmt.minSubnormalExponent <;>
              simp_all
          · rw [ite_eq_right hsubnormal, hnormalUp]
            simp only [directedOverflow, ite_true, ite_eq_right hsubnormal]
            rfl

/--
View the dyadic policy entry point as one exact rational scaling.

The runtime definition branches on the sign of the exponent to avoid constructing an unnecessary
intermediate pair. This theorem gives proofs one uniform representation of that same computation.
-/
private theorem roundDyadicGeneral_eq_scaled
    (fmt : FloatFormat) (policy : QuantizationPolicy)
    (entropy : Nat) (value : Numerics.Dyadic) :
    roundDyadicGeneral fmt policy entropy value =
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo
          value.significand 1 value.exponent
      roundRatGeneralOfDenNeZero fmt policy entropy value.negative
        scaled.1 scaled.2
        (Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero
          value.significand 1 value.exponent (by decide)) := by
  rcases value with ⟨sign, mantissa, exponent⟩
  cases exponent <;> rfl

/--
General policy rounding under an explicit IEEE direction, native overflow, and gradual underflow
is the directed rounder's complete packed result.

The entropy argument is irrelevant because every `IEEERoundingMode` is deterministic.
-/
theorem roundDyadicGeneral_toRoundingMode_eq_roundDyadicWithRounding (fmt : FloatFormat)
    (mode : IEEERoundingMode) (entropy : Nat) (value : Numerics.Dyadic) :
    roundDyadicGeneral fmt
        { rounding := mode.toRoundingMode, overflow := .native, underflow := .gradual }
        entropy value =
      roundDyadicWithRounding fmt mode value := by
  rcases value with ⟨sign, mantissa, exponent⟩
  rw [roundDyadicGeneral_eq_scaled]
  dsimp only
  cases mode with
  | nearestEven =>
      simp only [IEEERoundingMode.toRoundingMode]
      change
        roundRatGeneralOfDenNeZero fmt QuantizationPolicy.nearestEven
            entropy sign
            (Numerics.RationalBinary.scaleByPowerOfTwo
              mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo
              mantissa 1 exponent).2 _ =
          roundDyadicWithRounding fmt .nearestEven
            { negative := sign, significand := mantissa, exponent := exponent }
      rw [roundRatGeneralOfDenNeZero_nearestEven_dyadic_eq]
      simpa only [roundDyadicWithRounding] using
        Model.roundDyadicGeneral_eq_roundDyadic fmt
          ({ negative := sign, significand := mantissa, exponent := exponent } :
            Numerics.Dyadic)
  | towardZero =>
      simp only [IEEERoundingMode.toRoundingMode]
      rw [roundRatGeneralOfDenNeZero_directed_dyadic_eq
        (fmt := fmt) (rounding := .towardZero)
        (roundUp := false) (sign := sign)
        (entropy := entropy) (mantissa := mantissa)
        (exponent := exponent)
        (hquot := by
          intro numerator denominator _
          exact roundQuot_towardZero_eq_roundQuotDirected
            sign entropy numerator denominator)
        (hoverflow := rfl) (htiny := rfl)]
      rw [roundRatMagnitudeDirectedScaled_dyadic_eq]
      simp [roundDyadicWithRounding, roundDyadicTowardZero]
  | towardPositiveInfinity =>
      simp only [IEEERoundingMode.toRoundingMode]
      rw [roundRatGeneralOfDenNeZero_directed_dyadic_eq
        (fmt := fmt) (rounding := .towardPositive)
        (roundUp := !sign) (sign := sign)
        (entropy := entropy) (mantissa := mantissa)
        (exponent := exponent)
        (hquot := by
          intro numerator denominator hdenominator
          exact roundQuot_towardPositive_eq_roundQuotDirected
            sign entropy numerator denominator hdenominator)
        (hoverflow := rfl) (htiny := rfl)]
      rw [roundRatMagnitudeDirectedScaled_dyadic_eq]
      cases sign <;>
        simp [roundDyadicWithRounding, roundDyadicUp]
  | towardNegativeInfinity =>
      simp only [IEEERoundingMode.toRoundingMode]
      rw [roundRatGeneralOfDenNeZero_directed_dyadic_eq
        (fmt := fmt) (rounding := .towardNegative)
        (roundUp := sign) (sign := sign)
        (entropy := entropy) (mantissa := mantissa)
        (exponent := exponent)
        (hquot := by
          intro numerator denominator hdenominator
          exact roundQuot_towardNegative_eq_roundQuotDirected
            sign entropy numerator denominator hdenominator)
        (hoverflow := rfl) (htiny := rfl)]
      rw [roundRatMagnitudeDirectedScaled_dyadic_eq]
      cases sign <;>
        simp [roundDyadicWithRounding, roundDyadicDown]

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
