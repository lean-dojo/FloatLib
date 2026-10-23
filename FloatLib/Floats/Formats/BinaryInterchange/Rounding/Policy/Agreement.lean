/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.NearestAwayAgreement
import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic
import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof

/-!
# Agreement between policy and directed dyadic rounding

`roundDyadicGeneral` and `Internal.Directed.roundDyadic` are independent executable algorithms. The
first embeds a dyadic into the rational policy engine, and the second uses dedicated shift-based
dyadic packers. This file proves that their complete packed results agree for each
`IEEERoundingMode` when overflow is native and underflow is gradual. The proof includes signed zero,
subnormal carry, custom exponent bias, finite-only encodings, and native overflow words, so it is
more than an equality of real denotations.

The ordinary `roundDyadic` entry point dispatches these policies to the directed engine, so the
agreement says that the dispatch does not change any result. Stochastic, saturating, and
flush-to-zero policies are specified by the general policy implementation. The scaled-dyadic
lemmas behind the proof are in `Rounding.Policy.ScaledDyadic`, and the nearest-away case is
`Rounding.Policy.NearestAwayAgreement`.

-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

namespace Policy

/--
General policy rounding under an IEEE direction, native overflow, and gradual underflow is the
directed rounder's complete packed result.

The entropy argument is irrelevant because every `IEEERoundingMode` is deterministic.
-/
theorem roundDyadicGeneral_toRoundingMode (fmt : FloatFormat)
    (mode : IEEERoundingMode) (entropy : Nat) (value : Numerics.Dyadic) :
    roundDyadicGeneral fmt
        { rounding := mode.toRoundingMode, overflow := .native, underflow := .gradual }
        entropy value =
      Internal.Directed.roundDyadic fmt mode value := by
  rcases value with ⟨sign, mantissa, exponent⟩
  rw [roundDyadicGeneral_eq_roundRatGeneralOfDenNeZero]
  dsimp only
  cases mode with
  | nearest =>
      simp only [IEEERoundingMode.toRoundingMode]
      change
        roundRatGeneralOfDenNeZero fmt QuantizationPolicy.nearest
            entropy sign
            (Numerics.RationalBinary.scaleByPowerOfTwo
              mantissa 1 exponent).1
            (Numerics.RationalBinary.scaleByPowerOfTwo
              mantissa 1 exponent).2 _ =
          Internal.Directed.roundDyadic fmt .nearest
            { negative := sign, significand := mantissa, exponent := exponent }
      rw [roundRatGeneralOfDenNeZero_nearest_dyadic_eq]
      simpa only [Internal.Directed.roundDyadic] using
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
      simp [Internal.Directed.roundDyadic, roundDyadicTowardZero]
  | up =>
      simp only [IEEERoundingMode.toRoundingMode]
      rw [roundRatGeneralOfDenNeZero_directed_dyadic_eq
        (fmt := fmt) (rounding := .up)
        (roundUp := !sign) (sign := sign)
        (entropy := entropy) (mantissa := mantissa)
        (exponent := exponent)
        (hquot := by
          intro numerator denominator hdenominator
          exact roundQuot_up_eq_roundQuotDirected
            sign entropy numerator denominator hdenominator)
        (hoverflow := rfl) (htiny := rfl)]
      rw [roundRatMagnitudeDirectedScaled_dyadic_eq]
      cases sign <;>
        simp [Internal.Directed.roundDyadic, roundDyadicUp]
  | down =>
      simp only [IEEERoundingMode.toRoundingMode]
      rw [roundRatGeneralOfDenNeZero_directed_dyadic_eq
        (fmt := fmt) (rounding := .down)
        (roundUp := sign) (sign := sign)
        (entropy := entropy) (mantissa := mantissa)
        (exponent := exponent)
        (hquot := by
          intro numerator denominator hdenominator
          exact roundQuot_down_eq_roundQuotDirected
            sign entropy numerator denominator hdenominator)
        (hoverflow := rfl) (htiny := rfl)]
      rw [roundRatMagnitudeDirectedScaled_dyadic_eq]
      cases sign <;>
        simp [Internal.Directed.roundDyadic, roundDyadicDown]
  | nearestAway =>
      have hnearestAway := roundDyadicGeneral_nearestAway_eq_roundDyadicNearestAway fmt entropy
        { negative := sign, significand := mantissa, exponent := exponent }
      rw [roundDyadicGeneral_eq_roundRatGeneralOfDenNeZero] at hnearestAway
      exact hnearestAway
  | away =>
      simp only [IEEERoundingMode.toRoundingMode]
      rw [roundRatGeneralOfDenNeZero_directed_dyadic_eq
        (fmt := fmt) (rounding := .away)
        (roundUp := true) (sign := sign)
        (entropy := entropy) (mantissa := mantissa)
        (exponent := exponent)
        (hquot := by
          intro numerator denominator hdenominator
          exact roundQuot_away_eq_roundQuotDirected
            sign entropy numerator denominator hdenominator)
        (hoverflow := rfl) (htiny := rfl)]
      rw [roundRatMagnitudeDirectedScaled_dyadic_eq]
      simp [Internal.Directed.roundDyadic, roundDyadicAway]

end Policy

end FloatLib.Floats.Formats.BinaryInterchange.Model
