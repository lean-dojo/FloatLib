/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Semantics

import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Proof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic

/-!
# Correctness of direct posit quotient packing

The executable quotient path generates one destination-width normalized quotient prefix, jams
the exact Euclidean remainder into its sticky bit, and feeds that stream to the shared direct
Posit packer. This module proves that the result is the rounding of the exact rational quotient,
with NaR for division by zero. The proof applies at every format width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/-- A normalized quotient with a proper remainder lies between consecutive powers of two. -/
private theorem quotientFraction_power_bounds
    (quotient remainder denominator leading : Nat)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    (2 : Rat) ^ Int.ofNat leading ≤
        (quotient : Rat) + (remainder : Rat) / (denominator : Rat) ∧
      (quotient : Rat) + (remainder : Rat) / (denominator : Rat) <
        (2 : Rat) ^ Int.ofNat (leading + 1) := by
  have hbounds :=
    quotientFraction_bounds quotient remainder denominator
      hdenominator hremainder
  constructor
  · calc
      (2 : Rat) ^ Int.ofNat leading =
          ((2 ^ leading : Nat) : Rat) := by norm_num
      _ ≤ (quotient : Rat) := by exact_mod_cast hlower
      _ ≤
          (quotient : Rat) +
            (remainder : Rat) / (denominator : Rat) :=
        hbounds.1
  · calc
      (quotient : Rat) +
            (remainder : Rat) / (denominator : Rat) <
          (quotient : Rat) + 1 :=
        hbounds.2
      _ ≤ ((2 ^ (leading + 1) : Nat) : Rat) := by
        exact_mod_cast (show quotient + 1 ≤ 2 ^ (leading + 1) by omega)
      _ = (2 : Rat) ^ Int.ofNat (leading + 1) := by
        simp only [Int.ofNat_eq_natCast, zpow_natCast, Nat.cast_pow,
          Nat.cast_ofNat]

/-- The minimum positive value is the power of two at the bottom regime scale. -/
private theorem minPositiveRat_eq_power (format : Format) :
    Model.minPositiveRat format =
      (2 : Rat) ^ (-(4 * Int.ofNat (format.payloadBits - 1))) := by
  rw [← DyadicRounding.minPositive_toRat,
    DyadicRounding.minPositive_eq_fields]
  norm_num [FloatLib.Numerics.Dyadic.toRat,
    FloatLib.Numerics.Dyadic.signedSignificand]

/-- A normalized quotient is below minpos exactly when its leading scale is below minpos's. -/
private theorem quotientTarget_lt_minPositive_iff
    (format : Format) (targetExponent : Int)
    (quotient remainder denominator leading : Nat)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    (((quotient : Rat) +
          (remainder : Rat) / (denominator : Rat)) *
        (2 : Rat) ^ targetExponent <
      Model.minPositiveRat format) ↔
      targetExponent + Int.ofNat leading <
        -(4 * Int.ofNat (format.payloadBits - 1)) := by
  let fraction : Rat :=
    (quotient : Rat) + (remainder : Rat) / (denominator : Rat)
  let minScale : Int :=
    -(4 * Int.ofNat (format.payloadBits - 1))
  have hfraction :=
    quotientFraction_power_bounds quotient remainder denominator leading
      hlower hupper hdenominator hremainder
  change
    fraction * (2 : Rat) ^ targetExponent <
        Model.minPositiveRat format ↔
      targetExponent + Int.ofNat leading < minScale
  rw [minPositiveRat_eq_power]
  constructor
  · intro htarget
    by_contra hscale
    have hscaleLe :
        minScale ≤ targetExponent + Int.ofNat leading := by
      omega
    have htargetLower :
        (2 : Rat) ^ minScale ≤
          fraction * (2 : Rat) ^ targetExponent := by
      calc
        (2 : Rat) ^ minScale ≤
            (2 : Rat) ^
              (targetExponent + Int.ofNat leading) :=
          zpow_le_zpow_right₀ (by norm_num) hscaleLe
        _ = (2 : Rat) ^ Int.ofNat leading *
              (2 : Rat) ^ targetExponent := by
          rw [show
              targetExponent + Int.ofNat leading =
                Int.ofNat leading + targetExponent by omega,
            zpow_add₀ (by norm_num)]
        _ ≤ fraction * (2 : Rat) ^ targetExponent :=
          mul_le_mul_of_nonneg_right hfraction.1
            (zpow_nonneg (by norm_num) _)
    exact (not_lt_of_ge htargetLower) htarget
  · intro hscale
    have hscaleLe :
        targetExponent + Int.ofNat leading + 1 ≤ minScale := by
      omega
    calc
      fraction * (2 : Rat) ^ targetExponent <
          (2 : Rat) ^ Int.ofNat (leading + 1) *
            (2 : Rat) ^ targetExponent :=
        mul_lt_mul_of_pos_right hfraction.2
          (zpow_pos (by norm_num) _)
      _ = (2 : Rat) ^
          (targetExponent + Int.ofNat leading + 1) := by
        rw [← zpow_add₀ (by norm_num)]
        congr 1
        simp
        omega
      _ ≤ (2 : Rat) ^ minScale :=
        zpow_le_zpow_right₀ (by norm_num) hscaleLe

/-- A nonnegative regime that fills the payload rounds to maxpos. -/
private theorem roundPositiveCode_eq_maxPositive_of_saturated
    (format : Format) (targetExponent regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : 0 ≤ regime)
    (hsaturated : format.payloadBits ≤ regime.toNat + 1)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField)
    (hnotUnderflow :
      ¬(((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) *
          (2 : Rat) ^ targetExponent <
        Model.minPositiveRat format)) :
    Model.roundPositiveCode format
        (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) *
          (2 : Rat) ^ targetExponent) =
      format.signMaskNat - 1 := by
  have hfraction :=
    quotientFraction_power_bounds quotient remainder denominator leading
      hlower hupper hdenominator hremainder
  exact Model.roundPositiveCode_eq_maxPositive_of_lowerCode format _
    (mul_pos ((zpow_pos (by norm_num) _).trans_le hfraction.1) (zpow_pos (by norm_num) _))
    (le_of_not_gt hnotUnderflow)
    (GuardStickyRounding.lowerCodeForPositive_eq_maxPositive_of_saturatedScale
      format _ targetExponent regime exponentField leading hregime hsaturated hfraction.1 hscale)

/-- A negative regime that fills the payload places the normalized quotient below minpos. -/
private theorem quotientTarget_lt_minPositive_of_saturatedNegative
    (format : Format) (targetExponent regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : regime < 0)
    (hsaturated : format.payloadBits ≤ (-regime).toNat)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    ((quotient : Rat) +
        (remainder : Rat) / (denominator : Rat)) *
        (2 : Rat) ^ targetExponent <
      Model.minPositiveRat format := by
  let fraction : Rat :=
    (quotient : Rat) + (remainder : Rat) / (denominator : Rat)
  have hfraction :=
    quotientFraction_power_bounds quotient remainder denominator leading
      hlower hupper hdenominator hremainder
  exact
    GuardStickyRounding.normalizedTarget_lt_minPositive_of_saturatedScale
      format fraction targetExponent regime exponentField leading
      hregime hsaturated hexponent hfraction.2 hscale

/--
Splitting the quotient scale into regime and exponent fields preserves the rational value.
-/
private theorem quotientTarget_eq_fields
    (targetExponent regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) *
        (2 : Rat) ^ targetExponent =
      (((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField) *
        (2 : Rat) ^ (regime * 4) := by
  have hpower :
      (2 : Rat) ^ targetExponent =
        (2 : Rat) ^ Int.ofNat exponentField * (2 : Rat) ^ (regime * 4) /
          (2 : Rat) ^ Int.ofNat leading := by
    rw [← zpow_add₀ (by norm_num), ← zpow_sub₀ (by norm_num)]
    congr 1
    omega
  rw [hpower, show ((2 ^ leading : Nat) : Rat) = (2 : Rat) ^ Int.ofNat leading by norm_num]
  ring

/--
The shared direct dyadic packer rounds a normalized quotient prefix exactly as the unmaterialized
rational quotient fraction.
-/
theorem roundPositiveCode_prefix_eq_reference
    (format : Format) (targetExponent : Int)
    (quotient remainder denominator leading : Nat)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := jamRemainder quotient remainder
          exponent := targetExponent } =
      Model.roundPositiveCode format
        (((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) *
          (2 : Rat) ^ targetExponent) := by
  have hbounds := jamRemainder_bounds leading quotient remainder hlower hupper
  have hsignificand : jamRemainder quotient remainder ≠ 0 :=
    Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hbounds.1)
  have hleading :
      DirectDyadicPacking.leadingBit (jamRemainder quotient remainder) = leading := by
    rw [DirectDyadicPacking.leadingBit_eq_log2]
    exact (Nat.log2_eq_iff hsignificand).2 hbounds
  have hfraction :=
    quotientFraction_power_bounds quotient remainder denominator leading
      hlower hupper hdenominator hremainder
  have hpositive :
      0 < ((quotient : Rat) + (remainder : Rat) / (denominator : Rat)) *
        (2 : Rat) ^ targetExponent :=
    mul_pos ((zpow_pos (by norm_num) _).trans_le hfraction.1) (zpow_pos (by norm_num) _)
  have hunderflowIff :=
    quotientTarget_lt_minPositive_iff format targetExponent quotient remainder
      denominator leading hlower hupper hdenominator hremainder
  have hmod : 0 ≤ (targetExponent + Int.ofNat leading).emod 4 :=
    Int.emod_nonneg _ (by decide)
  have hmodLt : (targetExponent + Int.ofNat leading).emod 4 < 4 :=
    Int.emod_lt_of_pos _ (by decide)
  have hexponent : ((targetExponent + Int.ofNat leading).emod 4).toNat < 4 := by
    omega
  have hscale :
      targetExponent + Int.ofNat leading =
        (targetExponent + Int.ofNat leading).ediv 4 * 4 +
          Int.ofNat ((targetExponent + Int.ofNat leading).emod 4).toNat := by
    simp only [Int.ofNat_eq_natCast] at hmod ⊢
    rw [Int.toNat_of_nonneg hmod]
    exact (Int.ediv_mul_add_emod _ 4).symm
  unfold DirectDyadicPacking.roundPositiveCode Dyadic.isLessPowerOfTwoAtLeading
  simp only [Bool.or_false, beq_iff_eq, hsignificand, ↓reduceIte, hleading,
    decide_eq_true_eq]
  split_ifs with hunderflow hregime hsaturated hsaturated
  · unfold Model.roundPositiveCode
    rw [if_neg (not_le_of_gt hpositive), if_pos (hunderflowIff.2 hunderflow)]
  · exact (roundPositiveCode_eq_maxPositive_of_saturated format targetExponent _ _
      quotient remainder denominator leading hregime hsaturated hlower hupper
      hdenominator hremainder hscale (fun h => hunderflow (hunderflowIff.1 h))).symm
  · rw [GuardStickyRounding.roundInteriorCodeFromFields_eq_roundInteriorCode
      _ _ _ _ _ _ hbounds.1 hbounds.2, quotientTarget_eq_fields _ _ _ _ _ _ _ hscale]
    exact roundInteriorCode_eq_roundPositiveCode_positive format _ _ quotient remainder
      denominator leading hregime (by omega) hleadingWidth hexponent hlower hupper
      hdenominator hremainder
      (by
        rw [← quotientTarget_eq_fields _ _ _ _ _ _ _ hscale]
        exact hunderflowIff.not.2 hunderflow)
  · exact absurd
      (hunderflowIff.1 (quotientTarget_lt_minPositive_of_saturatedNegative format
        targetExponent _ _ quotient remainder denominator leading (by omega) hsaturated
        hexponent hlower hupper hdenominator hremainder hscale))
      hunderflow
  · rw [GuardStickyRounding.roundInteriorCodeFromFields_eq_roundInteriorCode
      _ _ _ _ _ _ hbounds.1 hbounds.2, quotientTarget_eq_fields _ _ _ _ _ _ _ hscale]
    exact roundInteriorCode_eq_roundPositiveCode_negative format _ _ quotient remainder
      denominator leading (by omega) (by omega) hleadingWidth hexponent hlower hupper
      hdenominator hremainder
      (by
        rw [← quotientTarget_eq_fields _ _ _ _ _ _ _ hscale]
        exact hunderflowIff.not.2 hunderflow)

/-- Direct positive quotient rounding refines exact rational division. -/
theorem roundPositiveCode_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumeratorSignificand : numerator.significand ≠ 0)
    (hnumeratorNegative : numerator.negative = false)
    (hdenominatorSignificand : denominator.significand ≠ 0)
    (hdenominatorNegative : denominator.negative = false) :
    roundPositiveCode format numerator denominator =
      Model.roundPositiveCode format
        (numerator.toRat / denominator.toRat) := by
  have hnumeratorBool : (numerator.significand == 0) = false :=
    beq_eq_false_iff_ne.mpr hnumeratorSignificand
  have hdenominatorBool : (denominator.significand == 0) = false :=
    beq_eq_false_iff_ne.mpr hdenominatorSignificand
  unfold roundPositiveCode
  simp only [hnumeratorBool, hnumeratorNegative,
    hdenominatorBool, hdenominatorNegative,
    Bool.false_or, Bool.false_eq_true, if_false]
  unfold quotientPrefix prefixAtLeading
  let leading := prefixLeading format
  let normalized :=
    normalizeSignificands numerator.significand denominator.significand
  let steps :=
    if normalized.numerator < normalized.denominator then leading + 1 else leading
  let scaledNumerator := normalized.numerator <<< steps
  let quotient := scaledNumerator / normalized.denominator
  let remainder := scaledNumerator % normalized.denominator
  let targetExponent :=
    numerator.exponent - denominator.exponent +
      Int.ofNat normalized.numeratorLeading -
      Int.ofNat normalized.denominatorLeading -
      Int.ofNat steps
  have hspec :=
    prefixAtLeading_quotient_spec leading numerator denominator
      hnumeratorSignificand hdenominatorSignificand
  have hexact :=
    prefixAtLeading_exactFraction leading numerator denominator
      hnumeratorSignificand hdenominatorSignificand
      hnumeratorNegative hdenominatorNegative
  change
    DirectDyadicPacking.roundPositiveCode format
        { negative := false
          significand := jamRemainder quotient remainder
          exponent := targetExponent } =
      Model.roundPositiveCode format
        (numerator.toRat / denominator.toRat)
  have hkernel :=
    roundPositiveCode_prefix_eq_reference
      format targetExponent quotient remainder
      normalized.denominator leading
      (by simp [leading, prefixLeading])
      (by
        simpa [normalized, steps, scaledNumerator, quotient,
          Nat.shiftLeft_eq] using hspec.2.1)
      (by
        simpa [normalized, steps, scaledNumerator, quotient,
          Nat.shiftLeft_eq] using hspec.2.2.1)
      (by simpa [normalized] using hspec.1)
      (by
        simpa [normalized, steps, scaledNumerator, remainder,
          Nat.shiftLeft_eq] using hspec.2.2.2)
  rw [show
      numerator.toRat / denominator.toRat =
        (((quotient : Rat) +
            (remainder : Rat) / (normalized.denominator : Rat)) *
          (2 : Rat) ^ targetExponent) by
    simpa [normalized, steps, scaledNumerator, quotient, remainder,
      targetExponent, Nat.shiftLeft_eq] using hexact]
  exact hkernel

/-- Direct positive quotient rounding always selects a finite nonnegative code. -/
theorem roundPositiveCode_lt_signMask
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    roundPositiveCode format numerator denominator <
      format.signMaskNat := by
  unfold roundPositiveCode
  split
  · exact format.signMaskNat_pos
  · exact DirectDyadicPacking.roundPositiveCode_lt_signMask
      format (quotientPrefix format numerator denominator)

/-- Direct positive quotient packing refines exact positive rational rounding. -/
theorem roundPositive_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic)
    (hnumeratorSignificand : numerator.significand ≠ 0)
    (hnumeratorNegative : numerator.negative = false)
    (hdenominatorSignificand : denominator.significand ≠ 0)
    (hdenominatorNegative : denominator.negative = false) :
    roundPositive format numerator denominator =
      Model.roundPositiveRat format
        (numerator.toRat / denominator.toRat) := by
  unfold roundPositive Model.roundPositiveRat
  rw [roundPositiveCode_eq_reference format numerator denominator
    hnumeratorSignificand hnumeratorNegative
    hdenominatorSignificand hdenominatorNegative]

/-- Direct signed quotient rounding refines exact rational division. -/
theorem round_eq_reference
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    round format numerator denominator =
      if denominator.toRat = 0 then
        Model.nar format
      else
        Model.roundRat format
          (numerator.toRat / denominator.toRat) :=
  DyadicQuotient.roundSignedWith_eq_reference format (roundPositive format)
    (roundPositive_eq_reference format) numerator denominator

/--
The direct quotient kernel and the general exact quotient rounder choose the same result.

Only their positive-magnitude kernels differ, and both are certified against the same rational
rounding specification.
-/
theorem round_eq_dyadicQuotient
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    round format numerator denominator =
      DyadicQuotient.round format numerator denominator := by
  rw [round_eq_reference, DyadicQuotient.round_eq_reference]

/-! ## Code-valued boundary -/

/-- The code-valued quotient is the encoding of the model-valued quotient. -/
theorem roundCode_eq_toNatBits
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    roundCode format numerator denominator =
      (round format numerator denominator).toNatBits := by
  unfold roundCode round DyadicQuotient.roundSignedWith
  split
  · exact (Model.nar_toNatBits format).symm
  · split
    · exact (Model.zero_toNatBits format).symm
    · dsimp only
      have hpositive :=
        roundPositiveCode_lt_signMask format
          (DyadicRounding.magnitude numerator)
          (DyadicRounding.magnitude denominator)
      have hbits := congrArg Model.toNatBits
        (DyadicRounding.ofNatBits_restoreSignCode format
          (Bool.xor numerator.negative denominator.negative) _ hpositive)
      rw [Model.toNatBits_ofNatBits_of_lt _
        (DyadicRounding.restoreSignCode_lt_modulus format _ _ hpositive)] at hbits
      simpa only [roundPositive] using hbits

/-- Every quotient code fits the configured posit word. -/
theorem roundCode_lt_modulus
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    roundCode format numerator denominator < format.modulus := by
  rw [roundCode_eq_toNatBits]
  exact Model.toNatBits_lt_modulus _

/-- Re-encoding the quotient code recovers the model-valued quotient. -/
theorem ofNatBits_roundCode
    (format : Format) (numerator denominator : FloatLib.Numerics.Dyadic) :
    Model.ofNatBits (roundCode format numerator denominator) =
      round format numerator denominator := by
  rw [roundCode_eq_toNatBits]
  exact Model.ofNatBits_toNatBits _

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient
