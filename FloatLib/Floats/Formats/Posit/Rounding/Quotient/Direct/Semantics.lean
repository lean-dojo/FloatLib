/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.PrefixProof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Semantics.Interior
import Mathlib.Tactic.NormNum

/-!
# Posit semantics of direct quotient prefixes

The representation-independent quotient-prefix bracket determines Posit regime, exponent,
fraction, and appended-bit rounding thresholds. Exact quotient-and-remainder bounds show that
truncation brackets the rational quotient and that jamming preserves its comparison with the
rounding threshold.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient

open FloatLib.Numerics
open FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
open FloatLib.Floats.Formats.Posit.Model.StickyPrefix

/--
The exact scaled quotient is strictly below the successor of a lower candidate whose successor
is either the next interior tail word or the zero-tail base of the next regime.

Both regime signs supply the two successor values from their own layout lemmas; this lemma
performs the common case split on whether the retained tail carries.
-/
private theorem quotientFraction_lt_lowerCandidateSuccessor_of_values
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading trailing candidate : Nat)
    (hleading : 0 < leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (htrailing : trailing < leading + 2)
    (hinterior :
      DirectDyadicPacking.tailPrefix
          exponentField (jamRemainder quotient remainder) leading trailing + 1 <
        2 ^ trailing →
      Model.nonnegativeRatAt format (candidate + 1) =
        Model.trailingRat trailing
            (DirectDyadicPacking.tailPrefix
              exponentField (jamRemainder quotient remainder) leading trailing + 1) *
          (2 : Rat) ^ (regime * 4))
    (hcarry :
      DirectDyadicPacking.tailPrefix
          exponentField (jamRemainder quotient remainder) leading trailing + 1 =
        2 ^ trailing →
      Model.nonnegativeRatAt format (candidate + 1) =
        (2 : Rat) ^ ((regime + 1) * 4)) :
    ((((quotient : Rat) +
              (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField) *
        (2 : Rat) ^ (regime * 4)) <
      Model.nonnegativeRatAt format (candidate + 1) := by
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  have htailBound :=
    DirectDyadicPacking.tailPrefix_lt_two_pow
      exponentField (jamRemainder quotient remainder) leading trailing
      hexponent hsignificandBounds.1 hsignificandBounds.2
  have htailStream :=
    tailPrefix_eq_streamPrefix
      exponentField (jamRemainder quotient remainder) leading trailing
      hsignificandBounds.1 hsignificandBounds.2
  by_cases htailSucc :
      DirectDyadicPacking.tailPrefix
          exponentField (jamRemainder quotient remainder) leading trailing + 1 <
        2 ^ trailing
  · rw [hinterior htailSucc, htailStream]
    exact mul_lt_mul_of_pos_right
      (quotientFraction_lt_trailingRat_streamPrefix_jammed_succ
        exponentField quotient remainder denominator leading trailing
        hleading hexponent hlower hupper hdenominator hremainder htrailing
        (htailStream ▸ htailSucc))
      (zpow_pos (by norm_num) _)
  · rw [hcarry (by omega), GuardStickyRounding.regimeScale_succ]
    exact mul_lt_mul_of_pos_right
      (quotientFraction_normalized_lt_sixteen
        exponentField quotient remainder denominator leading
        hexponent hupper hdenominator hremainder)
      (zpow_pos (by norm_num) _)

/--
The successor of an interior positive-regime quotient candidate is strictly above the exact
quotient.
-/
private theorem quotientFraction_lt_lowerCandidateSuccessor_positive
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    ((((quotient : Rat) +
              (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField) *
        (2 : Rat) ^ (regime * 4)) <
      Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField
            (jamRemainder quotient remainder) leading + 1) := by
  have hrunPos : 0 < regime.toNat + 1 := by
    omega
  have hregimeValue : Int.ofNat (regime.toNat + 1) - 1 = regime := by
    simp [Int.toNat_of_nonneg hregime]
  have hcandidateCode :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField (jamRemainder quotient remainder) leading =
        (2 ^ (regime.toNat + 1) - 1) * 2 ^ (format.payloadBits - (regime.toNat + 1)) +
          DirectDyadicPacking.tailPrefix exponentField (jamRemainder quotient remainder) leading
            (format.payloadBits - (regime.toNat + 1) - 1) := by
    simp [DirectDyadicPacking.lowerCandidateFromFields, hregime, Nat.not_le.mpr hrun,
      Nat.shiftLeft_eq]
  refine quotientFraction_lt_lowerCandidateSuccessor_of_values
    format regime exponentField quotient remainder denominator leading
    (format.payloadBits - (regime.toNat + 1) - 1) _
    (lt_of_lt_of_le format.payloadBits_pos hleadingWidth)
    hexponent hlower hupper hdenominator hremainder (by omega) ?_ ?_
  · intro htailSucc
    rw [hcandidateCode, Nat.add_assoc,
      nonnegativeRatAt_positiveInterior format _ _ hrunPos hrun htailSucc, hregimeValue]
  · intro htailFull
    rw [hcandidateCode, show DirectDyadicPacking.tailPrefix exponentField
        (jamRemainder quotient remainder) leading (format.payloadBits - (regime.toNat + 1) - 1) =
        2 ^ (format.payloadBits - (regime.toNat + 1) - 1) - 1 by omega,
      nonnegativeRatAt_positiveInteriorCarry format _ hrunPos hrun,
      show Int.ofNat (regime.toNat + 1) = regime + 1 by omega]

/--
The successor of an interior negative-regime quotient candidate is strictly above the exact
quotient.
-/
private theorem quotientFraction_lt_lowerCandidateSuccessor_negative
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    ((((quotient : Rat) +
              (remainder : Rat) / (denominator : Rat)) /
            (2 ^ leading : Nat) *
          (2 : Rat) ^ Int.ofNat exponentField) *
        (2 : Rat) ^ (regime * 4)) <
      Model.nonnegativeRatAt format
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField
            (jamRemainder quotient remainder) leading + 1) := by
  have hrunPos : 0 < (-regime).toNat := by
    omega
  have hregimeValue : -(Int.ofNat (-regime).toNat) = regime := by
    rw [Int.ofNat_eq_natCast, Int.toNat_of_nonneg (by omega)]
    omega
  have hcandidateCode :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField (jamRemainder quotient remainder) leading =
        2 ^ (format.payloadBits - (-regime).toNat - 1) +
          DirectDyadicPacking.tailPrefix exponentField (jamRemainder quotient remainder) leading
            (format.payloadBits - (-regime).toNat - 1) := by
    simp [DirectDyadicPacking.lowerCandidateFromFields, Int.not_le.mpr hregime,
      Nat.not_le.mpr hrun, Nat.shiftLeft_eq]
  refine quotientFraction_lt_lowerCandidateSuccessor_of_values
    format regime exponentField quotient remainder denominator leading
    (format.payloadBits - (-regime).toNat - 1) _
    (lt_of_lt_of_le format.payloadBits_pos hleadingWidth)
    hexponent hlower hupper hdenominator hremainder (by omega) ?_ ?_
  · intro htailSucc
    rw [hcandidateCode, Nat.add_assoc,
      nonnegativeRatAt_negativeInterior format _ _ hrunPos hrun htailSucc, hregimeValue]
  · intro htailFull
    rw [hcandidateCode, show DirectDyadicPacking.tailPrefix exponentField
        (jamRemainder quotient remainder) leading (format.payloadBits - (-regime).toNat - 1) =
        2 ^ (format.payloadBits - (-regime).toNat - 1) - 1 by omega,
      nonnegativeRatAt_negativeInteriorCarry format _ hrunPos hrun, hregimeValue]

/--
An interior positive-regime quotient prefix is exactly the rational model's greatest lower code.
-/
theorem lowerCodeForPositive_eq_lowerCandidateFromQuotient_positive
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    Model.lowerCodeForPositive format
        (((((quotient : Rat) +
                  (remainder : Rat) / (denominator : Rat)) /
                (2 ^ leading : Nat) *
              (2 : Rat) ^ Int.ofNat exponentField) *
            (2 : Rat) ^ (regime * 4))) =
      DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField
          (jamRemainder quotient remainder) leading := by
  let significand := jamRemainder quotient remainder
  let candidate :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  let trailing :=
    format.payloadBits - (regime.toNat + 1) - 1
  have hleading : 0 < leading :=
    lt_of_lt_of_le format.payloadBits_pos hleadingWidth
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  have htrailing : trailing < leading + 2 := by
    dsimp [trailing]
    omega
  apply Model.lowerCodeForPositive_eq_of_bracket
  · exact DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField significand leading
      hexponent hsignificandBounds.1 hsignificandBounds.2
  · rw [lowerCandidateValue_positive format regime
      exponentField significand leading
      hregime hrun hexponent hsignificandBounds.1 hsignificandBounds.2]
    rw [tailPrefix_eq_streamPrefix
      exponentField significand leading trailing
      hsignificandBounds.1 hsignificandBounds.2]
    exact mul_le_mul_of_nonneg_right
      (trailingRat_streamPrefix_jammed_le_quotientFraction
        exponentField quotient remainder denominator leading trailing
        hleading hexponent hlower hupper hdenominator hremainder htrailing)
      (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  · intro _hsuccessor
    exact quotientFraction_lt_lowerCandidateSuccessor_positive
      format regime exponentField quotient remainder denominator leading
      hregime hrun hleadingWidth hexponent hlower hupper
      hdenominator hremainder

/--
An interior negative-regime quotient prefix is exactly the rational model's greatest lower code.
-/
theorem lowerCodeForPositive_eq_lowerCandidateFromQuotient_negative
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    Model.lowerCodeForPositive format
        (((((quotient : Rat) +
                  (remainder : Rat) / (denominator : Rat)) /
                (2 ^ leading : Nat) *
              (2 : Rat) ^ Int.ofNat exponentField) *
            (2 : Rat) ^ (regime * 4))) =
      DirectDyadicPacking.lowerCandidateFromFields
        format regime exponentField
          (jamRemainder quotient remainder) leading := by
  let significand := jamRemainder quotient remainder
  let candidate :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  let trailing :=
    format.payloadBits - (-regime).toNat - 1
  have hleading : 0 < leading :=
    lt_of_lt_of_le format.payloadBits_pos hleadingWidth
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  have htrailing : trailing < leading + 2 := by
    dsimp [trailing]
    omega
  apply Model.lowerCodeForPositive_eq_of_bracket
  · exact DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField significand leading
      hexponent hsignificandBounds.1 hsignificandBounds.2
  · rw [lowerCandidateValue_negative format regime
      exponentField significand leading
      hregime hrun hexponent hsignificandBounds.1 hsignificandBounds.2]
    rw [tailPrefix_eq_streamPrefix
      exponentField significand leading trailing
      hsignificandBounds.1 hsignificandBounds.2]
    exact mul_le_mul_of_nonneg_right
      (trailingRat_streamPrefix_jammed_le_quotientFraction
        exponentField quotient remainder denominator leading trailing
        hleading hexponent hlower hupper hdenominator hremainder htrailing)
      (zpow_pos (by norm_num : (0 : Rat) < 2) _).le
  · intro _hsuccessor
    exact quotientFraction_lt_lowerCandidateSuccessor_negative
      format regime exponentField quotient remainder denominator leading
      hregime hrun hleadingWidth hexponent hlower hupper
      hdenominator hremainder

/--
Interior guard/sticky rounding of a jammed quotient makes the exact threshold decision once the
rounding threshold of its lower candidate is known to be the one-bit-wider retained tail word.

Both regime signs obtain that threshold from their own candidate lemma and share this proof.
-/
private theorem roundInteriorCode_eq_quotientMidpointDecision_of_threshold
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading regimeFieldBits retained : Nat)
    (hretained : format.payloadBits - regimeFieldBits = retained)
    (hpadding : retained + 1 < leading + 2)
    (hleading : 0 < leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hthreshold :
      Model.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField (jamRemainder quotient remainder) leading) =
        Model.trailingRat (retained + 1)
            (2 * DirectDyadicPacking.tailPrefix
                exponentField (jamRemainder quotient remainder) leading retained + 1) *
          (2 : Rat) ^ (regime * 4)) :
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading regimeFieldBits =
      let lower :=
        DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField
            (jamRemainder quotient remainder) leading
      let threshold := Model.roundingThreshold format lower
      let target :=
        ((((quotient : Rat) +
                (remainder : Rat) / (denominator : Rat)) /
              (2 ^ leading : Nat) *
            (2 : Rat) ^ Int.ofNat exponentField) *
          (2 : Rat) ^ (regime * 4))
      if target < threshold then
        lower
      else if threshold < target then
        lower + 1
      else if lower % 2 = 0 then
        lower
      else
        lower + 1 := by
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  have hmidpointBound :=
    streamMidpointRaw_lt_two_pow
      (exactTailRaw_lt_two_pow exponentField (jamRemainder quotient remainder) leading
        hexponent hsignificandBounds.1 hsignificandBounds.2)
      (by omega : retained < leading + 2)
  rw [tailPrefix_eq_streamPrefix exponentField (jamRemainder quotient remainder) leading retained
      hsignificandBounds.1 hsignificandBounds.2,
    trailingRat_streamMidpointRaw _ _ retained (by omega)] at hthreshold
  apply roundInteriorCode_eq_rationalMidpointDecision
    format regime exponentField (jamRemainder quotient remainder) leading regimeFieldBits
    retained _ hretained (by omega)
  · rw [hthreshold, Rat.mul_lt_mul_right (zpow_pos (by norm_num) _),
      quotientFraction_lt_trailingRat_iff exponentField quotient remainder denominator leading _
        hexponent hlower hupper hdenominator hremainder hmidpointBound]
    exact quotientTailFraction_lt_midpoint_iff_jammed
      exponentField quotient remainder denominator leading retained
      hleading hlower hdenominator hremainder hpadding
  · rw [hthreshold, Rat.mul_lt_mul_right (zpow_pos (by norm_num) _),
      trailingRat_lt_quotientFraction_iff exponentField quotient remainder denominator leading _
        hexponent hlower hupper hdenominator hremainder hmidpointBound]
    exact midpoint_lt_quotientTailFraction_iff_jammed
      exponentField quotient remainder denominator leading retained
      hleading hlower hdenominator hremainder hpadding

/--
Interior positive-regime guard/sticky rounding makes the exact quotient threshold decision.
-/
theorem roundInteriorCode_eq_quotientMidpointDecision_positive
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading
        (regime.toNat + 2) =
      let lower :=
        DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField
            (jamRemainder quotient remainder) leading
      let threshold := Model.roundingThreshold format lower
      let target :=
        ((((quotient : Rat) +
                (remainder : Rat) / (denominator : Rat)) /
              (2 ^ leading : Nat) *
            (2 : Rat) ^ Int.ofNat exponentField) *
          (2 : Rat) ^ (regime * 4))
      if target < threshold then
        lower
      else if threshold < target then
        lower + 1
      else if lower % 2 = 0 then
        lower
      else
        lower + 1 := by
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  exact roundInteriorCode_eq_quotientMidpointDecision_of_threshold
    format regime exponentField quotient remainder denominator leading
    (regime.toNat + 2) (format.payloadBits - (regime.toNat + 1) - 1)
    (by omega) (by omega) (lt_of_lt_of_le format.payloadBits_pos hleadingWidth)
    hexponent hlower hupper hdenominator hremainder
    (lowerCandidateThreshold_positive format regime exponentField _ leading
      hregime hrun hexponent hsignificandBounds.1 hsignificandBounds.2)

/--
Interior negative-regime guard/sticky rounding makes the exact quotient threshold decision.
-/
theorem roundInteriorCode_eq_quotientMidpointDecision_negative
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator) :
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading
        ((-regime).toNat + 1) =
      let lower :=
        DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField
            (jamRemainder quotient remainder) leading
      let threshold := Model.roundingThreshold format lower
      let target :=
        ((((quotient : Rat) +
                (remainder : Rat) / (denominator : Rat)) /
              (2 ^ leading : Nat) *
            (2 : Rat) ^ Int.ofNat exponentField) *
          (2 : Rat) ^ (regime * 4))
      if target < threshold then
        lower
      else if threshold < target then
        lower + 1
      else if lower % 2 = 0 then
        lower
      else
        lower + 1 := by
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  exact roundInteriorCode_eq_quotientMidpointDecision_of_threshold
    format regime exponentField quotient remainder denominator leading
    ((-regime).toNat + 1) (format.payloadBits - (-regime).toNat - 1)
    (by omega) (by omega) (lt_of_lt_of_le format.payloadBits_pos hleadingWidth)
    hexponent hlower hupper hdenominator hremainder
    (lowerCandidateThreshold_negative format regime exponentField _ leading
      hregime hrun hexponent hsignificandBounds.1 hsignificandBounds.2)

/--
Interior positive-regime field rounding is the exact rational positive quotient rounder.
-/
theorem roundInteriorCode_eq_roundPositiveCode_positive
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hnotUnderflow :
      ¬(((((quotient : Rat) +
                  (remainder : Rat) / (denominator : Rat)) /
                (2 ^ leading : Nat) *
              (2 : Rat) ^ Int.ofNat exponentField) *
            (2 : Rat) ^ (regime * 4)) <
        Model.minPositiveRat format)) :
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading
        (regime.toNat + 2) =
      Model.roundPositiveCode format
        ((((quotient : Rat) +
                  (remainder : Rat) / (denominator : Rat)) /
                (2 ^ leading : Nat) *
              (2 : Rat) ^ Int.ofNat exponentField) *
            (2 : Rat) ^ (regime * 4)) := by
  let target : Rat :=
    ((((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField) *
      (2 : Rat) ^ (regime * 4))
  have hquotientPositive : (0 : Rat) < quotient := by
    exact_mod_cast lt_of_lt_of_le (Nat.two_pow_pos leading) hlower
  have hfractionNonnegative : (0 : Rat) ≤ (remainder : Rat) / (denominator : Rat) :=
    div_nonneg (Nat.cast_nonneg remainder) (Nat.cast_nonneg denominator)
  have hleadingPositive : (0 : Rat) < (2 ^ leading : Nat) := by
    exact_mod_cast Nat.two_pow_pos leading
  have htargetPositive : 0 < target :=
    mul_pos
      (mul_pos
        (div_pos (add_pos_of_pos_of_nonneg hquotientPositive hfractionNonnegative)
          hleadingPositive)
        (zpow_pos (by norm_num) _))
      (zpow_pos (by norm_num) _)
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  change
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading
        (regime.toNat + 2) =
      Model.roundPositiveCode format target
  rw [roundInteriorCode_eq_quotientMidpointDecision_positive
    format regime exponentField quotient remainder denominator leading
    hregime hrun hleadingWidth hexponent hlower hupper
    hdenominator hremainder]
  unfold Model.roundPositiveCode
  rw [if_neg (not_le.mpr htargetPositive)]
  rw [if_neg hnotUnderflow]
  rw [lowerCodeForPositive_eq_lowerCandidateFromQuotient_positive
    format regime exponentField quotient remainder denominator leading
    hregime hrun hleadingWidth hexponent hlower hupper
    hdenominator hremainder]
  rw [if_pos
    (lowerCandidateFromFields_succ_lt_signMask_positive
      format regime exponentField
        (jamRemainder quotient remainder) leading
      hregime hrun hexponent
      hsignificandBounds.1 hsignificandBounds.2)]

/--
Interior negative-regime field rounding is the exact rational positive quotient rounder.
-/
theorem roundInteriorCode_eq_roundPositiveCode_negative
    (format : Format) (regime : Int)
    (exponentField quotient remainder denominator leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hleadingWidth : format.payloadBits ≤ leading)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ quotient)
    (hupper : quotient < 2 ^ (leading + 1))
    (hdenominator : 0 < denominator)
    (hremainder : remainder < denominator)
    (hnotUnderflow :
      ¬(((((quotient : Rat) +
                  (remainder : Rat) / (denominator : Rat)) /
                (2 ^ leading : Nat) *
              (2 : Rat) ^ Int.ofNat exponentField) *
            (2 : Rat) ^ (regime * 4)) <
        Model.minPositiveRat format)) :
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading
        ((-regime).toNat + 1) =
      Model.roundPositiveCode format
        ((((quotient : Rat) +
                  (remainder : Rat) / (denominator : Rat)) /
                (2 ^ leading : Nat) *
              (2 : Rat) ^ Int.ofNat exponentField) *
            (2 : Rat) ^ (regime * 4)) := by
  let target : Rat :=
    ((((quotient : Rat) +
            (remainder : Rat) / (denominator : Rat)) /
          (2 ^ leading : Nat) *
        (2 : Rat) ^ Int.ofNat exponentField) *
      (2 : Rat) ^ (regime * 4))
  have hquotientPositive : (0 : Rat) < quotient := by
    exact_mod_cast lt_of_lt_of_le (Nat.two_pow_pos leading) hlower
  have hfractionNonnegative : (0 : Rat) ≤ (remainder : Rat) / (denominator : Rat) :=
    div_nonneg (Nat.cast_nonneg remainder) (Nat.cast_nonneg denominator)
  have hleadingPositive : (0 : Rat) < (2 ^ leading : Nat) := by
    exact_mod_cast Nat.two_pow_pos leading
  have htargetPositive : 0 < target :=
    mul_pos
      (mul_pos
        (div_pos (add_pos_of_pos_of_nonneg hquotientPositive hfractionNonnegative)
          hleadingPositive)
        (zpow_pos (by norm_num) _))
      (zpow_pos (by norm_num) _)
  have hsignificandBounds :=
    jamRemainder_bounds leading quotient remainder hlower hupper
  change
    roundInteriorCode format regime exponentField
        (jamRemainder quotient remainder) leading
        ((-regime).toNat + 1) =
      Model.roundPositiveCode format target
  rw [roundInteriorCode_eq_quotientMidpointDecision_negative
    format regime exponentField quotient remainder denominator leading
    hregime hrun hleadingWidth hexponent hlower hupper
    hdenominator hremainder]
  unfold Model.roundPositiveCode
  rw [if_neg (not_le.mpr htargetPositive)]
  rw [if_neg hnotUnderflow]
  rw [lowerCodeForPositive_eq_lowerCandidateFromQuotient_negative
    format regime exponentField quotient remainder denominator leading
    hregime hrun hleadingWidth hexponent hlower hupper
    hdenominator hremainder]
  rw [if_pos
    (lowerCandidateFromFields_succ_lt_signMask_negative
      format regime exponentField
        (jamRemainder quotient remainder) leading
      hregime hrun hexponent
      hsignificandBounds.1 hsignificandBounds.2)]

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicQuotient
