/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Semantics.Candidates
import FloatLib.Numerics.Exact.Dyadic.Order
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Inv

/-!
# Correctness of interior guard-and-sticky Posit rounding

Here the shared guard/sticky decision theorem meets direct field rounding. Lower-candidate
semantics and the one-bit-wider threshold connect the two, and the resulting refinement says that
direct field rounding agrees with the standard appended-bit rounding specification in positive and
negative regimes alike.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding

open FloatLib.Numerics

/-!
## Rational midpoint semantics

A rational target need not be dyadic, a quotient like 1/3 for instance. A finite stream can
determine its rounded code anyway, provided the stream compares with its midpoint the same way the
target compares with the standard one-bit-wider threshold. That pair of order equivalences is
the theorem below.
-/

/--
Interior guard/sticky rounding implements an exact rational midpoint decision.

The order hypotheses connect the rational target to the finite stream, so callers can establish
the rounding decision independently of the Posit bit layout.
-/
theorem roundInteriorCode_eq_rationalMidpointDecision
    (format : Format) (regime : Int)
    (exponentField significand leading regimeFieldBits retained : Nat)
    (target : Rat)
    (hretained :
      format.payloadBits - regimeFieldBits = retained)
    (htrailing : retained < leading + 2)
    (hbelow :
      target <
          Model.roundingThreshold format
            (DirectDyadicPacking.lowerCandidateFromFields
              format regime exponentField significand leading) ↔
        exactTailRaw exponentField significand leading <
          streamMidpointRaw
            (exactTailRaw exponentField significand leading)
            (leading + 2) retained)
    (habove :
      Model.roundingThreshold format
            (DirectDyadicPacking.lowerCandidateFromFields
              format regime exponentField significand leading) <
          target ↔
        streamMidpointRaw
            (exactTailRaw exponentField significand leading)
            (leading + 2) retained <
          exactTailRaw exponentField significand leading) :
    roundInteriorCode format regime exponentField significand leading
        regimeFieldBits =
      let lower :=
        DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading
      let threshold := Model.roundingThreshold format lower
      if target < threshold then
        lower
      else if threshold < target then
        lower + 1
      else if lower % 2 = 0 then
        lower
      else
        lower + 1 := by
  unfold roundInteriorCode
  dsimp only
  rw [hretained]
  rw [roundFromLower_eq_midpointDecision
    (DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading)
    (exactTailRaw exponentField significand leading)
    (leading + 2) retained htrailing]
  by_cases htargetBelow :
      target <
        Model.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading)
  · have hrawBelow := hbelow.mp htargetBelow
    simp [htargetBelow, hrawBelow]
  · have hrawNotBelow :
        ¬exactTailRaw exponentField significand leading <
          streamMidpointRaw
            (exactTailRaw exponentField significand leading)
            (leading + 2) retained := by
      exact fun hrawBelow => htargetBelow (hbelow.mpr hrawBelow)
    by_cases htargetAbove :
        Model.roundingThreshold format
              (DirectDyadicPacking.lowerCandidateFromFields
                format regime exponentField significand leading) <
            target
    · have hrawAbove := habove.mp htargetAbove
      simp [htargetBelow, hrawNotBelow, htargetAbove, hrawAbove]
    · have hrawNotAbove :
          ¬streamMidpointRaw
              (exactTailRaw exponentField significand leading)
              (leading + 2) retained <
            exactTailRaw exponentField significand leading := by
        exact fun hrawAbove => htargetAbove (habove.mpr hrawAbove)
      simp [htargetBelow, hrawNotBelow, htargetAbove, hrawNotAbove]

/-!
## Interior rounding

The layout and semantic lemmas above pin down both adjacent encoded values and their one-bit-wider
rounding threshold. The helper below carries the argument for positive and negative regimes at
once. A complete stream is already exact, and a truncated stream is decided by its guard, sticky,
and retained parity bits alone.
-/

private theorem roundInteriorCode_eq_chooseNearest_of_semantics
    (format : Format) (regime : Int)
    (exponentField significand leading regimeFieldBits retained : Nat)
    (target : FloatLib.Numerics.Dyadic)
    (hretained :
      format.payloadBits - regimeFieldBits = retained)
    (hraw :
      exactTailRaw exponentField significand leading <
        2 ^ (leading + 2))
    (htarget :
      target.toRat =
        Model.trailingRat (leading + 2)
            (exactTailRaw exponentField significand leading) *
          (2 : Rat) ^ (regime * 4))
    (hthreshold :
      (DyadicRounding.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading)).toRat =
        Model.trailingRat (retained + 1)
            (2 * streamPrefix
                (exactTailRaw exponentField significand leading)
                (leading + 2) retained + 1) *
          (2 : Rat) ^ (regime * 4))
    (hlowerRange :
      DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading <
        format.signMaskNat)
    (hlowerValue :
      leading + 2 ≤ retained →
        Model.nonnegativeRatAt format
            (DirectDyadicPacking.lowerCandidateFromFields
              format regime exponentField significand leading) =
          target.toRat) :
    roundInteriorCode format regime exponentField significand leading
        regimeFieldBits =
      DyadicRounding.chooseNearestCode target
        (DyadicRounding.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading))
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading)
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) := by
  let width := leading + 2
  let raw :=
    exactTailRaw exponentField significand leading
  let lower :=
    DirectDyadicPacking.lowerCandidateFromFields
      format regime exponentField significand leading
  by_cases hcomplete : width ≤ retained
  · have hguard :
        streamGuard raw width retained = false := by
      unfold streamGuard
      rw [ite_eq_right (by omega)]
    have hsticky :
        streamSticky raw width retained = false := by
      unfold streamSticky
      have hzero : width - retained - 1 = 0 := by
        omega
      rw [hzero]
      simp [Nat.mod_one]
    have htargetLess :
        target.toRat <
          (DyadicRounding.roundingThreshold format lower).toRat := by
      rw [← hlowerValue hcomplete]
      rw [DyadicRounding.roundingThreshold_toRat]
      exact Model.nonnegativeRatAt_lt_roundingThreshold
        format hlowerRange
    have hless :
        target.isLess
            (DyadicRounding.roundingThreshold format lower) = true := by
      rw [Dyadic.isLess_eq_decide]
      simp only [decide_eq_true_eq]
      exact htargetLess
    unfold roundInteriorCode
    dsimp only
    rw [hretained, hguard, hsticky]
    simp [lower, DyadicRounding.chooseNearestCode_eq, hless]
  · have htrailing : retained < width := by
      omega
    unfold roundInteriorCode
    dsimp only
    rw [hretained]
    rw [roundFromLower_eq_midpointDecision
      lower raw width retained htrailing]
    rw [DyadicRounding.chooseNearestCode_eq]
    simp only [Dyadic.isLess_eq_decide, decide_eq_true_eq]
    rw [htarget, hthreshold]
    simp only [
      normalizedTail_lt_midpoint_iff regime hraw htrailing,
      midpoint_lt_normalizedTail_iff regime hraw htrailing]
    rfl

/--
Interior guard/sticky rounding selects the exact nearest-even code once the lower candidate and
its one-bit-wider threshold are known to denote the retained tail at the regime scale.

Both regime signs supply these two values from their own layout lemmas.
-/
private theorem roundInteriorCode_eq_chooseNearest_of_layout
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading regimeFieldBits retained : Nat)
    (hretained :
      format.payloadBits - regimeFieldBits = retained)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField)
    (hvalue :
      Model.nonnegativeRatAt format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading) =
        Model.trailingRat retained
            (DirectDyadicPacking.tailPrefix exponentField significand leading retained) *
          (2 : Rat) ^ (regime * 4))
    (hthreshold :
      Model.nonnegativeRatAt format.nextPrecision
          (2 * DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading + 1) =
        Model.trailingRat (retained + 1)
            (2 * DirectDyadicPacking.tailPrefix exponentField significand leading retained + 1) *
          (2 : Rat) ^ (regime * 4)) :
    roundInteriorCode format regime exponentField significand leading
        regimeFieldBits =
      DyadicRounding.chooseNearestCode
        { negative := false
          significand
          exponent := targetExponent }
        (DyadicRounding.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading))
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading)
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) := by
  have hnormalized :=
    normalizedValue_eq_trailingRat_mul_regime
      targetExponent regime exponentField significand leading
      hexponent hlower hupper hscale
  have htail :=
    tailPrefix_eq_streamPrefix exponentField significand leading retained hlower hupper
  apply roundInteriorCode_eq_chooseNearest_of_semantics
      format regime exponentField significand leading regimeFieldBits retained
      { negative := false
        significand
        exponent := targetExponent }
      hretained
      (exactTailRaw_lt_two_pow exponentField significand leading hexponent hlower hupper)
      hnormalized
  · rw [DyadicRounding.roundingThreshold_toRat]
    unfold Model.roundingThreshold
    rw [hthreshold, htail]
  · exact DirectDyadicPacking.lowerCandidateFromFields_lt_signMask
      format regime exponentField significand leading
      hexponent hlower hupper
  · intro hcomplete
    rw [hvalue, htail, trailingRat_streamPrefix_eq_of_width_le _ _ retained hcomplete]
    exact hnormalized.symm

/--
Direct guard/sticky rounding in an interior positive regime selects the exact nearest-even code.

The assumptions describe a normalized significand, a two-bit exponent field, and a regime that
leaves room for its terminator.
-/
theorem roundInteriorCode_eq_chooseNearest_positive
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    roundInteriorCode format regime exponentField significand leading
        (regime.toNat + 2) =
      DyadicRounding.chooseNearestCode
        { negative := false
          significand
          exponent := targetExponent }
        (DyadicRounding.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading))
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading)
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) :=
  roundInteriorCode_eq_chooseNearest_of_layout
    format targetExponent regime exponentField significand leading
    (regime.toNat + 2) (format.payloadBits - (regime.toNat + 1) - 1) (by omega)
    hexponent hlower hupper hscale
    (lowerCandidateValue_positive format regime exponentField significand leading
      hregime hrun hexponent hlower hupper)
    (lowerCandidateThreshold_positive format regime exponentField significand leading
      hregime hrun hexponent hlower hupper)

/--
Direct guard/sticky rounding in an interior negative regime selects the exact nearest-even code.

The proof is shared with the positive-regime theorem, and the two differ in the tapered regime
layout and the retained payload count alone.
-/
theorem roundInteriorCode_eq_chooseNearest_negative
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    roundInteriorCode format regime exponentField significand leading
        ((-regime).toNat + 1) =
      DyadicRounding.chooseNearestCode
        { negative := false
          significand
          exponent := targetExponent }
        (DyadicRounding.roundingThreshold format
          (DirectDyadicPacking.lowerCandidateFromFields
            format regime exponentField significand leading))
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading)
        (DirectDyadicPacking.lowerCandidateFromFields
          format regime exponentField significand leading + 1) :=
  roundInteriorCode_eq_chooseNearest_of_layout
    format targetExponent regime exponentField significand leading
    ((-regime).toNat + 1) (format.payloadBits - (-regime).toNat - 1) (by omega)
    hexponent hlower hupper hscale
    (lowerCandidateValue_negative format regime exponentField significand leading
      hregime hrun hexponent hlower hupper)
    (lowerCandidateThreshold_negative format regime exponentField significand leading
      hregime hrun hexponent hlower hupper)

/--
A normalized target whose regime is not below the smallest regime of the format is at least
`minPos`.
-/
private theorem not_isLess_minPositive_of_regime
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : -Int.ofNat (format.payloadBits - 1) ≤ regime)
    (hlower : 2 ^ leading ≤ significand)
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    ({ negative := false
       significand
       exponent := targetExponent } :
      FloatLib.Numerics.Dyadic).isLess
        (DyadicRounding.minPositive format) = false := by
  rw [Dyadic.isLess_eq_decide, decide_eq_false_iff_not, not_lt]
  unfold DyadicRounding.minPositive
  rw [Dyadic.toRat_mk_false, Dyadic.toRat_mk_false, Nat.cast_one, one_mul]
  calc
    (2 : Rat) ^ (-(4 * Int.ofNat (format.payloadBits - 1))) ≤
        (2 : Rat) ^ (regime * 4 + Int.ofNat exponentField) :=
      zpow_le_zpow_right₀ (by norm_num) (by simp only [Int.ofNat_eq_natCast] at *; omega)
    _ = (2 : Rat) ^ (targetExponent + Int.ofNat leading) := by rw [hscale]
    _ ≤ (significand : Rat) * (2 : Rat) ^ targetExponent :=
      zpow_add_le_mul_zpow targetExponent leading (by
        rw [Int.ofNat_eq_natCast, zpow_natCast]
        exact_mod_cast hlower)

/--
Interior positive-regime guard/sticky rounding is the complete exact-dyadic positive rounder.

A nonnegative regime puts the target at or above `minPos`. The interior layout ensures that the
lower candidate and its successor are both finite positive codes.
-/
theorem roundInteriorCode_eq_roundPositiveCode_positive
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hrun : regime.toNat + 1 < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    roundInteriorCode format regime exponentField significand leading
        (regime.toNat + 2) =
      DyadicRounding.roundPositiveCode format
        { negative := false
          significand
          exponent := targetExponent } := by
  have hsignificand : significand ≠ 0 := by
    have hpower := Nat.two_pow_pos leading
    omega
  have hnotUnderflow :=
    not_isLess_minPositive_of_regime format targetExponent regime exponentField significand
      leading (by simp only [Int.ofNat_eq_natCast]; omega) hlower hscale
  rw [roundInteriorCode_eq_chooseNearest_positive
      format targetExponent regime exponentField significand leading
      hregime hrun hexponent hlower hupper hscale,
    DyadicRounding.roundPositiveCode_eq_chooseNearestCode_of_lowerCode
      format _ _ hsignificand rfl hnotUnderflow
      (lowerCodeForPositive_eq_lowerCandidateFromFields_positive
        format targetExponent regime exponentField significand leading
        hregime hrun hexponent hlower hupper hscale)
      (lowerCandidateFromFields_succ_lt_signMask_positive
        format regime exponentField significand leading
        hregime hrun hexponent hlower hupper)]

/--
Interior negative-regime guard/sticky rounding is the complete exact-dyadic positive rounder.

This is the tapered-layout counterpart of
`roundInteriorCode_eq_roundPositiveCode_positive`, and both expose the same format-independent
semantic boundary to native-word and fixed-limb kernels.
-/
theorem roundInteriorCode_eq_roundPositiveCode_negative
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hrun : (-regime).toNat < format.payloadBits)
    (hexponent : exponentField < 4)
    (hlower : 2 ^ leading ≤ significand)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    roundInteriorCode format regime exponentField significand leading
        ((-regime).toNat + 1) =
      DyadicRounding.roundPositiveCode format
        { negative := false
          significand
          exponent := targetExponent } := by
  have hsignificand : significand ≠ 0 := by
    have hpower := Nat.two_pow_pos leading
    omega
  have hnotUnderflow :=
    not_isLess_minPositive_of_regime format targetExponent regime exponentField significand
      leading (by simp only [Int.ofNat_eq_natCast]; omega) hlower hscale
  rw [roundInteriorCode_eq_chooseNearest_negative
      format targetExponent regime exponentField significand leading
      hregime hrun hexponent hlower hupper hscale,
    DyadicRounding.roundPositiveCode_eq_chooseNearestCode_of_lowerCode
      format _ _ hsignificand rfl hnotUnderflow
      (lowerCodeForPositive_eq_lowerCandidateFromFields_negative
        format targetExponent regime exponentField significand leading
        hregime hrun hexponent hlower hupper hscale)
      (lowerCandidateFromFields_succ_lt_signMask_negative
        format regime exponentField significand leading
        hregime hrun hexponent hlower hupper)]


end FloatLib.Floats.Formats.Posit.Model.GuardStickyRounding
