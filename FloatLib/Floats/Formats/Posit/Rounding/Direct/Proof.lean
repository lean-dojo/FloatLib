/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Candidate.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Rounding.GuardSticky.Semantics.Interior
public import FloatLib.Numerics.ShiftRightJam

import FloatLib.Numerics.Exact.Dyadic.Order

/-!
# Correctness of direct exact-dyadic posit packing

The one-pass scale, regime, exponent, fraction, guard, and sticky calculation in
`Direct.Runtime` refines the exact posit rounding specification at every width. It covers
regimes that consume the payload, appended-bit threshold ties, finite-endpoint saturation, and
negative results obtained through posit negation.

Direct packing avoids the reference rounder's search. Their equality gives both algorithms the
same semantics at every configured width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking

open FloatLib.Numerics

/-! ## Complete arbitrary-width rounding -/

/--
The scalar leading-exponent underflow check is exactly comparison with the format's minimum
positive value.
-/
private theorem isLessMinPositive_eq
    (format : Format) (target : FloatLib.Numerics.Dyadic)
    (hnegative : target.negative = false) :
    Dyadic.isLessPowerOfTwoAtLeading
        target.significand target.exponent
        (leadingBit target.significand)
        (-(4 * Int.ofNat (format.payloadBits - 1))) =
      target.isLess (DyadicRounding.minPositive format) := by
  rw [Dyadic.isLessPowerOfTwoAtLeading_eq
    target.significand target.exponent
    (leadingBit target.significand)
    (-(4 * Int.ofNat (format.payloadBits - 1)))
    (leadingBit_eq_log2 target.significand)]
  rw [Dyadic.isLessNonnegativeFields_eq, Dyadic.isLessFields_eq,
    DyadicRounding.minPositive_eq_fields]
  cases target
  simp_all

private theorem roundPositiveCode_eq_maxPositive_of_saturated
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : 0 ≤ regime)
    (hsaturated : format.payloadBits ≤ regime.toNat + 1)
    (hlower : 2 ^ leading ≤ significand)
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField)
    (hnotUnderflow :
      ({ negative := false
         significand
         exponent := targetExponent } :
        FloatLib.Numerics.Dyadic).isLess
          (DyadicRounding.minPositive format) = false) :
    DyadicRounding.roundPositiveCode format
        { negative := false
          significand
          exponent := targetExponent } =
      format.signMaskNat - 1 := by
  have hsignificand : significand ≠ 0 := by
    have hpower := Nat.two_pow_pos leading
    omega
  have hlowerRat :
      (2 : Rat) ^ Int.ofNat leading ≤ (significand : Rat) := by
    norm_num
    exact_mod_cast hlower
  have hlowerCode :
      DyadicRounding.lowerCodeForPositive format
          { negative := false
            significand
            exponent := targetExponent } =
        format.signMaskNat - 1 := by
    rw [DyadicRounding.lowerCodeForPositive_eq_reference]
    change
      Model.lowerCodeForPositive format
          ((significand : Rat) * (2 : Rat) ^ targetExponent) =
        format.signMaskNat - 1
    exact
      GuardStickyRounding.lowerCodeForPositive_eq_maxPositive_of_saturatedScale
        format (significand : Rat) targetExponent regime
        exponentField leading hregime hsaturated hlowerRat hscale
  unfold DyadicRounding.roundPositiveCode
  simp only [beq_eq_false_iff_ne.mpr hsignificand, Bool.false_or,
    Bool.false_eq_true, if_false]
  rw [if_neg (by simpa using hnotUnderflow)]
  rw [hlowerCode]
  rw [if_neg]
  have hpositive := format.signMaskNat_pos
  omega

private theorem negativeSaturatedUnderflows
    (format : Format) (targetExponent regime : Int)
    (exponentField significand leading : Nat)
    (hregime : regime < 0)
    (hsaturated : format.payloadBits ≤ (-regime).toNat)
    (hexponent : exponentField < 4)
    (hupper : significand < 2 ^ (leading + 1))
    (hscale :
      targetExponent + Int.ofNat leading =
        regime * 4 + Int.ofNat exponentField) :
    ({ negative := false
       significand
       exponent := targetExponent } :
      FloatLib.Numerics.Dyadic).isLess
        (DyadicRounding.minPositive format) = true := by
  have hupperRat :
      (significand : Rat) <
        (2 : Rat) ^ Int.ofNat (leading + 1) := by
    norm_num
    exact_mod_cast hupper
  rw [FloatLib.Numerics.Dyadic.isLess_eq_decide,
    decide_eq_true_eq, DyadicRounding.minPositive_toRat]
  change
    (significand : Rat) * (2 : Rat) ^ targetExponent <
      Model.minPositiveRat format
  exact
    GuardStickyRounding.normalizedTarget_lt_minPositive_of_saturatedScale
      format (significand : Rat) targetExponent regime
      exponentField leading hregime hsaturated hexponent
      hupperRat hscale

/-- Direct positive rounding selects exactly the shared exact-dyadic code. -/
theorem roundPositiveCode_eq_dyadic
    (format : Format) (target : FloatLib.Numerics.Dyadic) :
    roundPositiveCode format target =
      DyadicRounding.roundPositiveCode format target := by
  obtain ⟨negative, significand, exponent⟩ := target
  by_cases hspecial : (significand == 0 || negative) = true
  · simp only [roundPositiveCode, DyadicRounding.roundPositiveCode, hspecial,
      if_true]
  simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hspecial
  obtain ⟨hsignificand, hnegative⟩ := hspecial
  subst hnegative
  have hleading := leadingBit_eq_log2 significand
  have hlower : 2 ^ leadingBit significand ≤ significand :=
    hleading ▸ Nat.log2_self_le hsignificand
  have hupper : significand < 2 ^ (leadingBit significand + 1) :=
    hleading ▸ Nat.lt_log2_self
  have hmod : 0 ≤ (exponent + Int.ofNat (leadingBit significand)).emod 4 :=
    Int.emod_nonneg _ (by decide)
  have hmodLt : (exponent + Int.ofNat (leadingBit significand)).emod 4 < 4 :=
    Int.emod_lt_of_pos _ (by decide)
  have hexponent :
      ((exponent + Int.ofNat (leadingBit significand)).emod 4).toNat < 4 := by
    omega
  have hscale :
      exponent + Int.ofNat (leadingBit significand) =
        (exponent + Int.ofNat (leadingBit significand)).ediv 4 * 4 +
          Int.ofNat
            ((exponent + Int.ofNat (leadingBit significand)).emod 4).toNat := by
    simp only [Int.ofNat_eq_natCast] at hmod ⊢
    rw [Int.toNat_of_nonneg hmod]
    exact (Int.ediv_mul_add_emod _ 4).symm
  have hmin := isLessMinPositive_eq format ⟨false, significand, exponent⟩ rfl
  dsimp only at hmin
  unfold roundPositiveCode
  dsimp only
  rw [if_neg (by simpa using hsignificand), hmin]
  by_cases hunderflow :
      (⟨false, significand, exponent⟩ : FloatLib.Numerics.Dyadic).isLess
        (DyadicRounding.minPositive format) = true
  · rw [if_pos hunderflow]
    unfold DyadicRounding.roundPositiveCode
    rw [if_neg (by simpa using hsignificand), if_pos hunderflow]
  have hnotUnderflow := Bool.eq_false_iff.mpr hunderflow
  rw [if_neg hunderflow]
  split_ifs with hregime hsaturated hsaturated
  · exact (roundPositiveCode_eq_maxPositive_of_saturated format exponent _ _
      significand _ hregime hsaturated hlower hscale hnotUnderflow).symm
  · rw [GuardStickyRounding.roundInteriorCodeFromFields_eq_roundInteriorCode
      _ _ _ _ _ _ hlower hupper]
    exact GuardStickyRounding.roundInteriorCode_eq_roundPositiveCode_positive
      format exponent _ _ significand _ hregime (by omega) hexponent hlower
      hupper hscale hnotUnderflow
  · exact absurd (negativeSaturatedUnderflows format exponent _ _ significand _
      (by omega) hsaturated hexponent hupper hscale) hunderflow
  · rw [GuardStickyRounding.roundInteriorCodeFromFields_eq_roundInteriorCode
      _ _ _ _ _ _ hlower hupper]
    exact GuardStickyRounding.roundInteriorCode_eq_roundPositiveCode_negative
      format exponent _ _ significand _ (by omega) (by omega) hexponent hlower
      hupper hscale hnotUnderflow

/-! ## Shift-with-jam preservation -/

private theorem fractionPrefix_eq_div_sub
    (significand leading count : Nat)
    (hcount : count ≤ leading)
    (hlower : 2 ^ leading ≤ significand) :
    fractionPrefix significand leading count =
      significand / 2 ^ (leading - count) - 2 ^ count := by
  unfold fractionPrefix
  rw [if_pos hcount, Nat.shiftRight_eq_div_pow]
  simp only [Nat.shiftLeft_eq, one_mul]
  have hpower :
      2 ^ leading = 2 ^ (leading - count) * 2 ^ count := by
    rw [← pow_add]
    congr 1
    omega
  have hdecompose :
      significand =
        (significand - 2 ^ leading) +
          2 ^ (leading - count) * 2 ^ count := by
    calc
      significand =
          (significand - 2 ^ leading) + 2 ^ leading :=
        (Nat.sub_add_cancel hlower).symm
      _ =
          (significand - 2 ^ leading) +
            2 ^ (leading - count) * 2 ^ count := by
        rw [hpower]
  have hdivision :
      significand / 2 ^ (leading - count) =
        (significand - 2 ^ leading) / 2 ^ (leading - count) +
          2 ^ count := by
    calc
      significand / 2 ^ (leading - count) =
          ((significand - 2 ^ leading) +
              2 ^ (leading - count) * 2 ^ count) /
            2 ^ (leading - count) := by
        exact congrArg
          (fun value => value / 2 ^ (leading - count))
          hdecompose
      _ =
          (significand - 2 ^ leading) / 2 ^ (leading - count) +
            2 ^ count := by
        rw [Nat.add_mul_div_left _ _
          (Nat.two_pow_pos (leading - count))]
  rw [hdivision, Nat.add_sub_cancel]

private theorem fractionPrefix_shiftRightJam
    (significand shift window count : Nat)
    (hcount : count < window)
    (hjamLower :
      2 ^ window ≤ FloatLib.Numerics.shiftRightJam significand shift)
    (hlower : 2 ^ (shift + window) ≤ significand) :
    fractionPrefix
        (FloatLib.Numerics.shiftRightJam significand shift) window count =
      fractionPrefix significand (shift + window) count := by
  rw [fractionPrefix_eq_div_sub _ window count (by omega) hjamLower]
  rw [fractionPrefix_eq_div_sub _ (shift + window) count (by omega) hlower]
  rw [FloatLib.Numerics.shiftRightJam_div_pow
    significand shift (window - count) (by omega)]
  have hexponent :
      shift + (window - count) = shift + window - count := by
    omega
  rw [hexponent]

private theorem tailPrefix_shiftRightJam
    (exponentField significand shift window count : Nat)
    (hwindow : 2 ≤ window)
    (hcount : count ≤ window - 2)
    (hjamLower :
      2 ^ window ≤ FloatLib.Numerics.shiftRightJam significand shift)
    (hlower : 2 ^ (shift + window) ≤ significand) :
    tailPrefix exponentField
        (FloatLib.Numerics.shiftRightJam significand shift) window count =
      tailPrefix exponentField
        significand (shift + window) count := by
  unfold tailPrefix
  by_cases hexponent : count ≤ 2
  · rw [if_pos hexponent, if_pos hexponent]
  · rw [if_neg hexponent, if_neg hexponent]
    rw [fractionPrefix_shiftRightJam
      significand shift window (count - 2)
      (by omega) hjamLower hlower]

private theorem tailBit_shiftRightJam
    (exponentField significand shift window index : Nat)
    (hwindow : 2 ≤ window)
    (hindex : index ≤ window - 2) :
    GuardStickyRounding.tailBit exponentField
        (FloatLib.Numerics.shiftRightJam significand shift) window index =
      GuardStickyRounding.tailBit exponentField
        significand (shift + window) index := by
  unfold GuardStickyRounding.tailBit
  by_cases hexponent : index < 2
  · rw [if_pos hexponent, if_pos hexponent]
  · rw [if_neg hexponent, if_neg hexponent]
    dsimp only
    have hjamFraction : index - 2 < window := by omega
    have hvalueFraction : index - 2 < shift + window := by omega
    rw [if_pos hjamFraction, if_pos hvalueFraction]
    have hposition : 0 < window - (index - 2) - 1 := by omega
    rw [FloatLib.Numerics.shiftRightJam_testBit
      significand shift (window - (index - 2) - 1) hposition]
    congr 1
    omega

private theorem tailHasNonzeroAfter_shiftRightJam
    (exponentField significand shift window retained : Nat)
    (hwindow : 2 ≤ window)
    (hretained : retained ≤ window - 2) :
    GuardStickyRounding.tailHasNonzeroAfter exponentField
        (FloatLib.Numerics.shiftRightJam significand shift) window
        (retained + 1) =
      GuardStickyRounding.tailHasNonzeroAfter exponentField
        significand (shift + window) (retained + 1) := by
  by_cases hzero : retained = 0
  · subst retained
    unfold GuardStickyRounding.tailHasNonzeroAfter
    simp only [Nat.zero_add, Nat.reduceLT, if_true, Nat.reduceSub]
    apply congrArg (fun suffixNonzero =>
      exponentField % 2 != 0 || suffixNonzero)
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    exact FloatLib.Numerics.shiftRightJam_mod_pow_ne_zero_iff
      significand shift window (by omega)
  · unfold GuardStickyRounding.tailHasNonzeroAfter
    have hconsumed : ¬retained + 1 < 2 := by omega
    simp only [if_neg hconsumed]
    have hconsumedFraction : retained + 1 - 2 = retained - 1 := by
      omega
    rw [hconsumedFraction]
    have hjamFraction : retained - 1 < window := by omega
    have hvalueFraction : retained - 1 < shift + window := by omega
    simp only [if_pos hjamFraction, if_pos hvalueFraction]
    let extra := window - (retained - 1)
    have hextra : 0 < extra := by
      dsimp [extra]
      omega
    have hwidth :
        shift + extra =
          shift + window - (retained - 1) := by
      dsimp [extra]
      omega
    apply Bool.eq_iff_iff.mpr
    simp only [bne_iff_ne]
    rw [← hwidth]
    exact FloatLib.Numerics.shiftRightJam_mod_pow_ne_zero_iff
      significand shift extra hextra

private theorem lowerCandidateFromFields_shiftRightJam
    (format : Format) (regime : Int)
    (exponentField significand shift window : Nat)
    (hwindow : 2 ≤ window)
    (hpayload : format.payloadBits ≤ window)
    (hjamLower :
      2 ^ window ≤ FloatLib.Numerics.shiftRightJam significand shift)
    (hlower : 2 ^ (shift + window) ≤ significand)
    (hpositiveInterior :
      0 ≤ regime → regime.toNat + 1 < format.payloadBits)
    (hnegativeInterior :
      ¬0 ≤ regime → (-regime).toNat < format.payloadBits) :
    lowerCandidateFromFields format regime exponentField
        (FloatLib.Numerics.shiftRightJam significand shift) window =
      lowerCandidateFromFields format regime exponentField
        significand (shift + window) := by
  by_cases hregime : 0 ≤ regime
  · let run := regime.toNat + 1
    have hrun : run < format.payloadBits :=
      hpositiveInterior hregime
    have htrailing :
        format.payloadBits - run - 1 ≤ window - 2 := by
      dsimp [run]
      omega
    simp only [lowerCandidateFromFields, if_pos hregime]
    rw [tailPrefix_shiftRightJam exponentField significand shift
      window (format.payloadBits - run - 1)
      hwindow htrailing hjamLower hlower]
  · let run := (-regime).toNat
    have hrun : run < format.payloadBits :=
      hnegativeInterior hregime
    have hrunPositive : 0 < run := by
      dsimp [run]
      omega
    have htrailing :
        format.payloadBits - run - 1 ≤ window - 2 := by
      omega
    simp only [lowerCandidateFromFields, if_neg hregime]
    rw [tailPrefix_shiftRightJam exponentField significand shift
      window (format.payloadBits - run - 1)
      hwindow htrailing hjamLower hlower]

private theorem roundInteriorCodeFromFields_shiftRightJam
    (format : Format) (regime : Int)
    (exponentField significand shift window regimeFieldBits : Nat)
    (hwindow : 2 ≤ window)
    (hpayload : format.payloadBits ≤ window)
    (hregimeFieldBits : 2 ≤ regimeFieldBits)
    (hinterior : regimeFieldBits ≤ format.payloadBits)
    (hjamLower :
      2 ^ window ≤ FloatLib.Numerics.shiftRightJam significand shift)
    (hlower : 2 ^ (shift + window) ≤ significand)
    (hpositiveInterior :
      0 ≤ regime → regime.toNat + 1 < format.payloadBits)
    (hnegativeInterior :
      ¬0 ≤ regime → (-regime).toNat < format.payloadBits) :
    GuardStickyRounding.roundInteriorCodeFromFields format regime exponentField
        (FloatLib.Numerics.shiftRightJam significand shift) window
        regimeFieldBits =
      GuardStickyRounding.roundInteriorCodeFromFields format regime exponentField
        significand (shift + window) regimeFieldBits := by
  have hretained :
      format.payloadBits - regimeFieldBits ≤ window - 2 := by
    omega
  unfold GuardStickyRounding.roundInteriorCodeFromFields
  dsimp only
  rw [lowerCandidateFromFields_shiftRightJam format regime exponentField
    significand shift window hwindow hpayload hjamLower hlower
    hpositiveInterior hnegativeInterior]
  rw [tailBit_shiftRightJam exponentField significand shift window
    (format.payloadBits - regimeFieldBits) hwindow hretained]
  rw [tailHasNonzeroAfter_shiftRightJam exponentField significand shift window
    (format.payloadBits - regimeFieldBits) hwindow hretained]

/--
Retaining a normalized leading window and jamming every discarded one into its low bit preserves
the complete direct Posit code.

The theorem is independent of a storage carrier. The retained value has its leading one at index
`window`, so it occupies `window + 1` bits. The bounds `2 ≤ window` and
`format.payloadBits ≤ window` leave room for the rounding information. The dyadic exponent
increases by the discarded shift.
-/
theorem roundPositiveCode_shiftRightJam
    (format : Format) (window : Nat)
    (hwindow : 2 ≤ window)
    (hpayload : format.payloadBits ≤ window)
    (significand shift : Nat) (exponent : Int)
    (hlower : 2 ^ (shift + window) ≤ significand)
    (hupper : significand < 2 ^ (shift + window + 1))
    (hjammedUpper :
      FloatLib.Numerics.shiftRightJam significand shift <
        2 ^ (window + 1)) :
    roundPositiveCode format
        { negative := false
          significand :=
            FloatLib.Numerics.shiftRightJam significand shift
          exponent := exponent + Int.ofNat shift } =
      roundPositiveCode format
        { negative := false
          significand
          exponent } := by
  have hsignificand : significand ≠ 0 :=
    Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hlower)
  have hsignificandLog : significand.log2 = shift + window :=
    (Nat.log2_eq_iff hsignificand).2 ⟨hlower, hupper⟩
  have hjammedLower :
      2 ^ window ≤ FloatLib.Numerics.shiftRightJam significand shift := by
    have hquotient :=
      FloatLib.Numerics.shiftRightJam_div_pow significand shift window (by omega)
    exact (Nat.div_pos_iff.1
      (hquotient ▸ Nat.div_pos hlower (Nat.two_pow_pos _))).2
  have hjammedNe : FloatLib.Numerics.shiftRightJam significand shift ≠ 0 :=
    Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hjammedLower)
  have hjammedLog :
      (FloatLib.Numerics.shiftRightJam significand shift).log2 = window :=
    (Nat.log2_eq_iff hjammedNe).2 ⟨hjammedLower, hjammedUpper⟩
  have hscale :
      exponent + Int.ofNat shift + Int.ofNat window =
        exponent + Int.ofNat (shift + window) := by
    simp only [Int.ofNat_eq_natCast, Int.natCast_add, add_assoc]
  unfold roundPositiveCode Dyadic.isLessPowerOfTwoAtLeading
  simp only [Bool.or_false, beq_iff_eq, hjammedNe, hsignificand, ↓reduceIte,
    leadingBit_eq_log2, hjammedLog, hsignificandLog, hscale]
  split_ifs <;>
    first
    | rfl
    | (apply roundInteriorCodeFromFields_shiftRightJam _ _ _ _ _ _ _ hwindow
        hpayload _ _ hjammedLower hlower <;> omega)

/-- Direct positive rounding always returns a nonnegative finite code. -/
theorem roundPositiveCode_lt_signMask
    (format : Format) (target : FloatLib.Numerics.Dyadic) :
    roundPositiveCode format target < format.signMaskNat := by
  rw [roundPositiveCode_eq_dyadic]
  unfold DyadicRounding.roundPositiveCode
  split
  · exact format.signMaskNat_pos
  · split
    · exact format.one_lt_signMaskNat
    · dsimp only
      have hlower :
          DyadicRounding.lowerCodeForPositive format target <
            format.signMaskNat := by
        unfold DyadicRounding.lowerCodeForPositive
        apply Model.lowerCodeByBisection_lt_upper
        exact format.signMaskNat_pos
      split
      · rename_i hupper
        rcases DyadicRounding.chooseNearestCode_eq_lower_or_upper
            target
            (DyadicRounding.roundingThreshold format
              (DyadicRounding.lowerCodeForPositive format target))
            (DyadicRounding.lowerCodeForPositive format target)
            (DyadicRounding.lowerCodeForPositive format target + 1) with
          hchoice | hchoice
        · rw [hchoice]
          exact hlower
        · rw [hchoice]
          exact hupper
      · exact hlower

/-- Direct positive result packing is extensionally the shared dyadic rounder. -/
theorem roundPositive_eq_dyadic
    (format : Format) (target : FloatLib.Numerics.Dyadic) :
    roundPositive format target =
      DyadicRounding.roundPositive format target := by
  unfold roundPositive DyadicRounding.roundPositive
  rw [roundPositiveCode_eq_dyadic]

/-- Every direct signed code is a valid complete Posit encoding. -/
theorem roundCode_lt_modulus
    (format : Format) (value : FloatLib.Numerics.Dyadic) :
    roundCode format value < format.modulus := by
  unfold roundCode
  split
  · exact Nat.two_pow_pos format.bits
  · dsimp only
    apply DyadicRounding.restoreSignCode_lt_modulus
    exact roundPositiveCode_lt_signMask format _

/-- Re-encoding the direct code gives the model-valued direct rounder. -/
theorem ofNatBits_roundCode
    (format : Format) (value : FloatLib.Numerics.Dyadic) :
    Model.ofNatBits (roundCode format value) =
      round format value := by
  unfold roundCode round
  split
  · rfl
  · dsimp only
    have hpositive :=
      roundPositiveCode_lt_signMask format
        (DyadicRounding.magnitude value)
    rw [DyadicRounding.ofNatBits_restoreSignCode
      format value.negative _ hpositive]
    rfl

/-- Complete direct exact-dyadic rounding equals the exact model rounder. -/
theorem round_eq_dyadic
    (format : Format) (value : FloatLib.Numerics.Dyadic) :
    round format value = DyadicRounding.round format value := by
  unfold round DyadicRounding.round
  split
  · rfl
  · dsimp only
    split <;> rw [roundPositive_eq_dyadic]

/-- Complete direct rounding therefore equals exact rational Posit Standard rounding. -/
theorem round_eq_roundRat
    (format : Format) (value : FloatLib.Numerics.Dyadic) :
    round format value = Model.roundRat format value.toRat := by
  rw [round_eq_dyadic, DyadicRounding.round_eq_roundRat]

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicPacking
