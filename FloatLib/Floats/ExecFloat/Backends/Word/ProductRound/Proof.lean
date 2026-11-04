/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.ProductRound.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.Generic.ProductRound.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shared proof for finishing a native-word product

The one-word and two-word multiplication kernels end with the same stage: carry handling, the
overflow test, and field packing of a rounded `UInt64` significand, preceded by the normal-range
test (`normal_eq_normalSpec`). We prove that stage here. Product construction stays in each backend,
because the machine representation and its capacity bounds differ.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeWordProduct

open NativeSmallWord

/--
Decoding `finishWord` with its decline marker gives `finish?`.

The decline marker has to be at least `2 ^ fmt.bitWidth`, so that no packed word equals it. Such a
`UInt64` marker needs spare code space and exists only when `fmt.bitWidth ≤ 63`. The one-word
multiplier, the only user, has `Eligible` formats of at most 62 bits and the marker `2 ^ 63`.
Binary64 products go through the two-word multiplier, which calls `finishWord?` and declines with
`none`.
-/
theorem finishWord_decode
    (fmt : FloatFormat)
    (decline : UInt64)
    (hdecline : 2 ^ fmt.bitWidth ≤ decline.toNat)
    (sign : Bool) (position rounded : UInt64) :
    (if finishWord fmt decline sign position rounded == decline then
        none
      else
        some <| NativeSmallWord.ofWord <|
          finishWord fmt decline sign position rounded) =
      finish? fmt sign position rounded := by
  have hwidth : fmt.bitWidth ≤ 64 := by
    by_contra hwide
    have hpow : 2 ^ 64 < 2 ^ fmt.bitWidth := Nat.pow_lt_pow_right (by decide) (by omega)
    have := decline.toNat_lt
    omega
  let carry := rounded == carryBit fmt
  let normalizedPosition := if carry then position + 1 else position
  let overflowThreshold :=
    (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2)
  let normalizedMantissa :=
    if carry then hiddenBit fmt else rounded
  let exponentOffset :=
    (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2)
  let exponent := normalizedPosition - exponentOffset
  let fraction := normalizedMantissa - hiddenBit fmt
  let packed :=
    NativeSmallWord.packFields fmt sign exponent fraction
  change
    (if
        (if overflowThreshold < normalizedPosition then decline else packed) ==
            decline then
      none
    else
      some <| NativeSmallWord.ofWord <|
        if overflowThreshold < normalizedPosition then decline else packed) =
      (if overflowThreshold < normalizedPosition then
        none
      else
        some packed).map NativeSmallWord.ofWord
  by_cases hoverflow : overflowThreshold < normalizedPosition
  · simp [hoverflow]
  have hpacked :
      packed ≠ decline := by
    intro heq
    have hbound :=
      NativeSmallWord.packFields_toNat_lt
        hwidth sign exponent fraction
    have heqNat := congrArg UInt64.toNat heq
    unfold packed at heqNat
    omega
  simp [hoverflow, hpacked]

/-- A word chosen by the native carry test has the natural value chosen by the matching test. -/
private theorem toNat_ite_carry {p : Prop} [Decidable p] (carry : Bool) (hcarry : carry = true ↔ p)
    (chosen other : UInt64) (chosenNat otherNat : Nat) (hchosen : chosen.toNat = chosenNat)
    (hother : other.toNat = otherNat) :
    (if carry then chosen else other).toNat = if p then chosenNat else otherNat := by
  by_cases hp : p
  · rw [ite_eq_left (hcarry.mpr hp), ite_eq_left hp, hchosen]
  · rw [ite_eq_right (fun h => hp (hcarry.mp h)), ite_eq_right hp, hother]

/--
Native carry, overflow, and packing agree with the natural-number normal-result specification.

Callers supply the representation facts for their product implementation: the natural values of
the position and rounded significand and the no-wrap fact for incrementing the position. The
implicit and carry bits, the overflow threshold and the exponent offset are computed from the
width bound alone.
-/
theorem finish_eq
    (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64)
    (sign : Bool) (position rounded : UInt64)
    (positionNat roundedNat : Nat)
    (hposition : position.toNat = positionNat)
    (hpositionAdd : (position + 1).toNat = positionNat + 1)
    (hrounded : rounded.toNat = roundedNat)
    (hnormal :
      fmt.bias + 2 * fmt.fracWidth - 1 ≤ positionNat)
    (hroundedLower :
      2 ^ fmt.fracWidth ≤ roundedNat) :
    finish? fmt sign position rounded =
      (let carry := roundedNat = pow2 (fmt.fracWidth + 1)
       let normalizedPosition :=
         if carry then positionNat + 1 else positionNat
       let overflowThreshold :=
         3 * fmt.bias + 2 * fmt.fracWidth - 2
       if overflowThreshold < normalizedPosition then
         none
       else
         let normalizedMantissa :=
           if carry then pow2 fmt.fracWidth else roundedNat
         let exponentOffset :=
           fmt.bias + 2 * fmt.fracWidth - 2
         some <| ofFields fmt sign
           (normalizedPosition - exponentOffset)
           (normalizedMantissa - pow2 fmt.fracWidth)) := by
  have hhidden := hiddenBit_toNat_of_width fmt hwidth
  have hcarryBit := carryBit_toNat_of_width fmt hwidth
  unfold finish? finishWord?
  dsimp only
  rw [apply_ite (Option.map NativeSmallWord.ofWord), Option.map_none, Option.map_some]
  have hcarry :
      (rounded == carryBit fmt) =
        (roundedNat == 2 ^ (fmt.fracWidth + 1)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    rw [← UInt64.toNat_inj, hrounded, hcarryBit]
  rw [hcarry]
  let carry := roundedNat = 2 ^ (fmt.fracWidth + 1)
  let normalizedPositionWord :=
    if rounded == carryBit fmt then position + 1 else position
  let normalizedPositionNat :=
    if carry then positionNat + 1 else positionNat
  have hcarryIff : (rounded == carryBit fmt) = true ↔ carry := by
    rw [hcarry, beq_iff_eq]
  have hnormalizedPosition :
      normalizedPositionWord.toNat = normalizedPositionNat :=
    toNat_ite_carry _ hcarryIff _ _ _ _ hpositionAdd hposition
  have hoverflowThreshold :
      (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
        3 * fmt.bias + 2 * fmt.fracWidth - 2 :=
    overflowThreshold_toNat hwidth
  have hnormalizedPositionWordDef :
      (if (roundedNat == 2 ^ (fmt.fracWidth + 1)) = true then
          position + 1
        else position) = normalizedPositionWord := by
    unfold normalizedPositionWord
    rw [hcarry]
  have hnormalizedPositionNatDef :
      (if roundedNat = pow2 (fmt.fracWidth + 1) then
          positionNat + 1
        else positionNat) = normalizedPositionNat := by
    unfold normalizedPositionNat carry
    rw [pow2_eq_two_pow]
  rw [hnormalizedPositionWordDef, hnormalizedPositionNatDef]
  have hoverflowWordIff :
      (3 * biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2) <
          normalizedPositionWord ↔
        3 * fmt.bias + 2 * fmt.fracWidth - 2 <
          normalizedPositionNat := by
    rw [UInt64.lt_iff_toNat_lt, hoverflowThreshold,
      hnormalizedPosition]
  by_cases hoverflow :
      3 * fmt.bias + 2 * fmt.fracWidth - 2 <
        normalizedPositionNat
  · rw [ite_eq_left (hoverflowWordIff.mpr hoverflow),
      ite_eq_left hoverflow]
  rw [ite_eq_right (fun h => hoverflow (hoverflowWordIff.mp h)),
    ite_eq_right hoverflow]
  let normalizedMantissaWord :=
    if rounded == carryBit fmt then hiddenBit fmt else rounded
  let normalizedMantissaNat :=
    if carry then 2 ^ fmt.fracWidth else roundedNat
  have hnormalizedMantissa :
      normalizedMantissaWord.toNat = normalizedMantissaNat :=
    toNat_ite_carry _ hcarryIff _ _ _ _ hhidden hrounded
  have hexponentOffset :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2).toNat =
        fmt.bias + 2 * fmt.fracWidth - 2 :=
    exponentOffset_toNat hwidth
  have hexponentLe :
      (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2) ≤
        normalizedPositionWord := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hexponentOffset, hnormalizedPosition]
    unfold normalizedPositionNat carry
    split <;> omega
  have hexponent :
      (normalizedPositionWord -
          (biasWord fmt + 2 * UInt64.ofNat fmt.fracWidth - 2)).toNat =
        normalizedPositionNat -
          (fmt.bias + 2 * fmt.fracWidth - 2) := by
    rw [UInt64.toNat_sub_of_le _ _ hexponentLe,
      hnormalizedPosition, hexponentOffset]
  have hfractionLe :
      hiddenBit fmt ≤ normalizedMantissaWord := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hhidden, hnormalizedMantissa]
    unfold normalizedMantissaNat carry
    split <;> omega
  have hfraction :
      (normalizedMantissaWord - hiddenBit fmt).toNat =
        normalizedMantissaNat - 2 ^ fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _ hfractionLe,
      hnormalizedMantissa, hhidden]
  have hnormalizedMantissaWordDef :
      (if (roundedNat == 2 ^ (fmt.fracWidth + 1)) = true then
          hiddenBit fmt
        else rounded) = normalizedMantissaWord := by
    unfold normalizedMantissaWord
    rw [hcarry]
  have hnormalizedMantissaNatDef :
      (if roundedNat = pow2 (fmt.fracWidth + 1) then
          pow2 fmt.fracWidth
        else roundedNat) = normalizedMantissaNat := by
    unfold normalizedMantissaNat carry
    simp only [pow2_eq_two_pow]
  rw [hnormalizedMantissaWordDef, hnormalizedMantissaNatDef]
  rw [NativeSmallWord.ofWord_packFields hwidth]
  rw [hexponent, hfraction]
  simp only [pow2_eq_two_pow]

/--
The normal-range test and `finish?` of a native product kernel compute
`FiniteProductRound.normalSpec?` on normalized operands.

Callers supply their product representation through three words and their natural values: the
leading-bit position of the exact product, the normal threshold `bias + 2 * fracWidth - 1`, and
the product rounded to `fracWidth + 1` bits.
-/
theorem normal_eq_normalSpec
    (fmt : FloatFormat) (hwidth : fmt.bitWidth ≤ 64) (hexpWidth : fmt.expWidth ≤ 31)
    (hfracWidth : fmt.fracWidth ≤ 62)
    (sign : Bool) (xExponent yExponent xMantissa yMantissa : UInt64)
    (hxExponent : 0 < xExponent.toNat ∧ xExponent.toNat < 2 ^ fmt.expWidth)
    (hyExponent : 0 < yExponent.toNat ∧ yExponent.toNat < 2 ^ fmt.expWidth)
    (hxMantissa :
      2 ^ fmt.fracWidth ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hyMantissa :
      2 ^ fmt.fracWidth ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (leading threshold rounded : UInt64)
    (hleading : leading.toNat = (xMantissa.toNat * yMantissa.toNat).log2)
    (hthreshold : threshold.toNat = fmt.bias + 2 * fmt.fracWidth - 1)
    (hrounded :
      rounded.toNat =
        Numerics.roundShiftRightEven (xMantissa.toNat * yMantissa.toNat)
          ((xMantissa.toNat * yMantissa.toNat).log2 - fmt.fracWidth)) :
    (if leading + ((xExponent - 1) + (yExponent - 1)) < threshold then none
      else finish? fmt sign (leading + ((xExponent - 1) + (yExponent - 1))) rounded) =
      FiniteProductRound.normalSpec? fmt sign xExponent.toNat yExponent.toNat
        xMantissa.toNat yMantissa.toNat := by
  unfold FiniteProductRound.normalSpec?
  dsimp only
  set productNat := xMantissa.toNat * yMantissa.toNat
  have hpowExp : 2 ^ fmt.expWidth ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hexpWidth
  have hxExponent31 : xExponent.toNat < 2 ^ 31 := hxExponent.2.trans_le hpowExp
  have hyExponent31 : yExponent.toNat < 2 ^ 31 := hyExponent.2.trans_le hpowExp
  obtain ⟨hproductLower, hproductUpper⟩ :=
    FiniteProductRound.normalizedProduct_bounds fmt hxMantissa hyMantissa
  have hproductNe : productNat ≠ 0 := Nat.ne_of_gt ((Nat.two_pow_pos _).trans_le hproductLower)
  have hleadingLower : 2 * fmt.fracWidth ≤ leading.toNat := by
    rw [hleading]
    exact (Nat.le_log2 hproductNe).2 hproductLower
  have hleadingUpper : leading.toNat < 2 * fmt.fracWidth + 2 := by
    rw [hleading]
    exact (Nat.log2_lt hproductNe).2 hproductUpper
  have hscale := NativeSmallWord.productScale_toNat xExponent yExponent hxExponent.1 hyExponent.1
    (by omega)
  have hposition :
      (leading + ((xExponent - 1) + (yExponent - 1))).toNat =
        productNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) := by
    rw [UInt64.toNat_add, hleading, hscale]
    apply Nat.mod_eq_of_lt
    norm_num at hxExponent31 hyExponent31 ⊢
    omega
  have hbias : fmt.bias < 2 ^ 31 :=
    (FloatFormat.bias_lt_pow_expWidth fmt).trans_le hpowExp
  by_cases hsubnormal :
      productNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) <
        fmt.bias + 2 * fmt.fracWidth - 1
  · have hsubnormalWord :
        leading + ((xExponent - 1) + (yExponent - 1)) < threshold := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [hposition, hthreshold]
      exact hsubnormal
    rw [ite_eq_left hsubnormalWord, ite_eq_left hsubnormal]
  have hsubnormalWord :
      ¬leading + ((xExponent - 1) + (yExponent - 1)) < threshold := by
    intro h
    apply hsubnormal
    have hnat := UInt64.lt_iff_toNat_lt.mp h
    rwa [hposition, hthreshold] at hnat
  rw [ite_eq_right hsubnormalWord, ite_eq_right hsubnormal]
  have hpositionAdd :
      (leading + ((xExponent - 1) + (yExponent - 1)) + 1).toNat =
        productNat.log2 + ((xExponent.toNat - 1) + (yExponent.toNat - 1)) + 1 := by
    rw [FloatLib.Numerics.FixedWord.uint64_add_toNat_of_lt _ _ (by
      rw [hposition, UInt64.toNat_one]
      omega), hposition, UInt64.toNat_one]
  have hroundedLower :
      2 ^ fmt.fracWidth ≤
        Numerics.roundShiftRightEven productNat (productNat.log2 - fmt.fracWidth) := by
    have hfracLog : fmt.fracWidth ≤ productNat.log2 := by
      rw [← hleading]
      omega
    simpa [roundMantissaToLeadingBitEven, hfracLog, pow2_eq_two_pow] using
      pow2_le_roundMantissaToLeadingBitEven productNat fmt.fracWidth hproductNe
  exact finish_eq fmt hwidth sign _ rounded _ _ hposition hpositionAdd hrounded (by omega)
    hroundedLower

end Model.NativeWordProduct
end FloatLib.Floats.Formats.BinaryInterchange
