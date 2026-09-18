/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Correctness of normal finite quotient rounding

Optimized finite-division backends share `normalSpec?` as their natural-number normal-result
specification. For conventional IEEE descriptors, `normalSpec_eq_roundRatScaled_of_some` proves
agreement with exact
nearest-even rational rounding when scaling the numerator requires a nonnegative left shift.
That shift bound is a caller obligation, not a check made by `normalSpec?`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound

/--
Candidate specification for a normal finite quotient.

Zero inputs and exponents outside the supported normal range return `none`. Agreement with exact
rational rounding requires `fmt.isIEEE = true` and
`RationalBinary.floorLog2 num den ≤ Int.ofNat fmt.fracWidth`; the latter ensures that the numerator
scaling is a left shift. Dispatchers use the complete rational implementation when a candidate
declines.
-/
def normalSpec? (fmt : FloatFormat) (sign : Bool)
    (num den : Nat) (exponent : Int) : Option (Model fmt) :=
  if den == 0 || num == 0 then
    none
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 num den
    let totalExponent := rationalExponent + exponent
    if totalExponent < fmt.ieeeMinNormalExponent ||
        Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent then
      none
    else
      let shift := Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
      let roundedMantissa :=
        Numerics.roundQuotientEven (num <<< shift) den
      let carry := roundedMantissa == Model.pow2 (fmt.fracWidth + 1)
      let normalizedExponent :=
        if carry then totalExponent + 1 else totalExponent
      if Int.ofNat fmt.ieeeMaxNormalExponent < normalizedExponent then
        none
      else
        let normalizedMantissa :=
          if carry then Model.pow2 fmt.fracWidth else roundedMantissa
        some <| Model.ofFields fmt sign
          (Int.toNat (normalizedExponent + Int.ofNat fmt.bias))
          (normalizedMantissa - Model.pow2 fmt.fracWidth)

/--
When numerator scaling is a nonnegative left shift, a successful normal quotient agrees with
conventional IEEE nearest-even rational rounding.
-/
theorem normalSpec_eq_roundRatScaled_of_some
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Bool) (num den : Nat) (exponent : Int) (result : Model fmt)
    (hshiftNonnegative :
      0 ≤ Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den)
    (hresult :
      normalSpec? fmt sign num den exponent = some result) :
    result = Model.roundRatScaled fmt sign num den exponent := by
  unfold normalSpec? at hresult
  by_cases hden : den = 0
  · simp [hden] at hresult
  by_cases hnum : num = 0
  · simp [hnum] at hresult
  let rationalExponent := Numerics.RationalBinary.floorLog2 num den
  let totalExponent := rationalExponent + exponent
  by_cases hlow : totalExponent < fmt.ieeeMinNormalExponent
  · simp [hden, hnum, rationalExponent, totalExponent, hlow] at hresult
  by_cases hhigh :
      Int.ofNat fmt.ieeeMaxNormalExponent < totalExponent
  · have hresult' := hresult
    simp [hden, hnum, rationalExponent, totalExponent, hlow] at hresult'
    exact (not_lt_of_ge hresult'.1 hhigh).elim
  have hbias := (fmt.isIEEE_eq_true_iff.mp hfmt).2
  have hnotUnder :
      ¬totalExponent < -Int.ofNat fmt.normalMantissaExpOffset := by
    have hoffset :
        Int.ofNat fmt.normalMantissaExpOffset =
          Int.ofNat fmt.bias + Int.ofNat fmt.fracWidth := by
      simp [FloatFormat.normalMantissaExpOffset, hbias]
    have hmin :
        fmt.ieeeMinNormalExponent = 1 - Int.ofNat fmt.bias := rfl
    have hfrac : 0 < Int.ofNat fmt.fracWidth := by
      simpa only [Int.ofNat_eq_natCast] using
        Int.natCast_pos.mpr fmt.fracWidth_pos
    intro hunder
    apply hlow
    rw [hmin]
    rw [hoffset] at hunder
    omega
  have hnotSub :
      ¬totalExponent < fmt.ieeeMinNormalExponent := hlow
  let shift :=
    Int.toNat (Int.ofNat fmt.fracWidth - rationalExponent)
  let roundedMantissa :=
    Numerics.roundQuotientEven (num <<< shift) den
  let carry :=
    roundedMantissa == Model.pow2 (fmt.fracWidth + 1)
  let normalizedExponent :=
    if carry then totalExponent + 1 else totalExponent
  have hscale :
      Numerics.RationalBinary.scaleByPowerOfTwo num den
          (Int.ofNat fmt.fracWidth - rationalExponent) =
        (num <<< shift, den) := by
    have hshift :
        Int.ofNat shift =
          Int.ofNat fmt.fracWidth - rationalExponent := by
      apply Int.toNat_of_nonneg
      simpa only [rationalExponent] using hshiftNonnegative
    rw [← hshift]
    rfl
  have hscaleRaw :
      Numerics.RationalBinary.scaleByPowerOfTwo num den
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den) =
        (num <<< (Int.ofNat fmt.fracWidth -
          Numerics.RationalBinary.floorLog2 num den).toNat, den) := by
    simpa only [shift, rationalExponent] using hscale
  have hhigh' :
      ¬Int.ofNat fmt.ieeeMaxNormalExponent <
        Numerics.RationalBinary.floorLog2 num den + exponent := by
    simpa only [totalExponent, rationalExponent] using hhigh
  have hnotUnder' :
      ¬Numerics.RationalBinary.floorLog2 num den + exponent <
        -Int.ofNat fmt.normalMantissaExpOffset := by
    simpa only [totalExponent, rationalExponent] using hnotUnder
  have hnotSub' :
      ¬Numerics.RationalBinary.floorLog2 num den + exponent <
        fmt.ieeeMinNormalExponent := by
    simpa only [totalExponent, rationalExponent] using hnotSub
  have hdenBool : (den == 0) = false := by
    simp [hden]
  have hnumBool : (num == 0) = false := by
    simp [hnum]
  cases hcarryValue : carry with
  | false =>
      have hcarry :
          roundedMantissa ≠ Model.pow2 (fmt.fracWidth + 1) := by
        simpa only [carry] using
          (beq_eq_false_iff_ne.mp hcarryValue)
      have hcarryRaw :
          Numerics.roundQuotientEven
              (num <<< (Int.ofNat fmt.fracWidth -
                Numerics.RationalBinary.floorLog2 num den).toNat) den ≠
            Model.pow2 (fmt.fracWidth + 1) := by
        simpa only [roundedMantissa, shift, rationalExponent] using hcarry
      have hcarryRawCast :
          Numerics.roundQuotientEven
              (num <<< ((fmt.fracWidth : Int) -
                Numerics.RationalBinary.floorLog2 num den).toNat) den ≠
            Model.pow2 (fmt.fracWidth + 1) := by
        simpa only [Int.ofNat_eq_natCast] using hcarryRaw
      have hnormalized :
          normalizedExponent = totalExponent := by
        simp only [normalizedExponent, hcarryValue, Bool.false_eq_true,
          ite_false]
      by_cases hoverflow :
          Int.ofNat fmt.ieeeMaxNormalExponent < normalizedExponent
      · rw [hnormalized] at hoverflow
        omega
      have hpacked :
          Model.ofFields fmt sign
              (Int.toNat (totalExponent + Int.ofNat fmt.bias))
              (roundedMantissa - Model.pow2 fmt.fracWidth) =
            result := by
        have hresult' := hresult
        simp [hden, hnum, rationalExponent, totalExponent, hlow] at hresult'
        have hpackedRaw := hresult'.2.2
        simpa only [totalExponent, rationalExponent, roundedMantissa, shift,
          Int.ofNat_eq_natCast, ite_eq_right hcarryRawCast] using hpackedRaw
      have hieee :
          Model.ieeeRoundRatScaled fmt sign num den exponent hfmt =
            Model.ofFields fmt sign
              (Int.toNat (totalExponent + Int.ofNat fmt.bias))
              (roundedMantissa - Model.pow2 fmt.fracWidth) := by
        unfold Model.ieeeRoundRatScaled
        have hoverflow' :
            ¬Int.ofNat fmt.ieeeMaxNormalExponent <
              Numerics.RationalBinary.floorLog2 num den + exponent := by
          simpa only [hnormalized, totalExponent, rationalExponent] using
            hoverflow
        have hcarryBool :
            (Numerics.roundQuotientEven
                (num <<< (Int.ofNat fmt.fracWidth -
                  Numerics.RationalBinary.floorLog2 num den).toNat) den ==
              Model.pow2 (fmt.fracWidth + 1)) = false :=
          beq_eq_false_iff_ne.mpr hcarryRaw
        simp only [hdenBool, hnumBool, Bool.false_eq_true, ite_false, hhigh',
          hnotUnder', hnotSub']
        rw [hscaleRaw]
        rw [hcarryBool]
        simp only [Bool.false_eq_true, ite_false, hoverflow', totalExponent,
          rationalExponent, roundedMantissa, shift]
      rw [Model.roundRatScaled, dite_eq_left hfmt]
      exact hpacked.symm.trans hieee.symm
  | true =>
      have hcarry :
          roundedMantissa = Model.pow2 (fmt.fracWidth + 1) := by
        simpa only [carry, beq_iff_eq] using hcarryValue
      have hcarryRaw :
          Numerics.roundQuotientEven
              (num <<< (Int.ofNat fmt.fracWidth -
                Numerics.RationalBinary.floorLog2 num den).toNat) den =
            Model.pow2 (fmt.fracWidth + 1) := by
        simpa only [roundedMantissa, shift, rationalExponent] using hcarry
      have hcarryRawCast :
          Numerics.roundQuotientEven
              (num <<< ((fmt.fracWidth : Int) -
                Numerics.RationalBinary.floorLog2 num den).toNat) den =
            Model.pow2 (fmt.fracWidth + 1) := by
        simpa only [Int.ofNat_eq_natCast] using hcarryRaw
      have hnormalized :
          normalizedExponent = totalExponent + 1 := by
        simp only [normalizedExponent, hcarryValue, ite_true]
      by_cases hoverflow :
          Int.ofNat fmt.ieeeMaxNormalExponent < normalizedExponent
      · have hresult' := hresult
        simp [hden, hnum, rationalExponent, totalExponent, hlow] at hresult'
        have hbound :
            totalExponent + 1 ≤
              Int.ofNat fmt.ieeeMaxNormalExponent := by
          have hboundRaw := hresult'.2.1
          rw [ite_eq_left hcarryRawCast] at hboundRaw
          simpa only [totalExponent, rationalExponent, Int.ofNat_eq_natCast] using
            hboundRaw
        rw [hnormalized] at hoverflow
        exact (not_lt_of_ge hbound hoverflow).elim
      have hpacked :
          Model.ofFields fmt sign
              (Int.toNat (totalExponent + 1 + Int.ofNat fmt.bias)) 0 =
            result := by
        have hresult' := hresult
        simp [hden, hnum, rationalExponent, totalExponent, hlow,
          Model.pow2_eq_two_pow] at hresult'
        have hpackedRaw := hresult'.2.2
        have hcarryRawPow :
            Numerics.roundQuotientEven
                (num <<< ((fmt.fracWidth : Int) -
                  Numerics.RationalBinary.floorLog2 num den).toNat) den =
              2 ^ (fmt.fracWidth + 1) := by
          simpa only [Int.ofNat_eq_natCast, Model.pow2_eq_two_pow] using
            hcarryRaw
        simpa only [Nat.sub_self, totalExponent, rationalExponent,
          Int.ofNat_eq_natCast, Model.pow2_eq_two_pow,
          ite_eq_left hcarryRawPow] using hpackedRaw
      have hieee :
          Model.ieeeRoundRatScaled fmt sign num den exponent hfmt =
            Model.ofFields fmt sign
              (Int.toNat (totalExponent + 1 + Int.ofNat fmt.bias)) 0 := by
        unfold Model.ieeeRoundRatScaled
        have hoverflow' :
            ¬Int.ofNat fmt.ieeeMaxNormalExponent <
              Numerics.RationalBinary.floorLog2 num den + exponent + 1 := by
          simpa only [hnormalized, totalExponent, rationalExponent] using
            hoverflow
        have hcarryBool :
            (Numerics.roundQuotientEven
                (num <<< (Int.ofNat fmt.fracWidth -
                  Numerics.RationalBinary.floorLog2 num den).toNat) den ==
              Model.pow2 (fmt.fracWidth + 1)) = true :=
          beq_iff_eq.mpr hcarryRaw
        have hcarryBoolPow :
            (Numerics.roundQuotientEven
                (num <<< (Int.ofNat fmt.fracWidth -
                  Numerics.RationalBinary.floorLog2 num den).toNat) den ==
              2 ^ (fmt.fracWidth + 1)) = true := by
          simpa only [Model.pow2_eq_two_pow] using hcarryBool
        simp only [hdenBool, hnumBool, Bool.false_eq_true, ite_false, hhigh',
          hnotUnder', hnotSub']
        rw [hscaleRaw]
        simp only [hcarryBoolPow, ite_true, hoverflow', ite_false,
          Model.pow2_eq_two_pow, Nat.sub_self, totalExponent,
          rationalExponent]
      rw [Model.roundRatScaled, dite_eq_left hfmt]
      exact hpacked.symm.trans hieee.symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound
