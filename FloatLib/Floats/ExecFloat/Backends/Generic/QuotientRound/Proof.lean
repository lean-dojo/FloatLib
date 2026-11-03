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
  -- Both sides compute the same rounded significand and carry; read off `normalSpec?`'s answer.
  have hresult' := hresult
  dsimp only at hresult'
  simp only [hdenBool, hnumBool, Bool.or_self, Bool.false_eq_true, ite_false, hnotSub', hhigh',
    decide_false] at hresult'
  rw [Model.roundRatScaled, dite_eq_left hfmt]
  unfold Model.ieeeRoundRatScaled
  simp only [hdenBool, hnumBool, Bool.false_eq_true, ite_false, hhigh', hnotUnder', hnotSub']
  rw [hscaleRaw]
  dsimp only
  generalize Numerics.roundQuotientEven
    (num <<< (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den).toNat) den = m
    at hresult' ⊢
  by_cases hoverflow : Int.ofNat fmt.ieeeMaxNormalExponent <
      if (m == pow2 (fmt.fracWidth + 1)) = true then
        Numerics.RationalBinary.floorLog2 num den + exponent + 1
      else Numerics.RationalBinary.floorLog2 num den + exponent
  · rw [ite_eq_left hoverflow] at hresult'
    simp at hresult'
  · rw [ite_eq_right hoverflow] at hresult'
    simp only [gt_iff_lt, hoverflow, ite_false]
    exact (Option.some.inj hresult').symm

end FloatLib.Floats.Formats.BinaryInterchange.Model.FiniteQuotientRound
