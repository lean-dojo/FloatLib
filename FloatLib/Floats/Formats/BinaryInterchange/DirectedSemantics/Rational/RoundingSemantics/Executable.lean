/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.RoundedReal

/-!
# Executable packing semantics

For a descriptor with `fmt.isIEEE = true`, a finite result produced by `roundRatScaled` denotes
`roundAt` applied to the corresponding real value. Finiteness excludes the zero denominator, whose
invalid result is a NaN.

The positive proof covers underflow, subnormal and normal results, including a carry into the next
exponent. Finiteness excludes the overflow branches. The signed theorem restores the sign through
the symmetry proved in `RoundedReal`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics
open Directed.Internal

section

/-! ## Executable packing semantics -/

/--
Positive scaled-rational rounding of a nonzero quotient denotes the independent nearest-even
rounded-real value whenever the executable result is finite.
-/
private theorem toReal_roundRatScaled_false_eq_roundAt_of_ne_zero
    (fmt : FloatFormat) (numerator denominator : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnumerator : numerator ≠ 0) (hdenominator : denominator ≠ 0)
    (hfinite : isFinite (roundRatScaled fmt false numerator denominator exponent) = true) :
    toReal (roundRatScaled fmt false numerator denominator exponent) =
      roundAt fmt (signedScaledRatToReal false numerator denominator exponent) := by
  have hinfinity := FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  have hsubnormalLt := minSubnormalExponent_lt_minNormalExponent fmt
  have hround :=
    roundAt_scaledRat_eq fmt false numerator denominator exponent hdenominator
  simp only [Bool.false_eq_true, ite_false, Int.ofNat_eq_natCast, Int.cast_natCast] at hround
  rcases lt_or_ge fmt.maxNormalExponent
      (Numerics.RationalBinary.floorLog2 numerator denominator + exponent) with hoverflow | hmax
  · rw [roundRatScaled_false_eq_posInf_of_maxNormal_lt
      fmt numerator denominator exponent hfmt hnumerator hdenominator hoverflow,
      isFinite_posInf fmt hinfinity] at hfinite
    exact absurd hfinite Bool.false_ne_true
  rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
      (fmt.minSubnormalExponent - 1) with hunderflow | hlow
  · rw [fexpOf_total_eq_minSubnormal fmt _ (by omega),
      roundQuotientEven_scaled_eq_zero numerator denominator _ hnumerator hdenominator
        (by omega)] at hround
    rw [roundRatScaled_false_eq_posZero_of_lt_minSubnormal_sub_one
      fmt numerator denominator exponent hfmt hnumerator hdenominator hunderflow,
      toReal_posZero, hround]
    simp
  rcases lt_or_ge (Numerics.RationalBinary.floorLog2 numerator denominator + exponent)
      fmt.minNormalExponent with hsubnormal | hnormal
  · have halign := subnormalAlignExp_add_minSubnormalExponent fmt
    rw [fexpOf_total_eq_minSubnormal fmt _ hsubnormal,
      show exponent - fmt.minSubnormalExponent =
        exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt) by omega] at hround
    rw [roundRatScaled_false_eq_subnormal
      fmt numerator denominator exponent hfmt hnumerator hdenominator hlow hsubnormal, hround]
    generalize hrounded :
      roundQuotientEven
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).1
        (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
          (exponent + Int.ofNat (FloatFormat.subnormalAlignExp fmt))).2 = rounded
    have hroundedLe : rounded ≤ pow2 fmt.fracWidth := by
      rw [← hrounded]
      exact roundQuotientEven_subnormal_le
        fmt numerator denominator exponent hnumerator hdenominator hsubnormal
    by_cases hzero : rounded = 0
    · simp [hzero, toReal_posZero]
    · simpa [hzero] using toReal_roundSubnormalUp fmt rounded hzero hroundedLe
  rw [fexpOf_total_eq_normal fmt _ hnormal,
    show exponent -
        (Numerics.RationalBinary.floorLog2 numerator denominator + exponent -
          Int.ofNat fmt.fracWidth) =
      Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator by
      omega] at hround
  have hbounds :=
    roundQuotientEven_normal_bounds fmt numerator denominator hnumerator hdenominator
  by_cases hcarry :
      roundQuotientEven
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)).1
          (Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator
            (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 numerator denominator)).2 =
        pow2 (fmt.fracWidth + 1)
  · have hcarryMax :
        Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1 ≤
          fmt.maxNormalExponent := by
      by_contra hnot
      rw [roundRatScaled_false_eq_posInf_of_carry
        fmt numerator denominator exponent hfmt hnumerator hdenominator hmax hcarry
          (lt_of_not_ge hnot),
        isFinite_posInf fmt hinfinity] at hfinite
      exact absurd hfinite Bool.false_ne_true
    rw [roundRatScaled_false_eq_normal_of_carry
      fmt numerator denominator exponent hfmt hnormal hcarry hcarryMax]
      at hfinite ⊢
    have hvalue :=
      toReal_ofFields_normalized fmt (pow2 fmt.fracWidth)
        (Numerics.RationalBinary.floorLog2 numerator denominator + exponent + 1)
        le_rfl (pow2_lt_pow2_succ fmt.fracWidth) (by omega) hcarryMax
        (by simpa only [Nat.sub_self] using hfinite)
    rw [Nat.sub_self] at hvalue
    rw [hvalue, hround, hcarry]
    exact normalizationCarry_value fmt _
  · rw [roundRatScaled_false_eq_normal_of_ne_carry
      fmt numerator denominator exponent hfmt hnumerator hdenominator hnormal hmax hcarry]
      at hfinite ⊢
    rw [toReal_ofFields_normalized fmt _ _ hbounds.1 (lt_of_le_of_ne hbounds.2 hcarry)
      hnormal hmax hfinite, hround]

/-- The invalid-operation result of a conventional IEEE format, its canonical NaN, is not finite. -/
private theorem isFinite_invalidResult_of_isIEEE (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    isFinite (invalidResult fmt) = false := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hexponent : expField (invalidResult fmt) = fmt.expAllOnesNat := by
    rw [invalidResult_eq_canonicalNaN_of_isIEEE fmt hfmt]
    change expField (ofBits ((posInf fmt).bits ||| FloatFormat.quietBit fmt)) = _
    rw [expField_or_quietBit]
    change expField (posInf fmt) = _
    rw [posInf_eq_ofModel_infinity, expField_ofModel_infinity]
  simp [isFinite, IEEE.isFinite, hencoding, hexponent]

/--
Finite scaled rational rounding is exact signed rational evaluation followed by one nearest-even
rounding in the destination format. A zero numerator rounds to zero. A zero denominator produces
the invalid NaN, which the finiteness hypothesis excludes.
-/
theorem toReal_roundRatScaled_eq_roundAt
    (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite (roundRatScaled fmt sign numerator denominator exponent) = true) :
    toReal (roundRatScaled fmt sign numerator denominator exponent) =
      roundAt fmt
        (signedScaledRatToReal sign numerator denominator exponent) := by
  have hdenominator : denominator ≠ 0 := by
    rintro rfl
    rw [roundRatScaled_den_zero, isFinite_invalidResult_of_isIEEE fmt hfmt] at hfinite
    exact Bool.false_ne_true hfinite
  by_cases hnumerator : numerator = 0
  · subst numerator
    rw [roundRatScaled_num_zero fmt sign denominator exponent hdenominator, toReal_zero]
    simp [signedScaledRatToReal, scaledRatToReal]
  cases sign with
  | false =>
      exact toReal_roundRatScaled_false_eq_roundAt_of_ne_zero
        fmt numerator denominator exponent hfmt hnumerator hdenominator hfinite
  | true =>
      rw [roundRatScaled_true_eq_neg_false
        fmt numerator denominator exponent hfmt hdenominator] at hfinite ⊢
      have hfiniteFalse :
          isFinite (roundRatScaled fmt false numerator denominator exponent) = true := by
        simpa using hfinite
      rw [toReal_neg _ hfiniteFalse,
        toReal_roundRatScaled_false_eq_roundAt_of_ne_zero
          fmt numerator denominator exponent hfmt hnumerator hdenominator hfiniteFalse]
      simp [signedScaledRatToReal, roundAt_neg]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
