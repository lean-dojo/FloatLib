/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds

/-!
# Range-limited directed bounds for finite-only binary formats

Every word of an `Encoding.finite` descriptor denotes a finite real. Outward rounding therefore
has a real enclosure contract exactly while the exact value lies between the largest negative and
positive finite values. Unlike the IEEE theorem, no infinity is available outside that range.

These results are specific to `Encoding.finite`. Formats using `Encoding.finiteMaxNaN` or
`Encoding.finiteUnsignedZero` reserve exceptional words and need their own boundary arguments.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open Directed.Internal

noncomputable section

private theorem finite_maxFiniteFracField (fmt : FloatFormat)
    (hfmt : fmt.encoding = .finite) :
    fmt.maxFiniteFracField = pow2 fmt.fracWidth - 1 := by
  simp [FloatFormat.maxFiniteFracField, FloatFormat.fracMaskNat,
    pow2_eq_two_pow, hfmt]

private theorem finite_packingGuard_eq_false
    (fmt : FloatFormat) (hfmt : fmt.encoding = .finite)
    (exponent : Int) (fraction : Nat)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hmax : exponent ≤ fmt.maxNormalExponent)
    (hfraction : fraction < pow2 fmt.fracWidth) :
    let encodedExponent :=
      Int.toNat (exponent + Int.ofNat fmt.exponentBias)
    (decide (encodedExponent > fmt.maxFiniteExpField) ||
        encodedExponent == fmt.maxFiniteExpField &&
          decide (fraction > fmt.maxFiniteFracField)) = false := by
  have hexponent :=
    encodedExponent_le_maxFiniteExpField fmt exponent hmin hmax
  have hfractionLe : fraction ≤ fmt.maxFiniteFracField := by
    rw [finite_maxFiniteFracField fmt hfmt]
    omega
  have hexponentNot :
      ¬Int.toNat (exponent + Int.ofNat fmt.exponentBias) > fmt.maxFiniteExpField :=
    not_lt_of_ge hexponent
  have hfractionNot : ¬fraction > fmt.maxFiniteFracField :=
    not_lt_of_ge hfractionLe
  simp only [hexponentNot, hfractionNot, decide_false, Bool.and_false,
    Bool.or_false]

/-- Positive downward rounding in a finite-only format is a real lower bound. -/
theorem toReal_roundDyadicPosDown_le_of_encoding_finite
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.encoding = .finite) (hm : mantissa ≠ 0) :
    toReal (roundDyadicPosDown fmt mantissa exponent) ≤
      (mantissa : ℝ) * bpow exponent := by
  by_cases hoverflow :
      fmt.maxNormalExponent < (mantissa.log2 : Int) + exponent
  · rw [roundDyadicPosDown_eq_posMaxFinite_of_overflow
      fmt mantissa exponent hoverflow]
    have hleading :
        bpow ((mantissa.log2 : Int) + exponent) ≤
          (mantissa : ℝ) * bpow exponent := by
      rw [bpow_add]
      have hmantissa : bpow (Int.ofNat mantissa.log2) ≤ (mantissa : ℝ) := by
        rw [bpow_ofNat]
        exact_mod_cast pow2_log2_le hm
      exact mul_le_mul_of_nonneg_right hmantissa (bpow_nonneg exponent)
    have hpower :
        bpow (fmt.maxNormalExponent + 1) ≤
          bpow ((mantissa.log2 : Int) + exponent) :=
      bpow_le_bpow_of_le hoverflow
    exact (toReal_posMaxFinite_lt_bpow fmt).le.trans (hpower.trans hleading)
  · have hmax :
        (mantissa.log2 : Int) + exponent ≤ fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    by_cases hunderflow :
        (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
    · rw [roundDyadicPosDown_eq_zero_of_underflow
        fmt mantissa exponent hunderflow, toReal_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
    · have hlow :
          fmt.minSubnormalExponent ≤ (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hunderflow
      by_cases hsubnormal :
          (mantissa.log2 : Int) + exponent < fmt.minNormalExponent
      · rw [roundDyadicPosDown_eq_subnormal
          fmt mantissa exponent hlow hsubnormal]
        let rounded := roundMantissaAtExponentDown mantissa exponent
          fmt.minSubnormalExponent
        have hrounded : rounded < pow2 fmt.fracWidth :=
          roundMantissaAtExponentDown_minSubnormal_lt_pow2
            fmt mantissa exponent hsubnormal
        rw [toReal_roundSubnormalDown fmt rounded hrounded]
        exact roundMantissaAtExponentDown_mul_bpow_le
          mantissa exponent fmt.minSubnormalExponent
      · have hnormal :
          fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hsubnormal
        let rounded := roundMantissaToLeadingBitDown mantissa fmt.fracWidth
        have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
          pow2_le_roundMantissaToLeadingBitDown mantissa fmt.fracWidth hm
        have hroundedHigh : rounded < pow2 (fmt.fracWidth + 1) :=
          roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth
        have hfraction : rounded - pow2 fmt.fracWidth < pow2 fmt.fracWidth :=
          by simpa [pow2_eq_two_pow] using
            normalizedMantissa_sub_pow2_lt fmt rounded hroundedLow hroundedHigh
        have hguard := finite_packingGuard_eq_false fmt hfmt
          ((mantissa.log2 : Int) + exponent)
          (rounded - pow2 fmt.fracWidth) hnormal hmax hfraction
        rw [roundDyadicPosDown_eq_normal
          fmt mantissa exponent hnormal hmax]
        simp only [rounded] at hguard
        simp only [hguard, Bool.false_eq_true, if_false]
        rw [toReal_ofFields_normalized fmt rounded
          ((mantissa.log2 : Int) + exponent)
          hroundedLow hroundedHigh hnormal hmax
          (isFinite_eq_true_of_encoding_finite hfmt _)]
        have halign := roundMantissaAtExponentDown_mul_bpow_le mantissa exponent
          ((mantissa.log2 : Int) + exponent - (fmt.fracWidth : Int))
        rw [roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown] at halign
        simpa only [rounded, Int.ofNat_eq_natCast] using halign

/--
Within the largest-finite range, positive upward rounding in a finite-only format is a real upper
bound. Outside that range the executable operation saturates, so no such theorem is possible.
-/
theorem le_toReal_roundDyadicPosUp_of_encoding_finite
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.encoding = .finite) (hm : mantissa ≠ 0)
    (hbound :
      (mantissa : ℝ) * bpow exponent ≤ toReal (posMaxFinite fmt)) :
    (mantissa : ℝ) * bpow exponent ≤
      toReal (roundDyadicPosUp fmt mantissa exponent) := by
  by_cases hoverflow :
      fmt.maxNormalExponent < (mantissa.log2 : Int) + exponent
  · rw [roundDyadicPosUp_eq_nativeOverflow_of_overflow
      fmt mantissa exponent hoverflow]
    simpa only [nativeOverflow, hfmt, posMaxFinite] using hbound
  · have hmax :
        (mantissa.log2 : Int) + exponent ≤ fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    by_cases hunderflow :
        (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
    · rw [roundDyadicPosUp_eq_posMinSubnormal_of_underflow
        fmt mantissa exponent hunderflow, toReal_posMinSubnormal]
      have halign := le_roundMantissaAtExponentUp_mul_bpow
        mantissa exponent fmt.minSubnormalExponent
      rw [roundMantissaAtExponentUp_eq_one_of_lt_minSubnormal
        fmt mantissa exponent hm hunderflow] at halign
      simpa using halign
    · have hlow :
          fmt.minSubnormalExponent ≤ (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hunderflow
      by_cases hsubnormal :
          (mantissa.log2 : Int) + exponent < fmt.minNormalExponent
      · rw [roundDyadicPosUp_eq_subnormal
          fmt mantissa exponent hlow hsubnormal]
        let rounded := roundMantissaAtExponentUp mantissa exponent
          fmt.minSubnormalExponent
        have hroundedNe : rounded ≠ 0 :=
          roundMantissaAtExponentUp_ne_zero mantissa exponent
            fmt.minSubnormalExponent hm
        have hroundedHigh : rounded ≤ pow2 fmt.fracWidth :=
          roundMantissaAtExponentUp_minSubnormal_le_pow2
            fmt mantissa exponent hsubnormal
        rw [toReal_roundSubnormalUp fmt rounded hroundedNe hroundedHigh]
        exact le_roundMantissaAtExponentUp_mul_bpow
          mantissa exponent fmt.minSubnormalExponent
      · have hnormal :
          fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hsubnormal
        by_cases hcarry :
            roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
              pow2 (fmt.fracWidth + 1)
        · by_cases hcarryOverflow :
              fmt.maxNormalExponent <
                (mantissa.log2 : Int) + exponent + 1
          · rw [roundDyadicPosUp_eq_nativeOverflow_of_carry_overflow
              fmt mantissa exponent hnormal hmax hcarry hcarryOverflow]
            simpa only [nativeOverflow, hfmt, posMaxFinite] using hbound
          · have hcarryMax :
                (mantissa.log2 : Int) + exponent + 1 ≤
                  fmt.maxNormalExponent :=
              le_of_not_gt hcarryOverflow
            rw [roundDyadicPosUp_eq_normal_of_carry
              fmt mantissa exponent hnormal hmax hcarry hcarryMax]
            have hpack := toReal_ofFields_normalized fmt (pow2 fmt.fracWidth)
              ((mantissa.log2 : Int) + exponent + 1)
              le_rfl (pow2_lt_pow2_succ fmt.fracWidth)
              (by omega) hcarryMax
              (by
                simpa only [Nat.sub_self] using
                  isFinite_eq_true_of_encoding_finite hfmt
                    (ofFields fmt false
                      (Int.toNat
                        ((mantissa.log2 : Int) + exponent + 1 +
                          Int.ofNat fmt.exponentBias)) 0))
            simp only [Nat.sub_self] at hpack
            rw [hpack]
            have halign := le_roundMantissaAtExponentUp_mul_bpow mantissa exponent
              ((mantissa.log2 : Int) + exponent - (fmt.fracWidth : Int))
            rw [roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp,
              hcarry] at halign
            exact halign.trans_eq
              (normalizationCarry_value fmt
                ((mantissa.log2 : Int) + exponent)).symm
        · let rounded := roundMantissaToLeadingBitUp mantissa fmt.fracWidth
          have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
            pow2_le_roundMantissaToLeadingBitUp mantissa fmt.fracWidth hm
          have hroundedHigh : rounded < pow2 (fmt.fracWidth + 1) :=
            lt_of_le_of_ne
              (roundMantissaToLeadingBitUp_le_pow2_succ
                mantissa fmt.fracWidth) hcarry
          have hfraction : rounded - pow2 fmt.fracWidth < pow2 fmt.fracWidth :=
            by simpa [pow2_eq_two_pow] using
              normalizedMantissa_sub_pow2_lt fmt rounded hroundedLow hroundedHigh
          have hguard := finite_packingGuard_eq_false fmt hfmt
            ((mantissa.log2 : Int) + exponent)
            (rounded - pow2 fmt.fracWidth) hnormal hmax hfraction
          rw [roundDyadicPosUp_eq_normal_of_no_carry
            fmt mantissa exponent hnormal hmax hcarry]
          simp only [rounded] at hguard
          simp only [hguard, Bool.false_eq_true, if_false]
          rw [toReal_ofFields_normalized fmt rounded
            ((mantissa.log2 : Int) + exponent)
            hroundedLow hroundedHigh hnormal hmax
            (isFinite_eq_true_of_encoding_finite hfmt _)]
          have halign := le_roundMantissaAtExponentUp_mul_bpow mantissa exponent
            ((mantissa.log2 : Int) + exponent - (fmt.fracWidth : Int))
          rw [roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp] at halign
          simpa only [rounded, Int.ofNat_eq_natCast] using halign

/-- Finite-only formats have signed zeros. -/
theorem supportsSignedZero_eq_true_of_encoding_finite
    (fmt : FloatFormat) (hfmt : fmt.encoding = .finite) :
    fmt.supportsSignedZero = true := by
  simp [FloatFormat.supportsSignedZero, hfmt]

/-- Saturating overflow results of opposite signs are negations of each other. -/
theorem nativeOverflow_true_eq_neg_false_of_encoding_finite
    (fmt : FloatFormat) (hfmt : fmt.encoding = .finite) :
    nativeOverflow fmt true = neg (nativeOverflow fmt false) := by
  simp [nativeOverflow, hfmt]

/--
Range-limited downward rounding of an exact dyadic is a real lower bound in a finite-only format.
-/
theorem toReal_roundDyadicDown_le_of_encoding_finite
    (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.encoding = .finite)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    toReal (roundDyadicDown fmt d) ≤ d.toReal := by
  by_cases hmant : d.significand = 0
  · simp [roundDyadicDown, Numerics.Dyadic.toReal, hmant]
  · have hmagnitudeNonneg :
        0 ≤ (d.significand : ℝ) * bpow d.exponent :=
      mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
    have hmagnitude :
        (d.significand : ℝ) * bpow d.exponent ≤
          toReal (posMaxFinite fmt) := by
      by_cases hsign : d.negative <;>
        simpa [Numerics.Dyadic.toReal, hsign,
          abs_of_nonneg hmagnitudeNonneg,
          bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hbound
    by_cases hsign : d.negative
    · have hupper := le_toReal_roundDyadicPosUp_of_encoding_finite
        fmt d.significand d.exponent hfmt hmant hmagnitude
      have hfinite := isFinite_eq_true_of_encoding_finite hfmt
        (roundDyadicPosUp fmt d.significand d.exponent)
      rw [show roundDyadicDown fmt d =
          neg (roundDyadicPosUp fmt d.significand d.exponent) by
        simp only [roundDyadicDown, beq_iff_eq, hmant, if_false, hsign, if_true,
          roundDyadicPosUp]
        exact roundDyadicMagnitudeUp_true_eq_neg_false fmt d.significand d.exponent
          (supportsSignedZero_eq_true_of_encoding_finite fmt hfmt)
          (nativeOverflow_true_eq_neg_false_of_encoding_finite fmt hfmt)]
      rw [toReal_neg _ hfinite]
      simpa [Numerics.Dyadic.toReal, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using neg_le_neg hupper
    · simpa [roundDyadicDown, roundDyadicPosDown,
        Numerics.Dyadic.toReal, hmant, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        toReal_roundDyadicPosDown_le_of_encoding_finite
          fmt d.significand d.exponent hfmt hmant

/--
Range-limited upward rounding of an exact dyadic is a real upper bound in a finite-only format.
-/
theorem le_toReal_roundDyadicUp_of_encoding_finite
    (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.encoding = .finite)
    (hbound : |d.toReal| ≤ toReal (posMaxFinite fmt)) :
    d.toReal ≤ toReal (roundDyadicUp fmt d) := by
  by_cases hmant : d.significand = 0
  · simp [roundDyadicUp, Numerics.Dyadic.toReal, hmant]
  · have hmagnitudeNonneg :
        0 ≤ (d.significand : ℝ) * bpow d.exponent :=
      mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
    have hmagnitude :
        (d.significand : ℝ) * bpow d.exponent ≤
          toReal (posMaxFinite fmt) := by
      by_cases hsign : d.negative <;>
        simpa [Numerics.Dyadic.toReal, hsign,
          abs_of_nonneg hmagnitudeNonneg,
          bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using hbound
    by_cases hsign : d.negative
    · have hlower := toReal_roundDyadicPosDown_le_of_encoding_finite
        fmt d.significand d.exponent hfmt hmant
      have hfinite := isFinite_eq_true_of_encoding_finite hfmt
        (roundDyadicPosDown fmt d.significand d.exponent)
      rw [show roundDyadicUp fmt d =
          neg (roundDyadicPosDown fmt d.significand d.exponent) by
        simp only [roundDyadicUp, beq_iff_eq, hmant, if_false, hsign, if_true,
          roundDyadicPosDown]
        exact roundDyadicMagnitudeDown_true_eq_neg_false fmt d.significand d.exponent
          (supportsSignedZero_eq_true_of_encoding_finite fmt hfmt)]
      rw [toReal_neg _ hfinite]
      simpa [Numerics.Dyadic.toReal, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using neg_le_neg hlower
    · simpa [roundDyadicUp, roundDyadicPosUp,
        Numerics.Dyadic.toReal, hmant, hsign,
        bpow, Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal] using
        le_toReal_roundDyadicPosUp_of_encoding_finite
          fmt d.significand d.exponent hfmt hmant hmagnitude

/-- Range-limited downward addition is a real lower bound in a finite-only format. -/
theorem toReal_addDown_le_of_encoding_finite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.encoding = .finite)
    (hbound : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (addDown x y) ≤ toReal x + toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt x)
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt y)
  rw [← toReal_addDyadic_of_toDyadic?_some hdx hdy] at hbound ⊢
  rw [addDown, addWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy]
  split_ifs with hzero
  · simp [Numerics.Dyadic.toReal, hzero]
  · exact toReal_roundDyadicDown_le_of_encoding_finite fmt _ hfmt hbound

/-- Range-limited upward addition is a real upper bound in a finite-only format. -/
theorem le_toReal_addUp_of_encoding_finite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.encoding = .finite)
    (hbound : |toReal x + toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal x + toReal y ≤ toReal (addUp x y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt x)
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt y)
  rw [← toReal_addDyadic_of_toDyadic?_some hdx hdy] at hbound ⊢
  rw [addUp, addWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy]
  split_ifs with hzero
  · simp [Numerics.Dyadic.toReal, hzero]
  · exact le_toReal_roundDyadicUp_of_encoding_finite fmt _ hfmt hbound

/-- Range-limited downward subtraction is a real lower bound in a finite-only format. -/
theorem toReal_subDown_le_of_encoding_finite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.encoding = .finite)
    (hbound : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (subDown x y) ≤ toReal x - toReal y := by
  have hy := isFinite_eq_true_of_encoding_finite hfmt y
  change toReal (addDown x (neg y)) ≤ toReal x - toReal y
  simpa [toReal_neg y hy, sub_eq_add_neg] using
    toReal_addDown_le_of_encoding_finite x (neg y) hfmt
      (by simpa [toReal_neg y hy, sub_eq_add_neg] using hbound)

/-- Range-limited upward subtraction is a real upper bound in a finite-only format. -/
theorem le_toReal_subUp_of_encoding_finite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.encoding = .finite)
    (hbound : |toReal x - toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal x - toReal y ≤ toReal (subUp x y) := by
  have hy := isFinite_eq_true_of_encoding_finite hfmt y
  change toReal x - toReal y ≤ toReal (addUp x (neg y))
  simpa [toReal_neg y hy, sub_eq_add_neg] using
    le_toReal_addUp_of_encoding_finite x (neg y) hfmt
      (by simpa [toReal_neg y hy, sub_eq_add_neg] using hbound)

/-- Range-limited downward multiplication is a real lower bound in a finite-only format. -/
theorem toReal_mulDown_le_of_encoding_finite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.encoding = .finite)
    (hbound : |toReal x * toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal (mulDown x y) ≤ toReal x * toReal y := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt x)
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt y)
  rw [← toReal_mulDyadic_of_toDyadic?_some hdx hdy] at hbound ⊢
  rw [mulDown, mulWithRounding_eq_of_toDyadic?_some .towardNegativeInfinity nofun hdx hdy]
  exact toReal_roundDyadicDown_le_of_encoding_finite fmt _ hfmt hbound

/-- Range-limited upward multiplication is a real upper bound in a finite-only format. -/
theorem le_toReal_mulUp_of_encoding_finite
    {fmt : FloatFormat} (x y : Model fmt) (hfmt : fmt.encoding = .finite)
    (hbound : |toReal x * toReal y| ≤ toReal (posMaxFinite fmt)) :
    toReal x * toReal y ≤ toReal (mulUp x y) := by
  obtain ⟨dx, hdx⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt x)
  obtain ⟨dy, hdy⟩ := exists_toDyadic?_of_isFinite (isFinite_eq_true_of_encoding_finite hfmt y)
  rw [← toReal_mulDyadic_of_toDyadic?_some hdx hdy] at hbound ⊢
  rw [mulUp, mulWithRounding_eq_of_toDyadic?_some .towardPositiveInfinity nofun hdx hdy]
  exact le_toReal_roundDyadicUp_of_encoding_finite fmt _ hfmt hbound

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
