/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Internal
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Properties
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Bounds for positive directed dyadic rounding

Positive executable dyadic rounding satisfies lower and upper bounds and agrees with real floor
or ceiling rounding in the stated finite cases. Downward overflow saturates at the largest
finite value, while upward overflow produces positive infinity.

The proofs separate underflow, subnormal, normal, and normalization-carry regimes. The public
results hide those packing details behind real and extended-real bounds. Formats without infinity
need range-limited upper-bound theorems instead: after finite saturation, no encoded value can
bound an arbitrarily large exact input.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open Directed.Internal

noncomputable section

private theorem nativeOverflow_false_eq_posInf
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    nativeOverflow fmt false = posInf fmt := by
  simp [nativeOverflow, FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt]

private theorem isFinite_roundSubnormalDown
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat) :
    isFinite
        (if mantissa = 0 then
          zero fmt false
        else
          ofFields fmt false 0 mantissa) = true := by
  by_cases hzero : mantissa = 0
  · rw [if_pos hzero]
    exact isFinite_eq_true_of_isZero_eq_true _
      (isZero_zero fmt false)
  · rw [if_neg hzero]
    exact isFinite_ofFields_ieee fmt hfmt false 0 mantissa
      fmt.expAllOnesNat_pos

private theorem isFinite_roundSubnormalUp
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (mantissa : Nat) :
    isFinite
        (if mantissa = 0 then
          posMinSubnormal fmt
        else if pow2 fmt.fracWidth ≤ mantissa then
          ofFields fmt false 1 0
        else
          ofFields fmt false 0 mantissa) = true := by
  by_cases hzero : mantissa = 0
  · simp [hzero, isFinite_posMinSubnormal]
  · rw [if_neg hzero]
    by_cases hnormal : pow2 fmt.fracWidth ≤ mantissa
    · rw [if_pos hnormal]
      exact isFinite_ofFields_ieee fmt hfmt false 1 0
        (by
          have hfour : 4 ≤ 2 ^ fmt.expWidth := by
            simpa using
              Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
                fmt.expWidth_ge_two
          unfold FloatFormat.expAllOnesNat
          omega)
    · rw [if_neg hnormal]
      exact isFinite_ofFields_ieee fmt hfmt false 0 mantissa
        fmt.expAllOnesNat_pos

/--
Below positive overflow, executable downward dyadic rounding equals independent real floor
rounding on the format grid.
-/
theorem toReal_roundDyadicPosDown_eq_roundAt_of_le_max
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent) :
    toReal (roundDyadicPosDown fmt mantissa exponent) =
      roundAtDown fmt ((mantissa : ℝ) * bpow exponent) := by
  by_cases hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
  · rw [roundDyadicPosDown_eq_zero_of_underflow fmt mantissa exponent hunderflow]
    rw [toReal_zero]
    rw [roundAtDown_pos_eq fmt mantissa exponent hfmt hm]
    rw [targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent
      (by
        rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
        exact hunderflow.trans (minSubnormalExponent_lt_minNormalExponent fmt))]
    rw [← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]
    rw [roundMantissaAtExponentDown_eq_zero_of_lt_minSubnormal
      fmt mantissa exponent hm hunderflow]
    simp
  · have hlow :
        fmt.minSubnormalExponent ≤
          (mantissa.log2 : Int) + exponent :=
      le_of_not_gt hunderflow
    by_cases hsubnormal :
        (mantissa.log2 : Int) + exponent <
          fmt.minNormalExponent
    · rw [roundDyadicPosDown_eq_subnormal fmt mantissa exponent hlow hsubnormal]
      let rounded :=
        roundMantissaAtExponentDown mantissa exponent
          (fmt.minSubnormalExponent)
      have hrounded :
          rounded < pow2 fmt.fracWidth :=
        roundMantissaAtExponentDown_minSubnormal_lt_pow2
          fmt mantissa exponent hsubnormal
      rw [toReal_roundSubnormalDown fmt rounded hrounded]
      rw [roundAtDown_pos_eq fmt mantissa exponent hfmt hm]
      rw [targetExponent_eq_minSubnormal_of_lt_minNormal
        fmt mantissa exponent (by
          rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
          exact hsubnormal)]
      rw [← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]
    · have hnormal :
          fmt.minNormalExponent ≤
            (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hsubnormal
      rw [roundDyadicPosDown_eq_normal fmt mantissa exponent hnormal hmax]
      let rounded :=
        roundMantissaToLeadingBitDown mantissa fmt.fracWidth
      have hroundedLow :
          pow2 fmt.fracWidth ≤ rounded :=
        pow2_le_roundMantissaToLeadingBitDown mantissa fmt.fracWidth hm
      have hroundedHigh :
          rounded < pow2 (fmt.fracWidth + 1) :=
        roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth
      have hguard :=
        normalizedGuard_eq_false fmt hfmt rounded
          ((mantissa.log2 : Int) + exponent)
          hroundedHigh hnormal hmax
      simp only [rounded] at hguard
      simp only [hguard, Bool.false_eq_true, if_false]
      rw [toReal_ofFields_normalized fmt rounded
        ((mantissa.log2 : Int) + exponent)
        hroundedLow hroundedHigh hnormal hmax
        (isFinite_ofFields_normalized fmt hfmt rounded
          ((mantissa.log2 : Int) + exponent)
          hnormal hmax)]
      rw [roundAtDown_pos_eq fmt mantissa exponent hfmt hm]
      rw [targetExponent_eq_normal fmt mantissa exponent (by
        rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
        exact hnormal)]
      rw [roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown
        mantissa fmt.fracWidth exponent]
      rfl

/-- Positive executable downward dyadic rounding never exceeds the exact real value. -/
theorem toReal_roundDyadicPosDown_le
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    toReal (roundDyadicPosDown fmt mantissa exponent) ≤
      (mantissa : ℝ) * bpow exponent := by
  by_cases hoverflow :
      fmt.maxNormalExponent <
        (mantissa.log2 : Int) + exponent
  · rw [roundDyadicPosDown_eq_posMaxFinite_of_overflow
      fmt mantissa exponent hoverflow]
    have hleading :
        bpow ((mantissa.log2 : Int) + exponent) ≤
          (mantissa : ℝ) * bpow exponent := by
      rw [bpow_add]
      have hmantissa :
          bpow (Int.ofNat mantissa.log2) ≤ (mantissa : ℝ) := by
        rw [bpow_ofNat]
        exact_mod_cast pow2_log2_le hm
      exact mul_le_mul_of_nonneg_right hmantissa (bpow_nonneg exponent)
    have hpower :
        bpow
            (fmt.maxNormalExponent + 1) ≤
          bpow ((mantissa.log2 : Int) + exponent) := by
      apply zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      simpa [bpow, bpow, Numerics.binaryRadix,
        Numerics.Radix.toReal] using hoverflow
    exact (toReal_posMaxFinite_lt_bpow fmt).le.trans
      (hpower.trans hleading)
  · have hmax :
        (mantissa.log2 : Int) + exponent ≤
          fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    rw [toReal_roundDyadicPosDown_eq_roundAt_of_le_max
      fmt mantissa exponent hfmt hm hmax]
    exact round_floor_le _

/-- Positive downward dyadic rounding always produces a finite value. -/
theorem isFinite_roundDyadicPosDown
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) :
    isFinite (roundDyadicPosDown fmt mantissa exponent) = true := by
  by_cases hoverflow :
      fmt.maxNormalExponent <
        (mantissa.log2 : Int) + exponent
  · rw [roundDyadicPosDown_eq_posMaxFinite_of_overflow
      fmt mantissa exponent hoverflow]
    exact isFinite_posMaxFinite fmt
  · have hmax :
        (mantissa.log2 : Int) + exponent ≤
          fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    by_cases hunderflow :
        (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
    · rw [roundDyadicPosDown_eq_zero_of_underflow fmt mantissa exponent hunderflow]
      exact isFinite_eq_true_of_isZero_eq_true _
        (isZero_zero fmt false)
    · have hlow :
          fmt.minSubnormalExponent ≤
            (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hunderflow
      by_cases hsubnormal :
          (mantissa.log2 : Int) + exponent <
            fmt.minNormalExponent
      · rw [roundDyadicPosDown_eq_subnormal fmt mantissa exponent hlow hsubnormal]
        exact isFinite_roundSubnormalDown fmt hfmt
          (roundMantissaAtExponentDown mantissa exponent
            fmt.minSubnormalExponent)
      · have hnormal :
            fmt.minNormalExponent ≤
              (mantissa.log2 : Int) + exponent :=
          le_of_not_gt hsubnormal
        let rounded :=
          roundMantissaToLeadingBitDown mantissa fmt.fracWidth
        have hroundedHigh :
            rounded < pow2 (fmt.fracWidth + 1) :=
          roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth
        have hfractionLe :
            rounded - pow2 fmt.fracWidth ≤ fmt.maxFiniteFracField :=
          fraction_le_maxFiniteFracField_ieee fmt hfmt rounded hroundedHigh
        have hguard :=
          packingGuard_eq_false fmt
            ((mantissa.log2 : Int) + exponent)
            (rounded - pow2 fmt.fracWidth)
            hnormal hmax hfractionLe
        rw [roundDyadicPosDown_eq_normal fmt mantissa exponent hnormal hmax]
        simp only [rounded] at hguard
        simp only [hguard, Bool.false_eq_true, if_false]
        exact
          isFinite_ofFields_of_normal_exponent fmt hfmt
            (rounded - pow2 fmt.fracWidth)
            ((mantissa.log2 : Int) + exponent)
            hnormal hmax

/-- Positive downward dyadic rounding is never classified as NaN. -/
theorem isNaN_roundDyadicPosDown_eq_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true) :
    isNaN (roundDyadicPosDown fmt mantissa exponent) = false :=
  isNaN_eq_false_of_isFinite_eq_true _
    (isFinite_roundDyadicPosDown fmt mantissa exponent hfmt)

/-- Positive downward dyadic rounding is a lower bound in the extended reals. -/
theorem toEReal_roundDyadicPosDown_le
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    toEReal (roundDyadicPosDown fmt mantissa exponent) ≤
      ((mantissa : ℝ) * bpow exponent : EReal) := by
  rw [toEReal_eq_coe_toReal_of_isFinite _
    (isFinite_roundDyadicPosDown fmt mantissa exponent hfmt)]
  exact EReal.coe_le_coe_iff.mpr
    (toReal_roundDyadicPosDown_le fmt mantissa exponent hfmt hm)

private theorem roundDyadicPosUp_underflow_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
      toReal (roundDyadicPosUp fmt mantissa exponent) =
        roundAtUp fmt ((mantissa : ℝ) * bpow exponent) := by
  have hround :=
    roundDyadicPosUp_eq_posMinSubnormal_of_underflow
      fmt mantissa exponent hunderflow
  constructor
  · rw [hround]
    exact isFinite_posMinSubnormal fmt
  · rw [hround, toReal_posMinSubnormal]
    rw [roundAtUp_pos_eq fmt mantissa exponent hfmt hm]
    rw [targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent
      (by
        rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
        exact hunderflow.trans (minSubnormalExponent_lt_minNormalExponent fmt))]
    rw [← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]
    rw [roundMantissaAtExponentUp_eq_one_of_lt_minSubnormal
      fmt mantissa exponent hm hunderflow]
    simp

private theorem roundDyadicPosUp_subnormal_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hlow :
      fmt.minSubnormalExponent ≤ (mantissa.log2 : Int) + exponent)
    (hhigh :
      (mantissa.log2 : Int) + exponent <
        fmt.minNormalExponent) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
      toReal (roundDyadicPosUp fmt mantissa exponent) =
        roundAtUp fmt ((mantissa : ℝ) * bpow exponent) := by
  let rounded :=
    roundMantissaAtExponentUp mantissa exponent
      (fmt.minSubnormalExponent)
  have hroundedNe : rounded ≠ 0 :=
    roundMantissaAtExponentUp_ne_zero mantissa exponent
      (fmt.minSubnormalExponent) hm
  have hroundedHigh : rounded ≤ pow2 fmt.fracWidth :=
    roundMantissaAtExponentUp_minSubnormal_le_pow2 fmt mantissa exponent hhigh
  have hround :=
    roundDyadicPosUp_eq_subnormal fmt mantissa exponent hlow hhigh
  constructor
  · rw [hround]
    exact isFinite_roundSubnormalUp fmt hfmt rounded
  · rw [hround]
    rw [toReal_roundSubnormalUp fmt rounded hroundedNe hroundedHigh]
    rw [roundAtUp_pos_eq fmt mantissa exponent hfmt hm]
    rw [targetExponent_eq_minSubnormal_of_lt_minNormal
      fmt mantissa exponent (by
        rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
        exact hhigh)]
    rw [← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]

private theorem roundDyadicPosUp_normal_no_carry_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth ≠
        pow2 (fmt.fracWidth + 1)) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
      toReal (roundDyadicPosUp fmt mantissa exponent) =
        roundAtUp fmt ((mantissa : ℝ) * bpow exponent) := by
  let rounded :=
    roundMantissaToLeadingBitUp mantissa fmt.fracWidth
  have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
    pow2_le_roundMantissaToLeadingBitUp mantissa fmt.fracWidth hm
  have hroundedHigh : rounded ≤ pow2 (fmt.fracWidth + 1) :=
    roundMantissaToLeadingBitUp_le_pow2_succ mantissa fmt.fracWidth
  have hroundedHigh' : rounded < pow2 (fmt.fracWidth + 1) :=
    lt_of_le_of_ne hroundedHigh hcarry
  have hround :=
    roundDyadicPosUp_eq_normal_of_no_carry
      fmt mantissa exponent hnormal hmax hcarry
  have hguard :=
    normalizedGuard_eq_false fmt hfmt rounded
      ((mantissa.log2 : Int) + exponent)
      hroundedHigh' hnormal hmax
  constructor
  · rw [hround]
    simp only [rounded] at hguard
    simp only [hguard, Bool.false_eq_true, if_false]
    exact
      isFinite_ofFields_normalized fmt hfmt rounded
        ((mantissa.log2 : Int) + exponent)
        hnormal hmax
  · rw [hround]
    simp only [rounded] at hguard
    simp only [hguard, Bool.false_eq_true, if_false]
    rw [toReal_ofFields_normalized fmt rounded
      ((mantissa.log2 : Int) + exponent)
      hroundedLow hroundedHigh' hnormal hmax
      (isFinite_ofFields_normalized fmt hfmt rounded
        ((mantissa.log2 : Int) + exponent)
        hnormal hmax)]
    rw [roundAtUp_pos_eq fmt mantissa exponent hfmt hm]
    rw [targetExponent_eq_normal fmt mantissa exponent (by
      rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
      exact hnormal)]
    rw [roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp
      mantissa fmt.fracWidth exponent]
    rfl

private theorem isFinite_roundDyadicPosUp_normal_of_carry
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
        pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      (mantissa.log2 : Int) + exponent + 1 ≤
        fmt.maxNormalExponent) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true := by
  have hnormalCarry :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent + 1 := by
    omega
  have hround :
      roundDyadicPosUp fmt mantissa exponent =
        ofFields fmt false
          (Int.toNat
            ((mantissa.log2 : Int) + exponent + 1 + Int.ofNat fmt.exponentBias))
          0 :=
    roundDyadicPosUp_eq_normal_of_carry
      fmt mantissa exponent hnormal hmax hcarry hcarryMax
  have hpack :=
    isFinite_ofFields_normalized fmt hfmt
      (pow2 fmt.fracWidth)
      ((mantissa.log2 : Int) + exponent + 1)
      hnormalCarry hcarryMax
  calc
    isFinite (roundDyadicPosUp fmt mantissa exponent) =
        isFinite
          (ofFields fmt false
            (Int.toNat
              ((mantissa.log2 : Int) + exponent + 1 + Int.ofNat fmt.exponentBias))
            0) :=
      congrArg isFinite hround
    _ = true := by simpa using hpack

private theorem toReal_roundDyadicPosUp_normal_of_carry_eq_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
        pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      (mantissa.log2 : Int) + exponent + 1 ≤
        fmt.maxNormalExponent) :
    toReal (roundDyadicPosUp fmt mantissa exponent) =
      roundAtUp fmt ((mantissa : ℝ) * bpow exponent) := by
  have hnormalCarry :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent + 1 := by
    omega
  have hround :
      roundDyadicPosUp fmt mantissa exponent =
        ofFields fmt false
          (Int.toNat
            ((mantissa.log2 : Int) + exponent + 1 + Int.ofNat fmt.exponentBias))
          0 :=
    roundDyadicPosUp_eq_normal_of_carry
      fmt mantissa exponent hnormal hmax hcarry hcarryMax
  have hpack :
      toReal
          (ofFields fmt false
            (Int.toNat
              ((mantissa.log2 : Int) + exponent + 1 + Int.ofNat fmt.exponentBias))
            0) =
        (pow2 fmt.fracWidth : ℝ) *
          bpow
            ((mantissa.log2 : Int) + exponent + 1 -
              Int.ofNat fmt.fracWidth) := by
    simpa using
      toReal_ofFields_normalized fmt
        (pow2 fmt.fracWidth)
        ((mantissa.log2 : Int) + exponent + 1)
        le_rfl (pow2_lt_pow2_succ fmt.fracWidth)
        hnormalCarry hcarryMax
        (isFinite_ofFields_normalized fmt hfmt
          (pow2 fmt.fracWidth)
          ((mantissa.log2 : Int) + exponent + 1)
          hnormalCarry hcarryMax)
  calc
    toReal (roundDyadicPosUp fmt mantissa exponent) =
        toReal
          (ofFields fmt false
            (Int.toNat
              ((mantissa.log2 : Int) + exponent + 1 + Int.ofNat fmt.exponentBias))
            0) :=
      congrArg toReal hround
    _ = (pow2 fmt.fracWidth : ℝ) *
          bpow
            ((mantissa.log2 : Int) + exponent + 1 -
              Int.ofNat fmt.fracWidth) :=
      hpack
    _ = roundAtUp fmt ((mantissa : ℝ) * bpow exponent) := by
      rw [roundAtUp_pos_eq fmt mantissa exponent hfmt hm]
      rw [targetExponent_eq_normal fmt mantissa exponent (by
        rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]
        exact hnormal)]
      rw [roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp
        mantissa fmt.fracWidth exponent]
      rw [hcarry]
      exact normalizationCarry_value fmt
        ((mantissa.log2 : Int) + exponent)

/--
Positive upward dyadic rounding is either positive infinity or the finite independent real
ceiling on the format grid.
-/
theorem roundDyadicPosUp_eq_posInf_or_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    roundDyadicPosUp fmt mantissa exponent = posInf fmt ∨
      (isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
        toReal (roundDyadicPosUp fmt mantissa exponent) =
          roundAtUp fmt ((mantissa : ℝ) * bpow exponent)) := by
  by_cases hoverflow :
      fmt.maxNormalExponent <
        (mantissa.log2 : Int) + exponent
  · exact Or.inl
      ((roundDyadicPosUp_eq_nativeOverflow_of_overflow
        fmt mantissa exponent hoverflow).trans
          (nativeOverflow_false_eq_posInf fmt hfmt))
  · have hmax :
        (mantissa.log2 : Int) + exponent ≤
          fmt.maxNormalExponent :=
      le_of_not_gt hoverflow
    by_cases hunderflow :
        (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
    · exact Or.inr
        (roundDyadicPosUp_underflow_finite_roundAt
          fmt mantissa exponent hfmt hm hunderflow)
    · have hlow :
          fmt.minSubnormalExponent ≤
            (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hunderflow
      by_cases hsubnormal :
          (mantissa.log2 : Int) + exponent <
            fmt.minNormalExponent
      · exact Or.inr
          (roundDyadicPosUp_subnormal_finite_roundAt
            fmt mantissa exponent hfmt hm hlow hsubnormal)
      · have hnormal :
            fmt.minNormalExponent ≤
              (mantissa.log2 : Int) + exponent :=
          le_of_not_gt hsubnormal
        by_cases hcarry :
            roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
              pow2 (fmt.fracWidth + 1)
        · by_cases hcarryOverflow :
              fmt.maxNormalExponent <
                (mantissa.log2 : Int) + exponent + 1
          · exact Or.inl
              ((roundDyadicPosUp_eq_nativeOverflow_of_carry_overflow
                fmt mantissa exponent hnormal hmax hcarry hcarryOverflow).trans
                  (nativeOverflow_false_eq_posInf fmt hfmt))
          · have hcarryMax :
                (mantissa.log2 : Int) + exponent + 1 ≤
                  fmt.maxNormalExponent :=
              le_of_not_gt hcarryOverflow
            exact Or.inr ⟨
              isFinite_roundDyadicPosUp_normal_of_carry
                fmt mantissa exponent hfmt hnormal hmax hcarry hcarryMax,
              toReal_roundDyadicPosUp_normal_of_carry_eq_roundAt
                fmt mantissa exponent hfmt hm hnormal hmax hcarry hcarryMax⟩
        · exact Or.inr
            (roundDyadicPosUp_normal_no_carry_finite_roundAt
              fmt mantissa exponent hfmt hm hnormal hmax hcarry)

/--
Positive upward dyadic rounding is finite and equals the real ceiling on the format grid whenever
the leading exponent is within range and normalizing the mantissa does not carry into the next
binade. The carry hypothesis is what separates this statement from
`roundDyadicPosUp_eq_posInf_or_finite_roundAt`: an exactly representable input never carries, so
it can never overflow under upward rounding.
-/
theorem roundDyadicPosUp_finite_roundAt_of_le_max_of_no_carry
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent)
    (hnoCarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth ≠
        pow2 (fmt.fracWidth + 1)) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
      toReal (roundDyadicPosUp fmt mantissa exponent) =
        roundAtUp fmt ((mantissa : ℝ) * bpow exponent) := by
  by_cases hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
  · exact roundDyadicPosUp_underflow_finite_roundAt
      fmt mantissa exponent hfmt hm hunderflow
  · have hlow :
        fmt.minSubnormalExponent ≤
          (mantissa.log2 : Int) + exponent :=
      le_of_not_gt hunderflow
    by_cases hsubnormal :
        (mantissa.log2 : Int) + exponent <
          fmt.minNormalExponent
    · exact roundDyadicPosUp_subnormal_finite_roundAt
        fmt mantissa exponent hfmt hm hlow hsubnormal
    · have hnormal :
          fmt.minNormalExponent ≤
            (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hsubnormal
      exact roundDyadicPosUp_normal_no_carry_finite_roundAt
        fmt mantissa exponent hfmt hm hnormal hmax hnoCarry

/-- Positive upward dyadic rounding is never classified as NaN. -/
theorem isNaN_roundDyadicPosUp_eq_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    isNaN (roundDyadicPosUp fmt mantissa exponent) = false := by
  rcases roundDyadicPosUp_eq_posInf_or_finite_roundAt
      fmt mantissa exponent hfmt hm with hinf | ⟨hfinite, _⟩
  · rw [hinf]
    exact isNaN_posInf fmt <|
      FloatFormat.supportsInfinity_eq_true_of_isIEEE fmt hfmt
  · exact isNaN_eq_false_of_isFinite_eq_true _ hfinite

/-- Positive upward dyadic rounding is an upper bound in the extended reals. -/
theorem le_toEReal_roundDyadicPosUp
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    ((mantissa : ℝ) * bpow exponent : EReal) ≤
      toEReal (roundDyadicPosUp fmt mantissa exponent) := by
  rcases roundDyadicPosUp_eq_posInf_or_finite_roundAt
      fmt mantissa exponent hfmt hm with hinf | ⟨hfinite, hround⟩
  · rw [hinf, toEReal_posInf fmt hfmt]
    exact le_top
  · rw [toEReal_eq_coe_toReal_of_isFinite _ hfinite, hround]
    exact EReal.coe_le_coe_iff.mpr (le_round_ceil _)

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
