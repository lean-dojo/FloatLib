/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Internal
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ERealSemantics
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SignedSemantics.Core

/-!
# Bounds for positive directed dyadic rounding

Positive executable downward dyadic rounding is finite and a real lower bound in every encoding,
because downward overflow saturates at the largest finite value. For conventional IEEE formats,
upward rounding is an upper bound, with overflow to positive infinity, and both directions agree
with real floor or ceiling rounding in the stated finite cases.

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

section

private theorem nativeOverflow_false_eq_posInf
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) :
    nativeOverflow fmt false = posInf fmt := by
  simp [nativeOverflow, FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt]

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
  · rw [ite_eq_right hzero]
    by_cases hnormal : pow2 fmt.fracWidth ≤ mantissa
    · rw [ite_eq_left hnormal]
      exact isFinite_ofFields_ieee fmt hfmt false 1 0 (FloatFormat.one_lt_expAllOnesNat fmt)
    · rw [ite_eq_right hnormal]
      exact isFinite_ofFields_ieee fmt hfmt false 0 mantissa
        fmt.expAllOnesNat_pos

/--
Below the normal range, downward positive rounded-real semantics is floor alignment at the
minimum subnormal exponent.
-/
private theorem roundAt_down_pos_eq_of_lt_minNormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (h : (mantissa.log2 : Int) + exponent < fmt.minNormalExponent) :
    roundAt fmt ((mantissa : ℝ) * bpow exponent) .down =
      (roundMantissaAtExponentDown mantissa exponent fmt.minSubnormalExponent : ℝ) *
        bpow fmt.minSubnormalExponent := by
  rw [roundAt_down_pos_eq fmt mantissa exponent hfmt,
    targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent
      (by rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]; exact h),
    ← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]

/--
Below the normal range, upward positive rounded-real semantics is ceiling alignment at the
minimum subnormal exponent.
-/
private theorem roundAt_up_pos_eq_of_lt_minNormal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (h : (mantissa.log2 : Int) + exponent < fmt.minNormalExponent) :
    roundAt fmt ((mantissa : ℝ) * bpow exponent) .up =
      (roundMantissaAtExponentUp mantissa exponent fmt.minSubnormalExponent : ℝ) *
        bpow fmt.minSubnormalExponent := by
  rw [roundAt_up_pos_eq fmt mantissa exponent hfmt,
    targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent
      (by rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]; exact h),
    ← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]

/--
In the normal range, downward positive rounded-real semantics is floor normalization of the
mantissa to its leading bit, at the leading exponent.
-/
private theorem roundAt_down_pos_eq_of_minNormal_le
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (h : fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent) :
    roundAt fmt ((mantissa : ℝ) * bpow exponent) .down =
      (roundMantissaToLeadingBitDown mantissa fmt.fracWidth : ℝ) *
        bpow ((mantissa.log2 : Int) + exponent - Int.ofNat fmt.fracWidth) := by
  rw [roundAt_down_pos_eq fmt mantissa exponent hfmt,
    targetExponent_eq_normal fmt mantissa exponent
      (by rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]; exact h),
    roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown mantissa fmt.fracWidth exponent]
  rfl

/--
In the normal range, upward positive rounded-real semantics is ceiling normalization of the
mantissa to its leading bit, at the leading exponent.
-/
private theorem roundAt_up_pos_eq_of_minNormal_le
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (h : fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent) :
    roundAt fmt ((mantissa : ℝ) * bpow exponent) .up =
      (roundMantissaToLeadingBitUp mantissa fmt.fracWidth : ℝ) *
        bpow ((mantissa.log2 : Int) + exponent - Int.ofNat fmt.fracWidth) := by
  rw [roundAt_up_pos_eq fmt mantissa exponent hfmt,
    targetExponent_eq_normal fmt mantissa exponent
      (by rw [← FloatFormat.minNormalExponent_eq_ieee fmt hfmt]; exact h),
    roundMantissaAtExponentUp_eq_roundMantissaToLeadingBitUp mantissa fmt.fracWidth exponent]
  rfl

/--
In an IEEE format a normalized mantissa at a normal exponent passes the packing overflow guard, so
the guarded normal pack is the finite word denoting `rounded * 2^(exponent - fracWidth)`, whichever
overflow word the guard would select.
-/
private theorem isFinite_toReal_guardedNormalPack
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (overflow : Model fmt)
    (rounded : Nat) (exponent : Int)
    (hlow : pow2 fmt.fracWidth ≤ rounded) (hhigh : rounded < pow2 (fmt.fracWidth + 1))
    (hnormal : fmt.minNormalExponent ≤ exponent) (hmax : exponent ≤ fmt.maxNormalExponent) :
    let encodedExponent := Int.toNat (exponent + Int.ofNat fmt.exponentBias)
    let fraction := rounded - pow2 fmt.fracWidth
    let word :=
      if encodedExponent > fmt.maxFiniteExpField ||
          (encodedExponent == fmt.maxFiniteExpField && fraction > fmt.maxFiniteFracField) then
        overflow
      else
        ofFields fmt false encodedExponent fraction
    isFinite word = true ∧
      toReal word = (rounded : ℝ) * bpow (exponent - Int.ofNat fmt.fracWidth) := by
  have hguard := normalizedGuard_eq_false fmt hfmt rounded exponent hhigh hmax
  dsimp only at hguard ⊢
  simp only [hguard, Bool.false_eq_true, ite_false]
  have hfinite := isFinite_ofFields_normalized fmt hfmt rounded exponent hmax
  exact ⟨hfinite, toReal_ofFields_normalized fmt rounded exponent hlow hhigh hnormal hmax hfinite⟩

/--
In a conventional IEEE format, below positive overflow, executable downward dyadic rounding equals
independent real floor rounding on the format grid.
-/
theorem toReal_roundDyadicPosDown_eq_roundAt_of_le_max
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hmax :
      (mantissa.log2 : Int) + exponent ≤
        fmt.maxNormalExponent) :
    toReal (roundDyadicPosDown fmt mantissa exponent) =
      roundAt fmt ((mantissa : ℝ) * bpow exponent) .down := by
  by_cases hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
  · rw [roundDyadicPosDown_eq_zero_of_underflow fmt mantissa exponent hunderflow]
    rw [toReal_zero, roundAt_down_pos_eq_of_lt_minNormal fmt mantissa exponent hfmt
      (hunderflow.trans (minSubnormalExponent_lt_minNormalExponent fmt))]
    rw [roundMantissaAtExponentDown_eq_zero_of_lt_minSubnormal
      fmt mantissa exponent hunderflow]
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
      rw [toReal_roundSubnormalDown fmt rounded hrounded,
        roundAt_down_pos_eq_of_lt_minNormal fmt mantissa exponent hfmt hsubnormal]
    · have hnormal :
          fmt.minNormalExponent ≤
            (mantissa.log2 : Int) + exponent :=
        le_of_not_gt hsubnormal
      rw [roundDyadicPosDown_eq_normal fmt mantissa exponent hnormal hmax,
        roundAt_down_pos_eq_of_minNormal_le fmt mantissa exponent hfmt hnormal]
      exact (isFinite_toReal_guardedNormalPack fmt hfmt (posMaxFinite fmt) _ _
        (pow2_le_roundMantissaToLeadingBitDown mantissa fmt.fracWidth hm)
        (roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth) hnormal hmax).2

/--
A word packed by the positive normal path is finite whenever the shared overflow guard does not
fire, in every encoding: the guard keeps the exponent field at or below the largest finite field
and, at that field, the fraction at or below the largest finite fraction.
-/
private theorem isFinite_ofFields_of_packingGuard_eq_false
    (fmt : FloatFormat) (exponent : Int) (fraction : Nat)
    (hmin : fmt.minNormalExponent ≤ exponent)
    (hfraction : fraction < 2 ^ fmt.fracWidth)
    (hguard :
      ¬(decide (Int.toNat (exponent + Int.ofNat fmt.exponentBias) > fmt.maxFiniteExpField) ||
          (Int.toNat (exponent + Int.ofNat fmt.exponentBias) == fmt.maxFiniteExpField &&
            decide (fraction > fmt.maxFiniteFracField))) = true) :
    isFinite
        (ofFields fmt false (Int.toNat (exponent + Int.ofNat fmt.exponentBias)) fraction) =
      true := by
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
    not_or, not_and, not_lt] at hguard
  apply isFinite_ofFields_normal_of_le_maxFinite
  · exact encodedExponent_ne_zero fmt exponent hmin
  · exact hfraction
  · omega

/--
Positive executable downward dyadic rounding never exceeds the exact real value, in every
encoding.
-/
theorem toReal_roundDyadicPosDown_le
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0) :
    toReal (roundDyadicPosDown fmt mantissa exponent) ≤
      (mantissa : ℝ) * bpow exponent := by
  have hleading :
      bpow ((mantissa.log2 : Int) + exponent) ≤ (mantissa : ℝ) * bpow exponent := by
    rw [bpow_add]
    have hmantissa : bpow (Int.ofNat mantissa.log2) ≤ (mantissa : ℝ) := by
      rw [bpow_ofNat]
      exact_mod_cast pow2_log2_le hm
    exact mul_le_mul_of_nonneg_right hmantissa (bpow_nonneg exponent)
  by_cases hoverflow : fmt.maxNormalExponent < (mantissa.log2 : Int) + exponent
  · rw [roundDyadicPosDown_eq_posMaxFinite_of_overflow fmt mantissa exponent hoverflow]
    exact (toReal_posMaxFinite_lt_bpow fmt).le.trans
      ((bpow_le_bpow_of_le hoverflow).trans hleading)
  have hmax : (mantissa.log2 : Int) + exponent ≤ fmt.maxNormalExponent :=
    le_of_not_gt hoverflow
  by_cases hunderflow : (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent
  · rw [roundDyadicPosDown_eq_zero_of_underflow fmt mantissa exponent hunderflow, toReal_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (bpow_nonneg _)
  have hlow : fmt.minSubnormalExponent ≤ (mantissa.log2 : Int) + exponent :=
    le_of_not_gt hunderflow
  by_cases hsubnormal : (mantissa.log2 : Int) + exponent < fmt.minNormalExponent
  · rw [roundDyadicPosDown_eq_subnormal fmt mantissa exponent hlow hsubnormal]
    rw [toReal_roundSubnormalDown fmt _
      (roundMantissaAtExponentDown_minSubnormal_lt_pow2 fmt mantissa exponent hsubnormal)]
    exact roundMantissaAtExponentDown_mul_bpow_le mantissa exponent fmt.minSubnormalExponent
  have hnormal : fmt.minNormalExponent ≤ (mantissa.log2 : Int) + exponent :=
    le_of_not_gt hsubnormal
  let rounded := roundMantissaToLeadingBitDown mantissa fmt.fracWidth
  have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
    pow2_le_roundMantissaToLeadingBitDown mantissa fmt.fracWidth hm
  have hroundedHigh : rounded < pow2 (fmt.fracWidth + 1) :=
    roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth
  have halign :
      (rounded : ℝ) * bpow ((mantissa.log2 : Int) + exponent - Int.ofNat fmt.fracWidth) ≤
        (mantissa : ℝ) * bpow exponent := by
    have h := roundMantissaAtExponentDown_mul_bpow_le mantissa exponent
      ((mantissa.log2 : Int) + exponent - (fmt.fracWidth : Int))
    rw [roundMantissaAtExponentDown_eq_roundMantissaToLeadingBitDown] at h
    simpa only [rounded, Int.ofNat_eq_natCast] using h
  rw [roundDyadicPosDown_eq_normal fmt mantissa exponent hnormal hmax]
  dsimp only
  split_ifs with hguard
  · -- The guard fires only at the largest exponent field with a fraction above the largest
    -- finite fraction, so the saturated result lies below the normalized mantissa.
    have hexponent := encodedExponent_le_maxFiniteExpField fmt _ hmax
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at hguard
    have hfield :
        Int.toNat ((mantissa.log2 : Int) + exponent + Int.ofNat fmt.exponentBias) =
            fmt.maxFiniteExpField ∧
          fmt.maxFiniteFracField < rounded - pow2 fmt.fracWidth := by
      omega
    have htotal : (mantissa.log2 : Int) + exponent = fmt.maxNormalExponent := by
      have hfieldInt := congrArg Int.ofNat hfield.1
      rw [ofNat_toNat_biasedExponent fmt _ hnormal] at hfieldInt
      unfold FloatFormat.maxNormalExponent
      omega
    rw [toReal_posMaxFinite, ← htotal]
    refine le_trans ?_ halign
    apply mul_le_mul_of_nonneg_right _ (bpow_nonneg _)
    exact_mod_cast (show pow2 fmt.fracWidth + fmt.maxFiniteFracField ≤ rounded by omega)
  · rw [toReal_ofFields_normalized fmt rounded _ hroundedLow hroundedHigh hnormal hmax
      (isFinite_ofFields_of_packingGuard_eq_false fmt _ _ hnormal
        (normalizedMantissa_sub_pow2_lt fmt rounded hroundedHigh) hguard)]
    exact halign

/-- Positive downward dyadic rounding always produces a finite value, in every encoding. -/
theorem isFinite_roundDyadicPosDown
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) :
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
        have hrounded := roundMantissaAtExponentDown_minSubnormal_lt_pow2
          fmt mantissa exponent hsubnormal
        dsimp only
        split_ifs
        · exact isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt false)
        · rw [isFinite_ofFields fmt false 0 _ (Nat.two_pow_pos _)
            (by simpa [pow2_eq_two_pow] using hrounded)]
          have hzeroAllOnes : (0 : Nat) ≠ fmt.expAllOnesNat :=
            (FloatFormat.expAllOnesNat_pos fmt).ne
          cases fmt.encoding <;> simp [hzeroAllOnes]
      · have hnormal :
            fmt.minNormalExponent ≤
              (mantissa.log2 : Int) + exponent :=
          le_of_not_gt hsubnormal
        have hroundedHigh :=
          roundMantissaToLeadingBitDown_lt_pow2_succ mantissa fmt.fracWidth
        rw [roundDyadicPosDown_eq_normal fmt mantissa exponent hnormal hmax]
        dsimp only
        split_ifs with hguard
        · exact isFinite_posMaxFinite fmt
        · apply isFinite_ofFields_of_packingGuard_eq_false fmt _ _ hnormal _ hguard
          rw [pow2_eq_two_pow, pow_succ] at hroundedHigh
          rw [pow2_eq_two_pow]
          omega

/-- Positive downward dyadic rounding is never classified as NaN. -/
theorem isNaN_roundDyadicPosDown_eq_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) :
    isNaN (roundDyadicPosDown fmt mantissa exponent) = false :=
  isNaN_eq_false_of_isFinite_eq_true _
    (isFinite_roundDyadicPosDown fmt mantissa exponent)

/-- Positive downward dyadic rounding is a lower bound in the extended reals. -/
theorem toEReal_roundDyadicPosDown_le
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hm : mantissa ≠ 0) :
    toEReal (roundDyadicPosDown fmt mantissa exponent) ≤
      ((mantissa : ℝ) * bpow exponent : EReal) := by
  rw [toEReal_eq_coe_toReal_of_isFinite _
    (isFinite_roundDyadicPosDown fmt mantissa exponent)]
  exact EReal.coe_le_coe_iff.mpr
    (toReal_roundDyadicPosDown_le fmt mantissa exponent hm)

private theorem roundDyadicPosUp_underflow_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0)
    (hunderflow :
      (mantissa.log2 : Int) + exponent < fmt.minSubnormalExponent) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
      toReal (roundDyadicPosUp fmt mantissa exponent) =
        roundAt fmt ((mantissa : ℝ) * bpow exponent) .up := by
  have hround :=
    roundDyadicPosUp_eq_posMinSubnormal_of_underflow
      fmt mantissa exponent hunderflow
  constructor
  · rw [hround]
    exact isFinite_posMinSubnormal fmt
  · rw [hround, toReal_posMinSubnormal, roundAt_up_pos_eq_of_lt_minNormal fmt mantissa exponent
      hfmt (hunderflow.trans (minSubnormalExponent_lt_minNormalExponent fmt))]
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
        roundAt fmt ((mantissa : ℝ) * bpow exponent) .up := by
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
    rw [toReal_roundSubnormalUp fmt rounded hroundedNe hroundedHigh,
      roundAt_up_pos_eq_of_lt_minNormal fmt mantissa exponent hfmt hhigh]

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
        roundAt fmt ((mantissa : ℝ) * bpow exponent) .up := by
  rw [roundDyadicPosUp_eq_normal_of_no_carry fmt mantissa exponent hnormal hmax hcarry,
    roundAt_up_pos_eq_of_minNormal_le fmt mantissa exponent hfmt hnormal]
  exact isFinite_toReal_guardedNormalPack fmt hfmt (nativeOverflow fmt false) _ _
    (pow2_le_roundMantissaToLeadingBitUp mantissa fmt.fracWidth hm)
    (lt_of_le_of_ne (roundMantissaToLeadingBitUp_le_pow2_succ mantissa fmt.fracWidth) hcarry)
    hnormal hmax

/--
A normalization carry that stays in range packs the smallest normal mantissa one binade higher,
which is finite and denotes the upward-rounded value.
-/
private theorem roundDyadicPosUp_normal_carry_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hnormal :
      fmt.minNormalExponent ≤
        (mantissa.log2 : Int) + exponent)
    (hcarry :
      roundMantissaToLeadingBitUp mantissa fmt.fracWidth =
        pow2 (fmt.fracWidth + 1))
    (hcarryMax :
      (mantissa.log2 : Int) + exponent + 1 ≤
        fmt.maxNormalExponent) :
    isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
      toReal (roundDyadicPosUp fmt mantissa exponent) =
        roundAt fmt ((mantissa : ℝ) * bpow exponent) .up := by
  have hfinite := isFinite_ofFields_normalized fmt hfmt (pow2 fmt.fracWidth)
    ((mantissa.log2 : Int) + exponent + 1) hcarryMax
  rw [Nat.sub_self] at hfinite
  rw [roundDyadicPosUp_eq_normal_of_carry fmt mantissa exponent hnormal hcarry hcarryMax,
    roundAt_up_pos_eq_of_minNormal_le fmt mantissa exponent hfmt hnormal, hcarry,
    ← normalizationCarry_value fmt ((mantissa.log2 : Int) + exponent)]
  refine ⟨hfinite, ?_⟩
  simpa using toReal_ofFields_normalized fmt (pow2 fmt.fracWidth)
    ((mantissa.log2 : Int) + exponent + 1) le_rfl (pow2_lt_pow2_succ fmt.fracWidth)
    (by omega) hcarryMax (by simpa using hfinite)

/--
In a conventional IEEE format, positive upward dyadic rounding is either positive infinity or the
finite independent real ceiling on the format grid.
-/
theorem roundDyadicPosUp_eq_posInf_or_finite_roundAt
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    roundDyadicPosUp fmt mantissa exponent = posInf fmt ∨
      (isFinite (roundDyadicPosUp fmt mantissa exponent) = true ∧
        toReal (roundDyadicPosUp fmt mantissa exponent) =
          roundAt fmt ((mantissa : ℝ) * bpow exponent) .up) := by
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
            exact Or.inr
              (roundDyadicPosUp_normal_carry_finite_roundAt
                fmt mantissa exponent hfmt hnormal hcarry hcarryMax)
        · exact Or.inr
            (roundDyadicPosUp_normal_no_carry_finite_roundAt
              fmt mantissa exponent hfmt hm hnormal hmax hcarry)

/--
In a conventional IEEE format, positive upward dyadic rounding is finite and equals the real ceiling
on the format grid whenever the leading exponent is within range and normalizing the mantissa does
not carry into the next binade. The carry hypothesis is what separates this statement from
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
        roundAt fmt ((mantissa : ℝ) * bpow exponent) .up := by
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

/-- In a conventional IEEE format, positive upward dyadic rounding is never classified as NaN. -/
theorem isNaN_roundDyadicPosUp_eq_false
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (hfmt : fmt.isIEEE = true)
    (hm : mantissa ≠ 0) :
    isNaN (roundDyadicPosUp fmt mantissa exponent) = false := by
  rcases roundDyadicPosUp_eq_posInf_or_finite_roundAt
      fmt mantissa exponent hfmt hm with hinf | ⟨hfinite, _⟩
  · rw [hinf]
    exact isNaN_posInf fmt
  · exact isNaN_eq_false_of_isFinite_eq_true _ hfinite

/--
In a conventional IEEE format, positive upward dyadic rounding is an upper bound in the extended
reals.
-/
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
