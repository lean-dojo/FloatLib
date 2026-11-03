/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Proof
import FloatLib.Numerics.Bitwise
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Basic
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Finite
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Bounds

/-!
# Correctness of binary square root

Lean's unpacked floating-point square root computes an integer square root and records whether the
discarded real fraction is below or above one half. This module proves that certificate correct,
connects the positive finite executable path to Lean's unpacked square-root model, proves that the
square root of a finite nonnegative value never overflows, and concludes that the result for a
conventional IEEE descriptor is one nearest-even rounding of the exact real square root.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/--
The residual classification produced from an integer square root locates the exact real square
root in the unit interval beginning at `Nat.sqrt n`, with the correct half-way comparison.
-/
theorem accuracyRepresents_natSqrt (n : Nat) :
    let root := Nat.sqrt n
    let remainder := n - root * root
    let accuracy : Accuracy :=
      if remainder = 0 then
        .exact
      else
        .inexact (if remainder ≤ root then .lt else .gt)
    accuracyRepresents root accuracy (Real.sqrt n) := by
  dsimp only
  let root := Nat.sqrt n
  let remainder := n - root * root
  change accuracyRepresents root
    (if remainder = 0 then
      .exact
    else
      .inexact (if remainder ≤ root then .lt else .gt))
    (Real.sqrt n)
  have hrootSq : root * root ≤ n := by
    simpa [root] using Nat.sqrt_le n
  have hnDecomp : n = root * root + remainder := by
    dsimp only [remainder]
    omega
  have hsqrtNonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt n) ^ 2 = n := by
    simp [Real.sq_sqrt (show (0 : ℝ) ≤ n by positivity)]
  by_cases hremainderZero : remainder = 0
  · simp only [ite_eq_left hremainderZero, accuracyRepresents]
    have hnEq : n = root * root := by omega
    rw [hnEq]
    norm_num [Nat.cast_mul, Real.sqrt_sq_eq_abs]
  ·
    have hrootLt : (root : ℝ) < Real.sqrt n := by
      have hnLt : root * root < n := by omega
      have hnLtCast : (root : ℝ) * root < (n : ℝ) := by
        exact_mod_cast hnLt
      have hrootNonneg : (0 : ℝ) ≤ root := by positivity
      nlinarith [hsqrtSq, hnLtCast]
    by_cases hremainderLe : remainder ≤ root
    · simp only [ite_eq_right hremainderZero, ite_eq_left hremainderLe, accuracyRepresents]
      constructor
      · exact hrootLt
      · have hremainderCast : (remainder : ℝ) ≤ root := by exact_mod_cast hremainderLe
        have hnDecompCast :
            (n : ℝ) = (root : ℝ) * root + remainder := by
          exact_mod_cast hnDecomp
        nlinarith [hsqrtSq]
    · simp only [ite_eq_right hremainderZero, ite_eq_right hremainderLe, accuracyRepresents]
      constructor
      · have hremainderLower : root + 1 ≤ remainder := by omega
        have hremainderCast : (root : ℝ) + 1 ≤ remainder := by
          exact_mod_cast hremainderLower
        have hnDecompCast :
            (n : ℝ) = (root : ℝ) * root + remainder := by
          exact_mod_cast hnDecomp
        nlinarith [hsqrtSq]
      · exact Real.real_sqrt_lt_nat_sqrt_succ

private theorem log2_sqrt (n : Nat) (hn : n ≠ 0) :
    (Nat.sqrt n).log2 = n.log2 / 2 := by
  have hsqrtPos : 0 < Nat.sqrt n := (Nat.sqrt_pos).2 (Nat.pos_of_ne_zero hn)
  apply (Nat.log2_eq_iff (Nat.ne_of_gt hsqrtPos)).2
  constructor
  · rw [Nat.le_sqrt, ← Nat.pow_add]
    calc
      2 ^ (n.log2 / 2 + n.log2 / 2) ≤ 2 ^ n.log2 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n := Nat.log2_self_le hn
  · rw [Nat.sqrt_lt, ← Nat.pow_add]
    calc
      n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ ((n.log2 / 2 + 1) + (n.log2 / 2 + 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)

private theorem totalExponent_sqrt_shift
    (mantissa shift root : Nat) (exponent target : Int)
    (hmantissa : mantissa ≠ 0)
    (hshift : (shift : Int) = exponent - 2 * target)
    (hroot : root = Nat.sqrt (mantissa <<< shift)) :
    Float.Model.totalExponent root target =
      (Float.Model.totalExponent mantissa exponent + 1).ediv 2 := by
  have hscaled : mantissa <<< shift ≠ 0 := by
    simp [Nat.shiftLeft_eq, hmantissa]
  unfold Float.Model.totalExponent
  rw [hroot, log2_sqrt _ hscaled,
    Nat.log2_shiftLeft_of_ne_zero mantissa shift hmantissa]
  change Int.ofNat ((mantissa.log2 + shift) / 2) + 1 + target =
    (Int.ofNat mantissa.log2 + 1 + exponent + 1) / 2
  simp only [Int.ofNat_eq_natCast] at *
  omega

private theorem sqrt_shift_mul_bpow
    (mantissa shift : Nat) (exponent target : Int)
    (hshift : (shift : Int) = exponent - 2 * target) :
    Real.sqrt (mantissa <<< shift : Nat) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target =
      Real.sqrt ((mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) := by
  have hscaledNonneg : (0 : Real) ≤ (mantissa <<< shift : Nat) := by
    positivity
  have hsourceNonneg :
      (0 : Real) ≤ (mantissa : Real) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    mul_nonneg (by positivity) (bpow.pos _ _).le
  have hlhsNonneg :
      0 ≤ Real.sqrt (mantissa <<< shift : Nat) *
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target :=
    mul_nonneg (Real.sqrt_nonneg _) (bpow.pos _ _).le
  apply Eq.symm
  apply (Real.sqrt_eq_iff_eq_sq hsourceNonneg hlhsNonneg).2
  rw [mul_pow, Real.sq_sqrt hscaledNonneg]
  have hcastShift :
      ((mantissa <<< shift : Nat) : Real) =
        (mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (Int.ofNat shift) := by
    rw [Nat.shiftLeft_eq, Nat.cast_mul]
    simp [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]
  rw [hcastShift]
  have hbpowSq :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target ^ 2 =
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (2 * target) := by
    rw [pow_two, ← bpow.add_exp]
    congr 1
    ring
  rw [hbpowSq, mul_assoc, ← bpow.add_exp]
  have hshiftInt : Int.ofNat shift = exponent - 2 * target := by
    simpa using hshift
  have hexponent : exponent = Int.ofNat shift + 2 * target := by
    omega
  rw [hexponent]

/--
Lean's positive finite model square root is one `roundWithAccuracy` of a certified integer root.
The root is nonzero, its accuracy locates a real `value` with `value * 2^target` equal to the exact
square root, and `target` never exceeds the root's target exponent, so normalization only discards
low bits.
-/
private theorem sqrt_finite_eq_roundWithAccuracy
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) (hmantissa : mantissa ≠ 0) :
    ∃ (root : Nat) (target : Int) (accuracy : Accuracy) (value : Real),
      Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
          (.finite .positive mantissa exponent (Nat.pos_of_ne_zero hmantissa)) =
        Float.Model.UnpackedFloat.roundWithAccuracy
          (FloatFormat.toModel fmt) .positive root target accuracy ∧
      root ≠ 0 ∧ accuracyRepresents root accuracy value ∧
      target ≤ (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent root target) ∧
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target =
        Real.sqrt ((mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) := by
  let spec := FloatFormat.toModel fmt
  let total := (Float.Model.totalExponent mantissa exponent + 1).ediv 2
  let target := min (exponent.ediv 2) (spec.targetExponent total)
  let shift := (exponent - 2 * target).toNat
  let scaled := mantissa <<< shift
  let root := Nat.sqrt scaled
  let remainder := scaled - root * root
  let accuracy : Accuracy :=
    if remainder = 0 then .exact
    else .inexact (if remainder ≤ root then .lt else .gt)
  have htargetLeHalf : target ≤ exponent.ediv 2 := min_le_left _ _
  have htwiceTargetLe : 2 * target ≤ exponent := by
    have h := Int.mul_le_of_le_ediv (a := target) (b := exponent) (c := 2)
      (by norm_num) htargetLeHalf
    omega
  have hshiftInt : (shift : Int) = exponent - 2 * target :=
    Int.toNat_of_nonneg (by omega)
  have hscaledNe : scaled ≠ 0 := by
    simp [scaled, Nat.shiftLeft_eq, hmantissa]
  have htotalRoot : Float.Model.totalExponent root target = total :=
    totalExponent_sqrt_shift mantissa shift root exponent target hmantissa hshiftInt rfl
  refine ⟨root, target, accuracy, Real.sqrt scaled, ?_, ?_, ?_, ?_,
    sqrt_shift_mul_bpow mantissa shift exponent target hshiftInt⟩
  · simp [spec, total, target, shift, scaled, root, remainder, accuracy,
      Float.Model.UnpackedFloat.sqrt, Float.Model.UnpackedFloat.sqrtCore]
  · exact Nat.ne_of_gt ((Nat.sqrt_pos).2 (Nat.pos_of_ne_zero hscaledNe))
  · simpa [root, remainder, accuracy] using accuracyRepresents_natSqrt scaled
  · have hright : target ≤ spec.targetExponent total := min_le_right _ _
    simpa [htotalRoot] using hright

/--
Lean's positive finite model square root has the same real value as independent nearest-even
rounding of the exact real square root whenever the packed result is finite.
-/
theorem toReal_ofModel_sqrt_finite_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≠ 0)
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive mantissa exponent
              (Nat.pos_of_ne_zero hmantissa)))) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
            (.finite .positive mantissa exponent
              (Nat.pos_of_ne_zero hmantissa)))) =
      roundAt fmt
        (Real.sqrt ((mantissa : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)) := by
  obtain ⟨root, target, accuracy, value, hsqrt, -, haccuracy, htargetLe, hscale⟩ :=
    sqrt_finite_eq_roundWithAccuracy fmt mantissa exponent hmantissa
  rw [hsqrt] at hfinite ⊢
  rw [toReal_ofModel_roundWithAccuracy_eq_roundAt fmt hfmt .positive root target accuracy value
    haccuracy htargetLe hfinite, ← hscale]
  simp [modelSignBit]

/-!
## Square root never overflows

The largest finite value of every IEEE descriptor exceeds one, so its square root is below it and
the rounded result stays inside the finite range. The proof first shows that packing a model value
whose biased exponent is in range yields a finite word, then that `roundWithAccuracy` of a
certified real below `2^maxNormal` packs to such a value, and so does one in the top binade below
the overflow threshold.
-/

/--
Packing a finite model value whose biased exponent stays below the all-ones pattern yields a
finite word. This is the converse of `noOverflow_of_isFinite_ofModel_finite`.
-/
theorem isFinite_ofModel_finite_of_noOverflow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int) (hm : mantissa ≠ 0)
    (hnoOverflow :
      ¬2 ^ (FloatFormat.toModel fmt).exponentBits ≤
        (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1) :
    isFinite (ofModel fmt (.finite sign mantissa exponent (Nat.pos_of_ne_zero hm))) = true := by
  have hencoding := (FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt |>.1
  have hlt :
      (exponent + (FloatFormat.toModel fmt).exponentBias +
          (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit).toNat + 1 <
        2 ^ fmt.expWidth :=
    Nat.lt_of_not_le hnoOverflow
  have hallOnes : 0 < FloatFormat.expAllOnesNat fmt := FloatFormat.expAllOnesNat_pos fmt
  simp only [isFinite, hencoding, IEEE.isFinite, bne_iff_ne, ne_eq]
  rw [← unpackExponent_toNat]
  unfold ofModel toModelBits ofModelBits Float.Model.UnpackedFloat.pack
  simp only [hnoOverflow, ite_false]
  split_ifs
  · rw [Float.Model.UnpackedFloat.unpackExponent_packComponents, BitVec.toNat_ofNat]
    change ¬ _ % 2 ^ fmt.expWidth = FloatFormat.expAllOnesNat fmt
    rw [Nat.mod_eq_of_lt (by omega)]
    unfold FloatFormat.expAllOnesNat
    omega
  · rw [Float.Model.UnpackedFloat.unpackExponent_packComponents]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
    omega

/--
In the normal range the target exponent is `k - fracWidth` for the leading exponent
`k = log2 mantissa + exponent`, so the real scaled to the target exponent times `2^(k - fracWidth)`
is the exact product.
-/
private theorem scaled_mul_bpow_eq_of_normal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) (value : Real)
    (hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ Int.ofNat mantissa.log2 + exponent) :
    value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (exponent - (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent)) *
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (Int.ofNat mantissa.log2 + exponent - fmt.fracWidth) =
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
  rw [targetExponent_eq_normal fmt mantissa exponent hnormal, mul_assoc, ← bpow.add_exp]
  congr 2
  simp only [Int.ofNat_eq_natCast]
  ring

/--
In the normal range a certified real at least `2^k`, for the leading exponent
`k = log2 mantissa + exponent`, scales to at least `2^fracWidth` at the target exponent.
-/
private theorem pow2_le_scaled_of_normal
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) (value : Real)
    (hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ Int.ofNat mantissa.log2 + exponent)
    (hlower : FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (Int.ofNat mantissa.log2 + exponent) ≤
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) :
    (pow2 fmt.fracWidth : Real) ≤
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (exponent - (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent)) := by
  apply le_of_mul_le_mul_right (a0 := bpow.pos Numerics.binaryRadix
    (Int.ofNat mantissa.log2 + exponent - fmt.fracWidth))
  rw [scaled_mul_bpow_eq_of_normal fmt mantissa exponent value hnormal, natCast_pow2_eq_bpow,
    ← bpow.add_exp]
  convert hlower using 2
  ring

/-- A rounded mantissa of at most `2^fracWidth` on the least-subnormal grid packs to a finite value. -/
private theorem isFinite_ofModel_finishRoundedMantissa_minSubnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) (rounded : Nat)
    (hle : rounded ≤ pow2 fmt.fracWidth) :
    isFinite
      (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, FloatFormat.ieeeMinSubnormalExponent fmt))) = true := by
  have hbias := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two fmt
  have hbiasPos : 1 ≤ fmt.bias := FloatFormat.bias_pos fmt
  by_cases hzero : rounded = 0
  · rw [hzero, finishRoundedMantissa_zero]
    exact isFinite_ofModel_zero fmt hfmt sign
  · rw [finishRoundedMantissa_at_minSubnormal fmt sign rounded hzero hle]
    apply isFinite_ofModel_finite_of_noOverflow fmt hfmt sign rounded _ hzero
    change
      ¬2 ^ fmt.expWidth ≤
        (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.bias + fmt.fracWidth).toNat + 1
    simp only [FloatFormat.ieeeMinSubnormalExponent, Int.ofNat_eq_natCast]
    omega

/--
Under a conventional IEEE descriptor a normalized rounded mantissa,
`2^fracWidth ≤ rounded < 2^(fracWidth + 1)`, at a normal leading exponent `k ≤ bias` packs to a
finite value.
-/
private theorem isFinite_ofModel_finishRoundedMantissa_normalized
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Sign) (rounded : Nat) (k : Int)
    (hlow : pow2 fmt.fracWidth ≤ rounded) (hhigh : rounded < pow2 (fmt.fracWidth + 1))
    (hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k) (hk : k ≤ Int.ofNat fmt.bias) :
    isFinite
      (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, k - fmt.fracWidth))) = true := by
  have hbias := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two fmt
  have hbiasPos : 1 ≤ fmt.bias := FloatFormat.bias_pos fmt
  rw [finishRoundedMantissa_normalized fmt sign rounded k hlow hhigh hnormal]
  apply isFinite_ofModel_finite_of_noOverflow fmt hfmt sign _ _
    (Nat.ne_of_gt ((pow2_pos _).trans_le hlow))
  change ¬2 ^ fmt.expWidth ≤ (k - fmt.fracWidth + fmt.bias + fmt.fracWidth).toNat + 1
  have hexp : k - fmt.fracWidth + fmt.bias + fmt.fracWidth = k + fmt.bias := by ring
  rw [hexp, hbias]
  simp only [FloatFormat.ieeeMinNormalExponent, Int.ofNat_eq_natCast] at hnormal hk
  omega

/-- Rounding a zero mantissa lands on the least-subnormal grid, so the packed result is finite. -/
private theorem isFinite_ofModel_roundWithAccuracy_zero
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (exponent : Int) (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents 0 accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent)) :
    isFinite
      (ofModel fmt
        (Float.Model.UnpackedFloat.roundWithAccuracy
          (FloatFormat.toModel fmt) sign 0 exponent accuracy)) = true := by
  obtain ⟨rounded, hone, -, hround⟩ :=
    roundWithAccuracy_zero_eq_finishRoundedMantissa fmt sign exponent accuracy value haccuracy hle
  rw [hround]
  exact isFinite_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt sign rounded
    (hone.trans (by rw [pow2_eq_two_pow]; exact Nat.one_le_two_pow))

/--
Rounding a nonnegative certified real whose magnitude is below `2^maxNormal` never overflows, so
the packed result is finite. The exponent premise is the documented precondition of
`roundWithAccuracy`: normalization may discard low bits but never shifts left.
-/
theorem isFinite_ofModel_roundWithAccuracy_of_lt_bpow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent))
    (hbound :
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt))) :
    isFinite
      (ofModel fmt
        (Float.Model.UnpackedFloat.roundWithAccuracy
          (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) = true := by
  by_cases hmantissa : mantissa = 0
  · subst mantissa
    exact isFinite_ofModel_roundWithAccuracy_zero fmt hfmt sign exponent accuracy value
      haccuracy hle
  let k : Int := Int.ofNat mantissa.log2 + exponent
  let target : Int :=
    (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent mantissa exponent)
  let scaled : Real :=
    value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (exponent - target)
  let rounded : Nat :=
    (Float.Model.UnpackedFloat.shiftToTargetExponent
      (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa
  have hvaluePos : 0 < value := pos_of_accuracyRepresents hmantissa haccuracy
  have hexactPos :
      0 < value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    mul_pos hvaluePos (bpow.pos _ _)
  have hmagnitude :
      magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) =
        k + 1 :=
    magnitude_mul_bpow_of_accuracyRepresents exponent hmantissa haccuracy
  have hk : k + 1 ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    rw [← hmagnitude]
    exact magnitude_le_of_abs_lt_bpow Numerics.binaryRadix _ _ hexactPos.ne'
      (by rw [abs_of_pos hexactPos]; exact hbound)
  have hscaled :
      scaledMantissa Numerics.binaryRadix (fexpOf fmt)
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) =
        scaled :=
    scaledMantissa_accuracy_mul_bpow fmt mantissa exponent accuracy value hfmt hmantissa haccuracy
  have hrounded : Int.ofNat rounded = nearestEven scaled :=
    roundedMantissa_shiftToTargetExponent_eq_nearestEven fmt mantissa exponent accuracy value haccuracy hle
  have hbias := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two fmt
  have hbiasPos : 1 ≤ fmt.bias := FloatFormat.bias_pos fmt
  rw [roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
  change
    isFinite
      (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign (rounded, target))) = true
  by_cases hsub : k < FloatFormat.ieeeMinNormalExponent fmt
  · have htargetMin : target = FloatFormat.ieeeMinSubnormalExponent fmt :=
      targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent hsub
    have hupperExact :
        value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.fracWidth) := by
      have hupper :=
        abs_lt_bpow_magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
      rw [abs_of_pos hexactPos, hmagnitude] at hupper
      refine hupper.trans_le ((bpow_le_bpow_iff Numerics.binaryRadix _ _).2 ?_)
      unfold FloatFormat.ieeeMinNormalExponent at hsub
      unfold FloatFormat.ieeeMinSubnormalExponent
      simp only [Int.ofNat_eq_natCast] at hsub ⊢
      omega
    have hscaledLe : scaled ≤ (pow2 fmt.fracWidth : Real) := by
      have hdenPos :
          0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt) := bpow.pos _ _
      apply le_of_mul_le_mul_right (a0 := hdenPos)
      calc
        scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt) =
            value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
          dsimp only [scaled]
          rw [htargetMin, mul_assoc, ← bpow.add_exp]
          congr 1
          ring_nf
        _ ≤ FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (FloatFormat.ieeeMinSubnormalExponent fmt + fmt.fracWidth) :=
          hupperExact.le
        _ = (pow2 fmt.fracWidth : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (FloatFormat.ieeeMinSubnormalExponent fmt) := by
          rw [natCast_pow2_eq_bpow, ← bpow.add_exp]
          congr 1
          ring
    have hroundedLe : rounded ≤ pow2 fmt.fracWidth :=
      Int.ofNat_le.mp (hrounded.trans_le (nearestEven_le_natCast_of_le hscaledLe))
    rw [htargetMin]
    exact isFinite_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt sign rounded hroundedLe
  · have hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k := le_of_not_gt hsub
    have htargetNormal : target = k - fmt.fracWidth :=
      targetExponent_eq_normal fmt mantissa exponent hnormal
    have hlowerExact :
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix k ≤
          value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent := by
      have hlower :=
        bpow_magnitude_sub_one_le Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
          hexactPos.ne'
      simpa [abs_of_pos hexactPos, hmagnitude] using hlower
    have hupperExact :
        value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k + 1) := by
      have hupper :=
        abs_lt_bpow_magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
      simpa [abs_of_pos hexactPos, hmagnitude] using hupper
    have hdenPos :
        0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) :=
      bpow.pos _ _
    have hscaledEq :
        scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
          value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
      scaled_mul_bpow_eq_of_normal fmt mantissa exponent value hnormal
    have hscaledLower : (pow2 fmt.fracWidth : Real) ≤ scaled :=
      pow2_le_scaled_of_normal fmt mantissa exponent value hnormal hlowerExact
    have hscaledUpper : scaled ≤ (pow2 (fmt.fracWidth + 1) : Real) := by
      apply le_of_mul_le_mul_right (a0 := hdenPos)
      calc
        scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
            value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
          hscaledEq
        _ ≤ FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k + 1) := hupperExact.le
        _ = (pow2 (fmt.fracWidth + 1) : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) := by
          rw [natCast_pow2_eq_bpow, ← bpow.add_exp]
          congr 1
          push_cast
          ring
    have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
      Int.ofNat_le.mp ((natCast_le_nearestEven_of_le hscaledLower).trans hrounded.symm.le)
    have hroundedHigh : rounded ≤ pow2 (fmt.fracWidth + 1) :=
      Int.ofNat_le.mp (hrounded.trans_le (nearestEven_le_natCast_of_le hscaledUpper))
    have hkBias : k + 1 ≤ Int.ofNat fmt.bias := by
      simpa [FloatFormat.ieeeMaxNormalExponent] using hk
    have hkMin : (1 : Int) - Int.ofNat fmt.bias ≤ k := by
      simpa [FloatFormat.ieeeMinNormalExponent] using hnormal
    by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
    · rw [htargetNormal, hcarry, finishRoundedMantissa_normalized_carry fmt sign k hnormal]
      apply isFinite_ofModel_finite_of_noOverflow fmt hfmt sign _ _ (by simp [pow2_eq_two_pow])
      change ¬2 ^ fmt.expWidth ≤ (k + 1 - fmt.fracWidth + fmt.bias + fmt.fracWidth).toNat + 1
      have hexp : k + 1 - fmt.fracWidth + fmt.bias + fmt.fracWidth = k + 1 + fmt.bias := by
        ring
      rw [hexp, hbias]
      simp only [Int.ofNat_eq_natCast] at hkBias hkMin
      omega
    · rw [htargetNormal]
      exact isFinite_ofModel_finishRoundedMantissa_normalized fmt hfmt sign rounded k hroundedLow
        (lt_of_le_of_ne hroundedHigh hcarry) hnormal (by omega)

/--
Rounding a nonnegative certified real below the overflow threshold
`2^(maxNormal + 1) - 2^(maxNormal - fracWidth - 1)` never overflows, so the packed result is finite.
Below `2^maxNormal` this is `isFinite_ofModel_roundWithAccuracy_of_lt_bpow`. In the top binade the
bound keeps the rounded mantissa below `2^(fracWidth + 1)`, so no carry reaches the next binade.
-/
theorem isFinite_ofModel_roundWithAccuracy_of_lt_overflow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent))
    (hbound :
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1) -
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) - fmt.fracWidth - 1)) :
    isFinite
      (ofModel fmt
        (Float.Model.UnpackedFloat.roundWithAccuracy
          (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) = true := by
  by_cases hmantissa : mantissa = 0
  · subst mantissa
    exact isFinite_ofModel_roundWithAccuracy_zero fmt hfmt sign exponent accuracy value
      haccuracy hle
  set emax : Int := Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) with hemax
  by_cases hbelow :
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix emax
  · exact isFinite_ofModel_roundWithAccuracy_of_lt_bpow fmt hfmt sign mantissa exponent accuracy
      value haccuracy hle hbelow
  have hlower : FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix emax ≤
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    le_of_not_gt hbelow
  let k : Int := Int.ofNat mantissa.log2 + exponent
  let target : Int :=
    (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent mantissa exponent)
  let scaled : Real :=
    value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (exponent - target)
  let rounded : Nat :=
    (Float.Model.UnpackedFloat.shiftToTargetExponent
      (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa
  have hvaluePos : 0 < value := pos_of_accuracyRepresents hmantissa haccuracy
  have hexactPos :
      0 < value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    mul_pos hvaluePos (bpow.pos _ _)
  have hmagnitude :
      magnitude Numerics.binaryRadix
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent) =
        k + 1 :=
    magnitude_mul_bpow_of_accuracyRepresents exponent hmantissa haccuracy
  have hupperBound :
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (emax + 1) := by
    have : 0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (emax - fmt.fracWidth - 1) := bpow.pos _ _
    linarith
  have hkUpper : k + 1 ≤ emax + 1 := by
    rw [← hmagnitude]
    exact magnitude_le_of_abs_lt_bpow Numerics.binaryRadix _ _ hexactPos.ne'
      (by rw [abs_of_pos hexactPos]; exact hupperBound)
  have hkLower : emax ≤ k := by
    have hupper :=
      abs_lt_bpow_magnitude Numerics.binaryRadix
        (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)
    rw [abs_of_pos hexactPos, hmagnitude] at hupper
    have : FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix emax <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k + 1) := hlower.trans_lt hupper
    have := (bpow_lt_bpow_iff Numerics.binaryRadix _ _).1 this
    omega
  have hk : k = emax := le_antisymm (by omega) hkLower
  have hbias := FloatFormat.two_pow_expWidth_eq_two_mul_bias_add_two fmt
  have hbiasPos : 1 ≤ fmt.bias := FloatFormat.bias_pos fmt
  have hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k := by
    rw [hk, hemax]
    simp only [FloatFormat.ieeeMinNormalExponent, FloatFormat.ieeeMaxNormalExponent,
      Int.ofNat_eq_natCast]
    omega
  have htargetNormal : target = k - fmt.fracWidth :=
    targetExponent_eq_normal fmt mantissa exponent hnormal
  have hrounded : Int.ofNat rounded = nearestEven scaled :=
    roundedMantissa_shiftToTargetExponent_eq_nearestEven fmt mantissa exponent accuracy value
      haccuracy hle
  have hdenPos :
      0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) :=
    bpow.pos _ _
  have hscaledEq :
      scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
        value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
    scaled_mul_bpow_eq_of_normal fmt mantissa exponent value hnormal
  have hscaledLower : (pow2 fmt.fracWidth : Real) ≤ scaled :=
    pow2_le_scaled_of_normal fmt mantissa exponent value hnormal (by
      change FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix k ≤ _
      rw [hk]
      exact hlower)
  have hscaledUpper : scaled < (pow2 (fmt.fracWidth + 1) : Real) - 1 / 2 := by
    apply lt_of_mul_lt_mul_right (a0 := hdenPos.le)
    calc
      scaled * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) =
          value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent :=
        hscaledEq
      _ < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (emax + 1) -
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (emax - fmt.fracWidth - 1) := hbound
      _ = ((pow2 (fmt.fracWidth + 1) : Real) - 1 / 2) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (k - fmt.fracWidth) := by
        rw [sub_mul, natCast_pow2_eq_bpow, ← bpow.add_exp, hk]
        have hhalf : (1 / 2 : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (emax - fmt.fracWidth) =
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
              (emax - fmt.fracWidth - 1) := by
          rw [show emax - fmt.fracWidth - 1 = emax - fmt.fracWidth + -1 by ring, bpow.add_exp]
          simp only [FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
            Numerics.Radix.toReal, zpow_neg, zpow_one]
          push_cast
          ring
        rw [hhalf]
        congr 2
        push_cast
        ring
  have hroundedLow : pow2 fmt.fracWidth ≤ rounded :=
    Int.ofNat_le.mp ((natCast_le_nearestEven_of_le hscaledLower).trans hrounded.symm.le)
  have hhigh : rounded < pow2 (fmt.fracWidth + 1) := by
    have herror := nearestEven_abs_sub_le_half scaled
    have hle' : (nearestEven scaled : Real) ≤ scaled + 1 / 2 := by
      have := (abs_le.mp herror).2
      linarith
    have hlt : (nearestEven scaled : Real) < (pow2 (fmt.fracWidth + 1) : Real) := by linarith
    have hint : nearestEven scaled < (pow2 (fmt.fracWidth + 1) : Int) := by exact_mod_cast hlt
    rw [← hrounded] at hint
    exact Int.ofNat_lt.mp hint
  rw [roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
  change
    isFinite
      (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign (rounded, target))) = true
  rw [htargetNormal]
  exact isFinite_ofModel_finishRoundedMantissa_normalized fmt hfmt sign rounded k hroundedLow
    hhigh hnormal (by rw [hk, hemax]; rfl)

/--
Lean's positive finite model square root packs to a finite word whenever the radicand is below
`2^(2 * maxNormal)`, which every finite IEEE value is.
-/
theorem isFinite_modelSqrt_of_lt_bpow
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≠ 0)
    (hbound :
      (mantissa : Real) * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt))) :
    isFinite
      (ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
          (.finite .positive mantissa exponent (Nat.pos_of_ne_zero hmantissa)))) = true := by
  obtain ⟨root, target, accuracy, value, hsqrt, -, haccuracy, htargetLe, hscale⟩ :=
    sqrt_finite_eq_roundWithAccuracy fmt mantissa exponent hmantissa
  have hmaxPos :
      0 < FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
        (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := bpow.pos _ _
  have hsquare :
      FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) ^ 2 =
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := by
    rw [pow_two, ← bpow.add_exp]
    congr 1
    ring
  have hsqrtBound :
      value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix target <
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
          (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := by
    rw [hscale]
    apply (Real.sqrt_lt' hmaxPos).2
    rw [hsquare]
    exact hbound
  rw [hsqrt]
  exact isFinite_ofModel_roundWithAccuracy_of_lt_bpow fmt hfmt .positive root target accuracy
    value haccuracy htargetLe hsqrtBound

/--
A positive finite value of a conventional IEEE descriptor is `significand * 2^exponent` with a
nonzero significand, and its square root packs Lean's positive finite model square root of that
pair.
-/
private theorem sqrt_eq_ofModel_sqrt_finite
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true) (hnonzero : isZero x = false)
    (hnonnegative : signBit x = false) :
    ∃ (significand : Nat) (exponent : Int) (hsignificand : significand ≠ 0),
      toReal x = (significand : Real) *
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent ∧
        sqrt x =
          ofModel fmt
            (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
              (.finite .positive significand exponent (Nat.pos_of_ne_zero hsignificand))) := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hsign : d.negative = false :=
    (sign_eq_signBit_of_toDyadic?_some hd).trans hnonnegative
  have hmantissa : d.significand ≠ 0 :=
    significand_ne_zero_of_toDyadic?_some_of_isZero_eq_false hd hnonzero
  have hmodel :
      toModel x =
        .finite .positive d.significand d.exponent (Nat.pos_of_ne_zero hmantissa) := by
    have hieeeDecode : ieeeToDyadic? x = some d := by
      simpa [toDyadic?, hfmt] using hd
    simpa [hsign] using
      toModel_eq_finite_of_ieeeToDyadic?_eq_some
        x d.negative d.significand d.exponent hmantissa hieeeDecode
  refine ⟨d.significand, d.exponent, hmantissa, ?_, ?_⟩
  · rw [toReal_eq, hd]
    simp [Numerics.Dyadic.toReal, hsign, Flocq.bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]
  · rw [Proof.sqrt_eq_spec, Spec.sqrt_eq_model hfmt x hfinite hnonnegative, hmodel]

/--
The square root of a finite nonnegative value, including either signed zero, is finite for every
conventional IEEE descriptor. The largest finite value exceeds one, so its square root lies below
it and rounding cannot reach infinity.
-/
theorem isFinite_sqrt_of_isFinite
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    isFinite (sqrt x) = true := by
  by_cases hzero : isZero x = true
  · rw [sqrt_of_isZero hzero]
    exact hfinite
  · have hnonnegative : signBit x = false := hdomain.resolve_left hzero
    have hnonzero : isZero x = false := Bool.eq_false_iff.mpr hzero
    obtain ⟨significand, exponent, hmantissa, hxReal, hsqrt⟩ :=
      sqrt_eq_ofModel_sqrt_finite x hfmt hfinite hnonzero hnonnegative
    have hxNonneg : 0 ≤ toReal x := by
      rw [hxReal]
      exact mul_nonneg (Nat.cast_nonneg _) (bpow.pos _ _).le
    have hxLe : toReal x ≤ toReal (posMaxFinite fmt) := by
      have := abs_toReal_le_posMaxFinite_of_isFinite x hfinite
      rwa [abs_of_nonneg hxNonneg] at this
    have hmaxLt := toReal_posMaxFinite_lt_bpow fmt
    rw [FloatFormat.maxNormalExponent_eq_ieee fmt hfmt] at hmaxLt
    have hbiasPos : 1 ≤ FloatFormat.ieeeMaxNormalExponent fmt := FloatFormat.bias_pos fmt
    have hexpLe :
        FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) + 1) ≤
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) :=
      (bpow_le_bpow_iff Numerics.binaryRadix _ _).2 (by
        simp only [Int.ofNat_eq_natCast]
        omega)
    have hbound :
        (significand : Real) *
            FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent <
          FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
            (2 * Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt)) := by
      rw [← hxReal]
      exact (hxLe.trans_lt hmaxLt).trans_le hexpLe
    rw [hsqrt]
    exact isFinite_modelSqrt_of_lt_bpow fmt hfmt significand exponent hmantissa hbound

private theorem toReal_sqrt_eq_roundAt_of_nonzero
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hnonnegative : signBit x = false)
    (hresult : isFinite (sqrt x) = true) :
    toReal (sqrt x) = roundAt fmt (Real.sqrt (toReal x)) := by
  obtain ⟨significand, exponent, hmantissa, hxReal, hsqrt⟩ :=
    sqrt_eq_ofModel_sqrt_finite x hfmt hfinite hnonzero hnonnegative
  rw [hsqrt] at hresult ⊢
  rw [toReal_ofModel_sqrt_finite_eq_roundAt fmt hfmt significand exponent hmantissa hresult,
    hxReal]

/--
A finite value with a nonnegative real interpretation satisfies the domain condition of
`toReal_sqrt_eq_roundAt`: it is a zero of either sign, or its sign bit is clear.
-/
theorem isZero_or_signBit_eq_false_of_toReal_nonneg {fmt : FloatFormat} (x : Model fmt)
    (hfinite : isFinite x = true) (hnonneg : 0 ≤ toReal x) :
    isZero x = true ∨ signBit x = false := by
  by_cases hzero : toReal x = 0
  · exact Or.inl ((isZero_eq_true_iff_toReal_eq_zero x hfinite).2 hzero)
  right
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hsign := sign_eq_signBit_of_toDyadic?_some hd
  cases hs : signBit x with
  | false => rfl
  | true =>
    have hnonpos : toReal x ≤ 0 := by
      have hreal : toReal x = d.toReal := by simp [toReal_eq, hd]
      rw [hreal]
      exact Dyadic.toReal_nonpos_of_negative_eq_true (hsign.trans hs)
    exact absurd (le_antisymm hnonpos hnonneg) hzero

/--
Generic executable square root performs one nearest-even rounding of the exact real square root
on every finite, nonnegative conventional IEEE input. The domain condition includes both signed
zeros. Alone among the arithmetic operations, it assumes no finiteness of the result:
`isFinite_sqrt_of_isFinite` shows that square root cannot overflow.
-/
theorem toReal_sqrt_eq_roundAt
    {fmt : FloatFormat} (x : Model fmt) (hfmt : fmt.isIEEE = true)
    (hfinite : isFinite x = true)
    (hdomain : isZero x = true ∨ signBit x = false) :
    toReal (sqrt x) = roundAt fmt (Real.sqrt (toReal x)) := by
  have hresult : isFinite (sqrt x) = true := isFinite_sqrt_of_isFinite x hfmt hfinite hdomain
  by_cases hzero : isZero x = true
  · have hxReal : toReal x = 0 := toReal_eq_zero_of_isZero x hzero
    rw [sqrt_of_isZero hzero, hxReal, Real.sqrt_zero, roundAt_zero]
  · exact toReal_sqrt_eq_roundAt_of_nonzero x hfmt hfinite
      (Bool.eq_false_iff.mpr hzero) (hdomain.resolve_left hzero) hresult

/-- The square root of a zero is exactly zero, for every descriptor. -/
theorem toReal_sqrt_of_isZero {fmt : FloatFormat} (x : Model fmt) (hzero : isZero x = true) :
    toReal (sqrt x) = 0 := by
  rw [sqrt_of_isZero hzero, toReal_eq_zero_of_isZero x hzero]

/--
The square root of a finite value with a clear sign bit is nonnegative in every rounding direction
and for every descriptor. A zero is its own square root.
-/
theorem toReal_sqrt_nonneg {fmt : FloatFormat} (mode : IEEERoundingMode)
    {x : Model fmt} (hfinite : isFinite x = true) (hsign : signBit x = false) :
    0 ≤ toReal (sqrt x (mode := mode)) := by
  by_cases hzeroTrue : isZero x = true
  · rw [sqrt_of_isZero hzeroTrue, toReal_eq_zero_of_isZero x hzeroTrue]
  have hzero : isZero x = false := Bool.eq_false_iff.mpr hzeroTrue
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
  have hchoose := chooseNaN1_none_of_isFinite x hfinite
  have hinf := isInf_eq_false_of_isFinite_eq_true x hfinite
  have hnan := isNaN_eq_false_of_isFinite_eq_true x hfinite
  have hnearest : 0 ≤ toReal (sqrt x) := by
    by_cases hfmt : fmt.isIEEE = true
    · rw [toReal_sqrt_eq_roundAt x hfmt hfinite (Or.inr hsign)]
      calc (0 : ℝ) = roundAt fmt 0 := (roundAt_zero fmt).symm
        _ ≤ roundAt fmt (Real.sqrt (toReal x)) := roundAt_mono fmt (Real.sqrt_nonneg _)
    · have hfmtFalse : fmt.isIEEE = false := Bool.eq_false_iff.mpr hfmt
      rw [Proof.sqrt_eq_spec]
      simp only [Spec.sqrt, chooseNaN1, hnan, hinf, hzero, hsign, hd, Bool.false_eq_true,
        ↓reduceIte]
      unfold FiniteSqrt.sqrtPositiveDyadic FiniteSqrt.sqrtGeneral Internal.roundDyadic
      simp only [hfmtFalse, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> first
        | with_reducible exact toReal_roundDyadicGeneral_nonneg fmt _ rfl
        | exact toReal_nonneg_of_signBit_eq_false (by simp)
  have hup : 0 ≤ toReal (roundDyadicUp fmt (sqrtDyadicBracket fmt d).upper) :=
    toReal_roundDyadicUp_nonneg fmt _ rfl
  have hdown : 0 ≤ toReal (roundDyadicDown fmt (sqrtDyadicBracket fmt d).lower) :=
    toReal_roundDyadicDown_nonneg fmt _ rfl
  cases mode with
  | nearest => exact hnearest
  | nearestAway => exact hnearest
  | up =>
      have hvalue : sqrt x (mode := .up) =
          roundDyadicUp fmt (sqrtDyadicBracket fmt d).upper := by
        simp [sqrt, Internal.Directed.sqrt, hchoose, hinf, hzero, hsign, hd]
      rw [hvalue]
      exact hup
  | away =>
      have hvalue : sqrt x (mode := .away) =
          roundDyadicUp fmt (sqrtDyadicBracket fmt d).upper := by
        simp [sqrt, Internal.Directed.sqrt, hchoose, hinf, hzero, hsign, hd]
      rw [hvalue]
      exact hup
  | down =>
      have hvalue : sqrt x (mode := .down) =
          roundDyadicDown fmt (sqrtDyadicBracket fmt d).lower := by
        simp [sqrt, Internal.Directed.sqrt, hchoose, hinf, hzero, hsign, hd]
      rw [hvalue]
      exact hdown
  | towardZero =>
      have hvalue : sqrt x (mode := .towardZero) =
          roundDyadicDown fmt (sqrtDyadicBracket fmt d).lower := by
        simp [sqrt, Internal.Directed.sqrt, hchoose, hinf, hzero, hsign, hd]
      rw [hvalue]
      exact hdown

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
