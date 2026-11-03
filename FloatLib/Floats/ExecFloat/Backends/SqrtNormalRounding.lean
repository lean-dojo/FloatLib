/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
public import Init.Data.Float.Model.Unpacked.Operations.Sqrt
public import Mathlib.Data.Nat.Sqrt

/-!
# Model square root of a normalized positive value

The binary32, binary64, one-word, two-word, and wide-limb square-root kernels compute the same
recipe: shift the significand so that its integer square root has exactly `fracWidth + 1` bits, take
the integer root, round it by comparing the remainder with the root, and pack the result with a
possible carry into the exponent field. This module proves once, for every IEEE format, that the
recipe agrees with `Float.Model.UnpackedFloat.sqrt` on the proof model.

Each kernel proves that its word arithmetic computes this recipe, that the scaled radicand and
encoded exponent satisfy the stated bounds, and that its scaling constants satisfy `htarget`
and `hshift`. `Backends.SqrtArithmetic` supplies the shared affine exponent identities, and the
word lemmas below (`sqrt_shiftLeft_bounds`, `sqrtRemainder_toNat`, `roundedRoot_toNat`,
`mod_two_beq_zero_of_toNat_eq`, `sqrtCarry_toNat`) give the steps that every `UInt64` kernel
repeats.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic

/--
On an IEEE format, a value that decodes to a positive dyadic with nonzero significand `mantissa`
has the positive finite proof model with that significand and exponent. The binary32, binary64,
two-word and wide-limb square-root proofs start from this model.
-/
theorem toModel_eq_finite_positive_of_toDyadic?_eq_some {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (x : Model fmt) (mantissa : Nat) (exponent : Int)
    (hmantissa : mantissa ≠ 0)
    (hdecode : toDyadic? x =
      some ({ negative := false, significand := mantissa, exponent := exponent } :
        Numerics.Dyadic)) :
    toModel x = .finite .positive mantissa exponent (Nat.pos_of_ne_zero hmantissa) := by
  simpa [modelSign] using
    toModel_eq_finite_of_ieeeToDyadic?_eq_some x false mantissa exponent hmantissa
      (by simpa [toDyadic?, hfmt] using hdecode)

/--
Scaling a nonzero significand `m` so that `2 * f ≤ log2 m + shift` and
`log2 m + 1 + shift ≤ 2 * f + 2` gives a radicand with `2 * f + 1` or `2 * f + 2` bits, whose
integer square root has exactly `f + 1` bits.
-/
theorem sqrt_shiftLeft_bounds (f m shift : Nat) (hm : m ≠ 0)
    (hshiftLower : 2 * f ≤ m.log2 + shift) (hshiftUpper : m.log2 + 1 + shift ≤ 2 * f + 2) :
    2 ^ (2 * f) ≤ m <<< shift ∧ m <<< shift < 2 ^ (2 * f + 2) ∧
      2 ^ f ≤ Nat.sqrt (m <<< shift) ∧ Nat.sqrt (m <<< shift) < 2 ^ (f + 1) := by
  have hleading : 2 ^ m.log2 ≤ m := (Nat.le_log2 hm).mp le_rfl
  have hscaledLower : 2 ^ (2 * f) ≤ m <<< shift := by
    rw [Nat.shiftLeft_eq]
    calc 2 ^ (2 * f) ≤ 2 ^ (m.log2 + shift) := Nat.pow_le_pow_right (by decide) hshiftLower
      _ = 2 ^ m.log2 * 2 ^ shift := Nat.pow_add ..
      _ ≤ m * 2 ^ shift := Nat.mul_le_mul_right _ hleading
  have hscaledUpper : m <<< shift < 2 ^ (2 * f + 2) :=
    lt_of_lt_of_le (Nat.shiftLeft_lt Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) hshiftUpper)
  refine ⟨hscaledLower, hscaledUpper, ?_, ?_⟩
  · rw [Nat.le_sqrt, ← Nat.pow_add, ← two_mul]
    exact hscaledLower
  · rw [Nat.sqrt_lt, ← Nat.pow_add]
    exact lt_of_lt_of_le hscaledUpper (Nat.pow_le_pow_right (by decide) (by omega))

/-- The remainder of a native integer square root is the remainder of the exact root. -/
theorem sqrtRemainder_toNat (scaled root : UInt64) (scaledValue : Nat)
    (hscaled : scaled.toNat = scaledValue) (hroot : root.toNat = Nat.sqrt scaledValue) :
    (scaled - root * root).toNat =
      scaledValue - Nat.sqrt scaledValue * Nat.sqrt scaledValue := by
  have hproductFit : Nat.sqrt scaledValue * Nat.sqrt scaledValue < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.sqrt_le scaledValue) (hscaled ▸ scaled.toNat_lt)
  have hproduct : (root * root).toNat = Nat.sqrt scaledValue * Nat.sqrt scaledValue := by
    rw [UInt64.toNat_mul, hroot, Nat.mod_eq_of_lt hproductFit]
  have hle : root * root ≤ scaled := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hproduct, hscaled]
    exact Nat.sqrt_le scaledValue
  rw [UInt64.toNat_sub_of_le _ _ hle, hscaled, hproduct]

/--
Rounding a native root to nearest by comparing its remainder with it agrees with the same rounding
of the exact root, when the incremented root fits in a word.
-/
theorem roundedRoot_toNat (root remainder : UInt64) (rootValue remainderValue : Nat)
    (hroot : root.toNat = rootValue) (hremainder : remainder.toNat = remainderValue)
    (hfit : rootValue + 1 < 2 ^ 64) :
    (if remainder ≤ root then root else root + 1).toNat =
      if remainderValue ≤ rootValue then rootValue else rootValue + 1 := by
  have hle : remainder ≤ root ↔ remainderValue ≤ rootValue := by
    rw [UInt64.le_iff_toNat_le, hremainder, hroot]
  by_cases h : remainderValue ≤ rootValue
  · rw [ite_eq_left (hle.mpr h), ite_eq_left h, hroot]
  · rw [ite_eq_right ((not_congr hle).mpr h), ite_eq_right h, UInt64.toNat_add, hroot]
    exact Nat.mod_eq_of_lt hfit

/-- The parity test of a native exponent position agrees with the test on its value. -/
theorem mod_two_beq_zero_of_toNat_eq (position : UInt64) (value : Nat)
    (hposition : position.toNat = value) :
    (position % 2 == 0) = (value % 2 == 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod, hposition]
  rfl

/--
The carry step of a native square-root kernel. When the rounded root word `rounded` equals the
carry word `carryBit`, worth `2 ^ (f + 1)`, the kernel adds one to the biased exponent word
`exponent` and takes the hidden-bit word `hiddenBit`, worth `2 ^ f`, as the significand; otherwise
it keeps `exponent` and `rounded`. The fraction word is the significand minus `hiddenBit`. If
`rounded` has the value `root ≥ 2 ^ f` and `exponent` has a value `q` whose successor fits in a
word, the exponent and fraction words have the values that
`ofModel_sqrt_finite_positive_eq_ofFields` packs.
-/
theorem sqrtCarry_toNat (f : Nat) (rounded exponent carryBit hiddenBit : UInt64) (root q : Nat)
    (hrounded : rounded.toNat = root) (hexponent : exponent.toNat = q)
    (hcarryBit : carryBit.toNat = 2 ^ (f + 1)) (hhiddenBit : hiddenBit.toNat = 2 ^ f)
    (hlower : 2 ^ f ≤ root) (hfit : q + 1 < 2 ^ 64) :
    (exponent + if rounded == carryBit then 1 else 0).toNat =
        q + (if root = pow2 (f + 1) then 1 else 0) ∧
      ((if rounded == carryBit then hiddenBit else rounded) - hiddenBit).toNat =
        (if root = pow2 (f + 1) then pow2 f else root) - pow2 f := by
  have hcarry : (rounded == carryBit) = decide (root = pow2 (f + 1)) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, hrounded, hcarryBit, pow2_eq_two_pow]
  rw [hcarry]
  by_cases hc : root = pow2 (f + 1)
  · rw [decide_eq_true hc, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left hc, ite_eq_left hc,
      UInt64.sub_self, UInt64.toNat_zero, Nat.sub_self, UInt64.toNat_add, hexponent,
      UInt64.toNat_one, Nat.mod_eq_of_lt hfit]
    exact ⟨rfl, rfl⟩
  · rw [decide_eq_false hc, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true,
      ite_eq_right hc, ite_eq_right hc, UInt64.add_zero, hexponent, Nat.add_zero,
      UInt64.toNat_sub_of_le _ _
        (UInt64.le_iff_toNat_le.mpr (by rw [hhiddenBit, hrounded]; exact hlower)),
      hrounded, hhiddenBit, pow2_eq_two_pow]
    exact ⟨rfl, rfl⟩

/--
The model square root of a positive finite `m * 2 ^ inputExponent` is the packed, rounded integer
root.

The root's biased exponent before a rounding carry is `q`, and `shift` scales the significand so
that the integer root of `m <<< shift` has exactly `fracWidth + 1` bits. Rounding compares the
remainder with the root, and a rounded root of `2 ^ (fracWidth + 1)` carries into the exponent
field.
-/
theorem ofModel_sqrt_finite_positive_eq_ofFields (fmt : FloatFormat)
    (m shift q : Nat) (inputExponent : Int) (hm : 0 < m)
    (hshiftLower : 2 * fmt.fracWidth ≤ m.log2 + shift)
    (hshiftUpper : m.log2 + 1 + shift ≤ 2 * fmt.fracWidth + 2)
    (hq : 1 ≤ q) (hqCarry : q + 1 ≤ 2 * fmt.bias)
    (htarget : min (inputExponent.ediv 2)
        ((FloatFormat.toModel fmt).targetExponent
          ((Float.Model.totalExponent m inputExponent + 1).ediv 2)) =
      Int.ofNat q - Int.ofNat fmt.bias - fmt.fracWidth)
    (hshift : (inputExponent - 2 * (Int.ofNat q - Int.ofNat fmt.bias - fmt.fracWidth)).toNat =
      shift) :
    let root := Nat.sqrt (m <<< shift)
    let remainder := m <<< shift - root * root
    let rounded := if remainder ≤ root then root else root + 1
    ofModel fmt
        (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
          (.finite .positive m inputExponent hm)) =
      ofFields fmt false
        (q + if rounded = pow2 (fmt.fracWidth + 1) then 1 else 0)
        ((if rounded = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth else rounded) -
          pow2 fmt.fracWidth) := by
  intro root remainder rounded
  set rootExponent : Int := Int.ofNat q - Int.ofNat fmt.bias with hrootExponent
  set accuracy : Float.Model.UnpackedFloat.Accuracy :=
    if remainder = 0 then .exact else .inexact (if remainder ≤ root then .lt else .gt)
    with haccuracy
  have hrounded : rounded = if remainder ≤ root then root else root + 1 := rfl
  have hcore :
      Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent =
        (root, rootExponent - fmt.fracWidth, accuracy) := by
    unfold Float.Model.UnpackedFloat.sqrtCore
    rw [htarget]
    dsimp only
    rw [hshift]
  simp only [Float.Model.UnpackedFloat.sqrt]
  change
    ofModel fmt
      (Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt) .positive
        (Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent).1
        (Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent).2.1
        (Float.Model.UnpackedFloat.sqrtCore (FloatFormat.toModel fmt) m inputExponent).2.2) = _
  rw [hcore]
  dsimp only [Prod.fst, Prod.snd]
  obtain ⟨-, -, hrootLower, hrootUpper⟩ :=
    sqrt_shiftLeft_bounds fmt.fracWidth m shift hm.ne' hshiftLower hshiftUpper
  rw [← pow2_eq_two_pow] at hrootLower hrootUpper
  have hroundedLower : pow2 fmt.fracWidth ≤ rounded := by
    rw [hrounded]
    split <;> omega
  have hroundedUpper : rounded ≤ pow2 (fmt.fracWidth + 1) := by
    rw [hrounded]
    split <;> omega
  simp only [Int.ofNat_eq_natCast] at hrootExponent
  have hminNormal : FloatFormat.ieeeMinNormalExponent fmt ≤ rootExponent := by
    unfold FloatFormat.ieeeMinNormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  have hmaxNormalCarry :
      rootExponent + 1 ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    unfold FloatFormat.ieeeMaxNormalExponent
    simp only [Int.ofNat_eq_natCast]
    omega
  have hmaxNormal : rootExponent ≤ Int.ofNat (FloatFormat.ieeeMaxNormalExponent fmt) := by
    omega
  have hminNormalCarry : FloatFormat.ieeeMinNormalExponent fmt ≤ rootExponent + 1 := by
    omega
  have hfirst := shiftToTargetExponent_normalized fmt root rootExponent accuracy
    hrootUpper hminNormal
  have hroundedMantissa :
      (Float.Model.UnpackedFloat.ExtendedMantissa.ofMantissaAndAccuracy
        root accuracy).roundedMantissa = rounded := by
    rw [haccuracy, hrounded]
    exact roundedMantissa_of_sqrtRemainder root remainder
  rw [roundWithAccuracy_eq_finishRoundedMantissa, hfirst]
  simp only [hroundedMantissa]
  have hpow : 0 < pow2 fmt.fracWidth := by simp [pow2_eq_two_pow]
  by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
  · have hfinish :
        finishRoundedMantissa (FloatFormat.toModel fmt) .positive
            (rounded, rootExponent - fmt.fracWidth) =
          .finite .positive (pow2 fmt.fracWidth) (rootExponent + 1 - fmt.fracWidth)
            (Nat.pos_of_ne_zero (by simp [pow2_eq_two_pow])) := by
      rw [hcarry]
      exact finishRoundedMantissa_normalized_carry fmt .positive rootExponent hminNormal
    have hpowLt : pow2 fmt.fracWidth < pow2 (fmt.fracWidth + 1) := by
      rw [pow2_eq_two_pow, pow2_eq_two_pow]
      exact Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
    have hpack :
        ofModel fmt
            (.finite .positive (pow2 fmt.fracWidth) (rootExponent + 1 - fmt.fracWidth)
              (Nat.pos_of_ne_zero (by simp [pow2_eq_two_pow]))) =
          ofFields fmt false (Int.toNat (rootExponent + 1 + Int.ofNat fmt.bias))
            (pow2 fmt.fracWidth - pow2 fmt.fracWidth) := by
      simpa [modelSign] using
        ofModel_finite_normalized_eq_ofFields fmt false (pow2 fmt.fracWidth)
          (rootExponent + 1) le_rfl hpowLt hminNormalCarry hmaxNormalCarry
    have hencoded : Int.toNat (rootExponent + 1 + Int.ofNat fmt.bias) = q + 1 := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hfinish, hpack, hencoded, ite_eq_left hcarry, ite_eq_left hcarry]
  · have hroundedHigh : rounded < pow2 (fmt.fracWidth + 1) :=
      lt_of_le_of_ne hroundedUpper hcarry
    have hfinish :
        finishRoundedMantissa (FloatFormat.toModel fmt) .positive
            (rounded, rootExponent - fmt.fracWidth) =
          .finite .positive rounded (rootExponent - fmt.fracWidth)
            (Nat.pos_of_ne_zero (Nat.ne_of_gt (hpow.trans_le hroundedLower))) :=
      finishRoundedMantissa_normalized fmt .positive rounded rootExponent
        hroundedLower hroundedHigh hminNormal
    have hpack :
        ofModel fmt
            (.finite .positive rounded (rootExponent - fmt.fracWidth)
              (Nat.pos_of_ne_zero (Nat.ne_of_gt (hpow.trans_le hroundedLower)))) =
          ofFields fmt false (Int.toNat (rootExponent + Int.ofNat fmt.bias))
            (rounded - pow2 fmt.fracWidth) := by
      simpa [modelSign] using
        ofModel_finite_normalized_eq_ofFields fmt false rounded rootExponent
          hroundedLower hroundedHigh hminNormal hmaxNormal
    have hencoded : Int.toNat (rootExponent + Int.ofNat fmt.bias) = q := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hfinish, hpack, hencoded, ite_eq_right hcarry, ite_eq_right hcarry, Nat.add_zero]

end FloatLib.Floats.Formats.BinaryInterchange.Model
