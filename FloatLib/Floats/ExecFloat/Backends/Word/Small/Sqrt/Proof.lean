/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Sqrt.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Small.Finite.Proof
public import FloatLib.Floats.ExecFloat.Backends.Word.ModelSqrt.Proof
public import FloatLib.Floats.ExecFloat.Backends.SqrtNormalRounding
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof

import FloatLib.Floats.ExecFloat.Backends.Generic.Kernel.Proof
import FloatLib.Floats.ExecFloat.Backends.Generic.Sqrt.Proof
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Correctness of the one-word square root for small IEEE formats

`sqrtPositiveCore_eq` shows that the kernel is Lean's logical unpacked square root, rounded and
packed, for every nonzero mantissa and finite scale of an eligible format. `sqrtPositive_eq` then
identifies the dispatcher with the shared finite kernel for every positive finite input.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model.NativeSmallWordSqrt

/-- The conventional bias is one below the power of two that the logical model uses. -/
private theorem two_pow_expWidth_sub_one (fmt : FloatFormat) :
    2 ^ (fmt.expWidth - 1) = fmt.bias + 1 := by
  unfold FloatFormat.bias
  have := Nat.one_le_two_pow (n := fmt.expWidth - 1)
  omega

/-- The rounding exponent of the logical square root is the kernel's root exponent. -/
private theorem target_exponent_eq (fmt : FloatFormat) (hbias : fmt.fracWidth + 1 ≤ fmt.bias)
    (m scale : Nat) (hleading : m.log2 ≤ fmt.fracWidth) :
    min ((Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)).ediv 2)
        ((FloatFormat.toModel fmt).targetExponent
          ((Float.Model.totalExponent m
            (Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1)) + 1).ediv 2)) =
      Int.ofNat ((m.log2 + scale + (fmt.bias + 1 - fmt.fracWidth)) / 2) -
        Int.ofNat fmt.bias - fmt.fracWidth := by
  have hf := fmt.fracWidth_pos
  have hpow := two_pow_expWidth_sub_one fmt
  have key := FloatLib.Floats.ExecFloat.Backends.SqrtArithmetic.target_exponent
    m.log2 scale (fmt.bias + fmt.fracWidth - 1) (fmt.bias + 1 - fmt.fracWidth) fmt.bias
    fmt.fracWidth hleading (by omega) (by omega) (by omega) (by omega)
  have hpowInt : (2 : Int) ^ (fmt.expWidth - 1) = (fmt.bias : Int) + 1 := by
    exact_mod_cast hpow
  simp only [Float.Model.Format.targetExponent, Float.Model.Format.mantissaBits,
    Float.Model.Format.minExponent, Float.Model.totalExponent, FloatFormat.toModel, hpowInt,
    Int.ofNat_eq_natCast, ← Int.div_def] at key ⊢
  rw [Int.max_def, Int.min_def] at key ⊢
  split_ifs at key ⊢ <;> omega

/-- The radicand shift of the logical square root is the kernel's shift. -/
private theorem shift_eq (fmt : FloatFormat) (hbias : fmt.fracWidth + 1 ≤ fmt.bias)
    (leading scale : Nat) (hleading : leading ≤ fmt.fracWidth) :
    (Int.ofNat scale - Int.ofNat (fmt.bias + fmt.fracWidth - 1) -
        2 * (Int.ofNat ((leading + scale + (fmt.bias + 1 - fmt.fracWidth)) / 2) -
          Int.ofNat fmt.bias - fmt.fracWidth)).toNat =
      (leading + scale + (fmt.bias + 1 - fmt.fracWidth)) % 2 + 2 * fmt.fracWidth - leading := by
  have hf := fmt.fracWidth_pos
  simp only [Int.ofNat_eq_natCast]
  omega

/--
For a nonzero mantissa below `2 ^ (fracWidth + 1)` and the scale of a finite value, the kernel is
Lean's logical unpacked square root of `mantissa * 2 ^ (scale - (bias + fracWidth - 1))`.
-/
theorem sqrtPositiveCore_eq (fmt : FloatFormat) (heligible : Eligible fmt)
    (mantissa scale : UInt64) (hm : 0 < mantissa.toNat)
    (hmBound : mantissa.toNat < 2 ^ (fmt.fracWidth + 1))
    (hscale : scale.toNat + 1 ≤ 2 * fmt.bias) :
    NativeSmallWord.ofWord (fmt := fmt) (sqrtPositiveCore fmt mantissa scale) =
      ofModel fmt (Float.Model.UnpackedFloat.sqrt (FloatFormat.toModel fmt)
        (.finite .positive mantissa.toNat
          (Int.ofNat scale.toNat - Int.ofNat (fmt.bias + fmt.fracWidth - 1)) hm)) := by
  obtain ⟨⟨_, hwidth⟩, hradicand, hbias⟩ := heligible
  have hf := fmt.fracWidth_pos
  have hexpWidth : fmt.expWidth ≤ 62 := by
    unfold FloatFormat.bitWidth at hwidth
    omega
  have hbiasLt : fmt.bias < 2 ^ 62 :=
    (FloatFormat.bias_lt_pow_expWidth fmt).trans_le (Nat.pow_le_pow_right (by decide) hexpWidth)
  have hmNat : mantissa.toNat ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hmWord : mantissa ≠ 0 := by
    intro h
    apply hmNat
    rw [h]
    rfl
  have hleadingLt : mantissa.toNat.log2 < fmt.fracWidth + 1 :=
    (Nat.log2_lt hmNat).2 hmBound
  let genericLeading := mantissa.toNat.log2
  let genericNumerator := genericLeading + scale.toNat + (fmt.bias + 1 - fmt.fracWidth)
  let genericShift := genericNumerator % 2 + 2 * fmt.fracWidth - genericLeading
  rw [ofModel_sqrt_finite_positive_eq_ofFields fmt mantissa.toNat genericShift
    (genericNumerator / 2) _ hm (by omega) (by omega) (by omega) (by omega)
    (target_exponent_eq fmt hbias mantissa.toNat scale.toNat (by omega))
    (shift_eq fmt hbias genericLeading scale.toNat (by omega))]
  unfold sqrtPositiveCore
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  let nativeFrac := UInt64.ofNat fmt.fracWidth
  let nativeLeading := mantissa.log2
  let nativeNumerator := nativeLeading + scale + (NativeSmallWord.biasWord fmt + 1 - nativeFrac)
  let nativeShift := nativeNumerator % 2 + 2 * nativeFrac - nativeLeading
  let nativeScaled := mantissa <<< nativeShift
  let nativeRoot := FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt nativeScaled
  let nativeRemainder := nativeScaled - nativeRoot * nativeRoot
  let nativeRounded := if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1
  let nativeCarry := nativeRounded == NativeSmallWord.carryBit fmt
  let nativeExponent := nativeNumerator / 2 + if nativeCarry then 1 else 0
  let nativeRoundedMantissa :=
    if nativeCarry then NativeSmallWord.hiddenBit fmt else nativeRounded
  let nativeFraction := nativeRoundedMantissa - NativeSmallWord.hiddenBit fmt
  let genericScaled := mantissa.toNat <<< genericShift
  let genericRoot := Nat.sqrt genericScaled
  let genericRemainder := genericScaled - genericRoot * genericRoot
  let genericRounded :=
    if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1
  change
    NativeSmallWord.ofWord (NativeSmallWord.packFields fmt false nativeExponent nativeFraction) =
      ofFields fmt false
        (genericNumerator / 2 + if genericRounded = pow2 (fmt.fracWidth + 1) then 1 else 0)
        ((if genericRounded = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth
          else genericRounded) - pow2 fmt.fracWidth)
  rw [NativeSmallWord.ofWord_packFields hwidth]
  have hfracNat : nativeFrac.toNat = fmt.fracWidth :=
    UInt64.toNat_ofNat_of_lt' (lt_trans (show fmt.fracWidth < 64 by omega) (by decide))
  have hleading : nativeLeading.toNat = genericLeading :=
    FloatLib.Numerics.FixedWord.log2_toNat mantissa
  have hbiasWord := NativeSmallWord.biasWord_toNat hwidth
  have hbiasOne : (NativeSmallWord.biasWord fmt + 1).toNat = fmt.bias + 1 := by
    rw [UInt64.toNat_add, hbiasWord]
    exact Nat.mod_eq_of_lt (by change fmt.bias + 1 < 2 ^ 64; omega)
  have hoffset :
      (NativeSmallWord.biasWord fmt + 1 - nativeFrac).toNat = fmt.bias + 1 - fmt.fracWidth := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hbiasOne, hfracNat]; omega)),
      hbiasOne, hfracNat]
  have hnumerator : nativeNumerator.toNat = genericNumerator := by
    have h1 : (nativeLeading + scale).toNat = genericLeading + scale.toNat := by
      rw [UInt64.toNat_add, hleading]
      exact Nat.mod_eq_of_lt (by omega)
    change (nativeLeading + scale + (NativeSmallWord.biasWord fmt + 1 - nativeFrac)).toNat = _
    rw [UInt64.toNat_add, h1, hoffset]
    exact Nat.mod_eq_of_lt (by change genericNumerator < 2 ^ 64; omega)
  have hparity : (nativeNumerator % 2).toNat = genericNumerator % 2 := by
    rw [UInt64.toNat_mod, hnumerator]
    rfl
  have hdouble : (2 * nativeFrac).toNat = 2 * fmt.fracWidth := by
    rw [UInt64.toNat_mul, hfracNat]
    exact Nat.mod_eq_of_lt (by change 2 * fmt.fracWidth < 2 ^ 64; omega)
  have hsum : (nativeNumerator % 2 + 2 * nativeFrac).toNat =
      genericNumerator % 2 + 2 * fmt.fracWidth := by
    rw [UInt64.toNat_add, hparity, hdouble]
    exact Nat.mod_eq_of_lt (by omega)
  have hshift : nativeShift.toNat = genericShift := by
    change (nativeNumerator % 2 + 2 * nativeFrac - nativeLeading).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsum, hleading]; omega)),
      hsum, hleading]
  have hshiftLt : genericShift < 64 := by omega
  have hscaledLt : genericScaled < 2 ^ (2 * fmt.fracWidth + 2) := by
    change mantissa.toNat <<< genericShift < _
    exact lt_of_lt_of_le (Nat.shiftLeft_lt Nat.lt_log2_self)
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hscaledFit : genericScaled < 2 ^ 64 :=
    lt_of_lt_of_le hscaledLt (Nat.pow_le_pow_right (by decide) hradicand)
  have hscaled : nativeScaled.toNat = genericScaled := by
    simpa only [nativeScaled, genericScaled, ← hshift, UInt64.ofNat_toNat] using
      FloatLib.Numerics.FixedWord.shiftLeft_toNat mantissa genericShift hshiftLt hscaledFit
  have hroot : nativeRoot.toNat = genericRoot := by
    change (FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt nativeScaled).toNat = _
    rw [FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrt_toNat, hscaled]
  have hrootLt : genericRoot < 2 ^ (fmt.fracWidth + 1) := by
    change Nat.sqrt genericScaled < _
    rw [Nat.sqrt_lt, ← Nat.pow_add]
    exact lt_of_lt_of_eq hscaledLt (by congr 1; omega)
  have hrootLower : 2 ^ fmt.fracWidth ≤ genericRoot := by
    have hpowLeading : 2 ^ genericLeading ≤ mantissa.toNat := Nat.log2_self_le hmNat
    have hscaledLower : 2 ^ (2 * fmt.fracWidth) ≤ genericScaled := by
      change 2 ^ (2 * fmt.fracWidth) ≤ mantissa.toNat <<< genericShift
      rw [Nat.shiftLeft_eq]
      calc
        2 ^ (2 * fmt.fracWidth) ≤ 2 ^ (genericLeading + genericShift) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ genericLeading * 2 ^ genericShift := Nat.pow_add ..
        _ ≤ mantissa.toNat * 2 ^ genericShift := Nat.mul_le_mul_right _ hpowLeading
    change 2 ^ fmt.fracWidth ≤ Nat.sqrt genericScaled
    rw [Nat.le_sqrt, ← Nat.pow_add]
    exact le_of_eq_of_le (by congr 1; omega) hscaledLower
  have hpowFit : 2 ^ (fmt.fracWidth + 1) < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hrootProductFit : genericRoot * genericRoot < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.sqrt_le genericScaled) hscaledFit
  have hrootProduct : (nativeRoot * nativeRoot).toNat = genericRoot * genericRoot := by
    rw [UInt64.toNat_mul, hroot]
    exact Nat.mod_eq_of_lt hrootProductFit
  have hrootProductLe : nativeRoot * nativeRoot ≤ nativeScaled := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hrootProduct, hscaled]
    exact Nat.sqrt_le genericScaled
  have hremainder : nativeRemainder.toNat = genericRemainder := by
    change (nativeScaled - nativeRoot * nativeRoot).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ hrootProductLe, hscaled, hrootProduct]
  have hremainderLe : nativeRemainder ≤ nativeRoot ↔ genericRemainder ≤ genericRoot := by
    rw [UInt64.le_iff_toNat_le, hremainder, hroot]
  have hrounded : nativeRounded.toNat = genericRounded := by
    change (if nativeRemainder ≤ nativeRoot then nativeRoot else nativeRoot + 1).toNat =
      if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1
    by_cases hle : nativeRemainder ≤ nativeRoot
    · rw [ite_eq_left hle, ite_eq_left (hremainderLe.mp hle), hroot]
    · rw [ite_eq_right hle, ite_eq_right ((not_congr hremainderLe).mp hle), UInt64.toNat_add, hroot]
      exact Nat.mod_eq_of_lt (by change genericRoot + 1 < 2 ^ 64; omega)
  have hroundedLe : genericRounded ≤ 2 ^ (fmt.fracWidth + 1) := by
    change (if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1) ≤ _
    split <;> omega
  have hroundedLower : 2 ^ fmt.fracWidth ≤ genericRounded := by
    change 2 ^ fmt.fracWidth ≤ if genericRemainder ≤ genericRoot then genericRoot else genericRoot + 1
    split <;> omega
  have hcarryBit := NativeSmallWord.carryBit_toNat_of_width fmt hwidth (by omega)
  have hhiddenBit := NativeSmallWord.hiddenBit_toNat_of_width fmt hwidth
  have hcarry : nativeCarry = decide (genericRounded = pow2 (fmt.fracWidth + 1)) := by
    change (nativeRounded == NativeSmallWord.carryBit fmt) = _
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, ← UInt64.toNat_inj, hrounded, hcarryBit,
      pow2_eq_two_pow]
  have hhalf : (nativeNumerator / 2).toNat = genericNumerator / 2 := by
    rw [UInt64.toNat_div, hnumerator]
    rfl
  have hexponent : nativeExponent.toNat =
      genericNumerator / 2 + if genericRounded = pow2 (fmt.fracWidth + 1) then 1 else 0 := by
    change (nativeNumerator / 2 + if nativeCarry then 1 else 0).toNat = _
    rw [hcarry]
    by_cases hc : genericRounded = pow2 (fmt.fracWidth + 1)
    · simp only [hc, decide_true, ite_true]
      rw [UInt64.toNat_add, hhalf]
      exact Nat.mod_eq_of_lt (by change genericNumerator / 2 + 1 < 2 ^ 64; omega)
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      rw [UInt64.toNat_add, hhalf]
      exact Nat.mod_eq_of_lt (by change genericNumerator / 2 + 0 < 2 ^ 64; omega)
  have hroundedMantissa : nativeRoundedMantissa.toNat =
      if genericRounded = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth
      else genericRounded := by
    change (if nativeCarry then NativeSmallWord.hiddenBit fmt else nativeRounded).toNat = _
    rw [hcarry]
    by_cases hc : genericRounded = pow2 (fmt.fracWidth + 1)
    · simp only [hc, decide_true, ite_true, hhiddenBit, pow2_eq_two_pow]
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false, hrounded]
  have hfraction : nativeFraction.toNat =
      (if genericRounded = pow2 (fmt.fracWidth + 1) then pow2 fmt.fracWidth
        else genericRounded) - pow2 fmt.fracWidth := by
    have hlower : NativeSmallWord.hiddenBit fmt ≤ nativeRoundedMantissa := by
      apply UInt64.le_iff_toNat_le.mpr
      rw [hroundedMantissa, hhiddenBit]
      split
      · rw [pow2_eq_two_pow]
      · exact hroundedLower
    change (nativeRoundedMantissa - NativeSmallWord.hiddenBit fmt).toNat = _
    rw [UInt64.toNat_sub_of_le _ _ hlower, hroundedMantissa, hhiddenBit]
    simp only [pow2_eq_two_pow]
  rw [hexponent, hfraction]

/-- The dispatcher agrees with the shared finite kernel on every positive finite input. -/
theorem sqrtPositive_eq {fmt : FloatFormat}
    (heligible : NativeSmallWord.StorageEligible fmt)
    (x : Model fmt)
    (hfinite : isFinite x = true)
    (hnonzero : isZero x = false)
    (hpositive : signBit x = false) :
    sqrtPositive heligible x hfinite hnonzero hpositive =
      NativeSmallWordFinite.sqrtPositive heligible x hfinite hnonzero hpositive := by
  unfold sqrtPositive
  split
  · rename_i hfast
    have hieee := hfast.1.1
    have hwidth := hfast.1.2
    have hbias := hfast.2.2
    let bits := NativeSmallWord.toWord x
    let exponent := NativeSmallWord.exponentField fmt bits
    let fraction := NativeSmallWord.fractionField fmt bits
    let mantissa := NativeSmallWordFinite.finiteMantissa fmt exponent fraction
    let scale : UInt64 := if exponent == 0 then 0 else exponent - 1
    have hencoding : fmt.encoding = .ieee :=
      ((FloatFormat.isIEEE_eq_true_iff fmt).mp hieee).1
    have hfieldFinite : expField x ≠ FloatFormat.expAllOnesNat fmt := by
      simpa [isFinite, hencoding, IEEE.isFinite] using hfinite
    have hexponent : exponent.toNat = expField x := by
      simpa [exponent, bits] using NativeSmallWord.exponentField_toNat hwidth x
    have hfraction : fraction.toNat = fracField x := by
      simpa [fraction, bits] using NativeSmallWord.fractionField_toNat hwidth x
    have hfracLt : fraction.toNat < 2 ^ fmt.fracWidth := hfraction ▸ fracField_lt_pow2 x
    have hexpLt : exponent.toNat < 2 ^ fmt.expWidth := hexponent ▸ expField_lt_pow2 x
    have hallOnes := FloatFormat.expAllOnesNat_eq_two_mul_bias_add_one fmt
    have hpowAll : FloatFormat.expAllOnesNat fmt = 2 ^ fmt.expWidth - 1 := rfl
    have hexpLe : exponent.toNat ≤ 2 * fmt.bias := by
      have hne : exponent.toNat ≠ FloatFormat.expAllOnesNat fmt := hexponent ▸ hfieldFinite
      omega
    let components : FiniteKernel.Components := {
      sign := NativeSmallWord.signField fmt bits
      exponent := exponent.toNat
      mantissa := mantissa.toNat }
    have hexceptional : exponent ≠ NativeSmallWord.exponentMask fmt := by
      intro heq
      apply hfieldFinite
      rw [← hexponent, ← NativeSmallWord.exponentMask_toNat hwidth, heq]
    have hnativeDecode : NativeSmallWordFinite.decode? x = some components := by
      unfold NativeSmallWordFinite.decode?
      dsimp only
      rw [ite_eq_right (by simpa only [beq_iff_eq] using hexceptional)]
    have hgenericDecode : FiniteKernel.decode? x = some components :=
      (NativeSmallWordFinite.decode_eq hfast.1 x).symm.trans hnativeDecode
    have hdyadic : toDyadic? x = some (components.toDyadic fmt) := by
      rw [FiniteKernel.toDyadic_eq_decode, hgenericDecode]
      rfl
    have hmNat : mantissa.toNat ≠ 0 := by
      intro hzero
      have hzeroSource :=
        isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hdyadic (by simpa using hzero)
      rw [hnonzero] at hzeroSource
      contradiction
    have hmLt : mantissa.toNat < 2 ^ (fmt.fracWidth + 1) := by
      have hpow : 2 ^ fmt.fracWidth < 2 ^ (fmt.fracWidth + 1) :=
        Nat.pow_lt_pow_right (by decide) (by omega)
      change (if exponent == 0 then fraction else fraction ||| NativeSmallWord.hiddenBit fmt).toNat < _
      split
      · omega
      · rw [UInt64.toNat_or, NativeSmallWord.hiddenBit_toNat_of_width fmt hwidth]
        exact Nat.or_lt_two_pow (by omega) hpow
    have hscale : scale.toNat + 1 ≤ 2 * fmt.bias := by
      change (if exponent == 0 then (0 : UInt64) else exponent - 1).toNat + 1 ≤ _
      split
      · change 0 + 1 ≤ _
        omega
      · rename_i hzero
        have hpos : (1 : UInt64) ≤ exponent := by
          apply UInt64.le_iff_toNat_le.mpr
          have : exponent.toNat ≠ 0 := by
            intro h
            apply hzero
            simp only [beq_iff_eq]
            exact UInt64.toNat_inj.mp (by simpa using h)
          change 1 ≤ exponent.toNat
          omega
        rw [UInt64.toNat_sub_of_le _ _ hpos]
        change exponent.toNat - 1 + 1 ≤ _
        omega
    have hexp : FiniteKernel.dyadicExponent fmt exponent.toNat =
        Int.ofNat scale.toNat - Int.ofNat (fmt.bias + fmt.fracWidth - 1) := by
      have hbiasEq := FloatFormat.exponentBias_eq_bias_of_isIEEE fmt hieee
      have hf := fmt.fracWidth_pos
      unfold FiniteKernel.dyadicExponent FloatFormat.minSubnormalExponent
        FloatFormat.minNormalExponent
      change _ = Int.ofNat (if exponent == 0 then (0 : UInt64) else exponent - 1).toNat - _
      by_cases hzero : exponent = 0
      · simp only [hzero, UInt64.toNat_zero, beq_self_eq_true, ite_true, hbiasEq,
          Int.ofNat_eq_natCast]
        omega
      · have hzeroNat : exponent.toNat ≠ 0 := by
          intro h
          exact hzero (UInt64.toNat_inj.mp (by simpa using h))
        have hpos : (1 : UInt64) ≤ exponent :=
          UInt64.le_iff_toNat_le.mpr (by change 1 ≤ exponent.toNat; omega)
        have hbeq : (exponent == 0) = false := beq_eq_false_iff_ne.mpr hzero
        have hbeqNat : (exponent.toNat == 0) = false := beq_eq_false_iff_ne.mpr hzeroNat
        simp only [hbeq, hbeqNat, Bool.false_eq_true, ite_false, hbiasEq, Int.ofNat_eq_natCast,
          UInt64.toNat_sub_of_le _ _ hpos]
        change _ = ((exponent.toNat - 1 : Nat) : Int) - _
        omega
    unfold NativeSmallWordFinite.sqrtPositive FiniteSqrt.sqrtPositiveDyadic
    change _ = if hzero : mantissa.toNat = 0 then posZero fmt else if fmt.isIEEE then
      ofModel fmt (NativeModelSqrt.sqrt (FloatFormat.toModel fmt)
        (.finite .positive mantissa.toNat (FiniteKernel.dyadicExponent fmt exponent.toNat)
          (Nat.pos_of_ne_zero hzero)))
      else FiniteSqrt.sqrtGeneral fmt mantissa.toNat (FiniteKernel.dyadicExponent fmt exponent.toNat)
    simp only [hmNat, ↓reduceDIte, hieee, ↓reduceIte, NativeModelSqrt.sqrt_eq, hexp]
    exact sqrtPositiveCore_eq fmt hfast mantissa scale (Nat.pos_of_ne_zero hmNat) hmLt hscale
  · rfl

end Model.NativeSmallWordSqrt
end FloatLib.Floats.Formats.BinaryInterchange
