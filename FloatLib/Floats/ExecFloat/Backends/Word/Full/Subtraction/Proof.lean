/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Std.Tactic.BVDecide
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Subtraction.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Word.Full.Core.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof

/-!
# Verified exact subtraction for nearby binary64 values

Sterbenz's lemma says that the difference of two finite floating-point values with the same sign and
magnitudes within a factor of two is representable, the way 1.5 minus 1.25 gives 0.25 with nothing
rounded. So the kernel computes the exact significand difference in `UInt64` and packs it, without
entering the arbitrary-precision generic addition kernel. We prove the positive normal-input core
first and then handle negative operands by negating and swapping them. `subSterbenz_refines` shows
that every accepted result is the finite kernel's, and `subSterbenz?_isSome_iff` states which inputs
the positive kernel accepts. Rejected inputs use the exact generic implementation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64

open FloatLib.Numerics.FixedWord

/-! ## Bit-level bridges for finite binary64 values -/

private theorem toUInt64_negate (x : Value) :
    toUInt64 (negate x) = toUInt64 x ^^^ 0x8000000000000000 := by
  cases x
  rfl

private theorem expField_xor_sign (bits : UInt64) :
    expField (bits ^^^ 0x8000000000000000) = expField bits := by
  apply UInt64.toNat_inj.mp
  change
    (expField (toUInt64 (negate (ofUInt64 bits)))).toNat =
      (expField (toUInt64 (ofUInt64 bits))).toNat
  rw [expField_toNat, expField_toNat, negate_eq, Model.expField_neg]

private theorem fracField_xor_sign (bits : UInt64) :
    fracField (bits ^^^ 0x8000000000000000) = fracField bits := by
  apply UInt64.toNat_inj.mp
  change
    (fracField (toUInt64 (negate (ofUInt64 bits)))).toNat =
      (fracField (toUInt64 (ofUInt64 bits))).toNat
  rw [fracField_toNat, fracField_toNat, negate_eq, Model.fracField_neg]

private theorem signBit_xor_sign (bits : UInt64) :
    signBit (bits ^^^ 0x8000000000000000) = !signBit bits := by
  change
    signBit (toUInt64 (negate (ofUInt64 bits))) =
      !signBit (toUInt64 (ofUInt64 bits))
  rw [signBit_eq, signBit_eq, negate_eq, Model.signBit_neg]
  simp [FloatFormat.supportsSignedZero, FloatFormat.binary64]

private theorem decode_negate_of_finiteExponent (x : Value)
    (hfinite : expField (toUInt64 x) ≠ 0x7ff) :
    decode? (negate x) =
      some {
        sign := !signBit (toUInt64 x)
        exponent := (expField (toUInt64 x)).toNat
        mantissa :=
          (finiteMantissa (expField (toUInt64 x))
            (fracField (toUInt64 x))).toNat } := by
  simp only [decode?, toUInt64_negate]
  rw [expField_xor_sign, fracField_xor_sign, signBit_xor_sign]
  simp [hfinite]

private theorem addFiniteComponents_negate_eq_components
    (x y : Value)
    (hxfinite : expField (toUInt64 x) ≠ 0x7ff)
    (hyfinite : expField (toUInt64 y) ≠ 0x7ff) :
    addFiniteComponents? x (negate y) =
      some (FiniteKernel.addComponents FloatFormat.binary64
        {
          sign := signBit (toUInt64 x)
          exponent := (expField (toUInt64 x)).toNat
          mantissa :=
            (finiteMantissa (expField (toUInt64 x))
              (fracField (toUInt64 x))).toNat }
        {
          sign := !signBit (toUInt64 y)
          exponent := (expField (toUInt64 y)).toNat
          mantissa :=
            (finiteMantissa (expField (toUInt64 y))
              (fracField (toUInt64 y))).toNat }) := by
  unfold addFiniteComponents?
  rw [decode_of_finiteExponent x hxfinite,
    decode_negate_of_finiteExponent y hyfinite]
  simp only [FiniteKernel.Internal.addComponents_eq]

@[simp] private theorem binary64_bias :
    FloatFormat.binary64.bias = 1023 := by
  decide

@[simp] private theorem binary64_align :
    FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 = 1074 := by
  decide

/-! ## Exact finite-difference packing -/

private def packExactDifferenceSpec
    (sign : Bool) (difference exponent : Nat) : Value :=
  if difference = 0 then
    Model.posZero FloatFormat.binary64
  else if difference.log2 + exponent < 53 then
    Model.ofFields FloatFormat.binary64 sign 0
      (difference <<< (exponent - 1))
  else
    let shift := 52 - difference.log2
    let mantissa := difference <<< shift
    let encodedExponent := exponent + difference.log2 - 52
    Model.ofFields FloatFormat.binary64 sign encodedExponent
      (mantissa - 2 ^ 52)

/-- The native leading-bit position of a nonzero difference below `2 ^ 53` is its natural one. -/
private theorem leadingPosition_facts (difference : UInt64)
    (hdifference : difference ≠ 0) (hdifferenceFit : difference.toNat < 2 ^ 53) :
    difference.log2.toNat = difference.toNat.log2 ∧ difference.log2.toNat < 53 :=
  ⟨FloatLib.Numerics.FixedWord.log2_toNat difference,
    log2_toNat_lt_of_toNat_lt_two_pow difference 53 hdifference hdifferenceFit⟩

/-- A left shift that keeps the leading bit of a word below bit 64 is exact. -/
private theorem shiftLeft_toNat_of_log2 (value shift : UInt64)
    (hfit : value.toNat.log2 + 1 + shift.toNat ≤ 64) :
    (value <<< shift).toNat = value.toNat <<< shift.toNat := by
  have hshiftLt : shift.toNat < 64 := by omega
  have hvalueFit : value.toNat <<< shift.toNat < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.shiftLeft_lt Nat.lt_log2_self) (Nat.pow_le_pow_right (by decide) hfit)
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hshiftLt, Nat.mod_eq_of_lt hvalueFit]

/-- The native subnormal test on a difference's leading-bit position is the test on its value. -/
private theorem leadingPosition_lt_iff (difference exponent : UInt64)
    (hdifference : difference ≠ 0) (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentFinite : exponent.toNat < 2047) :
    difference.log2 + exponent < 53 ↔ difference.toNat.log2 + exponent.toNat < 53 := by
  obtain ⟨hleading, hleadingLt⟩ := leadingPosition_facts difference hdifference hdifferenceFit
  rw [UInt64.lt_iff_toNat_lt, uint64_add_toNat_of_lt _ _ (by omega), hleading]
  exact Iff.rfl

private theorem packExactDifference_eq_spec_subnormal
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047)
    (hsubnormal : difference.log2 + exponent < 53) :
    packExactDifference sign difference exponent =
      packExactDifferenceSpec sign difference.toNat exponent.toNat := by
  have hzeroNat : difference.toNat ≠ 0 := by
    simpa [uint64_toNat_eq_zero] using hdifference
  have hsubnormalNat :=
    (leadingPosition_lt_iff difference exponent hdifference hdifferenceFit
      hexponentFinite).mp hsubnormal
  unfold packExactDifference packExactDifferenceSpec
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  simp only [beq_iff_eq, hdifference, hzeroNat, ite_false,
    hsubnormal, hsubnormalNat, ite_true]
  have hexponentWord : (1 : UInt64) ≤ exponent := by
    apply UInt64.le_iff_toNat_le.mpr
    simp
    omega
  have hwordShift :
      (exponent - 1).toNat = exponent.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le exponent 1 hexponentWord]
    simp
  have hnativeFraction :
      (difference <<< (exponent - 1)).toNat =
        difference.toNat <<< (exponent.toNat - 1) := by
    rw [shiftLeft_toNat_of_log2 _ _ (by omega), hwordShift]
  have hfractionFit :
      difference.toNat <<< (exponent.toNat - 1) < 2 ^ 64 := by
    rw [← hnativeFraction]
    exact UInt64.toNat_lt _
  have hnativeFractionWord :
      difference <<< (exponent - 1) =
        UInt64.ofNat
          (difference.toNat <<< (exponent.toNat - 1)) := by
    apply UInt64.toNat_inj.mp
    rw [hnativeFraction]
    exact (UInt64.toNat_ofNat_of_lt hfractionFit).symm
  rw [hnativeFractionWord]
  exact packFieldsWord_eq_ofNat sign 0 _

private theorem normalizedMantissa_toNat
    (difference : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53) :
    (difference <<< (52 - difference.log2)).toNat =
      difference.toNat <<< (52 - difference.toNat.log2) := by
  obtain ⟨hleading, hleadingLt⟩ := leadingPosition_facts difference hdifference hdifferenceFit
  have hleadingLe : difference.log2 ≤ (52 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    change difference.log2.toNat ≤ 52
    omega
  have hshift :
      ((52 : UInt64) - difference.log2).toNat =
        52 - difference.toNat.log2 := by
    rw [UInt64.toNat_sub_of_le _ _ hleadingLe, hleading]
    rfl
  rw [shiftLeft_toNat_of_log2 _ _ (by omega), hshift]

private theorem encodedExponent_word
    (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentFinite : exponent.toNat < 2047)
    (hnormal : ¬difference.log2 + exponent < 53) :
    exponent + difference.log2 - 52 =
      UInt64.ofNat
        (exponent.toNat + difference.toNat.log2 - 52) := by
  obtain ⟨hleading, hleadingLt⟩ := leadingPosition_facts difference hdifference hdifferenceFit
  have haddFit :
      exponent.toNat + difference.log2.toNat < 2 ^ 64 := by
    have hsmall : exponent.toNat + difference.log2.toNat < 2100 := by
      omega
    exact lt_trans hsmall (by norm_num)
  have hadd :
      (exponent + difference.log2).toNat =
        exponent.toNat + difference.toNat.log2 := by
    have h := uint64_add_toNat_of_lt exponent difference.log2 haddFit
    simpa only [hleading] using h
  have hnormalNat :
      53 ≤ difference.toNat.log2 + exponent.toNat := by
    have := (leadingPosition_lt_iff difference exponent hdifference hdifferenceFit
      hexponentFinite).not.mp hnormal
    omega
  have h52 : (52 : UInt64) ≤ exponent + difference.log2 := by
    apply UInt64.le_iff_toNat_le.mpr
    change 52 ≤ (exponent + difference.log2).toNat
    rw [hadd]
    omega
  have hencodedFit :
      exponent.toNat + difference.toNat.log2 - 52 < 2 ^ 64 := by
    have hsmall :
        exponent.toNat + difference.toNat.log2 - 52 < 2100 := by
      omega
    exact lt_trans hsmall (by norm_num)
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ h52, hadd]
  exact (UInt64.toNat_ofNat_of_lt hencodedFit).symm

private theorem uint64_sub_eq_ofNat
    (x y : UInt64) (hle : y ≤ x)
    (hfit : x.toNat - y.toNat < 2 ^ 64) :
    x - y = UInt64.ofNat (x.toNat - y.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ hle]
  exact (UInt64.toNat_ofNat_of_lt hfit).symm

private theorem normalizedFraction_word
    (difference : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53) :
    difference <<< (52 - difference.log2) -
        0x0010000000000000 =
      UInt64.ofNat
        (difference.toNat <<< (52 - difference.toNat.log2) -
          2 ^ 52) := by
  have hzeroNat : difference.toNat ≠ 0 := by
    simpa [uint64_toNat_eq_zero] using hdifference
  obtain ⟨hleading, hleadingLt⟩ := leadingPosition_facts difference hdifference hdifferenceFit
  have hleadingNatLe : difference.toNat.log2 ≤ 52 := by
    rw [← hleading]
    omega
  have hnativeMantissa :=
    normalizedMantissa_toNat difference hdifference hdifferenceFit
  have hmantissaLower :
      2 ^ 52 ≤ difference.toNat <<< (52 - difference.toNat.log2) := by
    exact two_pow_le_shiftLeft_sub_log2 52 difference.toNat hzeroNat
  have hbaseWord :
      (0x0010000000000000 : UInt64) ≤
        difference <<< (52 - difference.log2) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hnativeMantissa]
    simpa using hmantissaLower
  have hfractionFit :
      difference.toNat <<< (52 - difference.toNat.log2) - 2 ^ 52 <
        2 ^ 64 := by
    have hmantissaUpper :
        difference.toNat <<< (52 - difference.toNat.log2) < 2 ^ 53 := by
      exact shiftLeft_sub_log2_lt_two_pow 52 difference.toNat hleadingNatLe
    exact lt_trans (Nat.sub_lt_of_lt hmantissaUpper) (by norm_num)
  rw [uint64_sub_eq_ofNat _ _ hbaseWord (by
    rw [hnativeMantissa]
    norm_num
    exact hfractionFit)]
  rw [hnativeMantissa]
  congr 1

private theorem packExactDifference_eq_spec_normal
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentFinite : exponent.toNat < 2047)
    (hnormal : ¬difference.log2 + exponent < 53) :
    packExactDifference sign difference exponent =
      packExactDifferenceSpec sign difference.toNat exponent.toNat := by
  have hzeroNat : difference.toNat ≠ 0 := by
    simpa [uint64_toNat_eq_zero] using hdifference
  have hnormalNat :
      ¬difference.toNat.log2 + exponent.toNat < 53 := fun h =>
    hnormal ((leadingPosition_lt_iff difference exponent hdifference hdifferenceFit
      hexponentFinite).mpr h)
  unfold packExactDifference packExactDifferenceSpec
  simp only [FloatLib.Numerics.FixedWord.log2Word_eq_log2]
  simp only [beq_iff_eq, hdifference, hzeroNat, ite_false,
    hnormal, hnormalNat, ite_false]
  rw [encodedExponent_word difference exponent hdifference hdifferenceFit
      hexponentFinite hnormal,
    normalizedFraction_word difference hdifference hdifferenceFit]
  exact packFieldsWord_eq_ofNat sign
    (exponent.toNat + difference.toNat.log2 - 52)
    (difference.toNat <<< (52 - difference.toNat.log2) - 2 ^ 52)

private theorem packExactDifference_eq_spec
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047) :
    packExactDifference sign difference exponent =
      packExactDifferenceSpec sign difference.toNat exponent.toNat := by
  by_cases hsubnormal : difference.log2 + exponent < 53
  · exact packExactDifference_eq_spec_subnormal sign difference exponent
      hdifference hdifferenceFit hexponentPositive hexponentFinite hsubnormal
  · exact packExactDifference_eq_spec_normal sign difference exponent
      hdifference hdifferenceFit hexponentFinite hsubnormal

private theorem packExactDifferenceSpec_eq_round
    (sign : Bool) (difference exponent : Nat)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference < 2 ^ 53)
    (hexponentPositive : 0 < exponent)
    (hexponentFinite : exponent < 2047) :
    packExactDifferenceSpec sign difference exponent =
      FiniteProductRound.round FloatFormat.binary64 sign difference
        (exponent + 1073) := by
  have hleadingLt : difference.log2 < 53 := by
    rw [Nat.log2_lt]
    · exact hdifferenceFit
    · exact hdifference
  unfold packExactDifferenceSpec FiniteProductRound.round
  simp only [beq_iff_eq, hdifference, ite_false]
  by_cases hsubnormal : difference.log2 + exponent < 53
  · have hgenericSubnormal :
        difference.log2 + (exponent + 1073) <
          FloatFormat.binary64.bias +
            2 * FloatFormat.binary64.fracWidth - 1 := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [ite_eq_left hsubnormal, ite_eq_left hgenericSubnormal]
    have hscaleNotSmall :
        ¬exponent + 1073 <
          FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 := by
      simp only [binary64_align]
      omega
    rw [ite_eq_right hscaleNotSmall]
    have hshift :
        exponent + 1073 -
            FloatFormat.ieeeSubnormalAlignExp FloatFormat.binary64 =
          exponent - 1 := by
      simp only [binary64_align]
      omega
    rw [hshift]
    have hfractionPositive :
        difference <<< (exponent - 1) ≠ 0 := by
      simp [hdifference]
    have hfractionLt :
        difference <<< (exponent - 1) < 2 ^ 52 := by
      have hbound :
          difference.log2 + 1 + (exponent - 1) ≤ 52 := by
        omega
      exact lt_of_lt_of_le
        (Nat.shiftLeft_lt (m := exponent - 1) Nat.lt_log2_self)
        (Nat.pow_le_pow_right (n := 2) (by decide) hbound)
    simp only [hfractionPositive, ite_false]
    have hfractionNotBase :
        difference <<< (exponent - 1) ≠
          Model.pow2 FloatFormat.binary64.fracWidth := by
      simp only [binary64_fracWidth, Model.pow2_eq_two_pow]
      exact ne_of_lt hfractionLt
    simp only [hfractionNotBase, ite_false]
  · have hgenericNormal :
        ¬difference.log2 + (exponent + 1073) <
          FloatFormat.binary64.bias +
            2 * FloatFormat.binary64.fracWidth - 1 := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [ite_eq_right hsubnormal, ite_eq_right hgenericNormal]
    have hleadingLe : difference.log2 ≤ 52 := by
      omega
    have hgenericRounded :
        (if FloatFormat.binary64.fracWidth ≤ difference.log2 then
            Numerics.roundShiftRightEven difference
              (difference.log2 - FloatFormat.binary64.fracWidth)
          else
            difference <<<
              (FloatFormat.binary64.fracWidth - difference.log2)) =
          difference <<< (52 - difference.log2) := by
      simp only [binary64_fracWidth]
      by_cases htop : difference.log2 = 52
      · simp [htop]
      · have hsmall : difference.log2 < 52 := by
          omega
        simp [Nat.not_le_of_lt hsmall]
    rw [hgenericRounded]
    have hcarry :
        difference <<< (52 - difference.log2) ≠
          Model.pow2 (FloatFormat.binary64.fracWidth + 1) := by
      have hupper :=
        shiftLeft_sub_log2_lt_two_pow 52 difference hleadingLe
      simp only [binary64_fracWidth, Model.pow2_eq_two_pow]
      omega
    simp only [hcarry, ite_false]
    have hoverflow :
        ¬3 * FloatFormat.binary64.bias +
              2 * FloatFormat.binary64.fracWidth - 2 <
            difference.log2 + (exponent + 1073) := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [ite_eq_right hoverflow]
    have hencoded :
        difference.log2 + (exponent + 1073) -
            (FloatFormat.binary64.bias +
              2 * FloatFormat.binary64.fracWidth - 2) =
          exponent + difference.log2 - 52 := by
      simp only [binary64_bias, binary64_fracWidth]
      omega
    rw [hencoded]
    simp only [binary64_fracWidth, Model.pow2_eq_two_pow]

/-- Exact native difference packing agrees with the generic unsigned-scale rounder. -/
theorem packExactDifference_eq_round
    (sign : Bool) (difference exponent : UInt64)
    (hdifference : difference ≠ 0)
    (hdifferenceFit : difference.toNat < 2 ^ 53)
    (hexponentPositive : 0 < exponent.toNat)
    (hexponentFinite : exponent.toNat < 2047) :
    packExactDifference sign difference exponent =
      FiniteProductRound.round FloatFormat.binary64 sign difference.toNat
        (exponent.toNat + 1073) := by
  rw [packExactDifference_eq_spec sign difference exponent hdifference
    hdifferenceFit hexponentPositive hexponentFinite]
  exact packExactDifferenceSpec_eq_round sign difference.toNat exponent.toNat
    (by simpa [uint64_toNat_eq_zero] using hdifference)
    hdifferenceFit hexponentPositive hexponentFinite

/-! ## Component-level binary64 subtraction -/

/-- Normal binary64 components add through the exact dyadic sum of their values. -/
private theorem addComponents_normal (leftSign rightSign : Bool)
    (leftExponent rightExponent left right : Nat)
    (hleftExponent : leftExponent ≠ 0) (hrightExponent : rightExponent ≠ 0)
    (hleft : left ≠ 0) (hright : right ≠ 0) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := leftSign, exponent := leftExponent, mantissa := left }
        { sign := rightSign, exponent := rightExponent, mantissa := right } =
      roundDyadic FloatFormat.binary64
        (addDyadic
          { negative := leftSign, significand := left,
            exponent := Int.ofNat leftExponent - 1075 }
          { negative := rightSign, significand := right,
            exponent := Int.ofNat rightExponent - 1075 }) := by
  unfold FiniteKernel.addComponents
  rw [← roundDyadic_eq_internal,
    normalComponents_toDyadic leftSign leftExponent left hleftExponent hleft,
    normalComponents_toDyadic rightSign rightExponent right hrightExponent hright]

/-- A dyadic at a normal binary64 exponent rounds through the product rounder at that scale. -/
private theorem roundDyadic_normalScale (sign : Bool) (significand exponent : Nat) :
    roundDyadic FloatFormat.binary64
        { negative := sign, significand, exponent := Int.ofNat exponent - 1075 } =
      FiniteProductRound.round FloatFormat.binary64 sign significand (exponent + 1073) := by
  rw [FiniteProductRound.round_eq_roundDyadic FloatFormat.binary64 (by decide),
    roundScaleExponent]

private theorem normalExponent_succ (exponent : Nat) :
    Int.ofNat (exponent + 1) - 1075 = (Int.ofNat exponent - 1075) + 1 := by
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
  omega

private theorem addComponents_same_large_left
    (large small exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa := large }
        { sign := true, exponent, mantissa := small } =
      FiniteProductRound.round FloatFormat.binary64 false (large - small)
        (exponent + 1073) := by
  rw [addComponents_normal false true exponent exponent large small hexponent hexponent
      (by omega) hsmall,
    addDyadic_oppositeSign_sameExponent_largeLeft false true large small
      (Int.ofNat exponent - 1075) (by decide) hlt,
    roundDyadic_normalScale]

private theorem addComponents_same_equal
    (mantissa exponent : Nat)
    (hexponent : exponent ≠ 0) (hmantissa : mantissa ≠ 0) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa }
        { sign := true, exponent, mantissa } =
      packExactDifference false 0 (UInt64.ofNat exponent) := by
  unfold FiniteKernel.addComponents
  rw [normalComponents_toDyadic false exponent mantissa
      hexponent hmantissa,
    normalComponents_toDyadic true exponent mantissa
      hexponent hmantissa]
  rw [show addDyadic
      { negative := false, significand := mantissa, exponent := Int.ofNat exponent - 1075 }
      { negative := true, significand := mantissa, exponent := Int.ofNat exponent - 1075 } =
        { negative := false, significand := 0, exponent := 0 } by
      exact addDyadic_oppositeSign_sameExponent_eq_zero
        false true mantissa (Int.ofNat exponent - 1075)
        (by decide)]
  rfl

private theorem addComponents_same_large_right
    (small large exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlt : small < large) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa := small }
        { sign := true, exponent, mantissa := large } =
      FiniteProductRound.round FloatFormat.binary64 true (large - small)
        (exponent + 1073) := by
  rw [addComponents_normal false true exponent exponent small large hexponent hexponent hsmall
      (by omega),
    addDyadic_oppositeSign_sameExponent_largeRight false true small large
      (Int.ofNat exponent - 1075) (by decide) hlt,
    roundDyadic_normalScale]

private theorem addComponents_adjacent_large_left
    (large small exponent : Nat)
    (hexponent : exponent ≠ 0) (hlarge : large ≠ 0)
    (hsmall : small ≠ 0) (hlt : small < large <<< 1) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent := exponent + 1, mantissa := large }
        { sign := true, exponent, mantissa := small } =
      FiniteProductRound.round FloatFormat.binary64 false
        ((large <<< 1) - small) (exponent + 1073) := by
  rw [addComponents_normal false true (exponent + 1) exponent large small (by omega) hexponent
      hlarge hsmall,
    normalExponent_succ,
    addDyadic_oppositeSign_adjacentExponent_largeLeft false true large small
      (Int.ofNat exponent - 1075) hsmall (by decide) hlt,
    roundDyadic_normalScale]
  rfl

private theorem addComponents_adjacent_large_right
    (small large exponent : Nat)
    (hexponent : exponent ≠ 0) (hsmall : small ≠ 0)
    (hlarge : large ≠ 0) (hlt : small < large <<< 1) :
    FiniteKernel.addComponents FloatFormat.binary64
        { sign := false, exponent, mantissa := small }
        { sign := true, exponent := exponent + 1, mantissa := large } =
      FiniteProductRound.round FloatFormat.binary64 true
        ((large <<< 1) - small) (exponent + 1073) := by
  rw [addComponents_normal false true exponent (exponent + 1) small large hexponent (by omega)
      hsmall hlarge,
    normalExponent_succ,
    addDyadic_oppositeSign_adjacentExponent_largeRight false true small large
      (Int.ofNat exponent - 1075) hsmall (by decide) hlt,
    roundDyadic_normalScale]
  rfl

/-- The successor of a finite binary64 exponent field is exact. -/
private theorem exponent_succ_toNat (exponent : UInt64) (hexponent : exponent.toNat < 2047) :
    (exponent + 1).toNat = exponent.toNat + 1 := by
  rw [uint64_add_toNat_of_lt]
  · rfl
  · norm_num
    omega

/-- Facts `packExactDifference` needs about the significand difference at equal exponents. -/
private theorem sameExponentDifference_facts (upper lower : UInt64)
    (hupper : upper.toNat < 2 ^ 53) (hlt : lower.toNat < upper.toNat) :
    (upper - lower).toNat = upper.toNat - lower.toNat ∧ upper - lower ≠ 0 ∧
      (upper - lower).toNat < 2 ^ 53 := by
  have hdifference := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlt.le)
  refine ⟨hdifference, fun hzero => ?_, by omega⟩
  have hzeroNat := congrArg UInt64.toNat hzero
  rw [hdifference, UInt64.toNat_zero] at hzeroNat
  omega

private theorem adjacentDifference_facts (upper lower : UInt64)
    (hupper : 2 ^ 52 ≤ upper.toNat ∧ upper.toNat < 2 ^ 53)
    (hlower : 2 ^ 52 ≤ lower.toNat ∧ lower.toNat < 2 ^ 53)
    (hle : upper ≤ lower) :
    lower.toNat < upper.toNat <<< 1 ∧
      ((upper <<< 1) - lower).toNat = (upper.toNat <<< 1) - lower.toNat ∧
      (upper <<< 1) - lower ≠ 0 ∧
      ((upper <<< 1) - lower).toNat < 2 ^ 53 := by
  have hshiftFit : upper.toNat <<< 1 < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hshift : (upper <<< 1).toNat = upper.toNat <<< 1 := by
    simpa using shiftLeft_toNat upper 1 hshiftFit
  have hlt : lower.toNat < upper.toNat <<< 1 := by
    rw [Nat.shiftLeft_eq]
    norm_num
    omega
  have hword : lower ≤ upper <<< 1 :=
    UInt64.le_iff_toNat_le.mpr (by rw [hshift]; exact hlt.le)
  have hdifference :
      ((upper <<< 1) - lower).toNat = (upper.toNat <<< 1) - lower.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ hword, hshift]
  refine ⟨hlt, hdifference, ?_, ?_⟩
  · intro hzero
    have hzeroNat := congrArg UInt64.toNat hzero
    rw [hdifference] at hzeroNat
    simp only [UInt64.toNat_zero] at hzeroNat
    omega
  · have hleNat := UInt64.le_iff_toNat_le.mp hle
    rw [hdifference, Nat.shiftLeft_eq]
    norm_num
    omega

/--
Every result of `subSterbenz?` is also the result of the finite binary64 subtraction path
`addFiniteComponents? x (negate y)`, which handles the rejected inputs.
-/
theorem subSterbenz_refines (x y result : Value)
    (hfast : subSterbenz? x y = some result) :
    addFiniteComponents? x (negate y) = some result := by
  unfold subSterbenz? at hfast
  dsimp only at hfast
  set xBits := toUInt64 x with hxBits
  set yBits := toUInt64 y with hyBits
  set xExponent := expField xBits with hxExponent
  set yExponent := expField yBits with hyExponent
  set xFraction := fracField xBits with hxFraction
  set yFraction := fracField yBits with hyFraction
  set xMantissa := finiteMantissa xExponent xFraction with hxMantissa
  set yMantissa := finiteMantissa yExponent yFraction with hyMantissa
  by_cases hxSign : signBit xBits = true
  · simp [hxSign] at hfast
  have hxSignFalse : signBit xBits = false := by
    cases h : signBit xBits <;> simp_all
  by_cases hySign : signBit yBits = true
  · simp [hxSignFalse, hySign] at hfast
  have hySignFalse : signBit yBits = false := by
    cases h : signBit yBits <;> simp_all
  by_cases hxExponentZero : xExponent = 0
  · simp [hxSignFalse, hySignFalse, hxExponentZero] at hfast
  by_cases hyExponentZero : yExponent = 0
  · simp [hxSignFalse, hySignFalse, hyExponentZero] at hfast
  by_cases hxExponentExceptional : xExponent = 0x7ff
  · simp [hxSignFalse, hySignFalse, hxExponentExceptional] at hfast
  by_cases hyExponentExceptional : yExponent = 0x7ff
  · simp [hxSignFalse, hySignFalse, hyExponentExceptional] at hfast
  obtain ⟨⟨hxExponentPositive, hxExponentFinite⟩, hxMantissaBounds⟩ :
      (0 < xExponent.toNat ∧ xExponent.toNat < 2047) ∧
        (2 ^ 52 ≤ xMantissa.toNat ∧ xMantissa.toNat < 2 ^ 53) :=
    normalOperand_bounds x hxExponentZero hxExponentExceptional
  obtain ⟨⟨hyExponentPositive, hyExponentFinite⟩, hyMantissaBounds⟩ :
      (0 < yExponent.toNat ∧ yExponent.toNat < 2047) ∧
        (2 ^ 52 ≤ yMantissa.toNat ∧ yMantissa.toNat < 2 ^ 53) :=
    normalOperand_bounds y hyExponentZero hyExponentExceptional
  simp [hxSignFalse, hySignFalse, hxExponentZero, hyExponentZero,
    hxExponentExceptional, hyExponentExceptional] at hfast
  rw [addFiniteComponents_negate_eq_components x y hxExponentExceptional hyExponentExceptional]
  rw [← hxBits, ← hyBits, ← hxExponent, ← hyExponent, ← hxFraction,
    ← hyFraction, ← hxMantissa, ← hyMantissa, hxSignFalse, hySignFalse]
  simp only [Bool.not_false]
  by_cases hsame : xExponent = yExponent
  · simp [hsame] at hfast
    by_cases hle : yMantissa ≤ xMantissa
    · rw [ite_eq_left hle] at hfast
      have hresult := Option.some.inj hfast
      subst result
      by_cases hequal : xMantissa = yMantissa
      · rw [← hsame, ← hequal]
        rw [addComponents_same_equal xMantissa.toNat xExponent.toNat
          hxExponentPositive.ne' (by omega)]
        have hexponentRoundtrip :
            UInt64.ofNat xExponent.toNat = xExponent := by
          exact UInt64.ofNat_toNat
        rw [hexponentRoundtrip]
        simp [packExactDifference]
      · have hleNat : yMantissa.toNat ≤ xMantissa.toNat :=
          UInt64.le_iff_toNat_le.mp hle
        have hneNat : yMantissa.toNat ≠ xMantissa.toNat := by
          intro h
          apply hequal
          apply UInt64.toNat_inj.mp
          exact h.symm
        have hltNat : yMantissa.toNat < xMantissa.toNat :=
          Nat.lt_of_le_of_ne hleNat hneNat
        obtain ⟨hdifferenceNat, hdifferenceNonzero, hdifferenceFit⟩ :=
          sameExponentDifference_facts xMantissa yMantissa hxMantissaBounds.2 hltNat
        rw [← hsame]
        rw [addComponents_same_large_left
          xMantissa.toNat yMantissa.toNat xExponent.toNat
          hxExponentPositive.ne' (by omega) hltNat]
        rw [packExactDifference_eq_round false (xMantissa - yMantissa) xExponent
          hdifferenceNonzero hdifferenceFit hxExponentPositive hxExponentFinite,
          hdifferenceNat]
    · rw [ite_eq_right hle] at hfast
      have hresult := Option.some.inj hfast
      subst result
      have hltNat : xMantissa.toNat < yMantissa.toNat := by
        have hnotLeNat : ¬yMantissa.toNat ≤ xMantissa.toNat := by
          intro hleNat
          apply hle
          exact UInt64.le_iff_toNat_le.mpr hleNat
        omega
      obtain ⟨hdifferenceNat, hdifferenceNonzero, hdifferenceFit⟩ :=
        sameExponentDifference_facts yMantissa xMantissa hyMantissaBounds.2 hltNat
      rw [← hsame]
      rw [addComponents_same_large_right
        xMantissa.toNat yMantissa.toNat xExponent.toNat
        hxExponentPositive.ne' (by omega) hltNat]
      rw [packExactDifference_eq_round true (yMantissa - xMantissa) xExponent
        hdifferenceNonzero hdifferenceFit hxExponentPositive hxExponentFinite,
        hdifferenceNat]
  · by_cases hleft :
        xExponent = yExponent + 1 ∧ xMantissa ≤ yMantissa
    · have hleftCondition := hleft
      rcases hleft with ⟨hxAdjacent, hxyMantissa⟩
      simp only [ite_eq_right hsame, ite_eq_left hleftCondition] at hfast
      have hresult := Option.some.inj hfast
      subst result
      have hxExponentNat : xExponent.toNat = yExponent.toNat + 1 := by
        rw [hxAdjacent, exponent_succ_toNat yExponent hyExponentFinite]
      obtain ⟨hyLtShiftNat, hdifferenceNat, hdifferenceNonzero, hdifferenceFit⟩ :=
        adjacentDifference_facts xMantissa yMantissa
          hxMantissaBounds hyMantissaBounds hxyMantissa
      rw [hxExponentNat]
      rw [addComponents_adjacent_large_left
        xMantissa.toNat yMantissa.toNat yExponent.toNat
        hyExponentPositive.ne' (by omega) (by omega) hyLtShiftNat]
      rw [packExactDifference_eq_round false
        ((xMantissa <<< 1) - yMantissa) yExponent
        hdifferenceNonzero hdifferenceFit
        hyExponentPositive hyExponentFinite]
      rw [hdifferenceNat]
    · by_cases hright :
          yExponent = xExponent + 1 ∧ yMantissa ≤ xMantissa
      · have hrightCondition := hright
        rcases hright with ⟨hyAdjacent, hyxMantissa⟩
        simp only [ite_eq_right hsame, ite_eq_right hleft,
          ite_eq_left hrightCondition] at hfast
        have hresult := Option.some.inj hfast
        subst result
        have hyExponentNat : yExponent.toNat = xExponent.toNat + 1 := by
          rw [hyAdjacent, exponent_succ_toNat xExponent hxExponentFinite]
        obtain ⟨hxLtShiftNat, hdifferenceNat, hdifferenceNonzero, hdifferenceFit⟩ :=
          adjacentDifference_facts yMantissa xMantissa
            hyMantissaBounds hxMantissaBounds hyxMantissa
        rw [hyExponentNat]
        rw [addComponents_adjacent_large_right
          xMantissa.toNat yMantissa.toNat xExponent.toNat
          hxExponentPositive.ne' (by omega) (by omega) hxLtShiftNat]
        rw [packExactDifference_eq_round true
          ((yMantissa <<< 1) - xMantissa) xExponent
          hdifferenceNonzero hdifferenceFit
          hxExponentPositive hxExponentFinite]
        rw [hdifferenceNat]
      · simp [hsame, hleft, hright] at hfast

/--
`subSterbenz?` returns a result exactly when both operands are positive and normal and their
exponent fields are equal, or adjacent with the larger-exponent operand's significand no greater
than the other's. For `x = m_x * 2 ^ (e + 1)` and `y = m_y * 2 ^ e`, the adjacent test `m_x ≤ m_y`
is `x ≤ 2 * y`, the factor-two condition of Sterbenz's lemma.

`subFinite?` reaches it through `subSignedSterbenz?`, which negates and swaps two negative operands,
and falls back to `addFinite? x (negate y)` when `subSignedSterbenz?` declines.
-/
theorem subSterbenz?_isSome_iff (x y : Value) :
    (subSterbenz? x y).isSome = true ↔
      signBit (toUInt64 x) = false ∧ signBit (toUInt64 y) = false ∧
        expField (toUInt64 x) ≠ 0 ∧ expField (toUInt64 y) ≠ 0 ∧
        expField (toUInt64 x) ≠ 0x7ff ∧ expField (toUInt64 y) ≠ 0x7ff ∧
        (expField (toUInt64 x) = expField (toUInt64 y) ∨
          expField (toUInt64 x) = expField (toUInt64 y) + 1 ∧
            finiteMantissa (expField (toUInt64 x)) (fracField (toUInt64 x)) ≤
              finiteMantissa (expField (toUInt64 y)) (fracField (toUInt64 y)) ∨
          expField (toUInt64 y) = expField (toUInt64 x) + 1 ∧
            finiteMantissa (expField (toUInt64 y)) (fracField (toUInt64 y)) ≤
              finiteMantissa (expField (toUInt64 x)) (fracField (toUInt64 x))) := by
  unfold subSterbenz?
  dsimp only
  generalize signBit (toUInt64 x) = xSign
  generalize signBit (toUInt64 y) = ySign
  generalize expField (toUInt64 x) = xExponent
  generalize expField (toUInt64 y) = yExponent
  generalize finiteMantissa xExponent (fracField (toUInt64 x)) = xMantissa
  generalize finiteMantissa yExponent (fracField (toUInt64 y)) = yMantissa
  by_cases hguard : (xSign || ySign || xExponent == 0 || yExponent == 0 ||
      xExponent == 0x7ff || yExponent == 0x7ff) = true
  · rw [ite_eq_left hguard]
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    simp only [Bool.or_eq_true, beq_iff_eq] at hguard
    rintro ⟨hxSign, hySign, hxZero, hyZero, hxAll, hyAll, -⟩
    rcases hguard with (((((h | h) | h) | h) | h) | h)
    · rw [hxSign] at h; exact Bool.false_ne_true h
    · rw [hySign] at h; exact Bool.false_ne_true h
    · exact hxZero h
    · exact hyZero h
    · exact hxAll h
    · exact hyAll h
  · rw [ite_eq_right hguard]
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hguard
    obtain ⟨⟨⟨⟨⟨hxSign, hySign⟩, hxZero⟩, hyZero⟩, hxAll⟩, hyAll⟩ := hguard
    simp only [hxSign, hySign, true_and]
    refine ⟨fun h => ⟨hxZero, hyZero, hxAll, hyAll, ?_⟩, fun h => ?_⟩
    · by_cases hsame : xExponent = yExponent
      · exact Or.inl hsame
      · rw [ite_eq_right (by simpa using hsame)] at h
        by_cases hleft : (xExponent == yExponent + 1 && xMantissa ≤ yMantissa) = true
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hleft
          exact Or.inr (Or.inl hleft)
        · rw [ite_eq_right hleft] at h
          by_cases hright : (yExponent == xExponent + 1 && yMantissa ≤ xMantissa) = true
          · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hright
            exact Or.inr (Or.inr hright)
          · rw [ite_eq_right hright] at h
            simp at h
    · obtain ⟨-, -, -, -, h⟩ := h
      by_cases hsame : xExponent = yExponent
      · rw [ite_eq_left (by simpa using hsame)]
        split <;> rfl
      rw [ite_eq_right (by simpa using hsame)]
      by_cases hleft : (xExponent == yExponent + 1 && xMantissa ≤ yMantissa) = true
      · rw [ite_eq_left hleft]
        rfl
      rw [ite_eq_right hleft]
      rcases h with h | h | h
      · exact absurd h hsame
      · exact absurd (by simpa using h) hleft
      · rw [ite_eq_left (by simpa using h)]
        rfl

/--
Every result of `subSignedSterbenz?` is also the result of `addFiniteComponents? x (negate y)`.

For negative operands it reuses `subSterbenz_refines` after negating and swapping both inputs,
then uses commutativity of exact finite addition.
-/
theorem subSignedSterbenz_refines (x y result : Value)
    (hfast : subSignedSterbenz? x y = some result) :
    addFiniteComponents? x (negate y) = some result := by
  unfold subSignedSterbenz? at hfast
  dsimp only at hfast
  cases hxSign : signBit (toUInt64 x) <;>
    cases hySign : signBit (toUInt64 y)
  · exact subSterbenz_refines x y result (by simpa [hxSign, hySign] using hfast)
  · simp [hxSign, hySign] at hfast
  · simp [hxSign, hySign] at hfast
  · have hnegative :
        subSterbenz? (negate y) (negate x) = some result := by
      simpa [hxSign, hySign] using hfast
    have hrefines :=
      subSterbenz_refines (negate y) (negate x) result hnegative
    rw [negate_negate] at hrefines
    calc
      addFiniteComponents? x (negate y) =
          addFiniteComponents? (negate y) x := addFiniteComponents_comm _ _
      _ = some result := hrefines

end FloatLib.Floats.Formats.BinaryInterchange.Model.NativeBinary64
