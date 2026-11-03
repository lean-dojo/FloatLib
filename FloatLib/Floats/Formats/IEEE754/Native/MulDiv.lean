/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.LeanModel.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Representation
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.ExecFloat.Instances
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.SqrtSemantics
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.NonNaN
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Branches
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.RoundedReal

/-!
# Native multiplication and division

These theorems relate FloatLib's multiplication and division to the logical floating-point model
shipped with Lean, on the complete packed word. The operands are finite, signed zeros included;
the result is unrestricted, so subnormal results, overflow to infinity, `x / 0` and `0 / 0` are
covered.

A product rounds one exact dyadic in both models. A quotient is compared through its value: both
results are finite exactly when the exact quotient stays below the overflow threshold, and then
they are the nearest-even rounding of the same real with the same sign; otherwise both are the
infinity of the quotient's sign. These model equalities do not verify the machine instructions
used by compiled native code.

The configured operations are the first-order binary32 and binary64 instances of
`Configured.NativeDispatch`, the ones a client that imports `Configured` elaborates, so `rw` and
`simp` apply the bridges to client terms in either direction.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open Float.Model.UnpackedFloat
open FloatLib.Floats.Formats.Flocq (nearestEven)

/-- The sign bit of a product is the exclusive or of the operand sign bits. -/
private theorem modelSign_xor (s₁ s₂ : Sign) :
    modelSign (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) = s₁ * s₂ := by
  cases s₁ <;> cases s₂ <;> rfl

/-- Under a conventional IEEE descriptor, the signed zero is Lean's packed zero. -/
private theorem zero_eq_ofModel_zero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) : zero fmt sign = ofModel fmt (.zero (modelSign sign)) := by
  cases sign
  · simp [zero, posZero_eq_ofModel_zero]
  · simp [zero, FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt,
      negZero_eq_ofModel_zero]

/--
For finite operands, including signed zeros, dispatched multiplication gives the word that Lean's
unpacked model gets by multiplying and packing. The result may underflow or overflow to infinity.
-/
theorem mul_eq_ofModel_mul_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : (toModel x).isFinite = true)
    (hy : (toModel y).isFinite = true) :
    mul x y =
      ofModel fmt
        (Float.Model.UnpackedFloat.mul (FloatFormat.toModel fmt) (toModel x) (toModel y)) := by
  have hxle := @le_targetExponent_totalExponent_of_toModel_eq_finite fmt x
  have hyle := @le_targetExponent_totalExponent_of_toModel_eq_finite fmt y
  rw [Proof.mul_eq_spec, Spec.mul, toDyadic?_ieee_eq_model fmt hfmt x,
    toDyadic?_ieee_eq_model fmt hfmt y]
  cases hxmodel : toModel x <;> cases hymodel : toModel y <;>
    simp only [hxmodel, hymodel, Float.Model.UnpackedFloat.isFinite,
      Bool.false_eq_true] at hx hy
  case zero.zero s₁ s₂ =>
    simp [unpackedToDyadic?, Float.Model.UnpackedFloat.mul, zero_eq_ofModel_zero hfmt,
      modelSign_xor]
  case zero.finite s₁ s₂ m₂ e₂ hm₂ =>
    simp [unpackedToDyadic?, Float.Model.UnpackedFloat.mul, zero_eq_ofModel_zero hfmt,
      modelSign_xor]
  case finite.zero s₁ m₁ e₁ hm₁ s₂ =>
    simp [unpackedToDyadic?, Float.Model.UnpackedFloat.mul, zero_eq_ofModel_zero hfmt,
      modelSign_xor]
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    simp only [unpackedToDyadic?, Float.Model.UnpackedFloat.mul, roundDyadic, hfmt, ite_true,
      ieeeRoundDyadic, modelSign_xor]
    rw [roundWithAccuracy_exact_eq_round_of_le_targetExponent _ _ _ _
      (add_le_targetExponent_totalExponent_mul _ hm₁ hm₂ (hxle hxmodel) (hyle hymodel))]
    simp [hm₁.ne', hm₂.ne']

/-- The sign bit of a quotient is the exclusive or of the operand sign bits. -/
private theorem modelSign_xor_div (s₁ s₂ : Sign) :
    modelSign (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) = s₁ / s₂ := by
  cases s₁ <;> cases s₂ <;> rfl

/-- Under a conventional IEEE descriptor, the invalid-operation result is Lean's packed NaN. -/
private theorem invalidResult_eq_ofModel_notANumber {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) : invalidResult fmt = ofModel fmt .notANumber := by
  rw [invalidResult_eq_canonicalNaN_of_isIEEE fmt hfmt]
  unfold canonicalNaN ofBits ofModel ofModelBits Float.Model.UnpackedFloat.pack packedNaN
  congr 1
  apply BitVec.toNat_inj.mp
  have hf := fmt.fracWidth_pos
  have hw : FloatFormat.bitWidth fmt = 1 + fmt.expWidth + fmt.fracWidth := rfl
  have hexp : (2 ^ fmt.expWidth - 1) * 2 ^ fmt.fracWidth < 2 ^ FloatFormat.bitWidth fmt := by
    rw [hw, pow_add, pow_add]
    have := Nat.two_pow_pos fmt.expWidth
    have : 2 ^ fmt.expWidth - 1 < 2 * 2 ^ fmt.expWidth := by omega
    nlinarith [Nat.two_pow_pos fmt.fracWidth]
  have hquiet : 2 ^ (fmt.fracWidth - 1) < 2 ^ fmt.fracWidth :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hquietw : 2 ^ (fmt.fracWidth - 1) < 2 ^ FloatFormat.bitWidth fmt :=
    hquiet.trans (Nat.pow_lt_pow_right (by decide) (by unfold FloatFormat.bitWidth; omega))
  unfold FloatFormat.expMask FloatFormat.quietBit FloatFormat.quietBitNat FloatFormat.expMaskNat
    FloatFormat.expAllOnesNat FloatFormat.ofWordNat packComponents Sign.toBitVec
    FloatFormat.toModel
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hexp,
    Nat.mod_eq_of_lt hquietw]
  change _ = ((0#1 ++ -1#fmt.expWidth) ++ (1#fmt.fracWidth <<< (fmt.fracWidth - 1))).toNat
  rw [BitVec.toNat_append, BitVec.toNat_append]
  have hone : 1 % 2 ^ fmt.expWidth = 1 :=
    Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by have := fmt.expWidth_ge_two; omega))
  have hones : (2 ^ fmt.expWidth - 1) % 2 ^ fmt.expWidth = 2 ^ fmt.expWidth - 1 :=
    Nat.mod_eq_of_lt (by have := Nat.two_pow_pos fmt.expWidth; omega)
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hquiet, hone, hones]

/-- Under a conventional IEEE descriptor, the overflow result is Lean's packed infinity. -/
private theorem nativeOverflow_eq_ofModel_infinity {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) : nativeOverflow fmt sign = ofModel fmt (.infinity (modelSign sign)) := by
  cases sign <;> simp [nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt, posInf_eq_ofModel_infinity,
    negInf_eq_ofModel_infinity]

/-- Packing a finite unpacked value keeps its sign, also when it overflows to infinity. -/
private theorem signBit_ofModel_finite (fmt : FloatFormat) (sign : Sign) (mantissa : Nat)
    (exponent : Int) (hm : 0 < mantissa) :
    signBit (ofModel fmt (.finite sign mantissa exponent hm)) = modelSignBit sign := by
  rw [← modelSignBit_ofBitVec_unpackSign]
  unfold toModelBits ofModel ofModelBits Float.Model.UnpackedFloat.pack packedInfinity
  dsimp only
  split_ifs <;> rw [unpackSign_packComponents] <;> cases sign <;> rfl

/-- Lean's rounding with accuracy keeps the requested sign through packing. -/
private theorem signBit_ofModel_roundWithAccuracy (fmt : FloatFormat) (sign : Sign)
    (mantissa : Nat) (exponent : Int) (accuracy : Accuracy) :
    signBit (ofModel fmt (Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt)
      sign mantissa exponent accuracy)) = modelSignBit sign := by
  rw [roundWithAccuracy_eq_finishRoundedMantissa]
  unfold finishRoundedMantissa
  dsimp only
  split
  · exact signBit_ofModel_zero fmt sign
  · exact signBit_ofModel_finite fmt sign _ _ _

/-- A packed rounding with accuracy that is not finite is the infinity of the requested sign. -/
private theorem ofModel_roundWithAccuracy_eq_infinity {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy)
    (h : isFinite (ofModel fmt (Float.Model.UnpackedFloat.roundWithAccuracy
      (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) = false) :
    ofModel fmt (Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt)
      sign mantissa exponent accuracy) = ofModel fmt (.infinity sign) := by
  rw [roundWithAccuracy_eq_finishRoundedMantissa] at h ⊢
  unfold finishRoundedMantissa at h ⊢
  dsimp only at h ⊢
  split at h
  · simp [isFinite_ofModel_zero fmt hfmt] at h
  · rename_i hzero
    simp only [hzero, ↓reduceDIte]
    exact ofModel_finite_eq_ofModel_infinity_of_isFinite_eq_false fmt hfmt _ _ _ _ h

/-- Nearest-even rounding of a scaled rational with a nonzero denominator has the given sign. -/
private theorem signBit_roundRatScaled {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) (num den : Nat) (exponent : Int) (hden : den ≠ 0) :
    signBit (roundRatScaled fmt sign num den exponent) = sign := by
  rw [roundRatScaled, dite_eq_left_of_eq_true (eq_true hfmt)]
  unfold ieeeRoundRatScaled
  simp only [beq_iff_eq, hden, ite_false]
  split_ifs <;> (try split) <;> simp_all

/--
Positive nearest-even rounding of a nonzero scaled rational is finite, or it is `+∞` and the
unbounded rounding of the rational is at least `2 ^ (emax + 1)`.
-/
private theorem roundRatScaled_false_isFinite_or
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (num den : Nat) (exponent : Int)
    (hnum : num ≠ 0) (hden : den ≠ 0) :
    isFinite (roundRatScaled fmt false num den exponent) = true ∨
      (roundRatScaled fmt false num den exponent = posInf fmt ∧
        bpow (fmt.maxNormalExponent + 1) ≤ roundAt fmt (scaledRatToReal num den exponent)) := by
  have hbounds := scaledRatToReal_floorLog2_bounds num den exponent hnum hden
  rw [roundRatScaled_false_eq_of_isIEEE fmt num den exponent hfmt hnum hden]
  dsimp only
  split_ifs with hover hunder hsub hzero hfull hcarry hcarryOver
  · refine Or.inr ⟨rfl, ?_⟩
    have hgeneric : roundAt fmt (bpow (fmt.maxNormalExponent + 1)) =
        bpow (fmt.maxNormalExponent + 1) := by
      apply roundAt_of_genericFormat fmt
      apply FloatLib.Floats.Formats.Flocq.generic_format_bpow
      have := minNormalExponent_le_maxNormalExponent fmt
      simp only [fexpOf, FloatLib.Floats.Formats.Flocq.fltExp]
      refine max_le (by omega) ?_
      simp only [FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast]
      omega
    have hpow : bpow (fmt.maxNormalExponent + 1) ≤
        bpow (Numerics.RationalBinary.floorLog2 num den + exponent) :=
      bpow_le_bpow_of_le (by omega)
    rw [← hgeneric]
    exact roundAt_mono fmt (hpow.trans hbounds.1)
  · exact Or.inl (isFinite_posZero fmt)
  · exact Or.inl (isFinite_posZero fmt)
  · exact Or.inl (isFinite_ofFields_ieee fmt hfmt false 1 0 (FloatFormat.one_lt_expAllOnesNat fmt))
  · exact Or.inl (isFinite_ofFields_ieee fmt hfmt false 0 _ fmt.expAllOnesNat_pos)
  · refine Or.inr ⟨rfl, le_of_eq ?_⟩
    have hmax : Numerics.RationalBinary.floorLog2 num den + exponent = fmt.maxNormalExponent := by
      omega
    have hround := roundAt_scaledRat_eq fmt false num den exponent hden
    have htarget : fexpOf fmt (Numerics.RationalBinary.floorLog2 num den + exponent + 1) =
        fmt.maxNormalExponent - Int.ofNat fmt.fracWidth := by
      rw [hmax]
      exact fexpOf_total_eq_normal fmt _ (minNormalExponent_le_maxNormalExponent fmt)
    have hscaled : Numerics.RationalBinary.scaleByPowerOfTwo num den
          (exponent - (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth)) =
        Numerics.RationalBinary.scaleByPowerOfTwo num den
          (Int.ofNat fmt.fracWidth - Numerics.RationalBinary.floorLog2 num den) := by
      congr 1
      omega
    simp only [Bool.false_eq_true, ite_false] at hround
    rw [htarget, hscaled, hcarry] at hround
    change _ = roundAt fmt (signedScaledRatToReal false num den exponent)
    rw [hround]
    change bpow (fmt.maxNormalExponent + 1) =
      (pow2 (fmt.fracWidth + 1) : Real) * bpow (fmt.maxNormalExponent - Int.ofNat fmt.fracWidth)
    rw [← bpow_ofNat (fmt.fracWidth + 1), ← bpow_add]
    congr 1
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]
    ring
  · exact Or.inl (isFinite_ofFields_ieee fmt hfmt false _ 0
      (Directed.Internal.encodedExponent_lt_expAllOnes_ieee fmt hfmt _ (by omega)))
  · exact Or.inl (isFinite_ofFields_ieee fmt hfmt false _ _
      (Directed.Internal.encodedExponent_lt_expAllOnes_ieee fmt hfmt _ (by omega)))

/-- Nearest-even rounding sends the interval `[N - 1/2, N)` to an even integer `N`. -/
private theorem nearestEven_eq_of_sub_half_le {N : ℤ} (hN : Even N) {s : ℝ}
    (hlow : (N : ℝ) - 1 / 2 ≤ s) (hhigh : s < N) : nearestEven s = N := by
  have hfloor : ⌊s⌋ = N - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hodd : ¬Even (N - 1) := by
    rw [Int.not_even_iff_odd]
    exact hN.sub_odd odd_one
  unfold nearestEven
  simp only [hfloor, hodd, ite_false]
  push_cast
  split_ifs <;> linarith

/-- At or above the overflow threshold, positive nearest-even rounding of a rational is `+∞`. -/
private theorem roundRatScaled_false_eq_posInf_of_le
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (num den : Nat) (exponent : Int)
    (hnum : num ≠ 0) (hden : den ≠ 0)
    (hbound : bpow (fmt.maxNormalExponent + 1) - bpow (fmt.maxNormalExponent - fmt.fracWidth - 1) ≤
      scaledRatToReal num den exponent) :
    roundRatScaled fmt false num den exponent = posInf fmt := by
  have hbounds := scaledRatToReal_floorLog2_bounds num den exponent hnum hden
  by_cases hover : fmt.maxNormalExponent < Numerics.RationalBinary.floorLog2 num den + exponent
  · exact roundRatScaled_false_eq_posInf_of_maxNormal_lt fmt num den exponent hfmt hnum hden hover
  have hf := fmt.fracWidth_pos
  set E := fmt.maxNormalExponent with hE
  set f := fmt.fracWidth with hfdef
  have hsmall : bpow (E - f - 1) < bpow E :=
    (FloatLib.Floats.Formats.Flocq.bpow_lt_bpow_iff Numerics.binaryRadix _ _).2 (by omega)
  have hsplit : bpow (E + 1) = 2 * bpow E := by rw [bpow_add, bpow_one]; ring
  have hk : Numerics.RationalBinary.floorLog2 num den + exponent = E := by
    have hlt : bpow E < bpow (Numerics.RationalBinary.floorLog2 num den + exponent + 1) := by
      linarith [hbounds.2]
    have := (FloatLib.Floats.Formats.Flocq.bpow_lt_bpow_iff Numerics.binaryRadix _ _).1 hlt
    omega
  apply roundRatScaled_false_eq_posInf_of_carry fmt num den exponent hfmt hnum hden (by omega) ?_
    (by omega)
  dsimp only
  set sc := Numerics.RationalBinary.scaleByPowerOfTwo num den
    (Int.ofNat f - Numerics.RationalBinary.floorLog2 num den) with hsc
  have hsnd : sc.2 ≠ 0 := Numerics.RationalBinary.scaleByPowerOfTwo_snd_ne_zero num den _ hden
  have hshift : Int.ofNat f - Numerics.RationalBinary.floorLog2 num den =
      exponent + (f - E) := by simp only [Int.ofNat_eq_natCast]; omega
  have hratio : (sc.1 : ℝ) / sc.2 = scaledRatToReal num den exponent * bpow (f - E) := by
    rw [hsc, scaleByPowerOfTwo_real, scaledRatToReal_mul_bpow, hshift]
  have hscale : bpow (E + 1) * bpow (f - E) = 2 ^ (f + 1) := by
    rw [← bpow_add, show E + 1 + (f - E) = ((f + 1 : Nat) : Int) by push_cast; ring, bpow_natCast]
  have hhalf : bpow (E - f - 1) * bpow (f - E) = 1 / 2 := by
    rw [← bpow_add, show E - f - 1 + (f - E) = -1 by ring]
    change FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix (-1) = 1 / 2
    rw [FloatLib.Floats.Formats.Flocq.bpow_binaryRadix]
    norm_num
  have hpos : 0 < bpow (f - E) := bpow_pos _
  have hlow : ((2 ^ (f + 1) : ℤ) : ℝ) - 1 / 2 ≤ (sc.1 : ℝ) / sc.2 := by
    rw [hratio]
    push_cast
    rw [← hscale, ← hhalf, ← sub_mul]
    exact mul_le_mul_of_nonneg_right hbound hpos.le
  have hhigh : (sc.1 : ℝ) / sc.2 < ((2 ^ (f + 1) : ℤ) : ℝ) := by
    rw [hratio]
    push_cast
    rw [← hscale]
    have := hbounds.2
    rw [hk] at this
    exact mul_lt_mul_of_pos_right this hpos
  have hround := nearestEven_eq_of_sub_half_le
    (by rw [Int.even_pow]; exact ⟨even_two, by omega⟩) hlow hhigh
  rw [nearestEven_div_eq_roundQuotientEven _ _ hsnd] at hround
  rw [pow2_eq_two_pow]
  have h : ((Numerics.roundQuotientEven sc.1 sc.2 : Nat) : Int) = ((2 ^ (f + 1) : Nat) : Int) := by
    simpa using hround
  exact_mod_cast h

/-- At or above the overflow threshold, nearest-even rounding of a rational is the signed infinity. -/
private theorem roundRatScaled_eq_nativeOverflow_of_le {fmt : FloatFormat}
    (hfmt : fmt.isIEEE = true) (sign : Bool) (num den : Nat) (exponent : Int) (hden : den ≠ 0)
    (hbound : bpow (fmt.maxNormalExponent + 1) - bpow (fmt.maxNormalExponent - fmt.fracWidth - 1) ≤
      |signedScaledRatToReal sign num den exponent|) :
    roundRatScaled fmt sign num den exponent = nativeOverflow fmt sign := by
  have hnum : num ≠ 0 := by
    rintro rfl
    have hsmall : bpow (fmt.maxNormalExponent - fmt.fracWidth - 1) <
        bpow (fmt.maxNormalExponent + 1) :=
      (FloatLib.Floats.Formats.Flocq.bpow_lt_bpow_iff Numerics.binaryRadix _ _).2 (by omega)
    have hzero : signedScaledRatToReal sign 0 den exponent = 0 := by
      cases sign <;> simp [signedScaledRatToReal, scaledRatToReal]
    rw [hzero, abs_zero] at hbound
    linarith
  rw [abs_signedScaledRatToReal] at hbound
  have h := roundRatScaled_false_eq_posInf_of_le fmt hfmt num den exponent hnum hden hbound
  cases sign
  · simp [h, nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]
  · simp [roundRatScaled_true_eq_neg_false fmt num den exponent hfmt hden, h,
      nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt]

/--
Nearest-even rounding of a scaled rational is finite, or it is the infinity of its sign and the
unbounded rounding of the rational has magnitude at least `2 ^ (emax + 1)`.
-/
private theorem roundRatScaled_isFinite_or {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (sign : Bool) (num den : Nat) (exponent : Int) (hden : den ≠ 0) :
    isFinite (roundRatScaled fmt sign num den exponent) = true ∨
      (roundRatScaled fmt sign num den exponent = nativeOverflow fmt sign ∧
        bpow (fmt.maxNormalExponent + 1) ≤
          |roundAt fmt (signedScaledRatToReal sign num den exponent)|) := by
  by_cases hnum : num = 0
  · subst hnum
    rw [roundRatScaled_num_zero fmt sign den exponent hden]
    exact Or.inl (isFinite_eq_true_of_isZero_eq_true _ (isZero_zero fmt sign))
  have hnonneg : 0 ≤ roundAt fmt (scaledRatToReal num den exponent) := by
    have h := roundAt_mono fmt (show (0 : ℝ) ≤ scaledRatToReal num den exponent by
      exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (bpow_nonneg _))
    rwa [roundAt_zero] at h
  rcases roundRatScaled_false_isFinite_or fmt hfmt num den exponent hnum hden with h | ⟨h, hb⟩
  · cases sign
    · exact Or.inl h
    · rw [roundRatScaled_true_eq_neg_false fmt num den exponent hfmt hden, isFinite_neg]
      exact Or.inl h
  · right
    cases sign
    · refine ⟨by simp [h, nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt], ?_⟩
      simpa [signedScaledRatToReal, abs_of_nonneg hnonneg] using hb
    · refine ⟨by simp [roundRatScaled_true_eq_neg_false fmt num den exponent hfmt hden, h,
        nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt], ?_⟩
      simpa [signedScaledRatToReal, abs_of_nonneg hnonneg] using hb

/-- Finite values with the same real value, and the same sign when it is zero, are equal. -/
private theorem eq_of_toReal_eq {fmt : FloatFormat} {x y : Model fmt} (hx : isFinite x = true)
    (hy : isFinite y = true) (hvalue : toReal x = toReal y)
    (hsign : toReal x = 0 → signBit x = signBit y) : x = y := by
  by_cases hzero : toReal x = 0
  · have hxzero := (isZero_eq_true_iff_toReal_eq_zero x hx).mpr hzero
    have hyzero := (isZero_eq_true_iff_toReal_eq_zero y hy).mpr (hvalue ▸ hzero)
    have hdecode := toDyadic?_eq_zero_of_isZero_eq_true y hyzero
    rw [← hsign hzero] at hdecode
    exact eq_of_toDyadic?_eq_some (toDyadic?_eq_zero_of_isZero_eq_true x hxzero) hdecode
  · exact eq_of_toReal_eq_of_nonzero hvalue hzero

/--
For finite nonzero operands, FloatLib's scaled-rational quotient is the word Lean's unpacked
division packs.
-/
private theorem roundRatScaled_eq_ofModel_div {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (s₁ s₂ : Sign) (m₁ m₂ : Nat) (e₁ e₂ : Int) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) :
    roundRatScaled fmt (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂ (e₁ - e₂) =
      ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
        (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)) := by
  have hden : m₂ ≠ 0 := hm₂.ne'
  have hr : signedScaledRatToReal (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂
      (e₁ - e₂) =
      unpackedToReal (.finite s₁ m₁ e₁ hm₁) / unpackedToReal (.finite s₂ m₂ e₂ hm₂) :=
    signedScaledRatToReal_eq_div_toReal ⟨modelSignBit s₁, m₁, e₁⟩ ⟨modelSignBit s₂, m₂, e₂⟩
  let target := min (e₁ - e₂) ((FloatFormat.toModel fmt).targetExponent
    (Float.Model.totalExponent m₁ e₁ - Float.Model.totalExponent m₂ e₂))
  let numerator := m₁ <<< (e₁ - e₂ - target).toNat
  have hL : ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
      (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂)) =
      ofModel fmt (Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt)
        (s₁ / s₂) (numerator / m₂) target (accuracyOfFraction (numerator % m₂) m₂)) := rfl
  have haccuracy : accuracyRepresents (numerator / m₂) (accuracyOfFraction (numerator % m₂) m₂)
      ((numerator : ℝ) / m₂) := accuracyRepresents_accuracyOfFraction numerator m₂ hden
  have hle : target ≤ (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent (numerator / m₂) target) :=
    divCore_exponent_le_targetExponent (FloatFormat.toModel fmt) e₁ e₂ hm₁ hm₂
  have hvalue : |unpackedToReal (.finite s₁ m₁ e₁ hm₁) / unpackedToReal (.finite s₂ m₂ e₂ hm₂)| =
      (numerator : ℝ) / m₂ * bpow target := by
    rw [unpackedToReal_div_eq_shifted_quotient s₁ s₂ m₁ m₂ e₁ e₂ target hm₁ hm₂
      (min_le_left _ _), abs_mul, abs_of_nonneg (mul_nonneg (div_nonneg (Nat.cast_nonneg _)
        (Nat.cast_nonneg _)) (bpow_nonneg target))]
    split <;> simp [numerator]
  have hrealL : isFinite (ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
      (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) = true →
      toReal (ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
        (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) =
        roundAt fmt (signedScaledRatToReal (Bool.xor (modelSignBit s₁) (modelSignBit s₂))
          m₁ m₂ (e₁ - e₂)) := fun h => by
    rw [hr]
    exact toReal_ofModel_div_finite_eq_roundAt fmt hfmt s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂ h
  have hrealF := toReal_roundRatScaled_eq_roundAt fmt
    (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂ (e₁ - e₂) hfmt
  have hsignF := signBit_roundRatScaled hfmt
    (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂ (e₁ - e₂) hden
  have hsignL : signBit (ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
      (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) =
      Bool.xor (modelSignBit s₁) (modelSignBit s₂) := by
    rw [hL, signBit_ofModel_roundWithAccuracy]
    cases s₁ <;> cases s₂ <;> rfl
  have hfiniteF : isFinite (ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
      (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) = true →
      isFinite (roundRatScaled fmt (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂
        (e₁ - e₂)) = true := fun hL => by
    have hbound := abs_toReal_le_posMaxFinite_of_isFinite _ hL
    rw [hrealL hL] at hbound
    rcases roundRatScaled_isFinite_or hfmt (Bool.xor (modelSignBit s₁) (modelSignBit s₂))
      m₁ m₂ (e₁ - e₂) hden with hF | ⟨-, hbig⟩
    · exact hF
    · linarith [toReal_posMaxFinite_lt_bpow fmt]
  by_cases hlt : |signedScaledRatToReal (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂
      (e₁ - e₂)| < bpow (fmt.maxNormalExponent + 1) -
        bpow (fmt.maxNormalExponent - fmt.fracWidth - 1)
  · have hLfin : isFinite (ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
        (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) = true := by
      rw [hL]
      apply isFinite_ofModel_roundWithAccuracy_of_lt_overflow fmt hfmt _ _ _ _ _ haccuracy hle
      rw [hr, hvalue, FloatFormat.maxNormalExponent_eq_ieee fmt hfmt] at hlt
      exact hlt
    have hF := hfiniteF hLfin
    exact eq_of_toReal_eq hF hLfin (by rw [hrealF hF, hrealL hLfin])
      (fun _ => by rw [hsignF, hsignL])
  · have hF := roundRatScaled_eq_nativeOverflow_of_le hfmt
      (Bool.xor (modelSignBit s₁) (modelSignBit s₂)) m₁ m₂ (e₁ - e₂) hden (le_of_not_gt hlt)
    have hLinf : isFinite (ofModel fmt (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt)
        (.finite s₁ m₁ e₁ hm₁) (.finite s₂ m₂ e₂ hm₂))) = false := by
      by_contra hfin
      rw [Bool.not_eq_false] at hfin
      have := hfiniteF hfin
      rw [hF, isFinite_nativeOverflow hfmt] at this
      exact Bool.false_ne_true this
    rw [hL] at hLinf ⊢
    rw [hF, nativeOverflow_eq_ofModel_infinity hfmt, modelSign_xor_div,
      ofModel_roundWithAccuracy_eq_infinity hfmt _ _ _ _ hLinf]

/--
For finite operands, including signed zeros, dispatched division gives the word that Lean's
unpacked model gets by dividing and packing, including `x / 0` and `0 / 0`.
-/
theorem div_eq_ofModel_div_of_isFinite {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x y : Model fmt) (hx : (toModel x).isFinite = true)
    (hy : (toModel y).isFinite = true) :
    div x y =
      ofModel fmt
        (Float.Model.UnpackedFloat.div (FloatFormat.toModel fmt) (toModel x) (toModel y)) := by
  rw [Proof.div_eq_spec, Spec.div, toDyadic?_ieee_eq_model fmt hfmt x,
    toDyadic?_ieee_eq_model fmt hfmt y]
  cases hxmodel : toModel x <;> cases hymodel : toModel y <;>
    simp only [hxmodel, hymodel, Float.Model.UnpackedFloat.isFinite,
      Bool.false_eq_true] at hx hy
  case zero.zero s₁ s₂ =>
    simp [unpackedToDyadic?, Float.Model.UnpackedFloat.div,
      invalidResult_eq_ofModel_notANumber hfmt]
  case zero.finite s₁ s₂ m₂ e₂ hm₂ =>
    simp [unpackedToDyadic?, Float.Model.UnpackedFloat.div, hm₂.ne', zero_eq_ofModel_zero hfmt,
      modelSign_xor_div]
  case finite.zero s₁ m₁ e₁ hm₁ s₂ =>
    simp [unpackedToDyadic?, Float.Model.UnpackedFloat.div, hm₁.ne',
      nativeOverflow_eq_ofModel_infinity hfmt, modelSign_xor_div]
  case finite.finite s₁ m₁ e₁ hm₁ s₂ m₂ e₂ hm₂ =>
    simp only [unpackedToDyadic?, hm₁.ne', hm₂.ne', beq_iff_eq, ite_false]
    exact roundRatScaled_eq_ofModel_div hfmt s₁ s₂ m₁ m₂ e₁ e₂ hm₁ hm₂

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange

/-- A finite native binary32 value imports to a finite unpacked model. -/
private theorem isFinite_toModel_ofFloat32Model {x : Float32} (hx : x.isFinite = true) :
    (Model.toModel (Model.ofFloat32Model x.toModel)).isFinite = true := by
  simpa only [Model.toModel_ofFloat32Model, Float32.isFinite, Float32.Model.isFinite] using hx

/-- A finite native binary64 value imports to a finite unpacked model. -/
private theorem isFinite_toModel_ofFloatModel {x : Float} (hx : x.isFinite = true) :
    (Model.toModel (Model.ofFloatModel x.toModel)).isFinite = true := by
  simpa only [Model.toModel_ofFloatModel, Float.isFinite, Float.Model.isFinite] using hx

/-- Native binary32 multiplication commutes with the import adapter on finite inputs. -/
theorem toModel_ofFloat32_mul_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat32 (x * y) : Binary32) =
      Model.mul (toModel (ofFloat32 x : Binary32)) (toModel (ofFloat32 y : Binary32)) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.mul x.toModel y.toModel) = _
  rw [Float32.Model.mul, Model.ofFloat32Model_pack]
  have h := Model.mul_eq_ofModel_mul_of_isFinite (fmt := FloatFormat.binary32)
    (by decide) (Model.ofFloat32Model x.toModel) (Model.ofFloat32Model y.toModel)
    (isFinite_toModel_ofFloat32Model hx) (isFinite_toModel_ofFloat32Model hy)
  rw [Model.toModel_ofFloat32Model, Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- Native binary32 division commutes with the import adapter on finite inputs. -/
theorem toModel_ofFloat32_div_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat32 (x / y) : Binary32) =
      Model.div (toModel (ofFloat32 x : Binary32)) (toModel (ofFloat32 y : Binary32)) := by
  rw [toModel_ofFloat32, toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.div x.toModel y.toModel) = _
  rw [Float32.Model.div, Model.ofFloat32Model_pack]
  have h := Model.div_eq_ofModel_div_of_isFinite (fmt := FloatFormat.binary32)
    (by decide) (Model.ofFloat32Model x.toModel) (Model.ofFloat32Model y.toModel)
    (isFinite_toModel_ofFloat32Model hx) (isFinite_toModel_ofFloat32Model hy)
  rw [Model.toModel_ofFloat32Model, Model.toModel_ofFloat32Model] at h
  exact h.symm

/-- Native binary64 multiplication commutes with the import adapter on finite inputs. -/
theorem toModel_ofFloat_mul_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat (x * y) : Binary64) =
      Model.mul (toModel (ofFloat x : Binary64)) (toModel (ofFloat y : Binary64)) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.mul x.toModel y.toModel) = _
  rw [Float.Model.mul, Model.ofFloatModel_pack]
  have h := Model.mul_eq_ofModel_mul_of_isFinite (fmt := FloatFormat.binary64)
    (by decide) (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (isFinite_toModel_ofFloatModel hx) (isFinite_toModel_ofFloatModel hy)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

/-- Native binary64 division commutes with the import adapter on finite inputs. -/
theorem toModel_ofFloat_div_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    toModel (ofFloat (x / y) : Binary64) =
      Model.div (toModel (ofFloat x : Binary64)) (toModel (ofFloat y : Binary64)) := by
  rw [toModel_ofFloat, toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.div x.toModel y.toModel) = _
  rw [Float.Model.div, Model.ofFloatModel_pack]
  have h := Model.div_eq_ofModel_div_of_isFinite (fmt := FloatFormat.binary64)
    (by decide) (Model.ofFloatModel x.toModel) (Model.ofFloatModel y.toModel)
    (isFinite_toModel_ofFloatModel hx) (isFinite_toModel_ofFloatModel hy)
  rw [Model.toModel_ofFloatModel, Model.toModel_ofFloatModel] at h
  exact h.symm

/-- Importing a native binary32 product equals multiplying the imports with certified software. -/
theorem ofFloat32_mul_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat32 (x * y) : Binary32) = ofFloat32 x * ofFloat32 y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat32 (x * y) : Binary32) = toModel (ofFloat32 x * ofFloat32 y : Binary32)
  rw [toModel_ofFloat32_mul_of_isFinite x y hx hy]
  simp only [toModel_hMul]

/-- Importing a native binary32 quotient equals dividing the imports with certified software. -/
theorem ofFloat32_div_of_isFinite (x y : Float32)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat32 (x / y) : Binary32) = ofFloat32 x / ofFloat32 y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat32 (x / y) : Binary32) = toModel (ofFloat32 x / ofFloat32 y : Binary32)
  rw [toModel_ofFloat32_div_of_isFinite x y hx hy]
  simp only [toModel_hDiv]

/-- Importing a native binary64 product equals multiplying the imports with certified software. -/
theorem ofFloat_mul_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat (x * y) : Binary64) = ofFloat x * ofFloat y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat (x * y) : Binary64) = toModel (ofFloat x * ofFloat y : Binary64)
  rw [toModel_ofFloat_mul_of_isFinite x y hx hy]
  simp only [toModel_hMul]

/-- Importing a native binary64 quotient equals dividing the imports with certified software. -/
theorem ofFloat_div_of_isFinite (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (ofFloat (x / y) : Binary64) = ofFloat x / ofFloat y := by
  apply Configured.Family.toModel_injective
  change toModel (ofFloat (x / y) : Binary64) = toModel (ofFloat x / ofFloat y : Binary64)
  rw [toModel_ofFloat_div_of_isFinite x y hx hy]
  simp only [toModel_hDiv]

end FloatLib.Floats.ExecFloat.Binary
