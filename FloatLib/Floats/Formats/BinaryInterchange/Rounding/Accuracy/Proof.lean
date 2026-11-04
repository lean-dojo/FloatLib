/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Accuracy.Model
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof

/-!
# Rounded-real meaning of Lean accuracy certificates

Lean's unpacked-float model represents a positive real by a truncated natural mantissa, an
exponent and an `Accuracy` certificate. We prove that `roundWithAccuracy` rounds that real the
same way as the independent Flocq-style `roundAt` model, whenever normalization only shifts right
and the packed output stays finite. Agreement with `roundAt` needs a conventional IEEE
descriptor. Square root and the other non-dyadic kernels go through this bridge.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open Float.Model.UnpackedFloat
open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq

section

/--
Scaling a value certified over a nonzero mantissa by `2^exponent` gives binary magnitude
`log2 mantissa + exponent + 1`.
-/
theorem magnitude_mul_bpow_of_accuracyRepresents
    {mantissa : Nat} {accuracy : Accuracy} {value : Real} (exponent : Int)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value) :
    magnitude Numerics.binaryRadix (value * bpow Numerics.binaryRadix exponent) =
      Int.ofNat mantissa.log2 + exponent + 1 := by
  rw [magnitude_mul_bpow _ _ _ (pos_of_accuracyRepresents hmantissa haccuracy).ne',
    magnitude_of_accuracyRepresents hmantissa haccuracy]
  ring

/-- The model and rounded-real semantics choose the same exponent for a valid certificate. -/
theorem cexp_accuracy_mul_bpow_eq_targetExponent
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real) (hfmt : fmt.isIEEE = true)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value) :
    cexp Numerics.binaryRadix (fexpOf fmt)
        (value * bpow Numerics.binaryRadix exponent) =
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) := by
  rw [cexp, magnitude_mul_bpow_of_accuracyRepresents exponent hmantissa haccuracy]
  simp [fexpOf, fltExp, Float.Model.Format.targetExponent,
    Float.Model.totalExponent, Float.Model.Format.mantissaBits,
    Float.Model.Format.minExponent, FloatFormat.toModel,
    FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt,
    FloatFormat.ieeeMinSubnormalExponent, FloatFormat.bias]
  congr 1 <;> omega

/-- The certificate value at the model exponent is the canonical scaled mantissa. -/
theorem scaledMantissa_accuracy_mul_bpow
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real) (hfmt : fmt.isIEEE = true)
    (hmantissa : mantissa ≠ 0)
    (haccuracy : accuracyRepresents mantissa accuracy value) :
    scaledMantissa Numerics.binaryRadix (fexpOf fmt)
        (value * bpow Numerics.binaryRadix exponent) =
      value * bpow Numerics.binaryRadix
        (exponent -
          (FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent mantissa exponent)) := by
  rw [scaledMantissa,
    cexp_accuracy_mul_bpow_eq_targetExponent fmt mantissa exponent
      accuracy value hfmt hmantissa haccuracy]
  rw [show exponent -
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent) =
    exponent + -
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) by ring]
  rw [bpow.add_exp]
  ring

/--
When no left shift is needed, the first stage of `roundWithAccuracy` shifts the extended mantissa
right to the target exponent and reports that exponent unchanged.
-/
theorem shiftToTargetExponent_eq_of_le_targetExponent
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent)) :
    Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) mantissa exponent accuracy =
      (ExtendedMantissa.ofMantissaAndAccuracy mantissa accuracy >>>
          ((FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent mantissa exponent) - exponent).toNat,
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent)) := by
  unfold Float.Model.UnpackedFloat.shiftToTargetExponent
    Float.Model.UnpackedFloat.shiftToExponent
  apply Prod.ext
  · rfl
  · dsimp only
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hle)]
    omega

/--
When no left shift is needed, the rounded mantissa produced by the first stage of
`roundWithAccuracy` is the nearest-even integer of the represented real scaled to the target
exponent.
-/
theorem roundedMantissa_shiftToTargetExponent_eq_nearestEven
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent)) :
    Int.ofNat
        (Float.Model.UnpackedFloat.shiftToTargetExponent
          (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa =
      nearestEven
        (value * bpow Numerics.binaryRadix
          (exponent -
            (FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent mantissa exponent))) := by
  rw [shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
  dsimp only [Prod.fst]
  obtain ⟨shift, hshift⟩ : ∃ shift : Nat,
      shift = ((FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent) - exponent).toNat := ⟨_, rfl⟩
  have hshiftInt :
      (shift : Int) =
        (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent) - exponent := by
    rw [hshift]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hle)
  rw [← hshift, roundedMantissa_eq_nearestEven mantissa accuracy value shift haccuracy]
  congr 1
  rw [show exponent -
      (FloatFormat.toModel fmt).targetExponent
          (Float.Model.totalExponent mantissa exponent) =
    -(shift : Int) by omega]
  simp [bpow, Numerics.binaryRadix, Numerics.Radix.toReal, div_eq_mul_inv]

/--
Lean's `roundWithAccuracy` precondition holds if and only if the exponent is at or below the
format's minimum exponent or the mantissa has at least as many bits as the precision.
-/
theorem le_targetExponent_totalExponent_iff (spec : Float.Model.Format)
    (mantissa : Nat) (exponent : Int) :
    exponent ≤ spec.targetExponent (Float.Model.totalExponent mantissa exponent) ↔
      exponent ≤ spec.minExponent ∨ 2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa := by
  have hlog : spec.mantissaBitsWithoutImplicit ≤ mantissa.log2 ↔
      2 ^ spec.mantissaBitsWithoutImplicit ≤ mantissa := by
    rcases Nat.eq_zero_or_pos mantissa with rfl | hmantissa
    · have hwidth := spec.hm
      have hpow := Nat.two_pow_pos spec.mantissaBitsWithoutImplicit
      rw [Nat.log2_zero]
      omega
    · exact Nat.le_log2 hmantissa.ne'
  rw [← hlog]
  simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
    Float.Model.Format.mantissaBits]
  omega

/--
At a zero mantissa the `roundWithAccuracy` precondition forces the least-subnormal target
exponent.
-/
theorem targetExponent_totalExponent_zero_eq_minSubnormal (fmt : FloatFormat) (exponent : Int)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent)) :
    (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent) =
      FloatFormat.ieeeMinSubnormalExponent fmt := by
  have hfloor : exponent ≤ FloatFormat.ieeeMinSubnormalExponent fmt := by
    rw [← toModel_minExponent]
    exact ((le_targetExponent_totalExponent_iff _ 0 exponent).mp hle).resolve_right
      (Nat.not_le.mpr (Nat.two_pow_pos _))
  apply targetExponent_eq_minSubnormal_of_lt_minNormal
  have hwidth := fmt.fracWidth_pos
  unfold FloatFormat.ieeeMinSubnormalExponent at hfloor
  unfold FloatFormat.ieeeMinNormalExponent
  simp only [Nat.log2_zero, Int.ofNat_eq_natCast, Nat.cast_zero] at hfloor ⊢
  omega

/--
At a zero mantissa, under the `roundWithAccuracy` precondition, Lean's rounder finishes on the
least-subnormal grid a rounded mantissa of at most one, the nearest-even rounding of the scaled
represented value.
-/
theorem roundWithAccuracy_zero_eq_finishRoundedMantissa
    (fmt : FloatFormat) (sign : Sign) (exponent : Int) (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents 0 accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent)) :
    ∃ rounded : Nat, rounded ≤ 1 ∧
      Int.ofNat rounded =
        nearestEven (value * bpow Numerics.binaryRadix
          (exponent - FloatFormat.ieeeMinSubnormalExponent fmt)) ∧
      Float.Model.UnpackedFloat.roundWithAccuracy (FloatFormat.toModel fmt) sign 0 exponent
          accuracy =
        finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, FloatFormat.ieeeMinSubnormalExponent fmt) := by
  have htarget := targetExponent_totalExponent_zero_eq_minSubnormal fmt exponent hle
  have hfloor : exponent ≤ FloatFormat.ieeeMinSubnormalExponent fmt := htarget ▸ hle
  have hbelow : value < 1 := by
    simpa using (accuracyRepresents_bounds haccuracy).2
  obtain ⟨rounded, hrounded⟩ : ∃ rounded : Nat, rounded =
      (Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) 0 exponent accuracy).1.roundedMantissa := ⟨_, rfl⟩
  have hnearest :
      Int.ofNat rounded =
        nearestEven (value * bpow Numerics.binaryRadix
          (exponent - FloatFormat.ieeeMinSubnormalExponent fmt)) := by
    rw [hrounded, ← htarget]
    exact roundedMantissa_shiftToTargetExponent_eq_nearestEven
      fmt 0 exponent accuracy value haccuracy hle
  have hunitPos :=
    bpow.pos Numerics.binaryRadix (exponent - FloatFormat.ieeeMinSubnormalExponent fmt)
  have hunit :
      bpow Numerics.binaryRadix (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤ 1 := by
    have horder := (bpow_le_bpow_iff Numerics.binaryRadix
      (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) 0).mpr (by omega)
    simpa [bpow] using horder
  have hscaled :
      value * bpow Numerics.binaryRadix
          (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤ ((1 : Nat) : Real) := by
    rw [Nat.cast_one]
    exact (mul_le_mul hbelow.le hunit hunitPos.le zero_le_one).trans_eq (one_mul 1)
  refine ⟨rounded,
    Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaled)), hnearest, ?_⟩
  rw [roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt 0 exponent accuracy hle]
  rw [shiftToTargetExponent_eq_of_le_targetExponent fmt 0 exponent accuracy hle] at hrounded
  dsimp only at hrounded ⊢
  rw [← hrounded, htarget]

/--
For a conventional IEEE descriptor and an accuracy that represents `value` at a zero mantissa,
Lean's signed `roundWithAccuracy` result has the same real value as independent nearest-even
rounding of the represented signed real. This is the zero-mantissa case of
`toReal_ofModel_roundWithAccuracy_eq_roundAt`, under the same exponent premise. The result is a
signed zero or a signed least subnormal, so no finiteness premise is needed.
-/
theorem toReal_ofModel_roundWithAccuracy_zero_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (exponent : Int) (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents 0 accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent (Float.Model.totalExponent 0 exponent)) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) sign 0 exponent accuracy)) =
      roundAt fmt
        ((if modelSignBit sign then (-1 : Real) else 1) *
          (value * FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent)) := by
  have hfloor : exponent ≤ FloatFormat.ieeeMinSubnormalExponent fmt :=
    targetExponent_totalExponent_zero_eq_minSubnormal fmt exponent hle ▸ hle
  have hnonneg : 0 ≤ value := by
    simpa using (accuracyRepresents_bounds haccuracy).1
  have hbelow : value < 1 := by
    simpa using (accuracyRepresents_bounds haccuracy).2
  obtain ⟨rounded, hone, hnearest, hround⟩ :=
    roundWithAccuracy_zero_eq_finishRoundedMantissa fmt sign exponent accuracy value haccuracy hle
  have hsmall : rounded ≤ pow2 fmt.fracWidth :=
    hone.trans (by rw [pow2_eq_two_pow]; exact Nat.one_le_two_pow)
  have hpositive :
      roundAt fmt (value * bpow Numerics.binaryRadix exponent) =
        (rounded : Real) *
          bpow Numerics.binaryRadix (FloatFormat.ieeeMinSubnormalExponent fmt) := by
    rcases hnonneg.eq_or_lt with hzero | hpos
    · subst hzero
      have hscaled :
          (0 : Real) * bpow Numerics.binaryRadix
              (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤ ((0 : Nat) : Real) := by
        simp
      have hroundedZero : rounded = 0 :=
        Nat.le_zero.mp
          (Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaled)))
      rw [zero_mul, roundAt_zero, hroundedZero, Nat.cast_zero, zero_mul]
    · have hexactPos : 0 < value * bpow Numerics.binaryRadix exponent :=
        mul_pos hpos (bpow.pos _ _)
      have hcexp :
          cexp Numerics.binaryRadix (fexpOf fmt) (value * bpow Numerics.binaryRadix exponent) =
            FloatFormat.ieeeMinSubnormalExponent fmt := by
        have hmagnitude :
            magnitude Numerics.binaryRadix (value * bpow Numerics.binaryRadix exponent) ≤
              FloatFormat.ieeeMinSubnormalExponent fmt := by
          apply magnitude_le_of_abs_lt_bpow _ _ _ hexactPos.ne'
          rw [abs_of_pos hexactPos]
          have horder := (bpow_le_bpow_iff Numerics.binaryRadix exponent
            (FloatFormat.ieeeMinSubnormalExponent fmt)).mpr hfloor
          exact (mul_lt_mul_of_pos_right hbelow (bpow.pos _ _)).trans_le
            ((one_mul _).trans_le horder)
        simp only [cexp, fexpOf, fltExp, FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]
        apply max_eq_right
        omega
      unfold roundAt FloatLib.Floats.Formats.Flocq.round FloatLib.Floats.Formats.Flocq.toReal
      rw [scaledMantissa, hcexp, mul_assoc, ← bpow.add_exp, ← sub_eq_add_neg, ← hnearest]
      norm_num
  have hroundAt :
      roundAt fmt
          ((if modelSignBit sign then (-1 : Real) else 1) *
            (value * bpow Numerics.binaryRadix exponent)) =
        (if modelSignBit sign then (-1 : Real) else 1) *
          ((rounded : Real) *
            bpow Numerics.binaryRadix (FloatFormat.ieeeMinSubnormalExponent fmt)) := by
    cases sign <;> simp [modelSignBit, hpositive, roundAt_neg]
  rw [hroundAt, hround]
  exact toReal_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt sign rounded hsmall

/--
Lean's signed `roundWithAccuracy` result has the same real value as independent nearest-even
rounding of the represented signed real. The exponent premise is the documented precondition of
`roundWithAccuracy`: normalization may discard low bits, but must not require a preliminary left
shift. The finiteness premise excludes IEEE overflow, which has no value in `Real`. A zero
mantissa, which certifies a value below one ulp, rounds to a signed zero or a signed least
subnormal (`toReal_ofModel_roundWithAccuracy_zero_eq_roundAt`).
-/
theorem toReal_ofModel_roundWithAccuracy_eq_roundAt
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (sign : Sign) (mantissa : Nat) (exponent : Int)
    (accuracy : Accuracy) (value : Real)
    (haccuracy : accuracyRepresents mantissa accuracy value)
    (hle : exponent ≤
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent mantissa exponent))
    (hfinite :
      isFinite
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) = true) :
    toReal
        (ofModel fmt
          (Float.Model.UnpackedFloat.roundWithAccuracy
            (FloatFormat.toModel fmt) sign mantissa exponent accuracy)) =
      roundAt fmt
        ((if modelSignBit sign then (-1 : Real) else 1) *
          (value * bpow Numerics.binaryRadix exponent)) := by
  by_cases hmantissa : mantissa = 0
  · subst mantissa
    exact toReal_ofModel_roundWithAccuracy_zero_eq_roundAt fmt hfmt sign exponent accuracy value
      haccuracy hle
  obtain ⟨k, hk⟩ : ∃ k : Int, k = (mantissa.log2 : Int) + exponent := ⟨_, rfl⟩
  obtain ⟨rounded, hrounded⟩ : ∃ rounded : Nat, rounded =
      (Float.Model.UnpackedFloat.shiftToTargetExponent
        (FloatFormat.toModel fmt) mantissa exponent accuracy).1.roundedMantissa := ⟨_, rfl⟩
  have hvaluePos : 0 < value := pos_of_accuracyRepresents hmantissa haccuracy
  have hexactPos : 0 < value * bpow Numerics.binaryRadix exponent :=
    mul_pos hvaluePos (bpow.pos _ _)
  have hmagnitude :
      magnitude Numerics.binaryRadix (value * bpow Numerics.binaryRadix exponent) = k + 1 := by
    rw [magnitude_mul_bpow_of_accuracyRepresents exponent hmantissa haccuracy, hk]
    rfl
  have hnearest :
      Int.ofNat rounded =
        nearestEven (value * bpow Numerics.binaryRadix
          (exponent - (FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent mantissa exponent))) := by
    rw [hrounded]
    exact roundedMantissa_shiftToTargetExponent_eq_nearestEven
      fmt mantissa exponent accuracy value haccuracy hle
  have hroundAt :
      roundAt fmt
          ((if modelSignBit sign then (-1 : Real) else 1) *
            (value * bpow Numerics.binaryRadix exponent)) =
        (if modelSignBit sign then (-1 : Real) else 1) *
          ((rounded : Real) * bpow Numerics.binaryRadix
            ((FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent mantissa exponent))) := by
    have hpositive :
        roundAt fmt (value * bpow Numerics.binaryRadix exponent) =
          (rounded : Real) * bpow Numerics.binaryRadix
            ((FloatFormat.toModel fmt).targetExponent
              (Float.Model.totalExponent mantissa exponent)) := by
      unfold roundAt FloatLib.Floats.Formats.Flocq.round FloatLib.Floats.Formats.Flocq.toReal
      rw [cexp_accuracy_mul_bpow_eq_targetExponent fmt mantissa exponent accuracy value hfmt
          hmantissa haccuracy,
        scaledMantissa_accuracy_mul_bpow fmt mantissa exponent accuracy value hfmt hmantissa
          haccuracy, ← hnearest]
      norm_num
    cases sign <;> simp [modelSignBit, hpositive, roundAt_neg]
  rw [hroundAt]
  rw [roundWithAccuracy_eq_finishRoundedMantissa,
    shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
    at hfinite ⊢
  rw [shiftToTargetExponent_eq_of_le_targetExponent fmt mantissa exponent accuracy hle]
    at hrounded
  dsimp only at hrounded hfinite ⊢
  rw [← hrounded] at hfinite ⊢
  /- Bounds on the scaled real transfer to the rounded mantissa by monotonicity of
  nearest-even rounding. -/
  have hscaledMul : ∀ target : Int,
      value * bpow Numerics.binaryRadix (exponent - target) * bpow Numerics.binaryRadix target =
        value * bpow Numerics.binaryRadix exponent := by
    intro target
    rw [mul_assoc, ← bpow.add_exp, sub_add_cancel]
  have hlowerExact : bpow Numerics.binaryRadix k ≤ value * bpow Numerics.binaryRadix exponent := by
    simpa [abs_of_pos hexactPos, hmagnitude] using
      bpow_magnitude_sub_one_le Numerics.binaryRadix _ hexactPos.ne'
  have hupperExact :
      value * bpow Numerics.binaryRadix exponent < bpow Numerics.binaryRadix (k + 1) := by
    simpa [abs_of_pos hexactPos, hmagnitude] using
      abs_lt_bpow_magnitude Numerics.binaryRadix (value * bpow Numerics.binaryRadix exponent)
  by_cases hsub : k < FloatFormat.ieeeMinNormalExponent fmt
  · rw [targetExponent_eq_minSubnormal_of_lt_minNormal fmt mantissa exponent (hk ▸ hsub)]
      at hnearest hfinite ⊢
    have hscaledLe :
        value * bpow Numerics.binaryRadix
            (exponent - FloatFormat.ieeeMinSubnormalExponent fmt) ≤
          (pow2 fmt.fracWidth : Real) := by
      refine le_of_mul_le_mul_right ?_ (bpow.pos Numerics.binaryRadix
        (FloatFormat.ieeeMinSubnormalExponent fmt))
      rw [hscaledMul, natCast_pow2_eq_bpow, ← bpow.add_exp]
      refine hupperExact.le.trans ((bpow_le_bpow_iff Numerics.binaryRadix _ _).2 ?_)
      unfold FloatFormat.ieeeMinSubnormalExponent
      unfold FloatFormat.ieeeMinNormalExponent at hsub
      simp only [Int.ofNat_eq_natCast] at hsub ⊢
      omega
    rw [toReal_ofModel_finishRoundedMantissa_minSubnormal fmt hfmt sign rounded
      (Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaledLe)))]
  · have hnormal : FloatFormat.ieeeMinNormalExponent fmt ≤ k := le_of_not_gt hsub
    rw [targetExponent_eq_normal fmt mantissa exponent (hk ▸ hnormal), ← hk]
      at hnearest hfinite ⊢
    have hdenPos : 0 < bpow Numerics.binaryRadix (k - fmt.fracWidth) := bpow.pos _ _
    have hscaledLower :
        (pow2 fmt.fracWidth : Real) ≤
          value * bpow Numerics.binaryRadix (exponent - (k - fmt.fracWidth)) := by
      refine le_of_mul_le_mul_right ?_ hdenPos
      rw [hscaledMul, natCast_pow2_eq_bpow, ← bpow.add_exp, add_sub_cancel]
      exact hlowerExact
    have hscaledUpper :
        value * bpow Numerics.binaryRadix (exponent - (k - fmt.fracWidth)) ≤
          (pow2 (fmt.fracWidth + 1) : Real) := by
      refine le_of_mul_le_mul_right ?_ hdenPos
      rw [hscaledMul, natCast_pow2_eq_bpow, ← bpow.add_exp]
      refine hupperExact.le.trans_eq (congrArg _ ?_)
      push_cast
      ring
    rw [toReal_ofModel_finishRoundedMantissa_normal fmt hfmt sign rounded k
      (Int.ofNat_le.mp ((natCast_le_nearestEven_of_le hscaledLower).trans hnearest.symm.le))
      (Int.ofNat_le.mp (hnearest.trans_le (nearestEven_le_natCast_of_le hscaledUpper)))
      hnormal hfinite]

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
