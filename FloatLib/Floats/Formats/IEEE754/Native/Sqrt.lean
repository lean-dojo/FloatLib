/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.ExecFloat.Proof.Arithmetic

/-!
# Square-root agreement with Lean's floating-point model

These bridges compare FloatLib square root with the Lean 4.34 logical model underlying the native
floating-point types. Canonicalization forgets NaN payloads and signs while retaining all numeric
bits, including the sign of zero. The model equality does not verify the external machine
instructions used by compiled native operations.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open Float.Model (Format UnpackedFloat)
open Float.Model.UnpackedFloat

private theorem unpackExponent_eq_ones {fmt : FloatFormat} (x : Model fmt)
    (h : expField x = fmt.expAllOnesNat) :
    unpackExponent (toModelBits x) = -1#_ := by
  apply BitVec.toNat_inj.mp
  rw [unpackExponent_toNat, h, toNat_neg_one_exponentBits]

private theorem unpackMantissa_ne_zero {fmt : FloatFormat} (x : Model fmt)
    (h : fracField x ≠ 0) : unpackMantissa (toModelBits x) ≠ 0#_ := by
  intro heq
  apply h
  rw [← unpackMantissa_toNat, heq]
  rfl

private theorem toModel_of_isNaN {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) (hx : isNaN x = true) : toModel x = .notANumber := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hparts : expField x = fmt.expAllOnesNat ∧ fracField x ≠ 0 := by
    simpa [isNaN, hencoding, IEEE.isNaN] using hx
  simp [toModel, unpack, unpackExponent_eq_ones x hparts.1,
    unpackMantissa_ne_zero x hparts.2]

private theorem toModel_of_isInf {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) (hx : isInf x = true) :
    toModel x = .infinity (modelSign (signBit x)) := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hparts : expField x = fmt.expAllOnesNat ∧ fracField x = 0 := by
    simpa [isInf, hencoding, IEEE.isInf] using hx
  have hm : unpackMantissa (toModelBits x) = 0#_ := by
    apply BitVec.toNat_inj.mp
    simpa only [unpackMantissa_toNat, BitVec.toNat_ofNat, Nat.zero_mod] using hparts.2
  have hs : Sign.ofBitVec (unpackSign (toModelBits x)) = modelSign (signBit x) := by
    have h := modelSignBit_ofBitVec_unpackSign x
    cases hsign : Sign.ofBitVec (unpackSign (toModelBits x)) <;>
      cases hbit : signBit x <;> simp_all [modelSignBit, modelSign]
  simp [toModel, unpack, unpackExponent_eq_ones x hparts.1, hm, hs]

private theorem toModel_of_isZero {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) (hx : isZero x = true) :
    toModel x = .zero (modelSign (signBit x)) := by
  apply toModel_eq_zero_of_ieeeToDyadic?_eq_some x (signBit x) 0
  simpa [toDyadic?, hfmt] using toDyadic?_eq_zero_of_isZero_eq_true x hx

private theorem unpack_nan_or (spec : Format) (x y : BitVec spec.numBits)
    (hx : unpack spec x = .notANumber) : unpack spec (x ||| y) = .notANumber := by
  have he : unpackExponent x = -1#_ := by
    by_contra he
    simp only [unpack, he, ite_false] at hx
    split at hx <;> simp_all
    split at hx <;> simp_all
  have hm : unpackMantissa x ≠ 0#_ := by
    intro hm
    simp [unpack, he, hm] at hx
  have hm' : unpackMantissa (x ||| y) ≠ 0#_ := by
    simpa [unpackMantissa, BitVec.extractLsb'_or, BitVec.or_eq_zero_iff] using
      (show ¬(unpackMantissa x = 0#_ ∧ unpackMantissa y = 0#_) from fun h => hm h.1)
  have he' : unpackExponent (x ||| y) = -1#_ := by
    simp only [unpackExponent, BitVec.extractLsb'_or]
    change unpackExponent x ||| unpackExponent y = -1#_
    simp [he, BitVec.neg_one_eq_allOnes]
  simp [unpack, he', hm']

private theorem canonicalizeModel_quietNaN {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) (hx : isNaN x = true) :
    canonicalizeModel (quietNaN x) = ofModel fmt .notANumber := by
  have hencoding := ((FloatFormat.isIEEE_eq_true_iff fmt).mp hfmt).1
  have hnan : IEEE.isNaN x = true := by simpa [isNaN, hencoding] using hx
  unfold canonicalizeModel
  apply congrArg (ofModel fmt)
  simp only [quietNaN, hencoding, hnan, ite_true]
  exact unpack_nan_or (FloatFormat.toModel fmt) (toModelBits x) (FloatFormat.quietBit fmt)
    (toModel_of_isNaN hfmt x hx)

private theorem toModel_canonicalNaN (fmt : FloatFormat) :
    toModel (canonicalNaN fmt) = .notANumber := by
  have he : unpackExponent (toModelBits (posInf fmt)) = -1#_ := by
    rw [posInf_eq_ofModel_infinity]
    change unpackExponent (pack _ (.infinity .positive)) = -1#_
    simp [pack, packedInfinity]
  have hq : unpackMantissa (spec := FloatFormat.toModel fmt) (FloatFormat.quietBit fmt) ≠
      0#_ := by
    apply ne_of_apply_ne BitVec.toNat
    change ((2 ^ (fmt.fracWidth - 1) % 2 ^ fmt.bitWidth) >>> 0) %
      2 ^ fmt.fracWidth ≠ 0
    have hw : fmt.fracWidth - 1 < fmt.bitWidth := by
      unfold FloatFormat.bitWidth
      omega
    have hf : fmt.fracWidth - 1 < fmt.fracWidth := by
      have := fmt.fracWidth_pos
      omega
    rw [Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hw), Nat.shiftRight_zero,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hf)]
    exact Nat.ne_of_gt (Nat.two_pow_pos _)
  change unpack (FloatFormat.toModel fmt)
    ((posInf fmt).bits ||| FloatFormat.quietBit fmt) = .notANumber
  have hm : unpackMantissa (spec := FloatFormat.toModel fmt)
      ((posInf fmt).bits ||| FloatFormat.quietBit fmt) ≠ 0#_ := by
    change ((posInf fmt).bits ||| FloatFormat.quietBit fmt).extractLsb' 0 fmt.fracWidth ≠
      0#_
    rw [BitVec.extractLsb'_or, ne_eq, BitVec.or_eq_zero_iff]
    intro h
    exact hq h.2
  have he' : unpackExponent (spec := FloatFormat.toModel fmt)
      ((posInf fmt).bits ||| FloatFormat.quietBit fmt) = -1#_ := by
    change ((posInf fmt).bits ||| FloatFormat.quietBit fmt).extractLsb'
      fmt.fracWidth fmt.expWidth = -1#_
    rw [BitVec.extractLsb'_or]
    change (posInf fmt).bits.extractLsb' fmt.fracWidth fmt.expWidth = -1#fmt.expWidth at he
    rw [he]
    simp [BitVec.neg_one_eq_allOnes]
  simp [unpack, he', hm]

/--
Square root agrees on every conventional IEEE input after NaN canonicalization. The equality
retains signed zeros and covers negative arguments, infinities, and both kinds of NaN.
-/
theorem canonicalizeModel_sqrt_eq_model {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) :
    canonicalizeModel (sqrt x) =
      ofModel fmt (UnpackedFloat.sqrt (FloatFormat.toModel fmt) (toModel x)) := by
  rw [Proof.sqrt_eq_spec]
  cases hnan : isNaN x with
  | true =>
      simp [Spec.sqrt, chooseNaN1, hnan, canonicalizeModel_quietNaN hfmt x hnan,
        toModel_of_isNaN hfmt x hnan, UnpackedFloat.sqrt]
  | false =>
      have hcanonical :
          canonicalizeModel (invalidResult fmt) = ofModel fmt .notANumber := by
        rw [invalidResult_eq_canonicalNaN_of_isIEEE fmt hfmt]
        exact congrArg (ofModel fmt) (toModel_canonicalNaN fmt)
      cases hinf : isInf x with
      | true =>
          rw [toModel_of_isInf hfmt x hinf]
          cases hsign : signBit x <;>
            simp [Spec.sqrt, chooseNaN1, hnan, hinf, hsign, modelSign,
              UnpackedFloat.sqrt, hcanonical, nativeOverflow_eq_signedInf_of_isIEEE fmt hfmt,
              posInf_eq_ofModel_infinity]
      | false =>
          cases hzero : isZero x with
          | true =>
              have hm := toModel_of_isZero hfmt x hzero
              simp [Spec.sqrt, chooseNaN1, hnan, hinf, hzero, hm, UnpackedFloat.sqrt,
                canonicalizeModel]
          | false =>
              have hfinite := isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false
                x hnan hinf
              cases hsign : signBit x with
              | false =>
                  rw [Spec.sqrt_eq_model hfmt x hfinite hzero hsign,
                    canonicalizeModel_ofModel]
              | true =>
                  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfinite
                  have hd0 : d.significand ≠ 0 := by
                    intro heq
                    have := isZero_eq_true_of_toDyadic?_some_of_mant_eq_zero hd heq
                    simp [hzero] at this
                  have hm := toModel_eq_finite_of_ieeeToDyadic?_eq_some x
                    d.negative d.significand d.exponent hd0
                    (by simpa [toDyadic?, hfmt] using hd)
                  have hs : d.negative = true :=
                    (sign_eq_signBit_of_toDyadic?_some hd).trans hsign
                  simp [Spec.sqrt, chooseNaN1, hnan, hinf, hzero, hsign, hm, hs,
                    modelSign, UnpackedFloat.sqrt, hcanonical]

/-- Exporting a binary32 square root gives the square root of the exported Lean model. -/
theorem toFloat32Model_sqrt (x : Model FloatFormat.binary32) :
    toFloat32Model (sqrt x) = (toFloat32Model x).sqrt := by
  have h := congrArg toFloat32Model (canonicalizeModel_sqrt_eq_model (by decide) x)
  have hc : toFloat32Model (canonicalizeModel (sqrt x)) = toFloat32Model (sqrt x) :=
    congrArg Float32.Model.pack (toModel_canonicalizeModel _)
  rw [hc, toFloat32Model_ofModel] at h
  rw [show FloatFormat.binary32.toModel = Format.binary32 from rfl] at h
  simpa only [Float32.Model.sqrt, unpack_toFloat32Model] using h

/-- Exporting a binary64 square root gives the square root of the exported Lean model. -/
theorem toFloatModel_sqrt (x : Model FloatFormat.binary64) :
    toFloatModel (sqrt x) = (toFloatModel x).sqrt := by
  have h := congrArg toFloatModel (canonicalizeModel_sqrt_eq_model (by decide) x)
  have hc : toFloatModel (canonicalizeModel (sqrt x)) = toFloatModel (sqrt x) :=
    congrArg Float.Model.pack (toModel_canonicalizeModel _)
  rw [hc, toFloatModel_ofModel] at h
  rw [show FloatFormat.binary64.toModel = Format.binary64 from rfl] at h
  simpa only [Float.Model.sqrt, unpack_toFloatModel] using h

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange

/--
Lean 4.34 binary32 square root agrees with FloatLib square root through the existing native
adapter. Only NaN signs and payloads are discarded by the representation relation.
-/
theorem toModel_ofFloat32_sqrt (x : Float32) :
    toModel (ofFloat32 x.sqrt) =
      Model.canonicalizeModel (Model.sqrt (toModel (ofFloat32 x))) := by
  rw [toModel_ofFloat32, toModel_ofFloat32]
  change Model.ofFloat32Model (Float32.Model.sqrt x.toModel) = _
  rw [Float32.Model.sqrt, Model.ofFloat32Model_pack]
  have h := (Model.canonicalizeModel_sqrt_eq_model
    (fmt := FloatFormat.binary32) (by decide) (Model.ofFloat32Model x.toModel)).symm
  rw [Model.toModel_ofFloat32Model] at h
  exact h

/--
Lean 4.34 binary64 square root agrees with FloatLib square root through the existing native
adapter, including signed zeros and exceptional results.
-/
theorem toModel_ofFloat_sqrt (x : Float) :
    toModel (ofFloat x.sqrt) =
      Model.canonicalizeModel (Model.sqrt (toModel (ofFloat x))) := by
  rw [toModel_ofFloat, toModel_ofFloat]
  change Model.ofFloatModel (Float.Model.sqrt x.toModel) = _
  rw [Float.Model.sqrt, Model.ofFloatModel_pack]
  have h := (Model.canonicalizeModel_sqrt_eq_model
    (fmt := FloatFormat.binary64) (by decide) (Model.ofFloatModel x.toModel)).symm
  rw [Model.toModel_ofFloatModel] at h
  exact h

private theorem toModel_execSqrt {format : FloatFormat} {plan : Configured.StoragePlan format}
    [ExecFloat.Backend.PolicyFor (Configured.Family format (Configured.Code plan) plan)]
    (x : ExecFloat (Configured.Family format (Configured.Code plan) plan)) :
    toModel (ExecFloat.sqrt x) = Model.Spec.sqrt (toModel x) := by
  rw [ExecFloat.Proof.sqrt_eq_spec]
  change Configured.Family.toModel
    (ExecFloat.ModelCodec.liftUnary (Model.Spec.sqrt) x) = _
  simp [Configured.Family.toModel, toModel]

/--
Configured binary32 square root commutes with export to Lean's native `Float32`, for every
input word. This uses the installed certified software operation.
-/
theorem toFloat32_sqrt (x : ExecFloat.Binary 8 23) :
    toFloat32 (ExecFloat.sqrt x) = (toFloat32 x).sqrt := by
  apply (show Function.Injective Float32.toModel from
    fun ⟨a⟩ ⟨b⟩ h => congrArg Float32.ofModel h)
  change (toFloat32 (ExecFloat.sqrt x)).toModel = (toFloat32 x).toModel.sqrt
  rw [toModel_toFloat32_eq, toModel_toFloat32_eq]
  erw [toModel_execSqrt, ← Model.Proof.sqrt_eq_spec, Model.toFloat32Model_sqrt]

/--
Configured binary64 square root commutes with export to Lean's native `Float`, including
signed zeros, infinities, and NaNs under Lean's canonical representation.
-/
theorem toFloat_sqrt (x : ExecFloat.Binary 11 52) :
    toFloat (ExecFloat.sqrt x) = (toFloat x).sqrt := by
  apply (show Function.Injective Float.toModel from
    fun ⟨a⟩ ⟨b⟩ h => congrArg Float.ofModel h)
  change (toFloat (ExecFloat.sqrt x)).toModel = (toFloat x).toModel.sqrt
  rw [toModel_toFloat_eq, toModel_toFloat_eq]
  erw [toModel_execSqrt, ← Model.Proof.sqrt_eq_spec, Model.toFloatModel_sqrt]

end FloatLib.Floats.ExecFloat.Binary
