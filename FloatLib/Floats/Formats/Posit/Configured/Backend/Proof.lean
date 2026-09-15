/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Arithmetic.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Core
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Native.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Pair.Proof

/-!
# Correctness of configured posit backends

Every configured backend is proved equal to the independent exact operation in
`Configured.Spec`. The proofs cover the representation-independent exact-dyadic and two-limb
kernels as well as the direct packed-storage entry points.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Floats.ExecFloat

namespace Backend

variable {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-! ## Representation-independent backends -/

/-- Exact-dyadic addition refines configured posit addition. -/
theorem dyadicAdd_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    dyadicAdd left right = Spec.add left right := by
  unfold dyadicAdd Spec.add
  exact ModelCodec.liftBinary_congr
    Model.DirectDyadicArithmetic.add_eq_spec left right

/-- Exact-dyadic subtraction refines configured posit subtraction. -/
theorem dyadicSub_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    dyadicSub left right = Spec.sub left right := by
  unfold dyadicSub Spec.sub
  exact ModelCodec.liftBinary_congr
    Model.DirectDyadicArithmetic.sub_eq_spec left right

/-- Exact-dyadic multiplication refines configured posit multiplication. -/
theorem dyadicMul_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    dyadicMul left right = Spec.mul left right := by
  unfold dyadicMul Spec.mul
  exact ModelCodec.liftBinary_congr
    Model.DirectDyadicArithmetic.mul_eq_spec left right

/-- Rational-free dyadic division refines configured posit division. -/
theorem dyadicDiv_eq_spec
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    dyadicDiv left right = Spec.div left right := by
  unfold dyadicDiv Spec.div
  exact ModelCodec.liftBinary_congr
    Model.DirectDyadicArithmetic.div_eq_spec left right

/-- Rational-free dyadic square root refines configured posit square root. -/
theorem dyadicSqrt_eq_spec
    (value : FloatLib.Floats.ExecFloat (Family format code plan)) :
    dyadicSqrt value = Spec.sqrt value := by
  unfold dyadicSqrt Spec.sqrt
  exact ModelCodec.liftUnary_congr
    Model.DirectDyadicArithmetic.sqrt_eq_spec value

/-- Exact-dyadic fused multiply-add refines configured posit FMA. -/
theorem dyadicFma_eq_spec
    (left right addend : FloatLib.Floats.ExecFloat (Family format code plan)) :
    dyadicFma left right addend = Spec.fma left right addend := by
  unfold dyadicFma Spec.fma
  exact ModelCodec.liftTernary_congr
    Model.DirectDyadicArithmetic.fma_eq_spec left right addend

/-- Two-limb-rounded addition refines configured posit addition. -/
theorem nativeLimbAdd_eq_spec
    (heligible : Model.NativeLimb.Eligible format)
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    nativeLimbAdd heligible left right = Spec.add left right := by
  unfold nativeLimbAdd Spec.add
  exact ModelCodec.liftBinary_congr
    (Model.NativeLimbArithmetic.add_eq_spec heligible) left right

/-- Two-limb-rounded subtraction refines configured posit subtraction. -/
theorem nativeLimbSub_eq_spec
    (heligible : Model.NativeLimb.Eligible format)
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    nativeLimbSub heligible left right = Spec.sub left right := by
  unfold nativeLimbSub Spec.sub
  exact ModelCodec.liftBinary_congr
    (Model.NativeLimbArithmetic.sub_eq_spec heligible) left right

/-- Two-limb-rounded multiplication refines configured posit multiplication. -/
theorem nativeLimbMul_eq_spec
    (heligible : Model.NativeLimb.Eligible format)
    (left right : FloatLib.Floats.ExecFloat (Family format code plan)) :
    nativeLimbMul heligible left right = Spec.mul left right := by
  unfold nativeLimbMul Spec.mul
  exact ModelCodec.liftBinary_congr
    (Model.NativeLimbArithmetic.mul_eq_spec heligible) left right

/-- Two-limb-rounded fused multiply-add refines configured posit FMA. -/
theorem nativeLimbFma_eq_spec
    (heligible : Model.NativeLimb.Eligible format)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format code plan)) :
    nativeLimbFma heligible left right addend =
      Spec.fma left right addend := by
  unfold nativeLimbFma Spec.fma
  exact ModelCodec.liftTernary_congr
    (Model.NativeLimbArithmetic.fma_eq_spec heligible) left right addend

/-! ## Direct native-word storage -/

/-- Direct packed-storage addition refines configured posit addition. -/
theorem storedNativeWordAdd_eq_spec
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    storedNativeWordAdd heligible left right = Spec.add left right := by
  apply ModelCodec.decode_injective
    (F := Family format (Code plan) plan)
    (Model := Model format) (plan := plan)
  unfold storedNativeWordAdd Spec.add
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    NativeCode.toModel_pack, ModelCodec.decode_liftBinary]
  rw [Model.NativeWordArithmetic.addWordsCodeFlatValid_eq,
    Model.NativeWordArithmetic.addWordsCodeFlat_eq]
  rw [Model.NativeWordArithmetic.ofNatBits_addWordsCode]
  rw [Model.NativeWordArithmetic.addWords_eq_add heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (NativeCode.toUInt64_lt_modulus left.raw)
      (NativeCode.toUInt64_lt_modulus right.raw)]
  unfold NativeCode.word
  rw [Family.decode_eq_codeToModel left,
    Family.decode_eq_codeToModel right]
  rw [
    ← NativeCode.toModel_eq_ofUInt64 left.raw,
    ← NativeCode.toModel_eq_ofUInt64 right.raw,
    Model.DirectDyadicArithmetic.add_eq_spec]

/-- Direct packed-storage subtraction refines configured posit subtraction. -/
theorem storedNativeWordSub_eq_spec
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    storedNativeWordSub heligible left right = Spec.sub left right := by
  apply ModelCodec.decode_injective
    (F := Family format (Code plan) plan)
    (Model := Model format) (plan := plan)
  unfold storedNativeWordSub Spec.sub
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    NativeCode.toModel_pack, ModelCodec.decode_liftBinary]
  rw [Model.NativeWordArithmetic.subWordsCodeFlatValid_eq,
    Model.NativeWordArithmetic.subWordsCodeFlat_eq]
  rw [Model.NativeWordArithmetic.ofNatBits_subWordsCode]
  rw [Model.NativeWordArithmetic.subWords_eq_sub heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (NativeCode.toUInt64_lt_modulus left.raw)
      (NativeCode.toUInt64_lt_modulus right.raw)]
  unfold NativeCode.word
  rw [Family.decode_eq_codeToModel left,
    Family.decode_eq_codeToModel right]
  rw [
    ← NativeCode.toModel_eq_ofUInt64 left.raw,
    ← NativeCode.toModel_eq_ofUInt64 right.raw,
    Model.DirectDyadicArithmetic.sub_eq_spec]

/-- Direct packed-storage multiplication refines configured posit multiplication. -/
theorem storedNativeWordMul_eq_spec
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    storedNativeWordMul heligible left right = Spec.mul left right := by
  apply ModelCodec.decode_injective
    (F := Family format (Code plan) plan)
    (Model := Model format) (plan := plan)
  unfold storedNativeWordMul Spec.mul
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    NativeCode.toModel_pack, ModelCodec.decode_liftBinary]
  rw [Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid_eq,
    Model.NativeWordArithmetic.mulWordsCodeFlatValid_eq,
    Model.NativeWordArithmetic.mulWordsCodeFlat_eq]
  rw [Model.NativeWordArithmetic.ofNatBits_mulWordsCode]
  rw [Model.NativeWordArithmetic.mulWords_eq_mul heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (NativeCode.toUInt64_lt_modulus left.raw)
      (NativeCode.toUInt64_lt_modulus right.raw)]
  unfold NativeCode.word
  rw [Family.decode_eq_codeToModel left,
    Family.decode_eq_codeToModel right]
  rw [
    ← NativeCode.toModel_eq_ofUInt64 left.raw,
    ← NativeCode.toModel_eq_ofUInt64 right.raw,
    Model.DirectDyadicArithmetic.mul_eq_spec]

/-- Direct packed-storage division refines configured posit division. -/
theorem storedNativeWordDiv_eq_spec
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    storedNativeWordDiv heligible left right = Spec.div left right := by
  apply ModelCodec.decode_injective
    (F := Family format (Code plan) plan)
    (Model := Model format) (plan := plan)
  unfold storedNativeWordDiv Spec.div
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    NativeCode.toModel_pack, ModelCodec.decode_liftBinary]
  rw [Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid_eq]
  change
    Model.ofNatBits
        (Model.NativeWordArithmetic.divWordsCode heligible
          (NativeCode.word left.raw) (NativeCode.word right.raw)) =
      Model.Spec.div
        (ModelCodec.decode
          (F := Family format (Code plan) plan)
          (Model := Model format) (plan := plan) left)
        (ModelCodec.decode
          (F := Family format (Code plan) plan)
          (Model := Model format) (plan := plan) right)
  rw [Model.NativeWordArithmetic.ofNatBits_divWordsCode]
  rw [Model.NativeWordArithmetic.divWords_eq_div heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (NativeCode.toUInt64_lt_modulus left.raw)
      (NativeCode.toUInt64_lt_modulus right.raw)]
  unfold NativeCode.word
  rw [Family.decode_eq_codeToModel left,
    Family.decode_eq_codeToModel right]
  rw [
    ← NativeCode.toModel_eq_ofUInt64 left.raw,
    ← NativeCode.toModel_eq_ofUInt64 right.raw,
    Model.DirectDyadicArithmetic.div_eq_spec]

/-- Direct packed-storage square root refines configured posit square root. -/
theorem storedNativeWordSqrt_eq_spec
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    storedNativeWordSqrt heligible value = Spec.sqrt value := by
  apply ModelCodec.decode_injective
    (F := Family format (Code plan) plan)
    (Model := Model format) (plan := plan)
  unfold storedNativeWordSqrt Spec.sqrt
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    NativeCode.toModel_pack, ModelCodec.decode_liftUnary]
  rw [Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid_eq]
  rw [Model.NativeWordArithmetic.ofNatBits_sqrtWordCode]
  rw [Model.NativeWordArithmetic.sqrtWord_eq_sqrt heligible
      (NativeCode.word value.raw)
      (NativeCode.toUInt64_lt_modulus value.raw)]
  unfold NativeCode.word
  rw [Family.decode_eq_codeToModel value]
  rw [
    ← NativeCode.toModel_eq_ofUInt64 value.raw,
    Model.DirectDyadicArithmetic.sqrt_eq_spec]

/-- Direct packed-storage FMA refines configured posit FMA. -/
theorem storedNativeWordFma_eq_spec
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    storedNativeWordFma heligible left right addend =
      Spec.fma left right addend := by
  apply ModelCodec.decode_injective
    (F := Family format (Code plan) plan)
    (Model := Model format) (plan := plan)
  unfold storedNativeWordFma Spec.fma
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    NativeCode.toModel_pack, ModelCodec.decode_liftTernary]
  rw [Model.NativeWordArithmetic.fmaWordsCodeFlatValid_eq,
    Model.NativeWordArithmetic.fmaWordsCodeFlat_eq]
  rw [Model.NativeWordArithmetic.ofNatBits_fmaWordsCode]
  rw [Model.NativeWordArithmetic.fmaWords_eq_fma heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (NativeCode.word addend.raw)
      (NativeCode.toUInt64_lt_modulus left.raw)
      (NativeCode.toUInt64_lt_modulus right.raw)
      (NativeCode.toUInt64_lt_modulus addend.raw)]
  unfold NativeCode.word
  rw [Family.decode_eq_codeToModel left,
    Family.decode_eq_codeToModel right,
    Family.decode_eq_codeToModel addend]
  rw [
    ← NativeCode.toModel_eq_ofUInt64 left.raw,
    ← NativeCode.toModel_eq_ofUInt64 right.raw,
    ← NativeCode.toModel_eq_ofUInt64 addend.raw,
    Model.DirectDyadicArithmetic.fma_eq_spec]

/-! ## Direct two-limb storage -/

/-- Direct two-limb packed addition refines configured posit addition. -/
theorem storedNativeLimbAdd_eq_spec
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    storedNativeLimbAdd width_le heligible left right =
      Spec.add left right := by
  apply ModelCodec.decode_injective
    (F := Family format
      (Code (StoragePlan.pair width_le))
      (StoragePlan.pair width_le))
    (Model := Model format) (plan := StoragePlan.pair width_le)
  unfold storedNativeLimbAdd Spec.add
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    PairCode.toModel_packWord, ModelCodec.decode_liftBinary]
  rw [Model.NativeLimbPacked.ofNatBits_addCode_eq_add heligible
    (PairCode.word left.raw) (PairCode.word right.raw)
    left.raw.2 right.raw.2]
  rw [Model.NativeLimbArithmetic.add_eq_spec]
  rfl

/-- Direct two-limb packed subtraction refines configured posit subtraction. -/
theorem storedNativeLimbSub_eq_spec
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    storedNativeLimbSub width_le heligible left right =
      Spec.sub left right := by
  apply ModelCodec.decode_injective
    (F := Family format
      (Code (StoragePlan.pair width_le))
      (StoragePlan.pair width_le))
    (Model := Model format) (plan := StoragePlan.pair width_le)
  unfold storedNativeLimbSub Spec.sub
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    PairCode.toModel_packWord, ModelCodec.decode_liftBinary]
  rw [Model.NativeLimbPacked.ofNatBits_subCode_eq_sub heligible
    (PairCode.word left.raw) (PairCode.word right.raw)
    left.raw.2 right.raw.2]
  rw [Model.NativeLimbArithmetic.sub_eq_spec]
  rfl

/-- Direct two-limb packed multiplication refines configured posit multiplication. -/
theorem storedNativeLimbMul_eq_spec
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    storedNativeLimbMul width_le heligible left right =
      Spec.mul left right := by
  apply ModelCodec.decode_injective
    (F := Family format
      (Code (StoragePlan.pair width_le))
      (StoragePlan.pair width_le))
    (Model := Model format) (plan := StoragePlan.pair width_le)
  unfold storedNativeLimbMul Spec.mul
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    PairCode.toModel_packWord, ModelCodec.decode_liftBinary]
  rw [Model.NativeLimbPacked.ofNatBits_mulCode_eq_mul heligible
    (PairCode.word left.raw) (PairCode.word right.raw)
    left.raw.2 right.raw.2]
  rw [Model.NativeLimbArithmetic.mul_eq_spec]
  rfl

/--
Direct pair decoding followed by the shared quotient-prefix kernel refines configured division.
-/
theorem storedNativeLimbDiv_eq_spec
    {format : Format} (width_le : format.bits ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    storedNativeLimbDiv width_le left right =
      Spec.div left right := by
  apply ModelCodec.decode_injective
    (F := Family format
      (Code (StoragePlan.pair width_le))
      (StoragePlan.pair width_le))
    (Model := Model format) (plan := StoragePlan.pair width_le)
  unfold storedNativeLimbDiv Spec.div
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    PairCode.toModel_pack, Model.ofNatBits_toNatBits,
    ModelCodec.decode_liftBinary]
  rw [Model.NativeLimbArithmetic.divWords_eq_div format
    (PairCode.word left.raw) (PairCode.word right.raw)
    width_le left.raw.2 right.raw.2]
  rw [Family.decode_eq_codeToModel left,
    Family.decode_eq_codeToModel right]
  exact Model.DirectDyadicArithmetic.div_eq_spec _ _

/-- Direct two-limb packed square root refines configured posit square root. -/
theorem storedNativeLimbSqrt_eq_spec
    {format : Format} (width_le : format.bits ≤ 128)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    storedNativeLimbSqrt width_le value =
      Spec.sqrt value := by
  let heligible : Model.NativeLimb.Eligible format := width_le
  apply ModelCodec.decode_injective
    (F := Family format
      (Code (StoragePlan.pair width_le))
      (StoragePlan.pair width_le))
    (Model := Model format) (plan := StoragePlan.pair width_le)
  unfold storedNativeLimbSqrt Spec.sqrt
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    PairCode.toModel_pack, ModelCodec.decode_liftUnary]
  rw [Model.NativeLimbPacked.ofNatBits_sqrtCode_eq_sqrt heligible
    (PairCode.word value.raw) value.raw.2]
  rw [Model.DirectDyadicArithmetic.sqrt_eq_spec]
  rfl

/-- Direct two-limb packed FMA refines configured posit FMA. -/
theorem storedNativeLimbFma_eq_spec
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    storedNativeLimbFma width_le heligible left right addend =
      Spec.fma left right addend := by
  apply ModelCodec.decode_injective
    (F := Family format
      (Code (StoragePlan.pair width_le))
      (StoragePlan.pair width_le))
    (Model := Model format) (plan := StoragePlan.pair width_le)
  unfold storedNativeLimbFma Spec.fma
  rw [Family.decode_eq_codeToModel]
  simp only [FloatLib.Floats.ExecFloat.raw_ofRaw,
    PairCode.toModel_pack, ModelCodec.decode_liftTernary]
  rw [Model.NativeLimbPacked.ofNatBits_fmaCode_eq_fma heligible
    (PairCode.word left.raw) (PairCode.word right.raw)
    (PairCode.word addend.raw)
    left.raw.2 right.raw.2 addend.raw.2]
  rw [Model.NativeLimbArithmetic.fma_eq_spec]
  rfl

end Backend

end FloatLib.Floats.Formats.Posit.Configured
