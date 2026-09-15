/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

-- architecture: allow-proof-imports
-- Constructing range-checked packed codes requires the `_lt_modulus` lemmas and kernel
-- definitions in the imported `Proof` modules.
module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Add.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Fma.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Mul.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sqrt.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sub.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Arithmetic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Product.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Quotient.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.SquareRoot.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Native.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Pair.Runtime

/-!
# Configured posit backend runtime

The posit planner selects from representation-independent exact-dyadic backends, two-limb
model-valued backends, and direct packed-storage kernels that read `UInt64` words or `UInt64`
pairs.

Packed carriers pair a code with a proof that it lies below the format modulus. Their constructors
use the arithmetic kernels' range theorems; these proof arguments are erased during compilation.
Semantic refinement of the configured entry points is proved in
`FloatLib.Floats.Formats.Posit.Configured.Backend.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Floats.ExecFloat

namespace Backend

variable {format : Format} {plan : StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-! ## Representation-independent exact-dyadic kernels -/

/--
Exact-dyadic addition backend.

Finite inputs are aligned, added, and rounded entirely as signed binary integers.
-/
@[noinline] def dyadicAdd :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.DirectDyadicArithmetic.add

/-- Exact-dyadic subtraction backend. -/
@[noinline] def dyadicSub :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.DirectDyadicArithmetic.sub

/-- Exact-dyadic multiplication backend. -/
@[noinline] def dyadicMul :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.DirectDyadicArithmetic.mul

/-- Width-generic quotient-prefix division backend. -/
@[noinline] def dyadicDiv :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.DirectDyadicArithmetic.div

/--
Rational-free square-root backend.

The kernel is `DirectDyadicSquareRoot`: one destination-width integer root prefix, with the exact
square remainder jammed into the sticky bit before the single rounding step.
-/
@[noinline] def dyadicSqrt :=
  ModelCodec.liftUnary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.DirectDyadicArithmetic.sqrt

/-- Exact-dyadic fused multiply-add backend with one final rounding step. -/
@[noinline] def dyadicFma :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan)
    Model.DirectDyadicArithmetic.fma

/-! ## Representation-independent two-limb kernels -/

/-- Two-limb-rounded addition for formats of at most 128 bits. -/
@[noinline] def nativeLimbAdd
    (heligible : Model.NativeLimb.Eligible format) :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    (Model.NativeLimbArithmetic.add heligible)

/-- Two-limb-rounded subtraction for formats of at most 128 bits. -/
@[noinline] def nativeLimbSub
    (heligible : Model.NativeLimb.Eligible format) :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    (Model.NativeLimbArithmetic.sub heligible)

/-- Two-limb-rounded multiplication for formats of at most 128 bits. -/
@[noinline] def nativeLimbMul
    (heligible : Model.NativeLimb.Eligible format) :=
  ModelCodec.liftBinary (F := Family format code plan) (Model := Model format) (plan := plan)
    (Model.NativeLimbArithmetic.mul heligible)

/-- Two-limb-rounded fused multiply-add for formats of at most 128 bits. -/
@[noinline] def nativeLimbFma
    (heligible : Model.NativeLimb.Eligible format) :=
  ModelCodec.liftTernary (F := Family format code plan) (Model := Model format) (plan := plan)
    (Model.NativeLimbArithmetic.fma heligible)

/-! ## Direct built-in packed-storage kernels

These are the native kernels: `addWordsCodeFlatValid`, `subWordsCodeFlatValid`,
`fmaWordsCodeFlatValid`, `PackedProduct.mulWordsCodeValid`, `PackedQuotient.divWordsCodeValid`,
and `PackedSquareRoot.sqrtWordCodeValid` operate on `UInt64` words and consume the eligibility
witness.
-/

/--
Native-word addition that reads built-in packed storage directly.

Unlike `dyadicAdd`, this entry point does not reconstruct `Model` operands. Its `NativeCode`
capability is available only for built-in `UInt8`/`UInt16`/`UInt32`/`UInt64` plans.
-/
@[noinline] def storedNativeWordAdd
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  let resultCode :=
    Model.NativeWordArithmetic.addWordsCodeFlatValid heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (show (NativeCode.word left.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus left.raw)
      (show (NativeCode.word right.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (NativeCode.pack (plan := plan) resultCode
      (Model.NativeWordArithmetic.addWordsCodeFlatValid_lt_modulus heligible
        (NativeCode.word left.raw) (NativeCode.word right.raw)
        (show (NativeCode.word left.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus left.raw)
        (show (NativeCode.word right.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus right.raw)))

/-- Direct built-in packed-storage subtraction. -/
@[noinline] def storedNativeWordSub
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  let resultCode :=
    Model.NativeWordArithmetic.subWordsCodeFlatValid heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (show (NativeCode.word left.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus left.raw)
      (show (NativeCode.word right.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (NativeCode.pack (plan := plan) resultCode
      (Model.NativeWordArithmetic.subWordsCodeFlatValid_lt_modulus heligible
        (NativeCode.word left.raw) (NativeCode.word right.raw)
        (show (NativeCode.word left.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus left.raw)
        (show (NativeCode.word right.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus right.raw)))

/-- Direct built-in packed-storage multiplication. -/
@[noinline] def storedNativeWordMul
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  let resultCode :=
    Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (show (NativeCode.word left.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus left.raw)
      (show (NativeCode.word right.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (NativeCode.pack (plan := plan) resultCode
      (Model.NativeWordArithmetic.PackedProduct.mulWordsCodeValid_lt_modulus heligible
        (NativeCode.word left.raw) (NativeCode.word right.raw)
        (show (NativeCode.word left.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus left.raw)
        (show (NativeCode.word right.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus right.raw)))

/-- Direct built-in packed-storage division. -/
@[noinline] def storedNativeWordDiv
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  let resultCode :=
    Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (show (NativeCode.word left.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus left.raw)
      (show (NativeCode.word right.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (NativeCode.pack (plan := plan) resultCode
      (Model.NativeWordArithmetic.PackedQuotient.divWordsCodeValid_lt_modulus heligible
        (NativeCode.word left.raw) (NativeCode.word right.raw)
        (show (NativeCode.word left.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus left.raw)
        (show (NativeCode.word right.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus right.raw)))

/-- Direct built-in packed-storage square root. -/
@[noinline] def storedNativeWordSqrt
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  let resultCode :=
    Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid heligible
      (NativeCode.word value.raw)
      (show (NativeCode.word value.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus value.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (NativeCode.pack (plan := plan) resultCode
      (Model.NativeWordArithmetic.PackedSquareRoot.sqrtWordCodeValid_lt_modulus
        heligible (NativeCode.word value.raw)
        (show (NativeCode.word value.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus value.raw)))

/-- Direct built-in packed-storage fused multiply-add. -/
@[noinline] def storedNativeWordFma
    {format : Format} {plan : StoragePlan format}
    [NativeCode format plan]
    (heligible : Model.NativeWord.Eligible format)
    (left right addend :
      FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat (Family format (Code plan) plan) :=
  let resultCode :=
    Model.NativeWordArithmetic.fmaWordsCodeFlatValid heligible
      (NativeCode.word left.raw) (NativeCode.word right.raw)
      (NativeCode.word addend.raw)
      (show (NativeCode.word left.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus left.raw)
      (show (NativeCode.word right.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus right.raw)
      (show (NativeCode.word addend.raw).toNat < format.modulus from
        NativeCode.toUInt64_lt_modulus addend.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (NativeCode.pack (plan := plan) resultCode
      (Model.NativeWordArithmetic.fmaWordsCodeFlatValid_lt_modulus heligible
        (NativeCode.word left.raw) (NativeCode.word right.raw)
        (NativeCode.word addend.raw)
        (show (NativeCode.word left.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus left.raw)
        (show (NativeCode.word right.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus right.raw)
        (show (NativeCode.word addend.raw).toNat < format.modulus from
          NativeCode.toUInt64_lt_modulus addend.raw)))

/-! ## Direct two-limb packed-storage kernels -/

/-- Two-limb addition that reads and returns `.pair` storage directly. -/
@[noinline] def storedNativeLimbAdd
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.pair width_le)) (.pair width_le)) :=
  let resultCode :=
    Model.NativeLimbPacked.addCode heligible
      (PairCode.word left.raw) (PairCode.word right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (PairCode.packWord resultCode
      (Model.NativeLimbPacked.addCode_lt_modulus heligible
        (PairCode.word left.raw) (PairCode.word right.raw)))

/-- Direct two-limb packed-storage subtraction. -/
@[noinline] def storedNativeLimbSub
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.pair width_le)) (.pair width_le)) :=
  let resultCode :=
    Model.NativeLimbPacked.subCode heligible
      (PairCode.word left.raw) (PairCode.word right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (PairCode.packWord resultCode
      (Model.NativeLimbPacked.subCode_lt_modulus heligible
        (PairCode.word left.raw) (PairCode.word right.raw)))

/-- Direct two-limb packed-storage multiplication. -/
@[noinline] def storedNativeLimbMul
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.pair width_le)) (.pair width_le)) :=
  let resultCode :=
    Model.NativeLimbPacked.mulCode heligible
      (PairCode.word left.raw) (PairCode.word right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (PairCode.packWord resultCode
      (Model.NativeLimbPacked.mulCode_lt_modulus heligible
        (PairCode.word left.raw) (PairCode.word right.raw)))

/--
Width-generic quotient-prefix division with direct `.pair` operand decoding.

This is only a storage adapter: it removes the pair-to-model round trip while retaining the same
`DirectDyadicQuotient.round` kernel used by arbitrary-width Posits.
-/
@[noinline] def storedNativeLimbDiv
    {format : Format} (width_le : format.bits ≤ 128)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.pair width_le)) (.pair width_le)) :=
  let result :=
    Model.NativeLimbArithmetic.divWords format
      (PairCode.word left.raw) (PairCode.word right.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (PairCode.pack width_le result.toNatBits
      (Model.toNatBits_lt_modulus result))

/-- Direct two-limb packed-storage square root. -/
@[noinline] def storedNativeLimbSqrt
    {format : Format} (width_le : format.bits ≤ 128)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.pair width_le)) (.pair width_le)) :=
  let resultCode :=
    Model.NativeLimbPacked.sqrtCode (format := format)
      (PairCode.word value.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (PairCode.pack width_le resultCode
      (Model.NativeLimbPacked.sqrtCode_lt_modulus (format := format)
        (PairCode.word value.raw)))

/-- Direct two-limb packed-storage fused multiply-add. -/
@[noinline] def storedNativeLimbFma
    {format : Format} (width_le : format.bits ≤ 128)
    (heligible : Model.NativeLimb.Eligible format)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.pair width_le)) (.pair width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.pair width_le)) (.pair width_le)) :=
  let resultCode :=
    Model.NativeLimbPacked.fmaCode heligible
      (PairCode.word left.raw) (PairCode.word right.raw)
      (PairCode.word addend.raw)
  FloatLib.Floats.ExecFloat.ofRaw
    (PairCode.pack width_le resultCode
      (Model.NativeLimbPacked.fmaCode_lt_modulus heligible
        (PairCode.word left.raw) (PairCode.word right.raw)
        (PairCode.word addend.raw)))

end Backend

end FloatLib.Floats.Formats.Posit.Configured
