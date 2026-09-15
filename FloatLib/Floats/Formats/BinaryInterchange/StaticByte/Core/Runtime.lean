/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.TinyTable.Generic.Certified
public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Model.NumericalSystem
public import FloatLib.Numerics.Representations.StaticStorage
public import FloatLib.Numerics.Bitwise

/-!
# Static-byte runtime representation

Nominal binary formats of at most eight bits share a compact byte carrier, family interface,
model adapters, raw table execution, and exact operation specifications. The persistent code is
a `UInt8` together with an erased range proof. No `FloatFormat`, `BitVec`, or
arbitrary-precision integer is stored in a value.

Each standards package supplies a nominal type and a `Family` instance. The instance fixes the
binary-interchange proof model, proves that its codes fit in one byte, and names the monomorphic
kernels used at runtime. Table construction is isolated in `Core.Construction`; conversion and
lifting theorems are isolated in `Core.Proof`.

Nominal `Family` and `Plans.TablePlan` instances use `always_inline` so the compiler can eliminate
their closed format metadata and policy branches at a public call. The named table definitions
remain shared and lazy.

OCP, IEEE, ONNX, and custom format packages can share these carrier and refinement interfaces.
Each descriptor still determines its own exceptional-value policy.

Lean represents subtypes identically to their data carrier, so `Code F` has the runtime
representation of `UInt8`; its bound is proof-only. See Lean `Init.Prelude`,
<https://github.com/leanprover/lean4/blob/v4.34.0/src/Init/Prelude.lean#L641-L643>.

`benchmarks/scripts/checks/static-lowbit-codegen.sh` checks the intended allocation and
specialization properties.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.StaticByte

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Backend

universe u

/-- Bit-exact binary-interchange model value used to specify and prove a static byte format. -/
abbrev ModelValue (format : FloatFormat) :=
  FloatLib.Floats.Formats.BinaryInterchange.Model format

/--
Direct byte code for one at-most-eight-bit binary-interchange model.

The proof excludes patterns above the declared format width and is erased by Lean's compiler.
-/
abbrev ByteCode (format : FloatFormat) :=
  FloatLib.Numerics.StaticStorage.ByteCode (2 ^ format.bitWidth)

/-- Interpret a direct byte code in its exact-width binary proof model. -/
@[inline] def byteCodeToModel {format : FloatFormat} (code : ByteCode format) :
    ModelValue format :=
  FloatLib.Floats.Formats.BinaryInterchange.Model.ofNatBits code.1.toNat

/--
Six byte kernels and their refinement equations for one binary-interchange model.

The executable fields consume and return direct byte codes. Their equations interpret those codes
in the independent binary model and compare them with its specifications. A family may therefore
select exhaustive native-index tables, direct byte arithmetic, or a model adapter independently
for each operation without changing the universal carrier.
-/
structure Kernels (format : FloatFormat) where
  /-- Executable addition on direct byte codes. -/
  add : ByteCode format → ByteCode format → ByteCode format
  /-- Executable subtraction on direct byte codes. -/
  sub : ByteCode format → ByteCode format → ByteCode format
  /-- Executable multiplication on direct byte codes. -/
  mul : ByteCode format → ByteCode format → ByteCode format
  /-- Executable division on direct byte codes. -/
  div : ByteCode format → ByteCode format → ByteCode format
  /-- Executable square root on a direct byte code. -/
  sqrt : ByteCode format → ByteCode format
  /-- Executable fused multiply-add on direct byte codes. -/
  fma : ByteCode format → ByteCode format → ByteCode format → ByteCode format
  /-- Addition refines the independent model specification. -/
  add_eq_spec : ∀ left right,
    byteCodeToModel (add left right) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add
        (byteCodeToModel left) (byteCodeToModel right)
  /-- Subtraction refines the independent model specification. -/
  sub_eq_spec : ∀ left right,
    byteCodeToModel (sub left right) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub
        (byteCodeToModel left) (byteCodeToModel right)
  /-- Multiplication refines the independent model specification. -/
  mul_eq_spec : ∀ left right,
    byteCodeToModel (mul left right) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul
        (byteCodeToModel left) (byteCodeToModel right)
  /-- Division refines the independent model specification. -/
  div_eq_spec : ∀ left right,
    byteCodeToModel (div left right) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div
        (byteCodeToModel left) (byteCodeToModel right)
  /-- Square root refines the independent model specification. -/
  sqrt_eq_spec : ∀ value,
    byteCodeToModel (sqrt value) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt
        (byteCodeToModel value)
  /-- Fused multiply-add refines the independent model specification. -/
  fma_eq_spec : ∀ left right addend,
    byteCodeToModel (fma left right addend) =
      FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma
        (byteCodeToModel left) (byteCodeToModel right) (byteCodeToModel addend)

/--
Descriptor and certified kernels for a nominal static-byte format.

The class contains no global registry. It is resolved from the nominal format type, and concrete
packages provide monomorphic kernel fields rather than selecting a backend at runtime.
-/
class Family (F : Type u) where
  /-- Binary-interchange format used as the proof model. -/
  format : FloatFormat
  /-- Every valid code fits in one byte. -/
  width_le_eight : format.bitWidth ≤ 8
  /-- Statically selected proved kernels. -/
  kernels : Kernels format

/--
Inspection metadata for a nominal static-byte format.

This metadata is separate from `Family` so standards text never enters the runtime dictionaries
used by arithmetic.
-/
meta class FamilyInfo (F : Type u) where
  /-- Standard or specification that defines the nominal format. -/
  standard : String

/-- Direct byte carrier selected by a static-byte family. -/
abbrev Code (F : Type u) [Family F] :=
  ByteCode (Family.format (F := F))

instance familyEncodedFormat (F : Type u) [Family F] : EncodedFormat F where
  Code := Code F
  Scalar := ℝ

/-- Convert a valid byte code to the exact-width binary proof model. -/
@[inline] def codeToModel {F : Type u} [Family F] (code : Code F) :
    ModelValue (Family.format (F := F)) :=
  byteCodeToModel code

noncomputable instance (F : Type u) [Family F] : FormatSemantics F where
  denote code :=
    FloatLib.Floats.Formats.BinaryInterchange.Model.toNumericalValue
      (codeToModel code)

/-- Convert one model value to its direct valid byte code. -/
@[inline] def modelToByteCode (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8)
    (value : ModelValue format) : ByteCode format :=
  FloatLib.Numerics.StaticStorage.ByteCode.ofNat
    value.toNatBits
    (FloatLib.Floats.Formats.BinaryInterchange.Model.toNatBits_lt_two_pow value)
    (Nat.lt_two_pow_of_lt_two_pow_of_le
      (FloatLib.Floats.Formats.BinaryInterchange.Model.toNatBits_lt_two_pow value)
      width_le_eight)
/--
View an at-most-eight-bit binary-interchange model through the shared finite-encoding backend.

The encoding is a proved bijection between exact model values and their stored words. It is the
only binary-specific input required by the format-independent `TinyTable` implementation.
-/
def encoding (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8) :
    TinyTable.Encoding (ModelValue format) where
  radix := 2 ^ format.bitWidth
  radix_pos := Nat.two_pow_pos format.bitWidth
  radix_le_byte := by
    simpa only [show 256 = 2 ^ 8 by decide] using
      (Nat.pow_le_pow_right (by decide : 0 < 2) width_le_eight)
  decode code :=
    FloatLib.Floats.Formats.BinaryInterchange.Model.ofNatBits code.val
  encode value :=
    ⟨value.toNatBits,
      FloatLib.Floats.Formats.BinaryInterchange.Model.toNatBits_lt_two_pow value⟩
  decode_encode value :=
    FloatLib.Floats.Formats.BinaryInterchange.Model.ofNatBits_toNatBits value
  encode_decode code := by
    apply Fin.ext
    exact
      FloatLib.Floats.Formats.BinaryInterchange.Model.toNatBits_ofNatBits_of_lt
        code.val code.isLt

/-- Execute a shared certified binary table on the static-byte carrier. -/
@[always_inline, inline] def runBinary
    {format : FloatFormat} {spec : ModelValue format → ModelValue format → ModelValue format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedBinary (encoding format width_le_eight) spec)
    (left right : ByteCode format) : ByteCode format :=
  kernel.run left right

/-- Execute a shared certified unary table on the static-byte carrier. -/
@[always_inline, inline] def runUnary
    {format : FloatFormat} {spec : ModelValue format → ModelValue format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedUnary (encoding format width_le_eight) spec)
    (value : ByteCode format) : ByteCode format :=
  kernel.run value

/-- Execute a shared certified ternary table on the static-byte carrier. -/
@[always_inline, inline] def runTernary
    {format : FloatFormat}
    {spec : ModelValue format → ModelValue format → ModelValue format → ModelValue format}
    (width_le_eight : format.bitWidth ≤ 8)
    (kernel : TinyTable.CertifiedTernary (encoding format width_le_eight) spec)
    (left right addend : ByteCode format) : ByteCode format :=
  kernel.run left right addend

/-- Adapt a model-level ternary operation to the direct byte carrier. -/
@[inline] def modelTernary (format : FloatFormat) (width_le_eight : format.bitWidth ≤ 8)
    (op : ModelValue format → ModelValue format → ModelValue format → ModelValue format)
    (left right addend : ByteCode format) : ByteCode format :=
  modelToByteCode format width_le_eight <|
    op (byteCodeToModel left) (byteCodeToModel right) (byteCodeToModel addend)
/-- Convert one family model value to its direct valid byte code. -/
@[inline] def modelToCode {F : Type u} [Family F]
    (value : ModelValue (Family.format (F := F))) : Code F :=
  modelToByteCode (Family.format (F := F)) (Family.width_le_eight (F := F)) value

/-- Interpret a universal static-byte value in the binary proof model. -/
@[inline] def toModel {F : Type u} [Family F] (value : FloatLib.Floats.ExecFloat F) :
    ModelValue (Family.format (F := F)) :=
  codeToModel value.raw

/-- Repack a binary proof-model value into the direct static-byte carrier. -/
@[inline] def ofModel {F : Type u} [Family F]
    (value : ModelValue (Family.format (F := F))) :
    FloatLib.Floats.ExecFloat F :=
  FloatLib.Floats.ExecFloat.ofRaw (modelToCode value)

/-- Construct a static-byte value from a natural bit pattern, reduced to the format width. -/
@[inline] def ofNatBits (F : Type u) [Family F] (bits : Nat) :
    FloatLib.Floats.ExecFloat F :=
  ofModel <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.ofNatBits
      (fmt := Family.format (F := F)) bits

/-- Read the direct byte stored by a static-byte value. -/
@[inline] def toUInt8 {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) : UInt8 :=
  value.raw.1

/-- Read the canonical natural-number bit pattern. -/
@[inline] def toNatBits {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) : Nat :=
  value.raw.1.toNat

namespace Spec

/-- Static-byte addition specification lifted from the binary proof model. -/
def add {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ofModel (F := F) <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add
      (toModel (F := F) left) (toModel (F := F) right)

/-- Static-byte subtraction specification lifted from the binary proof model. -/
def sub {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ofModel (F := F) <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sub
      (toModel (F := F) left) (toModel (F := F) right)

/-- Static-byte multiplication specification lifted from the binary proof model. -/
def mul {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ofModel (F := F) <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.mul
      (toModel (F := F) left) (toModel (F := F) right)

/-- Static-byte division specification lifted from the binary proof model. -/
def div {F : Type u} [Family F]
    (left right : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ofModel (F := F) <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.div
      (toModel (F := F) left) (toModel (F := F) right)

/-- Static-byte square-root specification lifted from the binary proof model. -/
def sqrt {F : Type u} [Family F]
    (value : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ofModel (F := F) <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.sqrt
      (toModel (F := F) value)

/-- Static-byte fused multiply-add specification lifted from the binary proof model. -/
def fma {F : Type u} [Family F]
    (left right addend : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  ofModel (F := F) <|
    FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.fma
      (toModel (F := F) left) (toModel (F := F) right) (toModel (F := F) addend)

end Spec

end FloatLib.Floats.Formats.BinaryInterchange.StaticByte
