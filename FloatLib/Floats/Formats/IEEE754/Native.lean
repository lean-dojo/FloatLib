/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Type
public import FloatLib.Floats.ExecFloat.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core

/-!
# Lean native floating-point interoperability

Explicit conversions connect every configured binary format to Lean's runtime `Float32` and
`Float` types: `toFloat`, `ofFloat`, `toFloat32`, and `ofFloat32` round once in a `mode` option
when the two formats differ, and move the interchange word unchanged between `Binary64` and
`Float` and between `Binary32` and `Float32`. Lean names its IEEE binary64 runtime type `Float`,
and there is no core type named `Float64`.

At the conversion boundary:

* `ofBits32`, `toBits32`, `ofBits64`, and `toBits64` transport every interchange word unchanged
  inside FloatLib.
* The native conversions use Lean's public `Float32.ofBits`, `Float32.toBits`, `Float.ofBits`,
  and `Float.toBits` operations.
* Lean's logical model of `Float32.ofBits` and `Float.ofBits` canonicalizes NaN payloads, and so
  do the compiled runtime primitives (a compiled `(Float32.ofBits 0x7f800001).toBits` is
  `0x7fc00000`). Payload-preserving transport therefore stays in the `ofBits32`/`toBits32` and
  `ofBits64`/`toBits64` APIs.

The conversions themselves do not choose an arithmetic backend. Configured binary32 and binary64
arithmetic uses proved software kernels by default. Applications may opt into
`Configured.NativeFPU.Unchecked` for guarded host arithmetic, but those functions are outside the
proof-carrying planner and depend on the compiler and host runtime.

The companion `Native.Integer` module connects integer conversion to FloatLib's rounding
specifications. `Native.AddSub` proves agreement for finite operands, and `Native.Sqrt` covers every
input after NaN canonicalization. Import `FloatLib.Floats.Formats.IEEE754` or `FloatLib` to include
these proofs alongside the conversions.

## References

* IEEE 754-2019, Sections 3.4 and 3.6, defines binary interchange encodings.
* Lean's `Init.Data.Float.Float32` and `Init.Data.Float.Float` modules define the runtime
  types, their logical models, and the model-based conversion boundary used here.
-/

@[expose] public section

namespace FloatLib.Floats

open Formats.BinaryInterchange

namespace ExecFloat.Binary

/-! ## Exact encoded-word transport -/

/-- Construct configured IEEE binary32 from an exact 32-bit interchange word. -/
@[inline] def ofBits32 (bits : UInt32) : Binary32 :=
  FloatLib.Floats.ExecFloat.ofRaw ⟨bits, by
    exact UInt32.toNat_lt bits⟩

/-- Extract the exact 32-bit interchange word from configured IEEE binary32. -/
@[inline] def toBits32 (value : Binary32) : UInt32 :=
  value.raw.1

/-- Extracting the word just used to construct binary32 returns that word. -/
@[simp, grind =] theorem toBits32_ofBits32 (bits : UInt32) :
    toBits32 (ofBits32 bits) = bits :=
  rfl

/-- Reconstructing binary32 from its exact interchange word returns the original value. -/
@[simp, grind =] theorem ofBits32_toBits32 (value : Binary32) :
    ofBits32 (toBits32 value) = value := by
  apply FloatLib.Floats.ExecFloat.ext
  apply Subtype.ext
  rfl

/-- Construct configured IEEE binary64 from an exact 64-bit interchange word. -/
@[inline] def ofBits64 (bits : UInt64) : Binary64 :=
  FloatLib.Floats.ExecFloat.ofRaw ⟨bits, by
    exact UInt64.toNat_lt bits⟩

/-- Extract the exact 64-bit interchange word from configured IEEE binary64. -/
@[inline] def toBits64 (value : Binary64) : UInt64 :=
  value.raw.1

/-- Extracting the word just used to construct binary64 returns that word. -/
@[simp, grind =] theorem toBits64_ofBits64 (bits : UInt64) :
    toBits64 (ofBits64 bits) = bits :=
  rfl

/-- Reconstructing binary64 from its exact interchange word returns the original value. -/
@[simp, grind =] theorem ofBits64_toBits64 (value : Binary64) :
    ofBits64 (toBits64 value) = value := by
  apply FloatLib.Floats.ExecFloat.ext
  apply Subtype.ext
  rfl

/-! ## Lean runtime types -/

namespace Internal.Native

/-!
The general paths of the native conversions: a value of another format crosses through
`Model.cast` to or from the native word. They call the compiled status kernel of the cast and keep
its value, which is the value of `Model.cast` (`Model.value_cast`), so the conversions of every
format share the code of the cast library instead of inlining a copy of it.
-/

/-- The value of `Model.cast src dst value (mode := mode)`. -/
@[inline] def cast (src dst : FloatFormat) (value : Model src) (mode : Model.IEEERoundingMode) :
    Model dst :=
  (Model.Internal.Status.cast src dst value mode).value

/-- The binary64 interchange word of `value` cast to binary64 in `mode`. -/
def toWord64 {format : FloatFormat} (value : Model format) (mode : Model.IEEERoundingMode) :
    UInt64 :=
  UInt64.ofNat (cast format .binary64 value mode).toNatBits

/-- The binary32 interchange word of `value` cast to binary32 in `mode`. -/
def toWord32 {format : FloatFormat} (value : Model format) (mode : Model.IEEERoundingMode) :
    UInt32 :=
  UInt32.ofNat (cast format .binary32 value mode).toNatBits

/-- The binary64 interchange word `bits` cast to `format` in `mode`. -/
def ofWord64 (format : FloatFormat) (bits : UInt64) (mode : Model.IEEERoundingMode) :
    Model format :=
  cast .binary64 format (Model.ofNatBits bits.toNat) mode

/-- The binary32 interchange word `bits` cast to `format` in `mode`. -/
def ofWord32 (format : FloatFormat) (bits : UInt32) (mode : Model.IEEERoundingMode) :
    Model format :=
  cast .binary32 format (Model.ofNatBits bits.toNat) mode

end Internal.Native

section Native

variable {format : FloatFormat} {plan : Configured.StoragePlan format}

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan

/--
Convert a configured value to Lean's native binary64 `Float`, rounding once in `mode`
(nearest-even by default) when the format has values that binary64 cannot hold.

A binary64 value crosses as its interchange word, through Lean's public `Float.ofBits`. Every
other format is cast to binary64 by `Model.cast` first, which is exact for binary32, binary16, and
bfloat16. Both the logical model of `Float.ofBits` and its compiled primitive canonicalize a
noncanonical NaN payload, so a NaN with a payload does not round-trip through this function. Use
`toBits64` for payload-preserving serialization inside FloatLib.
-/
@[inline] def toFloat (value : Value) (mode : Model.IEEERoundingMode := .nearest) : Float :=
  match plan, value with
  | .word64 _, value =>
      if format = FloatFormat.binary64 then Float.ofBits value.raw.1
      else Float.ofBits (Internal.Native.toWord64 (toModel value) mode)
  | _, value => Float.ofBits (Internal.Native.toWord64 (toModel value) mode)

/--
Convert Lean's native binary64 `Float` to a configured value, rounding once in `mode`
(nearest-even by default) when the destination cannot hold every binary64 value. Lean calls its
64-bit IEEE runtime type `Float`.

The expected type selects the destination, as in `(ExecFloat.Binary.ofFloat 0.1 : BFloat16)`. A
binary64 destination receives the word of Lean's public `Float.toBits`, and every other
destination receives `Model.cast` of that word.
-/
@[inline] def ofFloat (value : Float) (mode : Model.IEEERoundingMode := .nearest) : Value :=
  match plan with
  | .word64 _ =>
      if h : format = FloatFormat.binary64 then
        FloatLib.Floats.ExecFloat.ofRaw ⟨value.toBits, by subst h; exact UInt64.toNat_lt _⟩
      else ofModel (Internal.Native.ofWord64 format value.toBits mode)
  | _ => ofModel (Internal.Native.ofWord64 format value.toBits mode)

/--
Convert a configured value to Lean's native `Float32`, rounding once in `mode` (nearest-even by
default) when the format has values that binary32 cannot hold.

A binary32 value crosses as its interchange word, through Lean's public `Float32.ofBits`. Every
other format is cast to binary32 by `Model.cast` first, which is exact for binary16 and bfloat16.
Both the logical model of `Float32.ofBits` and its compiled primitive canonicalize a noncanonical
NaN payload, so a NaN with a payload does not round-trip through this function. Use `toBits32`
for payload-preserving serialization inside FloatLib.
-/
@[inline] def toFloat32 (value : Value) (mode : Model.IEEERoundingMode := .nearest) : Float32 :=
  match plan, value with
  | .word32 _, value =>
      if format = FloatFormat.binary32 then Float32.ofBits value.raw.1
      else Float32.ofBits (Internal.Native.toWord32 (toModel value) mode)
  | _, value => Float32.ofBits (Internal.Native.toWord32 (toModel value) mode)

/--
Convert Lean's native binary32 `Float32` to a configured value, rounding once in `mode`
(nearest-even by default) when the destination cannot hold every binary32 value.

The expected type selects the destination. A binary32 destination receives the word of Lean's
public `Float32.toBits`, whose logical model and compiled primitive agree on every finite value
and infinity. A NaN reaches this function already canonicalized by whichever operation produced
it. Every other destination receives `Model.cast` of that word.
-/
@[inline] def ofFloat32 (value : Float32) (mode : Model.IEEERoundingMode := .nearest) : Value :=
  match plan with
  | .word32 _ =>
      if h : format = FloatFormat.binary32 then
        FloatLib.Floats.ExecFloat.ofRaw ⟨value.toBits, by subst h; exact UInt32.toNat_lt _⟩
      else ofModel (Internal.Native.ofWord32 format value.toBits mode)
  | _ => ofModel (Internal.Native.ofWord32 format value.toBits mode)

end Native

/-- Converting a native `Float32` keeps Lean's public interchange word. -/
@[simp, grind =] theorem toBits32_ofFloat32 (value : Float32) :
    toBits32 (ofFloat32 value) = value.toBits :=
  toBits32_ofBits32 value.toBits

/-- The logical model of a converted binary32 value is constructed from the same word. -/
@[simp, grind =] theorem toModel_toFloat32 (value : Binary32) :
    (toFloat32 value).toModel = Float32.Model.ofBits (toBits32 value) :=
  rfl

/--
A round trip of configured binary32 through `Float32` is the canonical-NaN normalization of the
generic Lean-model bridge.
-/
theorem ofFloat32_toFloat32 (value : Binary32) :
    (ofFloat32 (toFloat32 value) : Binary32) =
      ofBits32
        (Model.NativeBinary32.toUInt32
          (Model.canonicalizeModel
            (Model.NativeBinary32.ofUInt32 (toBits32 value)))) := by
  rfl

/-- Converting a native `Float` keeps Lean's public interchange word. -/
@[simp, grind =] theorem toBits64_ofFloat (value : Float) :
    toBits64 (ofFloat value) = value.toBits :=
  toBits64_ofBits64 value.toBits

/-- The logical model of a converted binary64 value is constructed from the same word. -/
@[simp, grind =] theorem toModel_toFloat (value : Binary64) :
    (toFloat value).toModel = Float.Model.ofBits (toBits64 value) :=
  rfl

/--
A round trip of configured binary64 through `Float` is the canonical-NaN normalization of the
generic Lean-model bridge.
-/
theorem ofFloat_toFloat (value : Binary64) :
    (ofFloat (toFloat value) : Binary64) =
      ofBits64
        (Model.NativeBinary64.toUInt64
          (Model.canonicalizeModel
            (Model.NativeBinary64.ofUInt64 (toBits64 value)))) := by
  rfl

/-! ## Exact source integration -/

/--
Lean's native binary32 participates as an exact signed-rational conversion source.

The decoder crosses the native bit boundary and then uses the configured binary32 decoder, so
`-0.0` decodes to `SignedRat.negZero`. The caller names the destination through
`ExecFloat.convert`, and native types do not join an implicit promotion lattice.
-/
instance nativeFloat32ExactDecoder :
    ExecFloat.ExactDecoder Float32 FloatLib.Numerics.SignedRat where
  decode value := ExecFloat.Binary.decode (ofFloat32 value : Binary32)

/-- Lean's native binary64 participates as an exact signed-rational conversion source. -/
instance nativeFloatExactDecoder :
    ExecFloat.ExactDecoder Float FloatLib.Numerics.SignedRat where
  decode value := ExecFloat.Binary.decode (ofFloat value : Binary64)

/-- Decoding a native `Float32` source decodes its binary32 interchange value. -/
@[simp, grind =] theorem nativeFloat32ExactDecoder_run (value : Float32) :
    ExecFloat.ExactDecoder.run value =
      ExecFloat.Binary.decode (ofFloat32 value : Binary32) :=
  rfl

/-- Decoding a native `Float` source decodes its binary64 interchange value. -/
@[simp, grind =] theorem nativeFloatExactDecoder_run (value : Float) :
    ExecFloat.ExactDecoder.run value =
      ExecFloat.Binary.decode (ofFloat value : Binary64) :=
  rfl

end ExecFloat.Binary
end FloatLib.Floats
