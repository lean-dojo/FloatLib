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

Explicit conversions connect `ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)` and
`ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)` to Lean's runtime `Float32` and
`Float` types. Lean names its IEEE binary64 runtime type `Float`; there is no separate core type
named `Float64`.

The conversion boundary is explicit:

* `ofBits32`, `toBits32`, `ofBits64`, and `toBits64` transport every interchange
  word exactly inside FloatLib;
* the native conversions use Lean's public `Float32.ofBits`, `Float32.toBits`,
  `Float.ofBits`, and `Float.toBits` operations;
* Lean's logical model of `Float32.ofBits` and `Float.ofBits` canonicalizes NaN payloads, and
  the compiled runtime primitives do the same (a compiled `(Float32.ofBits 0x7f800001).toBits`
  is `0x7fc00000`); exact payload-preserving transport therefore stays in the
  `ofBits32`/`toBits32` and `ofBits64`/`toBits64` APIs.

The conversions themselves do not choose an arithmetic backend. Configured binary32 and binary64
arithmetic uses proved software kernels by default. Applications may call
`Configured.NativeFPU.Unchecked` explicitly for guarded host arithmetic, but those functions are
outside the proof-carrying planner because exact packed-word equality with the software
specification has not been proved.

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
@[inline] def ofBits32 (bits : UInt32) :
    ExecFloat.Binary (exponentBits := 8) (fractionBits := 23) :=
  FloatLib.Floats.ExecFloat.ofRaw ⟨bits, by
    exact UInt32.toNat_lt bits⟩

/-- Extract the exact 32-bit interchange word from configured IEEE binary32. -/
@[inline] def toBits32
    (value : ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)) :
    UInt32 :=
  value.raw.1

/-- Extracting the word just used to construct binary32 returns that word. -/
@[simp, grind =] theorem toBits32_ofBits32 (bits : UInt32) :
    toBits32 (ofBits32 bits) = bits :=
  rfl

/-- Reconstructing binary32 from its exact interchange word returns the original value. -/
@[simp, grind =] theorem ofBits32_toBits32
    (value : ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)) :
    ofBits32 (toBits32 value) = value := by
  apply FloatLib.Floats.ExecFloat.ext
  apply Subtype.ext
  rfl

/-- Construct configured IEEE binary64 from an exact 64-bit interchange word. -/
@[inline] def ofBits64 (bits : UInt64) :
    ExecFloat.Binary (exponentBits := 11) (fractionBits := 52) :=
  FloatLib.Floats.ExecFloat.ofRaw ⟨bits, by
    exact UInt64.toNat_lt bits⟩

/-- Extract the exact 64-bit interchange word from configured IEEE binary64. -/
@[inline] def toBits64
    (value : ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)) :
    UInt64 :=
  value.raw.1

/-- Extracting the word just used to construct binary64 returns that word. -/
@[simp, grind =] theorem toBits64_ofBits64 (bits : UInt64) :
    toBits64 (ofBits64 bits) = bits :=
  rfl

/-- Reconstructing binary64 from its exact interchange word returns the original value. -/
@[simp, grind =] theorem ofBits64_toBits64
    (value : ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)) :
    ofBits64 (toBits64 value) = value := by
  apply FloatLib.Floats.ExecFloat.ext
  apply Subtype.ext
  rfl

/-! ## Lean runtime types -/

/--
Convert Lean's native binary32 value to configured `ExecFloat` binary32.

The definition uses Lean's public interchange conversion `Float32.toBits`. Its logical model and
the compiled primitive agree on every finite value and infinity; a NaN reaches this function
already canonicalized by whichever operation produced it.
-/
@[inline] def ofFloat32 (value : Float32) :
    ExecFloat.Binary (exponentBits := 8) (fractionBits := 23) :=
  ofBits32 value.toBits

/--
Convert configured `ExecFloat` binary32 to Lean's native `Float32`.

Both the logical model of `Float32.ofBits` and its compiled primitive canonicalize a
noncanonical NaN payload, so a configured NaN with a payload does not round-trip through this
function. Use `toBits32` for payload-preserving serialization inside FloatLib.
-/
@[inline] def toFloat32
    (value : ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)) :
    Float32 :=
  Float32.ofBits (toBits32 value)

/-- Native binary32 conversion exposes exactly Lean's public interchange word. -/
@[simp, grind =] theorem toBits32_ofFloat32 (value : Float32) :
    toBits32 (ofFloat32 value) = value.toBits :=
  toBits32_ofBits32 value.toBits

/-- The logical model of a converted binary32 value is constructed from the same word. -/
@[simp, grind =] theorem toModel_toFloat32
    (value : ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)) :
    (toFloat32 value).toModel = Float32.Model.ofBits (toBits32 value) :=
  rfl

/--
Converting configured binary32 through Lean's native model performs exactly the
canonical-NaN normalization already defined by the generic Lean-model bridge.
-/
theorem ofFloat32_toFloat32
    (value : ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)) :
    ofFloat32 (toFloat32 value) =
      ofBits32
        (Model.NativeBinary32.toUInt32
          (Model.canonicalizeModel
            (Model.NativeBinary32.ofUInt32 (toBits32 value)))) := by
  rfl

/--
Convert Lean's native binary64 `Float` to configured `ExecFloat` binary64.

Lean calls its 64-bit IEEE runtime type `Float`.
-/
@[inline] def ofFloat (value : Float) :
    ExecFloat.Binary (exponentBits := 11) (fractionBits := 52) :=
  ofBits64 value.toBits

/--
Convert configured `ExecFloat` binary64 to Lean's native binary64 `Float`.

Both the logical model of `Float.ofBits` and its compiled primitive canonicalize a noncanonical
NaN payload, so a configured NaN with a payload does not round-trip through this function. Use
`toBits64` for payload-preserving serialization inside FloatLib.
-/
@[inline] def toFloat
    (value : ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)) :
    Float :=
  Float.ofBits (toBits64 value)

/-- Native binary64 conversion exposes exactly Lean's public interchange word. -/
@[simp, grind =] theorem toBits64_ofFloat (value : Float) :
    toBits64 (ofFloat value) = value.toBits :=
  toBits64_ofBits64 value.toBits

/-- The logical model of a converted binary64 value is constructed from the same word. -/
@[simp, grind =] theorem toModel_toFloat
    (value : ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)) :
    (toFloat value).toModel = Float.Model.ofBits (toBits64 value) :=
  rfl

/--
Converting configured binary64 through Lean's native model performs exactly the
canonical-NaN normalization already defined by the generic Lean-model bridge.
-/
theorem ofFloat_toFloat
    (value : ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)) :
    ofFloat (toFloat value) =
      ofBits64
        (Model.NativeBinary64.toUInt64
          (Model.canonicalizeModel
            (Model.NativeBinary64.ofUInt64 (toBits64 value)))) := by
  rfl

/-! ## Exact source integration -/

/--
Lean's native binary32 participates as an exact signed-rational conversion source.

The decoder crosses the already documented native bit boundary and then uses the configured
binary32 decoder, so `-0.0` decodes to `SignedRat.negZero`. Destination selection remains explicit
through `ExecFloat.convert`; native types are not placed in an implicit promotion lattice.
-/
instance nativeFloat32ExactDecoder :
    ExecFloat.ExactDecoder Float32 FloatLib.Numerics.SignedRat where
  decode value := ExecFloat.Binary.decode (ofFloat32 value)

/-- Lean's native binary64 participates as an exact signed-rational conversion source. -/
instance nativeFloatExactDecoder :
    ExecFloat.ExactDecoder Float FloatLib.Numerics.SignedRat where
  decode value := ExecFloat.Binary.decode (ofFloat value)

/-- The native binary32 source capability uses exact interchange decoding. -/
@[simp, grind =] theorem nativeFloat32ExactDecoder_run (value : Float32) :
    ExecFloat.ExactDecoder.run value =
      ExecFloat.Binary.decode (ofFloat32 value) :=
  rfl

/-- The native binary64 source capability uses exact interchange decoding. -/
@[simp, grind =] theorem nativeFloatExactDecoder_run (value : Float) :
    ExecFloat.ExactDecoder.run value =
      ExecFloat.Binary.decode (ofFloat value) :=
  rfl

end ExecFloat.Binary
end FloatLib.Floats
