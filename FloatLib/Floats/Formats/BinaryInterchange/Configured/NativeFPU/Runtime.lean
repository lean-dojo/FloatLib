/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Core.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Codecs

/-!
# Direct-carrier software FMA for binary32 and binary64

These binary32 and binary64 FMA entry points execute the proved fixed-word kernel in both Lean's
logic and compiled code, with carrier conversion fixed statically. Addition, subtraction,
multiplication, division, and square root use the generic configured `Backend.word*` entry points.

Guarded `Float32` and `Float` experiments live in the separate
`Configured.NativeFPU.Unchecked` module. Importing this runtime does not expose them or pull native
floating-point primitives into certified clients.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU

open FloatLib.Floats

/-! ## Binary32 -/

/-- Configured IEEE binary32 value stored in a direct `UInt32` carrier. -/
abbrev Binary32Value
    (width_le : FloatFormat.binary32.bitWidth ≤ 32) :=
  ExecFloat
    (Family FloatFormat.binary32
      (Code (.word32 width_le)) (.word32 width_le))

/-- Every `UInt32` bit pattern fits the complete binary32 interchange width. -/
theorem binary32Bits_lt (bits : UInt32) :
    bits.toNat < 2 ^ FloatFormat.binary32.bitWidth := by
  simpa [FloatFormat.binary32, FloatFormat.bitWidth] using UInt32.toNat_lt bits

/-- Rewrap one complete binary32 interchange word in its configured carrier. -/
@[always_inline, inline] def ofBinary32Bits
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (bits : UInt32) : Binary32Value width_le :=
  ExecFloat.ofRaw ⟨bits, binary32Bits_lt bits⟩

/-! ### Direct-carrier fused multiply-add -/

/--
Proved software binary32 FMA with the `UInt32` carrier adapter fixed statically.

This uses the proved fixed-word FMA kernel. Spelling the carrier conversion directly avoids
retaining a `ModelCodec` structure and four indirect closure applications in compiled
monomorphic code.
-/
@[always_inline, inline] def softwareFma32
    {width_le : FloatFormat.binary32.bitWidth ≤ 32}
    (left right addend : Binary32Value width_le) : Binary32Value width_le :=
  ExecFloat.ofRaw <|
    Code.ofModel (plan := .word32 width_le) <|
      Model.FmaBackend.word
        (Code.toModel (plan := .word32 width_le) left.raw)
        (Code.toModel (plan := .word32 width_le) right.raw)
        (Code.toModel (plan := .word32 width_le) addend.raw)

/-! ## Binary64 -/

/-- Configured IEEE binary64 value stored in a direct `UInt64` carrier. -/
abbrev Binary64Value
    (width_le : FloatFormat.binary64.bitWidth ≤ 64) :=
  ExecFloat
    (Family FloatFormat.binary64
      (Code (.word64 width_le)) (.word64 width_le))

/-- Every `UInt64` bit pattern fits the complete binary64 interchange width. -/
theorem binary64Bits_lt (bits : UInt64) :
    bits.toNat < 2 ^ FloatFormat.binary64.bitWidth := by
  simpa [FloatFormat.binary64, FloatFormat.bitWidth] using UInt64.toNat_lt bits

/-- Rewrap one complete binary64 interchange word in its configured carrier. -/
@[always_inline, inline] def ofBinary64Bits
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (bits : UInt64) : Binary64Value width_le :=
  ExecFloat.ofRaw ⟨bits, binary64Bits_lt bits⟩

/-! ### Direct-carrier fused multiply-add -/

/--
Proved software binary64 FMA with the `UInt64` carrier adapter fixed statically.

As for binary32, the arithmetic uses the proved fixed-word kernel. The specialization exists to
make carrier conversion first-order in generated code, independently of the generic codec used
by arbitrary configured formats.
-/
@[always_inline, inline] def softwareFma64
    {width_le : FloatFormat.binary64.bitWidth ≤ 64}
    (left right addend : Binary64Value width_le) : Binary64Value width_le :=
  ExecFloat.ofRaw <|
    Code.ofModel (plan := .word64 width_le) <|
      Model.FmaBackend.word
        (Code.toModel (plan := .word64 width_le) left.raw)
        (Code.toModel (plan := .word64 width_le) right.raw)
        (Code.toModel (plan := .word64 width_le) addend.raw)

end FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU
