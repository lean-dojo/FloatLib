/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Kernels

/-!
# Raw `UInt8` kernels for packed posits

These entry points specialize the shared kernels to `UInt8` inputs and outputs. Configured runtime
wrappers use the generic range theorems from `FixedWords.Kernels`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Byte

/-! ## Addition and subtraction -/

/-- Raw `UInt8` addition kernel. -/
@[noinline] def addRaw
    (format : Format) (width_le : format.bits ≤ 8)
    (left right : UInt8)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt8 :=
  FixedWords.addRaw FixedWords.uint8Carrier
    format width_le left right hleft hright

/-- Raw `UInt8` subtraction kernel. -/
@[noinline] def subRaw
    (format : Format) (width_le : format.bits ≤ 8)
    (left right : UInt8)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt8 :=
  FixedWords.subRaw FixedWords.uint8Carrier
    format width_le left right hleft hright

/-! ## Multiplication and division -/

/-- Raw `UInt8` multiplication kernel. -/
@[noinline] def mulRaw
    (format : Format) (width_le : format.bits ≤ 8)
    (left right : UInt8)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt8 :=
  FixedWords.mulRaw FixedWords.uint8Carrier
    format width_le left right hleft hright

/-- Raw `UInt8` division kernel. -/
@[noinline] def divRaw
    (format : Format) (width_le : format.bits ≤ 8)
    (left right : UInt8)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt8 :=
  FixedWords.divRaw FixedWords.uint8Carrier
    format width_le left right hleft hright

/-! ## Square root and fused multiply-add -/

/--
Raw `UInt8` square-root kernel.

Inlining this wrapper exposes the format to the shared root-prefix kernel when the caller's
format is known.
-/
@[always_inline] def sqrtRaw
    (format : Format) (width_le : format.bits ≤ 8)
    (value : UInt8)
    (hvalue : value.toNat < format.modulus) : UInt8 :=
  FixedWords.sqrtRaw FixedWords.uint8Carrier
    format width_le value hvalue

/-- Raw `UInt8` fused multiply-add kernel. -/
@[noinline] def fmaRaw
    (format : Format) (width_le : format.bits ≤ 8)
    (left right addend : UInt8)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) : UInt8 :=
  FixedWords.fmaRaw FixedWords.uint8Carrier
    format width_le left right addend hleft hright haddend

end FloatLib.Floats.Formats.Posit.Configured.Backend.Byte
