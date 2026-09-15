/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Kernels

/-!
# Raw `UInt32` kernels for packed posits

These entry points specialize the shared kernels to `UInt32` inputs and outputs. Configured
runtime wrappers use the generic range theorems from `FixedWords.Kernels`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Word32

/-! ## Addition and subtraction -/

/-- Raw `UInt32` addition kernel. -/
@[noinline] def addRaw
    (format : Format) (width_le : format.bits ≤ 32)
    (left right : UInt32)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt32 :=
  FixedWords.addRaw FixedWords.uint32Carrier
    format width_le left right hleft hright

/-- Raw `UInt32` subtraction kernel. -/
@[noinline] def subRaw
    (format : Format) (width_le : format.bits ≤ 32)
    (left right : UInt32)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt32 :=
  FixedWords.subRaw FixedWords.uint32Carrier
    format width_le left right hleft hright

/-! ## Multiplication and division -/

/-- Raw `UInt32` multiplication kernel. -/
@[noinline] def mulRaw
    (format : Format) (width_le : format.bits ≤ 32)
    (left right : UInt32)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt32 :=
  FixedWords.mulRaw FixedWords.uint32Carrier
    format width_le left right hleft hright

/-- Raw `UInt32` division kernel. -/
@[noinline] def divRaw
    (format : Format) (width_le : format.bits ≤ 32)
    (left right : UInt32)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt32 :=
  FixedWords.divRaw FixedWords.uint32Carrier
    format width_le left right hleft hright

/-! ## Square root and fused multiply-add -/

/-- Raw `UInt32` square-root kernel. -/
@[noinline] def sqrtRaw
    (format : Format) (width_le : format.bits ≤ 32)
    (value : UInt32)
    (hvalue : value.toNat < format.modulus) : UInt32 :=
  FixedWords.sqrtRaw FixedWords.uint32Carrier
    format width_le value hvalue

/-- Raw `UInt32` fused multiply-add kernel. -/
@[noinline] def fmaRaw
    (format : Format) (width_le : format.bits ≤ 32)
    (left right addend : UInt32)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) : UInt32 :=
  FixedWords.fmaRaw FixedWords.uint32Carrier
    format width_le left right addend hleft hright haddend

end FloatLib.Floats.Formats.Posit.Configured.Backend.Word32
