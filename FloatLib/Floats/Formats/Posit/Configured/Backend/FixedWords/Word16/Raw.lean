/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Kernels

/-!
# Raw `UInt16` kernels for packed posits

These entry points specialize the shared kernels to `UInt16` inputs and outputs. Configured
runtime wrappers use the generic range theorems from `FixedWords.Kernels`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Word16

/-! ## Addition and subtraction -/

/-- Raw `UInt16` addition kernel. -/
@[noinline] def addRaw
    (format : Format) (width_le : format.bits ≤ 16)
    (left right : UInt16)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt16 :=
  FixedWords.addRaw FixedWords.uint16Carrier
    format width_le left right hleft hright

/-- Raw `UInt16` subtraction kernel. -/
@[noinline] def subRaw
    (format : Format) (width_le : format.bits ≤ 16)
    (left right : UInt16)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt16 :=
  FixedWords.subRaw FixedWords.uint16Carrier
    format width_le left right hleft hright

/-! ## Multiplication and division -/

/-- Raw `UInt16` multiplication kernel. -/
@[noinline] def mulRaw
    (format : Format) (width_le : format.bits ≤ 16)
    (left right : UInt16)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt16 :=
  FixedWords.mulRaw FixedWords.uint16Carrier
    format width_le left right hleft hright

/-- Raw `UInt16` division kernel. -/
@[noinline] def divRaw
    (format : Format) (width_le : format.bits ≤ 16)
    (left right : UInt16)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt16 :=
  FixedWords.divRaw FixedWords.uint16Carrier
    format width_le left right hleft hright

/-! ## Square root and fused multiply-add -/

/-- Raw `UInt16` square-root kernel. -/
@[noinline] def sqrtRaw
    (format : Format) (width_le : format.bits ≤ 16)
    (value : UInt16)
    (hvalue : value.toNat < format.modulus) : UInt16 :=
  FixedWords.sqrtRaw FixedWords.uint16Carrier
    format width_le value hvalue

/-- Raw `UInt16` fused multiply-add kernel. -/
@[noinline] def fmaRaw
    (format : Format) (width_le : format.bits ≤ 16)
    (left right addend : UInt16)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) : UInt16 :=
  FixedWords.fmaRaw FixedWords.uint16Carrier
    format width_le left right addend hleft hright haddend

end FloatLib.Floats.Formats.Posit.Configured.Backend.Word16
