/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Kernels

/-!
# Raw `UInt64` kernels for packed posits

These entry points preserve the native `UInt64` calling convention of the selected storage plan.
Configured runtime wrappers use the generic range certificates from `FixedWords.Kernels`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Word64

/-! ## Addition and subtraction -/

/-- Raw `UInt64` addition kernel. -/
@[noinline] def addRaw
    (format : Format) (width_le : format.bits ≤ 64)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt64 :=
  FixedWords.addRaw FixedWords.uint64Carrier
    format width_le left right hleft hright

/-- Raw `UInt64` subtraction kernel. -/
@[noinline] def subRaw
    (format : Format) (width_le : format.bits ≤ 64)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt64 :=
  FixedWords.subRaw FixedWords.uint64Carrier
    format width_le left right hleft hright

/-! ## Multiplication and division -/

/-- Raw `UInt64` multiplication kernel. -/
@[noinline] def mulRaw
    (format : Format) (width_le : format.bits ≤ 64)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt64 :=
  FixedWords.mulRaw FixedWords.uint64Carrier
    format width_le left right hleft hright

/-- Raw `UInt64` division kernel. -/
@[noinline] def divRaw
    (format : Format) (width_le : format.bits ≤ 64)
    (left right : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus) : UInt64 :=
  FixedWords.divRaw FixedWords.uint64Carrier
    format width_le left right hleft hright

/-! ## Square root and fused multiply-add -/

/-- Raw `UInt64` square-root kernel. -/
@[noinline] def sqrtRaw
    (format : Format) (width_le : format.bits ≤ 64)
    (value : UInt64)
    (hvalue : value.toNat < format.modulus) : UInt64 :=
  FixedWords.sqrtRaw FixedWords.uint64Carrier
    format width_le value hvalue

/-- Raw `UInt64` fused multiply-add kernel. -/
@[noinline] def fmaRaw
    (format : Format) (width_le : format.bits ≤ 64)
    (left right addend : UInt64)
    (hleft : left.toNat < format.modulus)
    (hright : right.toNat < format.modulus)
    (haddend : addend.toNat < format.modulus) : UInt64 :=
  FixedWords.fmaRaw FixedWords.uint64Carrier
    format width_le left right addend hleft hright haddend

end FloatLib.Floats.Formats.Posit.Configured.Backend.Word64
