/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word32.Raw
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Runtime

/-!
# Configured `UInt32` runtime for packed posits

These wrappers rebuild the statically selected `UInt32` carrier around unboxed raw kernels.
Range proofs are erased during compilation; semantic refinement is isolated in `Word32.Proof`.

The visible monomorphic boundary is intentional: it preserves the compiler's direct `UInt32`
calling convention. Arithmetic itself is shared in `FixedWords.Kernels`, so this file contains no
width-specific algorithm or fallback, only the small adapter required by the configured carrier.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Word32

variable {format : Format}

/-- Add two posits stored directly in a `UInt32` carrier. -/
@[always_inline] def add
    (width_le : format.bits ≤ 32)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word32 width_le)) (.word32 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word32 width_le)) (.word32 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨addRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.addRaw_lt_modulus FixedWords.uint32Carrier
        width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2⟩

/-- Subtract two posits stored directly in a `UInt32` carrier. -/
@[always_inline] def sub
    (width_le : format.bits ≤ 32)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word32 width_le)) (.word32 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word32 width_le)) (.word32 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨subRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.subRaw_lt_modulus FixedWords.uint32Carrier
        width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2⟩

/-- Multiply two posits stored directly in a `UInt32` carrier. -/
@[always_inline] def mul
    (width_le : format.bits ≤ 32)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word32 width_le)) (.word32 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word32 width_le)) (.word32 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨mulRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.mulRaw_lt_modulus FixedWords.uint32Carrier
        width_le left.raw.1 right.raw.1
        left.raw.2 right.raw.2⟩

/-- Divide two posits stored directly in a `UInt32` carrier. -/
@[always_inline] def div
    (width_le : format.bits ≤ 32)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word32 width_le)) (.word32 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word32 width_le)) (.word32 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨divRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.divRaw_lt_modulus FixedWords.uint32Carrier
        width_le left.raw.1 right.raw.1
        left.raw.2 right.raw.2⟩

/-- Take the square root of a posit stored directly in a `UInt32` carrier. -/
@[always_inline] def sqrt
    (width_le : format.bits ≤ 32)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word32 width_le)) (.word32 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word32 width_le)) (.word32 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨sqrtRaw format width_le value.raw.1 value.raw.2,
      FixedWords.sqrtRaw_lt_modulus FixedWords.uint32Carrier
        width_le value.raw.1 value.raw.2⟩

/-- Fused multiply-add for posits stored directly in a `UInt32` carrier. -/
@[always_inline] def fma
    (width_le : format.bits ≤ 32)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word32 width_le)) (.word32 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word32 width_le)) (.word32 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨fmaRaw format width_le left.raw.1 right.raw.1 addend.raw.1
        left.raw.2 right.raw.2 addend.raw.2,
      FixedWords.fmaRaw_lt_modulus FixedWords.uint32Carrier
        width_le left.raw.1 right.raw.1 addend.raw.1
        left.raw.2 right.raw.2 addend.raw.2⟩

end FloatLib.Floats.Formats.Posit.Configured.Backend.Word32
