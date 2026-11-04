/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Backend.FixedWords.Word64.Raw
public import FloatLib.Floats.Formats.Posit.Configured.Storage.Family.Runtime

/-!
# Configured `UInt64` runtime for packed posits

Each wrapper calls a native raw kernel and rebuilds the statically selected `UInt64` carrier
around the result, with range proofs that Lean erases when it compiles and a semantic refinement
that lives in `Word64.Proof`.

We keep this monomorphic boundary visible on purpose, because it preserves the compiler's direct
`UInt64` calling convention. Arithmetic itself is shared in `FixedWords.Kernels`. So the file has
no width-specific algorithm and no fallback, just the small adapter the configured carrier needs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured.Backend.Word64

variable {format : Format}

/-- Add two posits held in their packed `UInt64` carrier. -/
@[always_inline] def add
    (width_le : format.bits ≤ 64)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word64 width_le)) (.word64 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word64 width_le)) (.word64 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨addRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.addRaw_lt_modulus FixedWords.uint64Carrier
        width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2⟩

/-- Subtract two posits held in their packed `UInt64` carrier. -/
@[always_inline] def sub
    (width_le : format.bits ≤ 64)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word64 width_le)) (.word64 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word64 width_le)) (.word64 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨subRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.subRaw_lt_modulus FixedWords.uint64Carrier
        width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2⟩

/-- Multiply two posits held in their packed `UInt64` carrier. -/
@[always_inline] def mul
    (width_le : format.bits ≤ 64)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word64 width_le)) (.word64 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word64 width_le)) (.word64 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨mulRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.mulRaw_lt_modulus FixedWords.uint64Carrier
        width_le left.raw.1 right.raw.1
        left.raw.2 right.raw.2⟩

/-- Divide two posits held in their packed `UInt64` carrier. -/
@[always_inline] def div
    (width_le : format.bits ≤ 64)
    (left right :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word64 width_le)) (.word64 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word64 width_le)) (.word64 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨divRaw format width_le left.raw.1 right.raw.1 left.raw.2 right.raw.2,
      FixedWords.divRaw_lt_modulus FixedWords.uint64Carrier
        width_le left.raw.1 right.raw.1
        left.raw.2 right.raw.2⟩

/-- Take the square root of a posit held in its packed `UInt64` carrier. -/
@[always_inline] def sqrt
    (width_le : format.bits ≤ 64)
    (value :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word64 width_le)) (.word64 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word64 width_le)) (.word64 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨sqrtRaw format width_le value.raw.1 value.raw.2,
      FixedWords.sqrtRaw_lt_modulus FixedWords.uint64Carrier
        width_le value.raw.1 value.raw.2⟩

/-- Fused multiply-add for posits held in their packed `UInt64` carrier. -/
@[always_inline] def fma
    (width_le : format.bits ≤ 64)
    (left right addend :
      FloatLib.Floats.ExecFloat
        (Family format (Code (.word64 width_le)) (.word64 width_le))) :
    FloatLib.Floats.ExecFloat
      (Family format (Code (.word64 width_le)) (.word64 width_le)) :=
  FloatLib.Floats.ExecFloat.ofRaw
    ⟨fmaRaw format width_le left.raw.1 right.raw.1 addend.raw.1
        left.raw.2 right.raw.2 addend.raw.2,
      FixedWords.fmaRaw_lt_modulus FixedWords.uint64Carrier
        width_le left.raw.1 right.raw.1 addend.raw.1
        left.raw.2 right.raw.2 addend.raw.2⟩

end FloatLib.Floats.Formats.Posit.Configured.Backend.Word64
