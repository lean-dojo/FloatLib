/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Code.Runtime

/-!
# Two-limb runtime access for configured posits

Formats from 65 through 128 bits use a persistent `UInt128` pair by default. These operations
expose and pack that carrier directly, without constructing a model at the storage boundary.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

namespace PairCode

variable {format : Format}

/-- Read the two persistent limbs without reconstructing the exact-width proof model. -/
@[always_inline, inline] def word (code : PairCode format) :
    FloatLib.Numerics.FixedWord.UInt128 :=
  code.1

/--
Store one already-range-checked two-limb encoding directly.

Unlike `pack`, this carrier-native boundary performs no natural-number conversion. It is the
result constructor for arithmetic kernels whose complete code already resides in `UInt128`.
-/
@[always_inline, inline] def packWord
    (word : FloatLib.Numerics.FixedWord.UInt128)
    (hword : word.toNat < format.modulus) :
    PairCode format :=
  ⟨word, hword⟩

/--
Pack one already-range-checked complete encoding into two persistent limbs.

The format-width premise proves that conversion to `UInt128` is exact rather than modular.
-/
@[always_inline, inline] def pack
    (width_le : format.bits ≤ 128)
    (bits : Nat) (hbits : bits < format.modulus) :
    PairCode format :=
  ⟨FloatLib.Numerics.FixedWord.UInt128.ofNat bits,
    by
      rw [FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
        bits (bits_lt_storage_capacity format bits 128 hbits width_le)]
      exact hbits⟩

end PairCode

end FloatLib.Floats.Formats.Posit.Configured
