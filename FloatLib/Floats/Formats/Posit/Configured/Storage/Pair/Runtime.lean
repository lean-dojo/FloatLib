/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Code.Runtime

/-!
# Two-limb runtime access for configured posits

Formats from 65 through 128 bits are stored as a persistent `UInt128` pair by default, and these
operations read and pack that carrier as it is, with no model built at the storage boundary.
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
Store a two-limb encoding whose range is already checked.

Unlike `pack`, this carrier-native boundary does no natural-number conversion. Arithmetic kernels
whose complete code already sits in a `UInt128` use it to build their result.
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
