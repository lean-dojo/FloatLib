/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Pair.Runtime

/-!
# Correctness of two-limb posit packing

Direct pair packing decodes to the supplied complete encoding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

namespace PairCode

variable {format : Format}

/-- Direct carrier-native packing denotes the word's complete encoding. -/
@[simp, grind =] theorem toModel_packWord
    (width_le : format.bits ≤ 128)
    (word : FloatLib.Numerics.FixedWord.UInt128)
    (hword : word.toNat < format.modulus) :
    Code.toModel (plan := StoragePlan.pair width_le)
        (packWord word hword) =
      Model.ofNatBits (format := format) word.toNat := by
  rfl

/-- Direct pair packing denotes exactly the supplied complete encoding. -/
@[simp, grind =] theorem toModel_pack
    (width_le : format.bits ≤ 128)
    (bits : Nat) (hbits : bits < format.modulus) :
    Code.toModel (plan := StoragePlan.pair width_le)
        (pack width_le bits hbits) =
      Model.ofNatBits (format := format) bits := by
  simp only [Code.toModel, pack]
  rw [FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
    bits (bits_lt_storage_capacity format bits 128 hbits width_le)]

end PairCode

end FloatLib.Floats.Formats.Posit.Configured
