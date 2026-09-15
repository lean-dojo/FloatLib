/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Core

/-!
# Runtime packing for configured posits

`Code.toModel` and `Code.ofModel` form the canonical executable conversion pair for every static
posit carrier. Closed plans reduce to primitive or fixed-limb operations; the wide branch is the
identity on the exact-width proof model.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Numerics

/-- A valid Posit encoding fits every storage width at least as wide as its format. -/
theorem bits_lt_storage_capacity
    (format : Format) (bits wordWidth : Nat)
    (hbits : bits < format.modulus)
    (width_le : format.bits ≤ wordWidth) :
    bits < 2 ^ wordWidth := by
  apply StaticStorage.lt_capacity hbits
  simpa only [Format.modulus] using
    Nat.pow_le_pow_right (by decide : 0 < 2) width_le

namespace Code

variable {format : Format} {plan : StoragePlan format}

/-- Decode a packed runtime code into the exact-width proof model. -/
@[always_inline, inline] def toModel : Code plan → Model format :=
  match plan with
  | .byte _ => fun code => Model.ofNatBits code.1.toNat
  | .word16 _ => fun code => Model.ofNatBits code.1.toNat
  | .word32 _ => fun code => Model.ofNatBits code.1.toNat
  | .word64 _ => fun code => Model.ofNatBits code.1.toNat
  | .pair _ => fun code => Model.ofNatBits code.1.toNat
  | .wide => fun code => code

/-- Pack an exact proof-model value into the selected runtime carrier. -/
@[always_inline, inline] def ofModel : Model format → Code plan :=
  match plan with
  | .byte width_le => fun value =>
      StaticStorage.ByteCode.ofNat
        value.toNatBits
        (Model.toNatBits_lt_modulus value)
        (bits_lt_storage_capacity format value.toNatBits 8
          (Model.toNatBits_lt_modulus value) width_le)
  | .word16 width_le => fun value =>
      StaticStorage.Word16Code.ofNat
        value.toNatBits
        (Model.toNatBits_lt_modulus value)
        (bits_lt_storage_capacity format value.toNatBits 16
          (Model.toNatBits_lt_modulus value) width_le)
  | .word32 width_le => fun value =>
      StaticStorage.Word32Code.ofNat
        value.toNatBits
        (Model.toNatBits_lt_modulus value)
        (bits_lt_storage_capacity format value.toNatBits 32
          (Model.toNatBits_lt_modulus value) width_le)
  | .word64 width_le => fun value =>
      StaticStorage.Word64Code.ofNat
        value.toNatBits
        (Model.toNatBits_lt_modulus value)
        (bits_lt_storage_capacity format value.toNatBits 64
          (Model.toNatBits_lt_modulus value) width_le)
  | .pair width_le => fun value =>
      ⟨FloatLib.Numerics.FixedWord.UInt128.ofNat value.toNatBits, by
        rw [FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
          value.toNatBits (bits_lt_storage_capacity format
            value.toNatBits 128 (Model.toNatBits_lt_modulus value) width_le)]
        exact Model.toNatBits_lt_modulus value⟩
  | .wide => fun value => value

end Code

end FloatLib.Floats.Formats.Posit.Configured
