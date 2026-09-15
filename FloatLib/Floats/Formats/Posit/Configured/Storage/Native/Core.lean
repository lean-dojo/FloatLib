/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Code.Runtime

/-!
# Direct native-word capability for configured posits

`NativeCode` records when a built-in packed carrier can be read and written through `UInt64`
without reconstructing the exact-width model. Its laws connect that fast view to `Code.toModel`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

/--
Certified zero-extension of one built-in packed carrier into `UInt64`.

This capability is tied to `Code plan`, so a user-defined codec that requires marshalling cannot
accidentally select a direct native-word kernel.
-/
class NativeCode (format : Format) (plan : StoragePlan format) where
  /-- Zero-extend a packed code without changing its encoded natural value. -/
  toUInt64 : Code plan → UInt64
  /-- Pack an already-range-checked complete encoding without constructing `Model`. -/
  ofNat : (bits : Nat) → bits < format.modulus → Code plan
  /-- Every packed code remains in the descriptor's exact encoding range. -/
  toUInt64_lt_modulus :
    ∀ code, (toUInt64 code).toNat < format.modulus
  /-- Direct native-word decoding denotes the same exact-width model word. -/
  toModel_eq_ofUInt64 :
    ∀ code,
      Code.toModel code =
        Model.ofNatBits (format := format) (toUInt64 code).toNat
  /-- Direct packing denotes exactly the supplied complete encoding. -/
  toModel_ofNat :
    ∀ bits hbits,
      Code.toModel (ofNat bits hbits) =
        Model.ofNatBits (format := format) bits

end FloatLib.Floats.Formats.Posit.Configured
