/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Family.Proof

/-!
# Packing correctness for configured binary values

The storage-independent constructors form a lossless equivalence with the exact-width binary
model and with every in-range complete interchange word. This module depends only on the
representation interface; importing these proofs does not register arithmetic backends.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/-- Decoding immediately after packing a binary proof model returns the original model. -/
@[simp, grind =] theorem toModel_ofModel (value : Model format) :
    toModel (ofModel (plan := plan) (code := code) value) = value :=
  Configured.Family.toModel_ofModel value

/-- Packing immediately after decoding a configured binary value returns the original value. -/
@[simp, grind =] theorem ofModel_toModel
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ofModel (toModel value) = value :=
  Configured.Family.ofModel_toModel value

/-- Reconstructing a configured binary value from its complete word is lossless. -/
@[simp, grind =] theorem ofNatBits_toNatBits
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ofNatBits (toNatBits value) = value := by
  apply Configured.Family.toModel_injective
  simp [ofNatBits, toNatBits, toModel, ofModel]

/-- Reading an in-range complete word immediately after constructing it returns that word. -/
@[simp, grind =] theorem toNatBits_ofNatBits_of_lt
    (bits : Nat) (bits_lt : bits < 2 ^ format.bitWidth) :
    toNatBits (ofNatBits (plan := plan) (code := code) bits) = bits := by
  simp [ofNatBits, toNatBits, toModel, ofModel,
    Model.toNatBits_ofNatBits_of_lt bits bits_lt]

end FloatLib.Floats.ExecFloat.Binary
