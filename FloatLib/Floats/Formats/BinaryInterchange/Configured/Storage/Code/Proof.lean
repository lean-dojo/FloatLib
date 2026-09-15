/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Storage.Code.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Core.Proof
public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Core.Proof

/-!
# Packing equivalence for configured binary formats

These theorems prove that configured packing and decoding are mutual inverses for every selected
carrier. Codec instances reuse this equivalence instead of duplicating one proof for each
machine-word width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Numerics
namespace Code

variable {format : FloatFormat} {plan : StoragePlan format}

/-- The model word rebuilt from a bounded code has the code's natural-number value. -/
private theorem toNatBits_ofBits_ofNatLT (bits : Nat) (hbits : bits < 2 ^ format.bitWidth) :
    (Model.ofBits (fmt := format) (BitVec.ofNatLT bits hbits)).toNatBits = bits :=
  BitVec.toNat_ofNatLT bits hbits

/-- Decoding a freshly packed proof-model value returns that exact model. -/
@[simp, grind =] theorem toModel_ofModel (value : Model format) :
    toModel (plan := plan) (ofModel (plan := plan) value) = value := by
  cases plan with
  | byte width_le =>
      exact StaticByte.byteCodeToModel_modelToByteCode format width_le value
  | word16 width_le =>
      change Model.ofBits (BitVec.ofNatLT _ _) = value
      rw [BitVec.ofNatLT_eq_ofNat]
      simp only [ofModel, StaticStorage.Word16Code.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | word32 width_le =>
      change Model.ofBits (BitVec.ofNatLT _ _) = value
      rw [BitVec.ofNatLT_eq_ofNat]
      simp only [ofModel, StaticStorage.Word32Code.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | word64 width_le =>
      change Model.ofBits (BitVec.ofNatLT _ _) = value
      rw [BitVec.ofNatLT_eq_ofNat]
      simp only [ofModel, StaticStorage.Word64Code.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | wide =>
      rfl
  | limbs _ =>
      exact Model.WideLimb.toModel_ofModel value

/-- Repacking a decoded runtime code returns the original packed code. -/
@[simp, grind =] theorem ofModel_toModel (code : Code plan) :
    ofModel (plan := plan) (toModel code) = code := by
  cases plan with
  | byte width_le =>
      apply Subtype.ext
      apply UInt8.toNat_inj.mp
      change (UInt8.ofNat (Model.ofNatBits code.1.toNat).toNatBits).toNat = code.1.toNat
      rw [Model.toNatBits_ofNatBits_of_lt code.1.toNat code.2]
      exact congrArg UInt8.toNat (@UInt8.ofNat_toNat code.1)
  | word16 width_le =>
      apply Subtype.ext
      apply UInt16.toNat_inj.mp
      change (UInt16.ofNat (Model.ofBits (BitVec.ofNatLT code.1.toNat code.2)).toNatBits).toNat =
        code.1.toNat
      rw [toNatBits_ofBits_ofNatLT]
      exact congrArg UInt16.toNat (@UInt16.ofNat_toNat code.1)
  | word32 width_le =>
      apply Subtype.ext
      apply UInt32.toNat_inj.mp
      change (UInt32.ofNat (Model.ofBits (BitVec.ofNatLT code.1.toNat code.2)).toNatBits).toNat =
        code.1.toNat
      rw [toNatBits_ofBits_ofNatLT]
      exact congrArg UInt32.toNat (@UInt32.ofNat_toNat code.1)
  | word64 width_le =>
      apply Subtype.ext
      apply UInt64.toNat_inj.mp
      change (UInt64.ofNat (Model.ofBits (BitVec.ofNatLT code.1.toNat code.2)).toNatBits).toNat =
        code.1.toNat
      rw [toNatBits_ofBits_ofNatLT]
      exact congrArg UInt64.toNat (@UInt64.ofNat_toNat code.1)
  | wide =>
      rfl
  | limbs _ =>
      exact Model.WideLimb.ofModel_toModel code

end Code

end FloatLib.Floats.Formats.BinaryInterchange.Configured
