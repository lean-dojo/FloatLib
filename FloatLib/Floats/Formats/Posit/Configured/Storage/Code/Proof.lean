/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Code.Runtime

/-!
# Packing equivalence for configured posits

Configured posits may live in a byte, native word, fixed pair of limbs, or a wide carrier. The
public model is independent of that choice, so packing and decoding must be lossless for every
storage plan.

These mutual-inverse theorems discharge that obligation once by case analysis on the plan. Codec
instances and arithmetic capabilities reuse them instead of maintaining width-specific conversion
proofs that could drift apart.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Numerics

namespace Code

variable {format : Format} {plan : StoragePlan format}

/-- Decoding a freshly packed posit model returns that exact model. -/
@[simp, grind =] theorem toModel_ofModel (value : Model format) :
    toModel (plan := plan) (ofModel (plan := plan) value) = value := by
  cases plan with
  | byte width_le =>
      simp only [toModel, ofModel, StaticStorage.ByteCode.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | word16 width_le =>
      simp only [toModel, ofModel, StaticStorage.Word16Code.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | word32 width_le =>
      simp only [toModel, ofModel, StaticStorage.Word32Code.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | word64 width_le =>
      simp only [toModel, ofModel, StaticStorage.Word64Code.toNat_ofNat]
      exact Model.ofNatBits_toNatBits value
  | pair width_le =>
      simp only [toModel, ofModel]
      rw [FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat
        value.toNatBits
        (bits_lt_storage_capacity format value.toNatBits 128
          (Model.toNatBits_lt_modulus value) width_le)]
      exact Model.ofNatBits_toNatBits value
  | wide =>
      rfl

/-- Repacking a decoded posit code returns the original packed code. -/
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
      change (UInt16.ofNat (Model.ofNatBits code.1.toNat).toNatBits).toNat = code.1.toNat
      rw [Model.toNatBits_ofNatBits_of_lt code.1.toNat code.2]
      exact congrArg UInt16.toNat (@UInt16.ofNat_toNat code.1)
  | word32 width_le =>
      apply Subtype.ext
      apply UInt32.toNat_inj.mp
      change (UInt32.ofNat (Model.ofNatBits code.1.toNat).toNatBits).toNat = code.1.toNat
      rw [Model.toNatBits_ofNatBits_of_lt code.1.toNat code.2]
      exact congrArg UInt32.toNat (@UInt32.ofNat_toNat code.1)
  | word64 width_le =>
      apply Subtype.ext
      apply UInt64.toNat_inj.mp
      change (UInt64.ofNat (Model.ofNatBits code.1.toNat).toNatBits).toNat = code.1.toNat
      rw [Model.toNatBits_ofNatBits_of_lt code.1.toNat code.2]
      exact congrArg UInt64.toNat (@UInt64.ofNat_toNat code.1)
  | pair width_le =>
      apply Subtype.ext
      apply FloatLib.Numerics.FixedWord.UInt128.toNat_injective
      change
        (FloatLib.Numerics.FixedWord.UInt128.ofNat
          (Model.ofNatBits code.1.toNat).toNatBits).toNat =
            code.1.toNat
      rw [Model.toNatBits_ofNatBits_of_lt code.1.toNat code.2]
      exact
        FloatLib.Numerics.FixedWord.UInt128.toNat_ofNat code.1.toNat
          (lt_of_lt_of_le code.2
            (by
              unfold Format.modulus
              exact Nat.pow_le_pow_right (by decide) width_le))
  | wide =>
      rfl

end Code

end FloatLib.Floats.Formats.Posit.Configured
