/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Storage.Native.Core

/-!
# Native-word instances for configured posit carriers

The four primitive storage plans implement the direct `UInt64` capability. Each conversion is
proved exact from the plan's static width bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Configured

open FloatLib.Numerics

instance byteNativeCode (format : Format) (width_le : format.bits ≤ 8) :
    NativeCode format (StoragePlan.byte width_le) where
  toUInt64 code := code.1.toUInt64
  ofNat bits hbits :=
    StaticStorage.ByteCode.ofNat bits hbits
      (bits_lt_storage_capacity format bits 8 hbits width_le)
  toUInt64_lt_modulus code := by
    simpa using code.2
  toModel_eq_ofUInt64 _ := rfl
  toModel_ofNat bits hbits := by
    simp only [Code.toModel, StaticStorage.ByteCode.toNat_ofNat]

instance word16NativeCode (format : Format) (width_le : format.bits ≤ 16) :
    NativeCode format (StoragePlan.word16 width_le) where
  toUInt64 code := code.1.toUInt64
  ofNat bits hbits :=
    StaticStorage.Word16Code.ofNat bits hbits
      (bits_lt_storage_capacity format bits 16 hbits width_le)
  toUInt64_lt_modulus code := by
    simpa using code.2
  toModel_eq_ofUInt64 _ := rfl
  toModel_ofNat bits hbits := by
    simp only [Code.toModel, StaticStorage.Word16Code.toNat_ofNat]

instance word32NativeCode (format : Format) (width_le : format.bits ≤ 32) :
    NativeCode format (StoragePlan.word32 width_le) where
  toUInt64 code := code.1.toUInt64
  ofNat bits hbits :=
    StaticStorage.Word32Code.ofNat bits hbits
      (bits_lt_storage_capacity format bits 32 hbits width_le)
  toUInt64_lt_modulus code := by
    simpa using code.2
  toModel_eq_ofUInt64 _ := rfl
  toModel_ofNat bits hbits := by
    simp only [Code.toModel, StaticStorage.Word32Code.toNat_ofNat]

instance word64NativeCode (format : Format) (width_le : format.bits ≤ 64) :
    NativeCode format (StoragePlan.word64 width_le) where
  toUInt64 code := code.1
  ofNat bits hbits :=
    StaticStorage.Word64Code.ofNat bits hbits
      (bits_lt_storage_capacity format bits 64 hbits width_le)
  toUInt64_lt_modulus code := code.2
  toModel_eq_ofUInt64 _ := rfl
  toModel_ofNat bits hbits := by
    simp only [Code.toModel, StaticStorage.Word64Code.toNat_ofNat]

end FloatLib.Floats.Formats.Posit.Configured
