/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.Integer.Constructors
public import FloatLib.Floats.Formats.IEEE754.Native.Integer.FromInt
public import FloatLib.Floats.Formats.IEEE754.Native.Integer.ToInt
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.Formats.IEEE754.Native.Sqrt

/-!
# Native logical-model bridges

These regressions apply the public FloatLib bridges to symbolic inputs and selected boundary
cases. Concrete results are checked by the kernel; no host floating-point operation is executed.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.NativeModel

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.ExecFloat.Binary.Conversion
open FloatLib.Numerics
open FloatLib.Numerics.Representations

/-- Every native binary32 value survives the public import/export roundtrip. -/
theorem native32_roundtrip (value : Float32) :
    ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofFloat32 value) = value :=
  ExecFloat.Binary.toFloat32_ofFloat32 value

/-- Every native binary64 value survives the public import/export roundtrip. -/
theorem native64_roundtrip (value : Float) :
    ExecFloat.Binary.toFloat (ExecFloat.Binary.ofFloat value) = value :=
  ExecFloat.Binary.toFloat_ofFloat value

/-- A negative signaling NaN loses its sign and payload at the native boundary. -/
theorem native32_nan_canonicalized :
    ExecFloat.Binary.toBits32
      (ExecFloat.Binary.ofFloat32
        (ExecFloat.Binary.toFloat32 (ExecFloat.Binary.ofBits32 0xff800001))) = 0x7fc00000 := by
  rw [ExecFloat.Binary.ofFloat32_toFloat32]
  decide +kernel

/-- The integer constructor satisfies the conversion contract for any IEEE descriptor. -/
theorem integer_conversion_spec (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : Int) :
    specWith id Context.default (.finite (SignedRat.ofRat (n : Rat)))
      (.success (Model.ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n))
        (finiteStatus Context.default (n : Rat)
          (Model.ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n)))) :=
  Model.ofInt_conversion_spec fmt hfmt id n

/-- At the first binary32 integer tie, the even endpoint is the lower integer. -/
theorem int64_to_native32_tie_down :
    (ExecFloat.Binary.toModel
      (ExecFloat.Binary.ofFloat32 (16777217 : Int64).toFloat32)).toNatBits = 0x4b800000 := by
  rw [ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32]
  decide +kernel

/-- At the next tie, the even endpoint is the upper integer. -/
theorem int64_to_native32_tie_up :
    (ExecFloat.Binary.toModel
      (ExecFloat.Binary.ofFloat32 (16777219 : Int64).toFloat32)).toNatBits = 0x4b800002 := by
  rw [ExecFloat.Binary.toModel_ofFloat32_int64ToFloat32]
  decide +kernel

/-- Natural construction beyond `UInt64` still rounds a binary32 tie to the even endpoint. -/
theorem nat_to_native32_large_tie :
    (ExecFloat.Binary.toModel
      (ExecFloat.Binary.ofFloat32 (Float32.ofNat (2 ^ 80 + 2 ^ 56)))).toNatBits =
      0x67800000 := by
  rw [ExecFloat.Binary.toModel_ofFloat32_ofNat]
  decide +kernel

/-- An unbounded negative integer rounds directly to binary64 without narrowing its magnitude. -/
theorem int_to_native64_large_negative_tie :
    (ExecFloat.Binary.toModel
      (ExecFloat.Binary.ofFloat ((-(2 ^ 80 + 2 ^ 27) : Int).toFloat))).toNatBits =
      0xc4f0000000000000 := by
  rw [ExecFloat.Binary.toModel_ofFloat_intToFloat]
  decide +kernel

/-- Range checking applies after truncation: 127.75 still converts to signed eight-bit 127. -/
theorem native64_int8_boundary_fraction :
    (⟨(Float.ofBits 0x405ff00000000000).toInt8.toBitVec⟩ : FixedInt 8).toInt = 127 := by
  rw [ExecFloat.Binary.floatToInt8_eq_floatToIntSaturating]
  decide +kernel

/-- Finite overflow saturates at the positive signed endpoint. -/
theorem native64_int8_saturates :
    (⟨(Float.ofBits 0x4060000000000000).toInt8.toBitVec⟩ : FixedInt 8).toInt = 127 := by
  rw [ExecFloat.Binary.floatToInt8_eq_floatToIntSaturating]
  decide +kernel

/-- Negative infinity selects the negative signed endpoint. -/
theorem native32_int8_negative_infinity :
    (⟨(-Float32.inf).toInt8.toBitVec⟩ : FixedInt 8).toInt = -128 := by
  rw [ExecFloat.Binary.float32ToInt8_eq_floatToIntSaturating]
  decide +kernel

/-- The native integer policy maps NaN to zero. -/
theorem native32_int8_nan :
    (⟨Float32.nan.toInt8.toBitVec⟩ : FixedInt 8).toInt = 0 := by
  rw [ExecFloat.Binary.float32ToInt8_eq_floatToIntSaturating]
  decide +kernel

/-- Import commutes with both public binary64 operations on arbitrary finite native operands. -/
theorem native64_add_sub_commute (x y : Float)
    (hx : x.isFinite = true) (hy : y.isFinite = true) :
    ExecFloat.Binary.ofFloat (x + y) =
        ExecFloat.Binary.ofFloat x + ExecFloat.Binary.ofFloat y ∧
      ExecFloat.Binary.ofFloat (x - y) =
        ExecFloat.Binary.ofFloat x - ExecFloat.Binary.ofFloat y :=
  ⟨ExecFloat.Binary.ofFloat_add_of_isFinite x y hx hy,
    ExecFloat.Binary.ofFloat_sub_of_isFinite x y hx hy⟩

/-- The finite-input addition bridge permits overflow to infinity. -/
theorem native32_add_overflow :
    ExecFloat.Binary.toBits32
      (ExecFloat.Binary.ofFloat32 (Float32.ofBits 0x7f7fffff) +
        ExecFloat.Binary.ofFloat32 (Float32.ofBits 0x7f7fffff)) = 0x7f800000 := by
  rw [← ExecFloat.Binary.ofFloat32_add_of_isFinite _ _ (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- Public configured binary32 square root commutes with native export on every input word. -/
theorem native32_sqrt_commutes (value : ExecFloat.Binary 8 23) :
    ExecFloat.Binary.toFloat32 (ExecFloat.sqrt value) =
      (ExecFloat.Binary.toFloat32 value).sqrt :=
  ExecFloat.Binary.toFloat32_sqrt value

/-- Public configured binary64 square root commutes with native export on every input word. -/
theorem native64_sqrt_commutes (value : ExecFloat.Binary 11 52) :
    ExecFloat.Binary.toFloat (ExecFloat.sqrt value) =
      (ExecFloat.Binary.toFloat value).sqrt :=
  ExecFloat.Binary.toFloat_sqrt value

/-- Square root preserves negative zero through the configured operation and native adapter. -/
theorem native64_sqrt_negative_zero :
    (ExecFloat.Binary.toFloat
      (ExecFloat.sqrt (ExecFloat.Binary.ofBits64 0x8000000000000000))).toBits =
      0x8000000000000000 := by
  rw [ExecFloat.Binary.toFloat_sqrt]
  decide +kernel

/-- Square root of minus one exports as Lean's canonical quiet NaN. -/
theorem native32_sqrt_negative_one :
    (ExecFloat.Binary.toFloat32
      (ExecFloat.sqrt (ExecFloat.Binary.ofBits32 0xbf800000))).toBits = 0x7fc00000 := by
  rw [ExecFloat.Binary.toFloat32_sqrt]
  decide +kernel

end FloatLibTests.Conformance.BinaryInterchange.NativeModel
