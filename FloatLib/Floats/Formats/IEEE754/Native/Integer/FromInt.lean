/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.Integer.Rounding
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Proof
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32

/-!
# Native signed integers to binary floating point

The shared theorem connects Lean's integer constructor to the complete binary conversion
specification, including the selected word and rounding status. Fixed-width native conversions
then agree with the existing `ExecDType.intToFloat` operation at nearest-even rounding.

Lean 4.33 introduced the logical floating-point models. Lean 4.34 connects the signed native
casts to those models and exposes `ofNat`, `ofInt`, `Int.toFloat`, `Int.toFloat32`, and named
floating-point constants. The proofs here use the new signed-cast definitions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

universe u

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Binary.Conversion

/-- Lean's integer constructor selects exactly the rational conversion result. -/
theorem ofModel_ofInt_eq_roundRat (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : Int) :
    ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n) =
      roundRat fmt (SignedRat.ofRat (n : Rat)).negative
        (n : Rat).num.natAbs (n : Rat).den := by
  rw [ofModel_ofInt_eq_roundDyadic fmt hfmt n]
  simp only [SignedRat.negative_ofRat, Rat.num_intCast, Rat.den_intCast,
    show ((n : Rat) < 0) = (n < 0) from propext Rat.intCast_lt_intCast]
  exact (roundRat_den_one_eq_roundDyadic fmt hfmt (decide (n < 0)) n.natAbs).symm

/--
Lean's shared integer conversion satisfies the existing complete nearest-even conversion spec.
The destination adapter may expose the model word or pack it into a configured carrier.
-/
theorem ofInt_conversion_spec {Destination : Type u} (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (pack : Model fmt → Destination) (n : Int) :
    specWith pack Context.default (.finite (SignedRat.ofRat (n : Rat)))
      (.success (pack (ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n)))
        (finiteStatus Context.default (n : Rat)
          (ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n)))) := by
  apply (specWith_iff_eq_runWith _ _ _ _).2
  rw [ofModel_ofInt_eq_roundRat fmt hfmt n]
  simp only [runWith, quantizeFiniteWith, Context.default,
    Policy.roundRat_nearestEven_eq_execFloat _ _ _ _ _ (Rat.den_ne_zero _),
    SignedRat.value_ofRat]

/-- The core integer constructor agrees with the existing fixed-width conversion operation. -/
theorem ofModel_ofInt_eq_intToFloat {width : Nat} (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (n : Numerics.Representations.FixedInt width) :
    ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n.toInt) =
      ExecDType.intToFloat fmt n .nearestEven :=
  ofModel_ofInt_eq_roundDyadic fmt hfmt n.toInt

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange
open Numerics.Representations

/-- `Int8.toFloat` is the existing binary64 nearest-even integer conversion. -/
theorem toModel_ofFloat_int8ToFloat (n : Int8) :
    toModel (ofFloat n.toFloat) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 8) .nearestEven := by
  rw [toModel_ofFloat]
  simp only [Int8.toFloat, Float.Model.ofInt8,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt8]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 8)

/-- `Int16.toFloat` is the existing binary64 nearest-even integer conversion. -/
theorem toModel_ofFloat_int16ToFloat (n : Int16) :
    toModel (ofFloat n.toFloat) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 16) .nearestEven := by
  rw [toModel_ofFloat]
  simp only [Int16.toFloat, Float.Model.ofInt16,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt16]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 16)

/-- `Int32.toFloat` is the existing binary64 nearest-even integer conversion. -/
theorem toModel_ofFloat_int32ToFloat (n : Int32) :
    toModel (ofFloat n.toFloat) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 32) .nearestEven := by
  rw [toModel_ofFloat]
  simp only [Int32.toFloat, Float.Model.ofInt32,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt32]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 32)

/-- `Int64.toFloat` is the existing binary64 nearest-even integer conversion. -/
theorem toModel_ofFloat_int64ToFloat (n : Int64) :
    toModel (ofFloat n.toFloat) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 64) .nearestEven := by
  rw [toModel_ofFloat]
  simp only [Int64.toFloat, Float.Model.ofInt64,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt64]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 64)

/-- `ISize.toFloat` uses the platform's signed width and binary64 nearest-even rounding. -/
theorem toModel_ofFloat_iSizeToFloat (n : ISize) :
    toModel (ofFloat n.toFloat) =
      ExecDType.intToFloat FloatFormat.binary64
        (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits) .nearestEven := by
  rw [toModel_ofFloat]
  simp only [ISize.toFloat, Float.Model.ofISize,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofISize]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits)

/-- `Int8.toFloat32` is the existing binary32 nearest-even integer conversion. -/
theorem toModel_ofFloat32_int8ToFloat32 (n : Int8) :
    toModel (ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 8) .nearestEven := by
  rw [toModel_ofFloat32]
  simp only [Int8.toFloat32, Float32.Model.ofInt8,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt8]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 8)

/-- `Int16.toFloat32` is the existing binary32 nearest-even integer conversion. -/
theorem toModel_ofFloat32_int16ToFloat32 (n : Int16) :
    toModel (ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 16) .nearestEven := by
  rw [toModel_ofFloat32]
  simp only [Int16.toFloat32, Float32.Model.ofInt16,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt16]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 16)

/-- `Int32.toFloat32` is the existing binary32 nearest-even integer conversion. -/
theorem toModel_ofFloat32_int32ToFloat32 (n : Int32) :
    toModel (ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 32) .nearestEven := by
  rw [toModel_ofFloat32]
  simp only [Int32.toFloat32, Float32.Model.ofInt32,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt32]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 32)

/-- `Int64.toFloat32` is the existing binary32 nearest-even integer conversion. -/
theorem toModel_ofFloat32_int64ToFloat32 (n : Int64) :
    toModel (ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 64) .nearestEven := by
  rw [toModel_ofFloat32]
  simp only [Int64.toFloat32, Float32.Model.ofInt64,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt64]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 64)

/-- `ISize.toFloat32` uses the platform's signed width and binary32 nearest-even rounding. -/
theorem toModel_ofFloat32_iSizeToFloat32 (n : ISize) :
    toModel (ofFloat32 n.toFloat32) =
      ExecDType.intToFloat FloatFormat.binary32
        (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits) .nearestEven := by
  rw [toModel_ofFloat32]
  simp only [ISize.toFloat32, Float32.Model.ofISize,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofISize]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits)

end FloatLib.Floats.ExecFloat.Binary
