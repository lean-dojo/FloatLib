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

`ofInt_conversion_spec` connects Lean's integer constructor to the complete binary conversion
specification, including the selected word and rounding status. Fixed-width native conversions
then agree with `ExecDType.intToFloat` at nearest-even rounding.

Lean defines the signed native casts through its logical floating-point models and exposes
`ofNat`, `ofInt`, `Int.toFloat`, `Int.toFloat32`, and named
floating-point constants. The proofs here use those signed-cast definitions.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

universe u

open FloatLib.Numerics
open FloatLib.Floats.ExecFloat.Binary.Conversion

/-- Lean's integer constructor gives the `roundRat` result for the integer as a rational. -/
theorem ofModel_ofInt_eq_roundRat (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : Int) :
    ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n) =
      roundRat fmt (SignedRat.ofRat (n : Rat)).negative
        (n : Rat).num.natAbs (n : Rat).den := by
  rw [ofModel_ofInt_eq_roundDyadic fmt hfmt n]
  simp only [SignedRat.negative_ofRat, Rat.num_intCast, Rat.den_intCast,
    show ((n : Rat) < 0) = (n < 0) from propext Rat.intCast_lt_intCast]
  exact (roundRat_den_one_eq_roundDyadic fmt hfmt (decide (n < 0)) n.natAbs).symm

/--
Lean's shared integer conversion satisfies the complete nearest-even conversion specification.
The `pack` adapter may return the model word or store it in a configured carrier.
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
    Policy.roundRat_nearest_eq_execFloat _ _ _ _ _ (Rat.den_ne_zero _),
    SignedRat.value_ofRat]

/-- Lean's integer constructor agrees with fixed-width `ExecDType.intToFloat` at nearest-even. -/
theorem ofModel_ofInt_eq_intToFloat {width : Nat} (fmt : FloatFormat)
    (hfmt : fmt.isIEEE = true) (n : Numerics.Representations.FixedInt width) :
    ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n.toInt) =
      ExecDType.intToFloat fmt n .nearest :=
  ofModel_ofInt_eq_roundDyadic fmt hfmt n.toInt

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange
open Numerics.Representations

/-- `Int8.toFloat` agrees with nearest-even `ExecDType.intToFloat` into binary64. -/
theorem toModel_ofFloat_int8ToFloat (n : Int8) :
    toModel (ofFloat n.toFloat : Binary64) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 8) .nearest := by
  rw [toModel_ofFloat]
  simp only [Int8.toFloat, Float.Model.ofInt8,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt8]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 8)

/-- `Int16.toFloat` agrees with nearest-even `ExecDType.intToFloat` into binary64. -/
theorem toModel_ofFloat_int16ToFloat (n : Int16) :
    toModel (ofFloat n.toFloat : Binary64) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 16) .nearest := by
  rw [toModel_ofFloat]
  simp only [Int16.toFloat, Float.Model.ofInt16,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt16]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 16)

/-- `Int32.toFloat` agrees with nearest-even `ExecDType.intToFloat` into binary64. -/
theorem toModel_ofFloat_int32ToFloat (n : Int32) :
    toModel (ofFloat n.toFloat : Binary64) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 32) .nearest := by
  rw [toModel_ofFloat]
  simp only [Int32.toFloat, Float.Model.ofInt32,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt32]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 32)

/-- `Int64.toFloat` agrees with nearest-even `ExecDType.intToFloat` into binary64. -/
theorem toModel_ofFloat_int64ToFloat (n : Int64) :
    toModel (ofFloat n.toFloat : Binary64) =
      ExecDType.intToFloat FloatFormat.binary64 (⟨n.toBitVec⟩ : FixedInt 64) .nearest := by
  rw [toModel_ofFloat]
  simp only [Int64.toFloat, Float.Model.ofInt64,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofInt64]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 64)

/-- `ISize.toFloat` uses the platform's signed width and binary64 nearest-even rounding. -/
theorem toModel_ofFloat_iSizeToFloat (n : ISize) :
    toModel (ofFloat n.toFloat : Binary64) =
      ExecDType.intToFloat FloatFormat.binary64
        (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits) .nearest := by
  rw [toModel_ofFloat]
  simp only [ISize.toFloat, Float.Model.ofISize,
    Model.ofFloatModel_pack, Float.Model.UnpackedFloat.ofISize]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary64 (by decide)
    (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits)

/-- `Int8.toFloat32` agrees with nearest-even `ExecDType.intToFloat` into binary32. -/
theorem toModel_ofFloat32_int8ToFloat32 (n : Int8) :
    toModel (ofFloat32 n.toFloat32 : Binary32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 8) .nearest := by
  rw [toModel_ofFloat32]
  simp only [Int8.toFloat32, Float32.Model.ofInt8,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt8]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 8)

/-- `Int16.toFloat32` agrees with nearest-even `ExecDType.intToFloat` into binary32. -/
theorem toModel_ofFloat32_int16ToFloat32 (n : Int16) :
    toModel (ofFloat32 n.toFloat32 : Binary32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 16) .nearest := by
  rw [toModel_ofFloat32]
  simp only [Int16.toFloat32, Float32.Model.ofInt16,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt16]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 16)

/-- `Int32.toFloat32` agrees with nearest-even `ExecDType.intToFloat` into binary32. -/
theorem toModel_ofFloat32_int32ToFloat32 (n : Int32) :
    toModel (ofFloat32 n.toFloat32 : Binary32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 32) .nearest := by
  rw [toModel_ofFloat32]
  simp only [Int32.toFloat32, Float32.Model.ofInt32,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt32]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 32)

/-- `Int64.toFloat32` agrees with nearest-even `ExecDType.intToFloat` into binary32. -/
theorem toModel_ofFloat32_int64ToFloat32 (n : Int64) :
    toModel (ofFloat32 n.toFloat32 : Binary32) =
      ExecDType.intToFloat FloatFormat.binary32 (⟨n.toBitVec⟩ : FixedInt 64) .nearest := by
  rw [toModel_ofFloat32]
  simp only [Int64.toFloat32, Float32.Model.ofInt64,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofInt64]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt 64)

/-- `ISize.toFloat32` uses the platform's signed width and binary32 nearest-even rounding. -/
theorem toModel_ofFloat32_iSizeToFloat32 (n : ISize) :
    toModel (ofFloat32 n.toFloat32 : Binary32) =
      ExecDType.intToFloat FloatFormat.binary32
        (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits) .nearest := by
  rw [toModel_ofFloat32]
  simp only [ISize.toFloat32, Float32.Model.ofISize,
    Model.ofFloat32Model_pack, Float.Model.UnpackedFloat.ofISize]
  exact Model.ofModel_ofInt_eq_intToFloat FloatFormat.binary32 (by decide)
    (⟨n.toBitVec⟩ : FixedInt System.Platform.numBits)

end FloatLib.Floats.ExecFloat.Binary
