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
import FloatLib.Floats.Formats.BinaryInterchange.Operations.Classification.Semantics
import FloatLib.Floats.Formats.BinaryInterchange.Status.Tininess
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32

/-!
# Native signed integers to binary floating point

`ofInt_conversion_spec` shows that Lean's integer constructor gives the word and status of the
reference binary conversion `runWith`, so it satisfies `specWith`, the graph of `runWith` with a
nearest-value clause. `toReal_ofModel_ofInt_eq_roundAt` states the value without the reference
conversion: a finite result is the nearest-even rounding of the integer.
`finiteStatus_ofInt_underflow_false` shows that the conversion never signals underflow. Fixed-width
native conversions then agree with `ExecDType.intToFloat` at nearest-even rounding.

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
  exact (roundRat_den_one_eq_roundDyadic fmt (decide (n < 0)) n.natAbs).symm

/--
Lean's shared integer conversion gives the outcome of the reference conversion `runWith` for the
integer: the word, stored through `pack`, and the status `finiteStatus` of the default context.
It therefore satisfies `specWith`, whose nearest-value clause is the only part stated independently
of `runWith`; the status fields are the classifier-based ones of `finiteStatus`
(`finiteStatus_of_ieeeRoundingMode?_eq_some`). There `inexact` is set exactly when the delivered
value does not decode to `n`, and `finiteStatus_ofInt_underflow_false` shows that `underflow` is
never set. The `pack` adapter may return the model word or store it in a configured carrier.
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

/--
For a conventional IEEE descriptor, a finite result of Lean's integer constructor is the
nearest-even rounding of the integer onto the format grid (`roundAt`, ties to even). This is a
real-value statement; signed zeros and status are covered by `ofInt_conversion_spec`.
-/
theorem toReal_ofModel_ofInt_eq_roundAt (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : Int)
    (hfinite : isFinite (ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n)) = true) :
    toReal (ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n)) = roundAt fmt n := by
  rw [ofModel_ofInt_eq_roundDyadic fmt hfmt n] at hfinite ⊢
  rw [toReal_roundDyadic_eq_roundAt fmt hfmt _ hfinite, Dyadic.toReal_ofScaledInt_zero]

/--
Under a conventional IEEE descriptor, converting an integer never signals underflow: the status
that `ofInt_conversion_spec` gives has `underflow = false`. A nonzero integer has magnitude at
least one, at or above the smallest normal value, so neither the integer nor its nearest-even
rounding is tiny. Zero converts exactly.
-/
theorem finiteStatus_ofInt_underflow_false (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (n : Int) :
    (finiteStatus Context.default (n : Rat)
      (ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n))).underflow = false := by
  rw [finiteStatus_of_ieeeRoundingMode?_eq_some Context.default (mode := .nearest) rfl]
  simp only [Rat.num_intCast, Rat.den_intCast]
  by_cases hn : n = 0
  · subst hn
    have hzero : ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel 0) = posZero fmt := by
      rw [ofModel_ofInt_eq_roundDyadic fmt hfmt 0]
      simp [Dyadic.ofScaledInt, roundDyadic, hfmt, ieeeRoundDyadic, posZero_eq_ofModel_zero]
    have hexact : toRat? (posZero fmt) = some 0 := by
      simp [toRat?, toDyadic?_eq_zero_of_isZero_eq_true _ (isZero_posZero fmt)]
    simp [hzero, hexact]
  · set rounded := ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel n)
    have hone : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn
    -- The smallest normal value `2 ^ minNormalExponent` is at most one.
    have hminNormal : (2 : ℝ) ^ fmt.minNormalExponent ≤ 1 := by
      apply zpow_le_one_of_nonpos₀ (by norm_num)
      have := fmt.exponentBias_pos
      simp only [FloatFormat.minNormalExponent, Int.ofNat_eq_natCast]
      omega
    -- A finite result has magnitude at least one, so it is normal.
    have hnotTiny : isTinyAfterRounding rounded = false := by
      cases hfinite : isFinite rounded
      · simp [isTinyAfterRounding, hfinite]
      · have hroundOne : roundAt fmt 1 = 1 := by
          simp
        have habs : 1 ≤ |toReal rounded| := by
          rw [toReal_ofModel_ofInt_eq_roundAt fmt hfmt n hfinite]
          rcases le_or_gt 0 n with hpos | hneg
          · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (show (1 : Int) ≤ n by omega)
            have := roundAt_mono fmt h1
            rw [hroundOne] at this
            exact this.trans (le_abs_self _)
          · have h1 : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ -1 by omega)
            have := roundAt_mono fmt h1
            simp only [roundAt_neg, IEEERoundingMode.negate, hroundOne] at this
            exact (le_neg.mpr this).trans (neg_le_abs _)
        have hnormal : isNormal rounded = true :=
          (isNormal_iff_le_abs_toReal rounded).mpr ⟨hfinite, hminNormal.trans habs⟩
        simp [isTinyAfterRounding, hfinite, ((isNormal_iff_fields rounded).mp hnormal).2]
    -- The integer lies above the underflow midpoint, which is below the smallest normal value.
    have hmidpoint : (underflowMidpoint fmt).toReal < |(n : ℝ)| := by
      have hgap := (underflow_boundary_gaps fmt).2
      have hstep := FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix
        (fmt.minSubnormalExponent - 2)
      have hreal : (minNormalDyadic fmt).toReal = (2 : ℝ) ^ fmt.minNormalExponent := by
        have hsplit : fmt.minNormalExponent = (fmt.fracWidth : Int) + fmt.minSubnormalExponent := by
          simp only [FloatFormat.minSubnormalExponent, Int.ofNat_eq_natCast]
          ring
        rw [hsplit, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]
        simp only [minNormalDyadic, Numerics.Dyadic.toReal, Numerics.Dyadic.cast_signedSignificand,
          Bool.false_eq_true, ite_false, one_mul, pow2_eq_two_pow, Nat.cast_pow, Nat.cast_ofNat]
      linarith
    have htiny : rationalIsTinyAfterRoundingScaled fmt .nearest (decide ((n : Rat) < 0))
        n.natAbs 1 0 rounded = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      rw [rationalIsTinyAfterRoundingScaled_eq_true_iff _ _ _ _ _ _ _ one_ne_zero, hnotTiny] at h
      simp [scaledRatToReal] at h
      linarith
    rw [htiny]
    simp [hnotTiny]

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
