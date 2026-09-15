/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.Integer.Rounding
public import FloatLib.Floats.Formats.IEEE754.Native.Representation
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Semantics
import all Init.Data.SInt.Float
import all Init.Data.SInt.Float32

/-!
# Native floating point to signed integers

Lean 4.34 gives the signed native casts logical definitions using the floating-point models
introduced in Lean 4.33. They truncate toward zero, saturate overflow and infinities, and send
NaN to zero. FloatLib's checked conversion reports those exceptional cases as errors.

The shared policy below uses the same exact decoder and integral rounder as the checked
conversion. In-range means that the *truncated integer* is in range: for example, `127.75`
converts successfully to the signed eight-bit integer `127`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics
open Float.Model.UnpackedFloat

/--
Lean's integer conversion reads FloatLib's exact interpretation and truncates its finite dyadic.
Infinity endpoints are supplied by the destination; NaN maps to zero before saturation.
-/
theorem toInt_toModel_eq {fmt : FloatFormat} (hfmt : fmt.isIEEE = true)
    (x : Model fmt) (lower upper : Int) :
    (toModel x).toInt lower upper =
      match exactValue x with
      | .finite d => roundDyadicToInt .towardZero d
      | .infinity negative => if negative then lower else upper
      | .nan _ _ _ => 0 := by
  have hencoding := FloatFormat.encoding_eq_ieee_of_isIEEE fmt hfmt
  simp only [exactValue, toDyadic?, hfmt, ↓reduceIte,
    ieeeToDyadic?_eq_unpackedToDyadic?_toModel, toModel, unpack]
  split <;> rename_i hExponentOnes
  · have hexp : expField x = fmt.expAllOnesNat := by
      rw [← unpackExponent_toNat x, hExponentOnes]
      exact toNat_neg_one_exponentBits fmt
    split <;> rename_i hMantissa
    · have hfrac : fracField x = 0 := by
        rw [← unpackMantissa_toNat x, hMantissa]
        rfl
      simp only [unpackedToDyadic?, isInf, hencoding, IEEE.isInf, hexp, hfrac,
        beq_self_eq_true, Bool.and_self, ↓reduceIte]
      rw [← modelSignBit_ofBitVec_unpackSign x]
      cases Sign.ofBitVec (unpackSign (toModelBits x)) <;> rfl
    · have hfrac : fracField x ≠ 0 := by
        intro h
        apply hMantissa
        apply BitVec.toNat_inj.mp
        rw [unpackMantissa_toNat x, h]
        rfl
      simp [unpackedToDyadic?, isInf, hencoding, IEEE.isInf, hexp, hfrac, toInt]
  · split
    · split
      · simp [unpackedToDyadic?, toInt, roundDyadicToInt]
      · exact roundToInt_eq_roundDyadicToInt _ _ _
    · exact roundToInt_eq_roundDyadicToInt _ _ _

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecDType

open FloatLib.Numerics
open FloatLib.Numerics.Representations

/--
Toward-zero signed conversion with Lean's native exceptional-value policy.

This uses the checked conversion's exact decoder and integral rounder, then saturates finite
overflow. Infinities select their signed endpoint and NaN selects zero.
-/
def floatToIntSaturating {fmt : FloatFormat} (width : Nat) (x : Model fmt) : FixedInt width :=
  match Model.exactValue x with
  | .finite d => FixedInt.ofIntSaturating (Model.roundDyadicToInt .towardZero d)
  | .infinity negative => if negative then FixedInt.minCode width else FixedInt.maxCode width
  | .nan _ _ _ => FixedInt.ofInt 0

/-- The native policy is the existing saturating integer encoder applied to Lean's model result. -/
theorem floatToIntSaturating_eq_ofIntSaturating_toModel
    {fmt : FloatFormat} {width : Nat} (hfmt : fmt.isIEEE = true) (hwidth : 0 < width)
    (x : Model fmt) :
    floatToIntSaturating width x =
      FixedInt.ofIntSaturating
        ((Model.toModel x).toInt (FixedInt.minValue width) (FixedInt.maxValue width)) := by
  rw [Model.toInt_toModel_eq hfmt]
  have hbounds := FixedInt.minValue_le_maxValue hwidth
  have hlower : FixedInt.InRange width (FixedInt.minValue width) := ⟨le_rfl, hbounds⟩
  have hupper : FixedInt.InRange width (FixedInt.maxValue width) := ⟨hbounds, le_rfl⟩
  have hzero : FixedInt.InRange width 0 := by
    unfold FixedInt.InRange
    rw [FixedInt.minValue_eq hwidth, FixedInt.maxValue_eq]
    have hp : (0 : Int) < 2 ^ (width - 1) := Int.pow_pos (by decide)
    omega
  cases hv : Model.exactValue x with
  | finite d => simp [floatToIntSaturating, hv]
  | infinity negative =>
      cases negative <;>
        simp only [floatToIntSaturating, hv, Bool.false_eq_true, ↓reduceIte,
          FixedInt.ofIntSaturating, FixedInt.clamp_eq_self hlower,
          FixedInt.clamp_eq_self hupper]
      · exact (FixedInt.ofInt_toInt (FixedInt.maxCode width)).symm
      · exact (FixedInt.ofInt_toInt (FixedInt.minCode width)).symm
  | nan negative signaling payload =>
      simp [floatToIntSaturating, hv, FixedInt.ofIntSaturating, FixedInt.clamp_eq_self hzero]

/-- Checked conversion agrees with native saturation whenever its rounded integer is in range. -/
theorem floatToIntSaturating_of_exactValue_eq_finite_of_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt) (d : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite d)
    (hrange : FixedInt.InRange width (Model.roundDyadicToInt .towardZero d)) :
    floatToInt (width := width) x .towardZero =
      .success (floatToIntSaturating width x) { inexact := !Model.dyadicIsIntegral d } := by
  rw [floatToInt_of_exactValue_eq_finite_of_inRange x .towardZero d hvalue hrange]
  simp [floatToIntSaturating, hvalue, FixedInt.ofIntSaturating, FixedInt.clamp_eq_self hrange]

/-- On an in-range truncated integer, native saturation and the checked API return the same code. -/
theorem floatToIntSaturating_of_exactValue_eq_finite_of_real_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt) (d : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite d)
    (hrange : FixedInt.InRange width
      (if 0 ≤ d.toReal then ⌊d.toReal⌋ else ⌈d.toReal⌉)) :
    floatToInt (width := width) x .towardZero =
      .success (floatToIntSaturating width x) { inexact := !Model.dyadicIsIntegral d } := by
  rw [floatToInt_towardZero_of_exactValue_eq_finite_of_inRange x d hvalue hrange]
  rw [← Model.roundDyadicToInt_towardZero] at hrange ⊢
  simp [floatToIntSaturating, hvalue, FixedInt.ofIntSaturating, FixedInt.clamp_eq_self hrange]

/-- Out-of-range finite values saturate natively but are rejected by the checked conversion. -/
theorem floatToIntSaturating_of_exactValue_eq_finite_of_not_inRange
    {fmt : FloatFormat} {width : Nat} (x : Model fmt) (d : Numerics.Dyadic)
    (hvalue : Model.exactValue x = .finite d)
    (hrange : ¬FixedInt.InRange width (Model.roundDyadicToInt .towardZero d)) :
    floatToIntSaturating width x =
        FixedInt.ofIntSaturating (Model.roundDyadicToInt .towardZero d) ∧
      floatToInt (width := width) x .towardZero = .failure .outOfRange := by
  exact ⟨by simp [floatToIntSaturating, hvalue],
    floatToInt_of_exactValue_eq_finite_of_not_inRange x .towardZero d hvalue hrange⟩

/-- Infinity saturates to its signed endpoint while the checked API reports signed infinity. -/
theorem floatToIntSaturating_of_exactValue_eq_infinity
    {fmt : FloatFormat} (width : Nat) (x : Model fmt) (negative : Bool)
    (hvalue : Model.exactValue x = .infinity negative) :
    floatToIntSaturating width x =
        (if negative then FixedInt.minCode width else FixedInt.maxCode width) ∧
      floatToInt (width := width) x .towardZero =
        .failure (.infinity .source negative) := by
  exact ⟨by simp [floatToIntSaturating, hvalue],
    floatToInt_of_exactValue_eq_infinity x .towardZero negative hvalue⟩

/-- NaN maps to zero natively while the checked API reports its payload. -/
theorem floatToIntSaturating_of_exactValue_eq_nan
    {fmt : FloatFormat} (width : Nat) (x : Model fmt) (negative signaling : Bool) (payload : Nat)
    (hvalue : Model.exactValue x = .nan negative signaling payload) :
    floatToIntSaturating width x = FixedInt.ofInt 0 ∧
      floatToInt (width := width) x .towardZero =
        .failure (.exceptional .source (.nan (some payload))) := by
  exact ⟨by simp [floatToIntSaturating, hvalue],
    floatToInt_of_exactValue_eq_nan x .towardZero negative signaling payload hvalue⟩

end FloatLib.Floats.Formats.BinaryInterchange.ExecDType

namespace FloatLib.Numerics.Representations.FixedInt

private theorem ofIntSaturating_eq_ite {width : Nat} (hwidth : 0 < width) (n : Int) :
    ofIntSaturating (width := width) n =
      if minValue width ≤ n then
        if n ≤ maxValue width then ofInt n else maxCode width
      else minCode width := by
  have hbounds := minValue_le_maxValue hwidth
  split <;> rename_i hlower
  · split <;> rename_i hupper
    · simp [ofIntSaturating, clamp_eq_self (show InRange width n from ⟨hlower, hupper⟩)]
    · rw [ofIntSaturating, clamp, Quantization.Saturating.clamp,
        min_eq_left (by omega), max_eq_right hbounds]
      exact ofInt_toInt (maxCode width)
  · rw [ofIntSaturating, clamp, Quantization.Saturating.clamp,
      min_eq_right (by omega), max_eq_left (by omega)]
    exact ofInt_toInt (minCode width)

private theorem int8_ofIntClamp (n : Int) :
    (⟨(Int8.ofIntClamp n).toBitVec⟩ : FixedInt 8) = ofIntSaturating n := by
  rw [ofIntSaturating_eq_ite (by decide)]
  unfold Int8.ofIntClamp
  split_ifs <;> first | rfl | contradiction

private theorem int16_ofIntClamp (n : Int) :
    (⟨(Int16.ofIntClamp n).toBitVec⟩ : FixedInt 16) = ofIntSaturating n := by
  rw [ofIntSaturating_eq_ite (by decide)]
  unfold Int16.ofIntClamp
  split_ifs <;> first | rfl | contradiction

private theorem int32_ofIntClamp (n : Int) :
    (⟨(Int32.ofIntClamp n).toBitVec⟩ : FixedInt 32) = ofIntSaturating n := by
  rw [ofIntSaturating_eq_ite (by decide)]
  unfold Int32.ofIntClamp
  split_ifs <;> first | rfl | contradiction

private theorem int64_ofIntClamp (n : Int) :
    (⟨(Int64.ofIntClamp n).toBitVec⟩ : FixedInt 64) = ofIntSaturating n := by
  rw [ofIntSaturating_eq_ite (by decide)]
  unfold Int64.ofIntClamp
  split_ifs <;> first | rfl | contradiction

private theorem iSize_ofIntClamp (n : Int) :
    (⟨(ISize.ofIntClamp n).toBitVec⟩ : FixedInt System.Platform.numBits) =
      ofIntSaturating n := by
  rw [ofIntSaturating_eq_ite (by cases System.Platform.numBits_eq <;> omega)]
  unfold ISize.ofIntClamp
  simp only [minValue_eq (width := System.Platform.numBits)
      (by cases System.Platform.numBits_eq <;> omega), maxValue_eq,
    ISize.toInt_minValue, ISize.toInt_maxValue]
  split_ifs <;> simp only [ISize.toBitVec_ofIntLE, ISize.toBitVec_minValue,
    ISize.toBitVec_maxValue] <;> rfl

end FloatLib.Numerics.Representations.FixedInt

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange
open Numerics.Representations

/-- Native binary64 to `Int8` uses the shared toward-zero, saturation, and NaN-to-zero policy. -/
theorem floatToInt8_eq_floatToIntSaturating (x : Float) :
    (⟨x.toInt8.toBitVec⟩ : FixedInt 8) =
      ExecDType.floatToIntSaturating 8 (toModel (ofFloat x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int8_ofIntClamp _

/-- Native binary64 to `Int16` uses the shared signed conversion policy. -/
theorem floatToInt16_eq_floatToIntSaturating (x : Float) :
    (⟨x.toInt16.toBitVec⟩ : FixedInt 16) =
      ExecDType.floatToIntSaturating 16 (toModel (ofFloat x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int16_ofIntClamp _

/-- Native binary64 to `Int32` uses the shared signed conversion policy. -/
theorem floatToInt32_eq_floatToIntSaturating (x : Float) :
    (⟨x.toInt32.toBitVec⟩ : FixedInt 32) =
      ExecDType.floatToIntSaturating 32 (toModel (ofFloat x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int32_ofIntClamp _

/-- Native binary64 to `Int64` uses the shared signed conversion policy. -/
theorem floatToInt64_eq_floatToIntSaturating (x : Float) :
    (⟨x.toInt64.toBitVec⟩ : FixedInt 64) =
      ExecDType.floatToIntSaturating 64 (toModel (ofFloat x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int64_ofIntClamp _

/-- Native binary64 to `ISize` saturates to the platform's signed interval. -/
theorem floatToISize_eq_floatToIntSaturating (x : Float) :
    (⟨x.toISize.toBitVec⟩ : FixedInt System.Platform.numBits) =
      ExecDType.floatToIntSaturating System.Platform.numBits (toModel (ofFloat x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide)
    (by cases System.Platform.numBits_eq <;> omega)]
  change (⟨(ISize.ofIntClamp
      (x.toModel.unpack.toInt ISize.minValue.toInt ISize.maxValue.toInt)).toBitVec⟩ :
        FixedInt System.Platform.numBits) =
    FixedInt.ofIntSaturating
      (x.toModel.unpack.toInt (FixedInt.minValue _) (FixedInt.maxValue _))
  rw [FixedInt.minValue_eq (by cases System.Platform.numBits_eq <;> omega),
    FixedInt.maxValue_eq, ← ISize.toInt_minValue, ← ISize.toInt_maxValue]
  exact FixedInt.iSize_ofIntClamp _

/-- Native binary32 to `Int8` uses the shared toward-zero, saturation, and NaN-to-zero policy. -/
theorem float32ToInt8_eq_floatToIntSaturating (x : Float32) :
    (⟨x.toInt8.toBitVec⟩ : FixedInt 8) =
      ExecDType.floatToIntSaturating 8 (toModel (ofFloat32 x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int8_ofIntClamp _

/-- Native binary32 to `Int16` uses the shared signed conversion policy. -/
theorem float32ToInt16_eq_floatToIntSaturating (x : Float32) :
    (⟨x.toInt16.toBitVec⟩ : FixedInt 16) =
      ExecDType.floatToIntSaturating 16 (toModel (ofFloat32 x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int16_ofIntClamp _

/-- Native binary32 to `Int32` uses the shared signed conversion policy. -/
theorem float32ToInt32_eq_floatToIntSaturating (x : Float32) :
    (⟨x.toInt32.toBitVec⟩ : FixedInt 32) =
      ExecDType.floatToIntSaturating 32 (toModel (ofFloat32 x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int32_ofIntClamp _

/-- Native binary32 to `Int64` uses the shared signed conversion policy. -/
theorem float32ToInt64_eq_floatToIntSaturating (x : Float32) :
    (⟨x.toInt64.toBitVec⟩ : FixedInt 64) =
      ExecDType.floatToIntSaturating 64 (toModel (ofFloat32 x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide) (by decide)]
  exact FixedInt.int64_ofIntClamp _

/-- Native binary32 to `ISize` saturates to the platform's signed interval. -/
theorem float32ToISize_eq_floatToIntSaturating (x : Float32) :
    (⟨x.toISize.toBitVec⟩ : FixedInt System.Platform.numBits) =
      ExecDType.floatToIntSaturating System.Platform.numBits (toModel (ofFloat32 x)) := by
  rw [ExecDType.floatToIntSaturating_eq_ofIntSaturating_toModel (by decide)
    (by cases System.Platform.numBits_eq <;> omega)]
  change (⟨(ISize.ofIntClamp
      (x.toModel.unpack.toInt ISize.minValue.toInt ISize.maxValue.toInt)).toBitVec⟩ :
        FixedInt System.Platform.numBits) =
    FixedInt.ofIntSaturating
      (x.toModel.unpack.toInt (FixedInt.minValue _) (FixedInt.maxValue _))
  rw [FixedInt.minValue_eq (by cases System.Platform.numBits_eq <;> omega),
    FixedInt.maxValue_eq, ← ISize.toInt_minValue, ← ISize.toInt_maxValue]
  exact FixedInt.iSize_ofIntClamp _

end FloatLib.Floats.ExecFloat.Binary
