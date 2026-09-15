/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.Model.Representation
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Special

/-!
# Packed native floating-point models

The conversions below connect the descriptor-indexed `Model` to Lean's packed binary32 and
binary64 models. Converting from a native model retains every bit. Converting to one canonicalizes
NaN signs and payloads, as required by Lean's packed-value invariant.

Lean 4.33 introduced these logical floating-point models. Lean 4.34 adds public `nan` and `inf`
constants for `Float32`, `Float`, and their packed models, and strengthens the generic format
invariant to require at least two exponent bits. These additions let both native widths share the
representation and constant proofs below.

The generic representation lemmas imported here separate this normalization from arithmetic
refinement. They concern Lean's logical definitions; they add no assumption about native machine
instructions and do not select a floating-point backend.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open Float.Model (UnpackedFloat)

/-! ## Binary32 -/

/-- Read the exact canonical word stored by Lean's packed binary32 model. -/
@[inline] def ofFloat32Model (value : Float32.Model) : Model FloatFormat.binary32 :=
  ofModelBits value.toBits.toBitVec

/-- Pack binary32 bits into Lean's model, canonicalizing any NaN sign and payload. -/
@[inline] def toFloat32Model (value : Model FloatFormat.binary32) : Float32.Model :=
  Float32.Model.pack (toModel value)

/-- Native packed binary32 always satisfies the generic canonical-word invariant. -/
theorem isModelCanonical_ofFloat32Model (value : Float32.Model) :
    IsModelCanonical (ofFloat32Model value) :=
  value.valid

/-- Unpacking the exact native binary32 word agrees with Lean's unpacked interpretation. -/
@[simp] theorem toModel_ofFloat32Model (value : Float32.Model) :
    toModel (ofFloat32Model value) = value.unpack :=
  rfl

/-- Packing an unpacked value agrees across the binary32 representation boundary. -/
@[simp] theorem ofFloat32Model_pack (value : UnpackedFloat) :
    ofFloat32Model (Float32.Model.pack value) = ofModel FloatFormat.binary32 value :=
  rfl

/-- Converting to a packed native model and back performs exactly NaN canonicalization. -/
@[simp] theorem ofFloat32Model_toFloat32Model (value : Model FloatFormat.binary32) :
    ofFloat32Model (toFloat32Model value) = canonicalizeModel value :=
  rfl

/-- Reading the exact binary32 word loses no information from a native packed model. -/
theorem ofFloat32Model_injective : Function.Injective ofFloat32Model := by
  intro left right h
  cases left with
  | mk left hleft =>
    cases right with
    | mk right hright =>
      cases left
      cases right
      cases h
      rfl

/-- Every native binary32 model round-trips exactly through FloatLib's representation. -/
@[simp] theorem toFloat32Model_ofFloat32Model (value : Float32.Model) :
    toFloat32Model (ofFloat32Model value) = value := by
  apply ofFloat32Model_injective
  exact canonicalizeModel_eq_self _ (isModelCanonical_ofFloat32Model value)

/-- Canonicalization does not change the unpacked interpretation of a binary32 conversion. -/
@[simp] theorem unpack_toFloat32Model (value : Model FloatFormat.binary32) :
    (toFloat32Model value).unpack = toModel value :=
  toModel_canonicalizeModel value

/-- Packing already packed model output agrees with the direct binary32 model constructor. -/
@[simp] theorem toFloat32Model_ofModel (value : UnpackedFloat) :
    toFloat32Model (ofModel FloatFormat.binary32 value) = Float32.Model.pack value := by
  rw [← ofFloat32Model_pack, toFloat32Model_ofFloat32Model]

/-- Equality of packed binary32 conversions is equality of their unpacked interpretations. -/
theorem toFloat32Model_eq_iff (left right : Model FloatFormat.binary32) :
    toFloat32Model left = toFloat32Model right ↔ toModel left = toModel right := by
  constructor
  · intro h
    simpa only [unpack_toFloat32Model] using congrArg Float32.Model.unpack h
  · exact congrArg Float32.Model.pack

/-! ## Binary64 -/

/-- Read the exact canonical word stored by Lean's packed binary64 model. -/
@[inline] def ofFloatModel (value : Float.Model) : Model FloatFormat.binary64 :=
  ofModelBits value.toBits.toBitVec

/-- Pack binary64 bits into Lean's model, canonicalizing any NaN sign and payload. -/
@[inline] def toFloatModel (value : Model FloatFormat.binary64) : Float.Model :=
  Float.Model.pack (toModel value)

/-- Native packed binary64 always satisfies the generic canonical-word invariant. -/
theorem isModelCanonical_ofFloatModel (value : Float.Model) :
    IsModelCanonical (ofFloatModel value) :=
  value.valid

/-- Unpacking the exact native binary64 word agrees with Lean's unpacked interpretation. -/
@[simp] theorem toModel_ofFloatModel (value : Float.Model) :
    toModel (ofFloatModel value) = value.unpack :=
  rfl

/-- Packing an unpacked value agrees across the binary64 representation boundary. -/
@[simp] theorem ofFloatModel_pack (value : UnpackedFloat) :
    ofFloatModel (Float.Model.pack value) = ofModel FloatFormat.binary64 value :=
  rfl

/-- Converting to a packed native model and back performs exactly NaN canonicalization. -/
@[simp] theorem ofFloatModel_toFloatModel (value : Model FloatFormat.binary64) :
    ofFloatModel (toFloatModel value) = canonicalizeModel value :=
  rfl

/-- Reading the exact binary64 word loses no information from a native packed model. -/
theorem ofFloatModel_injective : Function.Injective ofFloatModel := by
  intro left right h
  cases left with
  | mk left hleft =>
    cases right with
    | mk right hright =>
      cases left
      cases right
      cases h
      rfl

/-- Every native binary64 model round-trips exactly through FloatLib's representation. -/
@[simp] theorem toFloatModel_ofFloatModel (value : Float.Model) :
    toFloatModel (ofFloatModel value) = value := by
  apply ofFloatModel_injective
  exact canonicalizeModel_eq_self _ (isModelCanonical_ofFloatModel value)

/-- Canonicalization does not change the unpacked interpretation of a binary64 conversion. -/
@[simp] theorem unpack_toFloatModel (value : Model FloatFormat.binary64) :
    (toFloatModel value).unpack = toModel value :=
  toModel_canonicalizeModel value

/-- Packing already packed model output agrees with the direct binary64 model constructor. -/
@[simp] theorem toFloatModel_ofModel (value : UnpackedFloat) :
    toFloatModel (ofModel FloatFormat.binary64 value) = Float.Model.pack value := by
  rw [← ofFloatModel_pack, toFloatModel_ofFloatModel]

/-- Equality of packed binary64 conversions is equality of their unpacked interpretations. -/
theorem toFloatModel_eq_iff (left right : Model FloatFormat.binary64) :
    toFloatModel left = toFloatModel right ↔ toModel left = toModel right := by
  constructor
  · intro h
    simpa only [unpack_toFloatModel] using congrArg Float.Model.unpack h
  · exact congrArg Float.Model.pack

/-! ## Native constants -/

/-- Lean's binary32 NaN has FloatLib's canonical IEEE quiet-NaN word. -/
@[simp] theorem ofFloat32Model_nan :
    ofFloat32Model Float32.Model.nan = canonicalNaN FloatFormat.binary32 :=
  rfl

/-- Lean's binary64 NaN has FloatLib's canonical IEEE quiet-NaN word. -/
@[simp] theorem ofFloatModel_nan :
    ofFloatModel Float.Model.nan = canonicalNaN FloatFormat.binary64 :=
  rfl

/-- Lean's positive binary32 infinity has the ordinary all-ones-exponent encoding. -/
@[simp] theorem ofFloat32Model_inf :
    ofFloat32Model Float32.Model.inf = posInf FloatFormat.binary32 :=
  (posInf_eq_ofModel_infinity _).symm

/-- Lean's positive binary64 infinity has the ordinary all-ones-exponent encoding. -/
@[simp] theorem ofFloatModel_inf :
    ofFloatModel Float.Model.inf = posInf FloatFormat.binary64 :=
  (posInf_eq_ofModel_infinity _).symm

/-- The binary32 NaN constant converts back to Lean's packed NaN. -/
@[simp] theorem toFloat32Model_canonicalNaN :
    toFloat32Model (canonicalNaN FloatFormat.binary32) = Float32.Model.nan := by
  rw [← ofFloat32Model_nan, toFloat32Model_ofFloat32Model]

/-- The binary64 NaN constant converts back to Lean's packed NaN. -/
@[simp] theorem toFloatModel_canonicalNaN :
    toFloatModel (canonicalNaN FloatFormat.binary64) = Float.Model.nan := by
  rw [← ofFloatModel_nan, toFloatModel_ofFloatModel]

/-- The binary32 positive-infinity constant converts back to Lean's packed infinity. -/
@[simp] theorem toFloat32Model_posInf :
    toFloat32Model (posInf FloatFormat.binary32) = Float32.Model.inf := by
  rw [← ofFloat32Model_inf, toFloat32Model_ofFloat32Model]

/-- The binary64 positive-infinity constant converts back to Lean's packed infinity. -/
@[simp] theorem toFloatModel_posInf :
    toFloatModel (posInf FloatFormat.binary64) = Float.Model.inf := by
  rw [← ofFloatModel_inf, toFloatModel_ofFloatModel]

/-- Lean's native binary32 NaN denotes the unpacked model's single NaN value. -/
theorem toModel_ofFloat32Model_nan :
    toModel (ofFloat32Model Float32.nan.toModel) = UnpackedFloat.notANumber :=
  unpack_pack_notANumber _

/-- Lean's native binary64 NaN denotes the unpacked model's single NaN value. -/
theorem toModel_ofFloatModel_nan :
    toModel (ofFloatModel Float.nan.toModel) = UnpackedFloat.notANumber :=
  unpack_pack_notANumber _

/-- Lean's native binary32 infinity denotes positive infinity in the unpacked model. -/
theorem toModel_ofFloat32Model_inf :
    toModel (ofFloat32Model Float32.inf.toModel) = UnpackedFloat.infinity .positive :=
  unpack_pack_infinity _ _

/-- Lean's native binary64 infinity denotes positive infinity in the unpacked model. -/
theorem toModel_ofFloatModel_inf :
    toModel (ofFloatModel Float.inf.toModel) = UnpackedFloat.infinity .positive :=
  unpack_pack_infinity _ _

end FloatLib.Floats.Formats.BinaryInterchange.Model
