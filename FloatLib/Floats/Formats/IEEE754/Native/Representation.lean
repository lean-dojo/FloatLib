/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native
public import FloatLib.Floats.Formats.IEEE754.Native.Model

/-!
# Native values through the shared representation bridge

Lean has named NaN and infinity constants alongside its logical floating-point models, and we're
glad it is making more of this model available for proofs.
Here we connect those constants and the `ofFloat` / `toFloat` adapters to the same packed-model
proofs used for arithmetic and integer conversion.

Every native value round-trips. In the other direction, a FloatLib word may carry a NaN payload
that Lean's model does not retain, and `Model.canonicalizeModel` describes that change. Finite
values, infinities, and both signed zeros keep their bits.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange

/-! ## Binary32 -/

/-- Importing a native value reads the word in its logical binary32 model. -/
@[simp] theorem toModel_ofFloat32 (value : Float32) :
    toModel (ofFloat32 value : Binary32) = Model.ofFloat32Model value.toModel :=
  rfl

/-- Exporting binary32 uses the shared packed-model conversion, including NaN normalization. -/
theorem toModel_toFloat32_eq (value : Binary32) :
    (toFloat32 value).toModel = Model.toFloat32Model (toModel value) :=
  rfl

/-- An imported native binary32 value already satisfies Lean's canonical-NaN invariant. -/
theorem isModelCanonical_ofFloat32 (value : Float32) :
    Model.IsModelCanonical (toModel (ofFloat32 value : Binary32)) :=
  Model.isModelCanonical_ofFloat32Model value.toModel

/-- Importing and then exporting a native binary32 value gives it back. -/
@[simp] theorem toFloat32_ofFloat32 (value : Float32) :
    toFloat32 (ofFloat32 value : Binary32) = value := by
  cases value with
  | ofModel model =>
      change Float32.ofModel (Model.toFloat32Model (Model.ofFloat32Model model)) = _
      rw [Model.toFloat32Model_ofFloat32Model]

/-- Lean's binary32 NaN imports as FloatLib's canonical quiet NaN. -/
theorem toModel_ofFloat32_nan :
    toModel (ofFloat32 Float32.nan : Binary32) = Model.canonicalNaN FloatFormat.binary32 :=
  Model.ofFloat32Model_nan

/-- Lean's binary32 infinity imports as FloatLib's positive infinity. -/
theorem toModel_ofFloat32_inf :
    toModel (ofFloat32 Float32.inf : Binary32) = Model.posInf FloatFormat.binary32 :=
  Model.ofFloat32Model_inf

/-! ## Binary64 -/

/-- Importing a native value reads the word in its logical binary64 model. -/
@[simp] theorem toModel_ofFloat (value : Float) :
    toModel (ofFloat value : Binary64) = Model.ofFloatModel value.toModel :=
  rfl

/-- Exporting binary64 uses the shared packed-model conversion, including NaN normalization. -/
theorem toModel_toFloat_eq (value : Binary64) :
    (toFloat value).toModel = Model.toFloatModel (toModel value) :=
  rfl

/-- An imported native binary64 value already satisfies Lean's canonical-NaN invariant. -/
theorem isModelCanonical_ofFloat (value : Float) :
    Model.IsModelCanonical (toModel (ofFloat value : Binary64)) :=
  Model.isModelCanonical_ofFloatModel value.toModel

/-- Importing and then exporting a native binary64 value gives it back. -/
@[simp] theorem toFloat_ofFloat (value : Float) :
    toFloat (ofFloat value : Binary64) = value := by
  cases value with
  | ofModel model =>
      change Float.ofModel (Model.toFloatModel (Model.ofFloatModel model)) = _
      rw [Model.toFloatModel_ofFloatModel]

/-- Lean's binary64 NaN imports as FloatLib's canonical quiet NaN. -/
theorem toModel_ofFloat_nan :
    toModel (ofFloat Float.nan : Binary64) = Model.canonicalNaN FloatFormat.binary64 :=
  Model.ofFloatModel_nan

/-- Lean's binary64 infinity imports as FloatLib's positive infinity. -/
theorem toModel_ofFloat_inf :
    toModel (ofFloat Float.inf : Binary64) = Model.posInf FloatFormat.binary64 :=
  Model.ofFloatModel_inf

end FloatLib.Floats.ExecFloat.Binary
