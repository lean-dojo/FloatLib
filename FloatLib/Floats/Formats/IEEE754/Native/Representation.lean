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

Lean 4.34 exposes named NaN and infinity constants alongside the logical floating-point models
introduced in Lean 4.33. We're glad Lean is making more of this model available for proofs.
Here we connect those constants and the existing `ofFloat` / `toFloat` adapters to the same
packed-model proofs used for arithmetic and integer conversion.

Every native value round-trips exactly. In the other direction, a FloatLib word may carry a
NaN payload that Lean's model does not retain; `Model.canonicalizeModel` describes that change.
Finite values, infinities, and both signed zeros retain their bits.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open Formats.BinaryInterchange

/-! ## Binary32 -/

/-- Importing a native value reads the word in its logical binary32 model. -/
@[simp] theorem toModel_ofFloat32 (value : Float32) :
    toModel (ofFloat32 value) = Model.ofFloat32Model value.toModel :=
  rfl

/-- Exporting binary32 uses the shared packed-model conversion, including NaN normalization. -/
theorem toModel_toFloat32_eq (value : ExecFloat.Binary 8 23) :
    (toFloat32 value).toModel = Model.toFloat32Model (toModel value) :=
  rfl

/-- An imported native binary32 value already satisfies Lean's canonical-NaN invariant. -/
theorem isModelCanonical_ofFloat32 (value : Float32) :
    Model.IsModelCanonical (toModel (ofFloat32 value)) :=
  Model.isModelCanonical_ofFloat32Model value.toModel

/-- Every native binary32 value is recovered exactly after importing and exporting it. -/
@[simp] theorem toFloat32_ofFloat32 (value : Float32) :
    toFloat32 (ofFloat32 value) = value := by
  cases value with
  | ofModel model =>
      change Float32.ofModel (Model.toFloat32Model (Model.ofFloat32Model model)) = _
      rw [Model.toFloat32Model_ofFloat32Model]

/-- Lean 4.34's binary32 NaN imports as FloatLib's canonical quiet NaN. -/
theorem toModel_ofFloat32_nan :
    toModel (ofFloat32 Float32.nan) = Model.canonicalNaN FloatFormat.binary32 :=
  Model.ofFloat32Model_nan

/-- Lean 4.34's binary32 infinity imports as FloatLib's positive infinity. -/
theorem toModel_ofFloat32_inf :
    toModel (ofFloat32 Float32.inf) = Model.posInf FloatFormat.binary32 :=
  Model.ofFloat32Model_inf

/-! ## Binary64 -/

/-- Importing a native value reads the word in its logical binary64 model. -/
@[simp] theorem toModel_ofFloat (value : Float) :
    toModel (ofFloat value) = Model.ofFloatModel value.toModel :=
  rfl

/-- Exporting binary64 uses the shared packed-model conversion, including NaN normalization. -/
theorem toModel_toFloat_eq (value : ExecFloat.Binary 11 52) :
    (toFloat value).toModel = Model.toFloatModel (toModel value) :=
  rfl

/-- An imported native binary64 value already satisfies Lean's canonical-NaN invariant. -/
theorem isModelCanonical_ofFloat (value : Float) :
    Model.IsModelCanonical (toModel (ofFloat value)) :=
  Model.isModelCanonical_ofFloatModel value.toModel

/-- Every native binary64 value is recovered exactly after importing and exporting it. -/
@[simp] theorem toFloat_ofFloat (value : Float) :
    toFloat (ofFloat value) = value := by
  cases value with
  | ofModel model =>
      change Float.ofModel (Model.toFloatModel (Model.ofFloatModel model)) = _
      rw [Model.toFloatModel_ofFloatModel]

/-- Lean 4.34's binary64 NaN imports as FloatLib's canonical quiet NaN. -/
theorem toModel_ofFloat_nan :
    toModel (ofFloat Float.nan) = Model.canonicalNaN FloatFormat.binary64 :=
  Model.ofFloatModel_nan

/-- Lean 4.34's binary64 infinity imports as FloatLib's positive infinity. -/
theorem toModel_ofFloat_inf :
    toModel (ofFloat Float.inf) = Model.posInf FloatFormat.binary64 :=
  Model.ofFloatModel_inf

end FloatLib.Floats.ExecFloat.Binary
