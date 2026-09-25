/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals.Certified
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Opt-in transcendentals for configured binary values

This module adds deterministic `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, and `tanh`
approximations and the `MathFunctions` instance to `ExecFloat.Binary`. The lifting theorems below
preserve the model results through packing. These kernels use nearest-even arithmetic and
IEEE-style exceptional values; they carry no general real-error bound.

`Binary.Certified.exp`, `log`, `expMinus1`, and `logPlus1` use rational enclosure refinement and
return `Option Value`. Every accepted result is proved finite and equal to nearest-even rounding
of the real function. The latter two functions form `exp x - 1` and `log (1 + x)` before rounding,
retaining small results near zero. Import `Configured.Transcendentals.Certified` alone for this
focused API. The `MathFunctions` instance uses the approximation kernels above.

`sinCosResult` reports arguments beyond the trigonometric reduction budget. Value-only sine and
cosine use the format's invalid result on failure. These APIs return no IEEE status flags;
the optional Arb adapter supports explicit rounding directions through an external library.

`import FloatLib` keeps binary elementary functions opt-in. Certified `sqrt` and `abs`, the
`MathFunctions` class, and its host `Float` and real instances are available by default.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/-- Deterministic approximation to `eˣ` in the configured binary format. -/
@[inline] def exp
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp value

/-- Deterministic approximation to the natural logarithm in the configured binary format. -/
@[inline] def log
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log value

/-- Deterministic approximation to sine in the configured binary format. -/
@[inline] def sin
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sin value

/-- Deterministic approximation to cosine in the configured binary format. -/
@[inline] def cos
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cos value

/--
Compute sine and cosine together, sharing argument reduction before repacking both results.
-/
@[inline] def sinCos
    (value : Value) : Value × Value :=
  let result := Model.sinCos (toModel value)
  (ofModel result.1, ofModel result.2)

/-- Joint sine/cosine evaluation preserving the model's explicit reduction-budget failure. -/
@[inline] def sinCosResult (value : Value) :
    Except Model.Transcendentals.TrigReductionError (Value × Value) :=
  (Model.sinCosResult (toModel value)).map fun result =>
    (ofModel result.1, ofModel result.2)

/-- Deterministic approximation to hyperbolic sine in the configured binary format. -/
@[inline] def sinh
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sinh value

/-- Deterministic approximation to hyperbolic cosine in the configured binary format. -/
@[inline] def cosh
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cosh value

/-- Deterministic approximation to hyperbolic tangent in the configured binary format. -/
@[inline] def tanh
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.tanh value

/-! ## Representation bridge theorems -/

/-- Decoding configured exponential exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_exp (value : Value) :
    toModel (exp value) = Model.exp (toModel value) := by
  simp [exp, toModel, Configured.Family.toModel]

/-- Decoding configured logarithm exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_log (value : Value) :
    toModel (log value) = Model.log (toModel value) := by
  simp [log, toModel, Configured.Family.toModel]

/-- Decoding configured sine exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_sin (value : Value) :
    toModel (sin value) = Model.sin (toModel value) := by
  simp [sin, toModel, Configured.Family.toModel]

/-- Decoding configured cosine exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_cos (value : Value) :
    toModel (cos value) = Model.cos (toModel value) := by
  simp [cos, toModel, Configured.Family.toModel]

/-- Decoding joint sine/cosine exposes both results of the shared model kernel. -/
@[simp, grind =] theorem toModel_sinCos (value : Value) :
    (toModel (sinCos value).1, toModel (sinCos value).2) =
      Model.sinCos (toModel value) := by
  simp [sinCos]

/-- Decoding a checked result preserves both the selected values and any reduction-budget error. -/
@[simp, grind =] theorem toModel_sinCosResult (value : Value) :
    (sinCosResult value).map (fun result => (toModel result.1, toModel result.2)) =
      Model.sinCosResult (toModel value) := by
  cases h : Model.sinCosResult (toModel value) <;> simp [sinCosResult, h, Except.map]

/-- Decoding configured hyperbolic sine exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_sinh (value : Value) :
    toModel (sinh value) = Model.sinh (toModel value) := by
  simp [sinh, toModel, Configured.Family.toModel]

/-- Decoding configured hyperbolic cosine exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_cosh (value : Value) :
    toModel (cosh value) = Model.cosh (toModel value) := by
  simp [cosh, toModel, Configured.Family.toModel]

/-- Decoding configured hyperbolic tangent exposes the deterministic model kernel exactly. -/
@[simp, grind =] theorem toModel_tanh (value : Value) :
    toModel (tanh value) = Model.tanh (toModel value) := by
  simp [tanh, toModel, Configured.Family.toModel]

/--
Configured binary values implement the shared elementary-function interface.

This lets generic programs use `MathFunctions.exp`, `MathFunctions.sin`, and the other operations
without knowing the binary descriptor. `sqrt` and `abs` here are the certified operations already
on the default import; the remaining fields have the same approximation boundary as the named
functions above.
-/
instance : MathFunctions (ExecFloat (Configured.Family format code plan)) where
  exp := exp
  tanh := tanh
  cosh := cosh
  sqrt := ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sqrt
  abs := ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.abs
  log := log
  pi := ofModel (Model.pi format)
  cos := cos
  sin := sin
  sinh := sinh

end FloatLib.Floats.ExecFloat.Binary
