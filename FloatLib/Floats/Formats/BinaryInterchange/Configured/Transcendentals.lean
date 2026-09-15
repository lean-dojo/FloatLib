/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Opt-in transcendentals for configured binary values

`import FloatLib` does not install `ExecFloat.Binary.exp`, `Model.exp`, `Model.pow`, or the
`MathFunctions` instances for configured and model binary values. The class and its host `Float`
and real instances are available without this module. Import this module to give `ExecFloat.Binary`
the deterministic elementary-function kernels (`exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`,
`tanh`) and the `MathFunctions` instance. Certified `sqrt` and `abs` stay on the default import;
this instance only republishes them for generic code.

These functions are deterministic approximations with IEEE-style handling of exceptional inputs.
The lifting theorems below say that packing does not change the selected model result; they do not
claim a real-error bound or correct rounding. Such claims require a separate certificate or proved
enclosure. The optional Arb-backed adapter has its own external-library trust boundary.

The functions use their configured internal approximation and nearest-even arithmetic; they do
not accept a per-call rounding direction or return IEEE status flags. `Configured.Rounding.Runtime`
provides directed rounding for the six primitive arithmetic operations, while the Arb adapter is
the current explicit-rounding path for transcendental point evaluation.

`sinCosResult` reports when an argument exceeds the default trigonometric reduction budget.
The value-only `sin`, `cos`, and `sinCos` operations return the format's invalid result in that
case. This resource failure is separate from IEEE status and from numerical accuracy certificates.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

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
instance : MathFunctions
    Value where
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
