/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.PowerProof
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof

/-!
# Opt-in transcendentals for configured binary values

This module adds deterministic `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`, `cosh`, and `tanh`
approximations, the floating-point power `pow`, and the `MathFunctions` instance to
`ExecFloat.Binary`. The lifting theorems below carry the model results through packing. These
kernels use nearest-even arithmetic and IEEE-style exceptional values. They carry no general
real-error bound.

Certification is an option. `exp x (certify := true)`, and likewise `log` and `pow`, refines
rational enclosures of the real function and returns `Except Certified.Failure Value`: either a
result proved finite and equal to nearest-even rounding of the real function, or the reason
there is none (an unsupported format, a nonfinite input, a domain or range failure, or a search
that did not settle within its `budget`). Once certification is requested there is no fallback to
the approximation. `expMinus1` and `logPlus1` exist only in certified form. They form `exp x - 1`
and `log (1 + x)` before rounding, retaining small results near zero. The `MathFunctions`
instance uses the approximation kernels.

```lean
ExecFloat.Binary.exp x (certify := true)
ExecFloat.Binary.pow x y (certify := true) (budget := { maxSteps := 32 })
```

Sine and cosine reduce their arguments by the Payne-Hanek reduction of
`Numerics.Enclosure.ArgumentReduction`, reading at most `2^21` bits of `2 / pi`. In a format with at
most 524,258 fraction bits, every finite argument below `2^(2^20)` stays within that limit.
Arguments that would need more bits, such as the largest ones of a 31-bit exponent field, and
reductions whose permitted windows are all rejected give the format's invalid result. These APIs
return no IEEE status flags. The optional Arb adapter supports directed rounding through an
external library.

`import FloatLib` keeps binary elementary functions opt-in. Certified `sqrt` and `abs`, the
`MathFunctions` class, and its host `Float` and real instances are available by default.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.Binary

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  ExecFloat.Binary format.expWidth format.fracWidth format.encoding format.exponentBias
    format.expWidth_ge_two format.fracWidth_pos format.exponentBias_pos
    format.exponentBias_le_maxFinite plan code

/--
The exponential `eˣ` in the configured binary format: by default the deterministic approximation,
and with `certify := true` a certified nearest-even result or the `Certified.Failure` that
prevented one, searching within `budget`.
-/
@[macro_inline] def exp (value : Value) (certify : Bool := false)
    (budget : Certified.Options := {}) :
    match certify with
    | true => Except Certified.Failure Value
    | false => Value :=
  match certify with
  | true => (Certified.exp (toModel value) budget).map ofModel
  | false => ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp value

/--
The natural logarithm in the configured binary format: by default the deterministic
approximation, and with `certify := true` a certified nearest-even result or the
`Certified.Failure` that prevented one, searching within `budget`.
-/
@[macro_inline] def log (value : Value) (certify : Bool := false)
    (budget : Certified.Options := {}) :
    match certify with
    | true => Except Certified.Failure Value
    | false => Value :=
  match certify with
  | true => (Certified.log (toModel value) budget).map ofModel
  | false => ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log value

/--
The power `base ^ exponent`, by `Model.pow` by default.

`Model.pow` gives zeros, infinities, and NaNs their IEEE 754 special cases. For an IEEE
descriptor, a finite result for a nonzero base and an integral exponent is correctly rounded, and
a positive base with any other exponent runs the certified search first, falling back to the
approximation `exp (exponent * log base)` when the search does not settle. With
`certify := true` only the certified search runs, for a finite positive base and a finite exponent,
and its failure is returned instead of the fallback.
-/
@[macro_inline] def pow (base exponent : Value) (certify : Bool := false)
    (budget : Certified.Options := {}) :
    match certify with
    | true => Except Certified.Failure Value
    | false => Value :=
  match certify with
  | true => (Certified.pow (toModel base) (toModel exponent) budget).map ofModel
  | false => ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.pow base exponent

/--
Certify `exp x - 1` with one final rounding, preserving signed zero, searching within `budget`.

There is no uncertified form: the result is a certified nearest-even value or the
`Certified.Failure` that prevented one.
-/
@[inline] def expMinus1 (value : Value) (budget : Certified.Options := {}) :
    Except Certified.Failure Value :=
  (Certified.expMinus1 (toModel value) budget).map ofModel

/--
Certify `log (1 + x)` with one final rounding, preserving signed zero, searching within `budget`.

There is no uncertified form: the result is a certified nearest-even value or the
`Certified.Failure` that prevented one.
-/
@[inline] def logPlus1 (value : Value) (budget : Certified.Options := {}) :
    Except Certified.Failure Value :=
  (Certified.logPlus1 (toModel value) budget).map ofModel

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

/-- Decoding configured exponential gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_exp (value : Value) :
    toModel (exp value) = Model.exp (toModel value) := by
  simp [exp, toModel, Configured.Family.toModel]

/-- Decoding configured logarithm gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_log (value : Value) :
    toModel (log value) = Model.log (toModel value) := by
  simp [log, toModel, Configured.Family.toModel]

/-- Decoding the configured power gives `Model.pow`. -/
@[simp, grind =] theorem toModel_pow (base exponent : Value) :
    toModel (pow base exponent) = Model.pow (toModel base) (toModel exponent) := by
  simp [pow, toModel, Configured.Family.toModel]

/-- Decoding configured sine gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_sin (value : Value) :
    toModel (sin value) = Model.sin (toModel value) := by
  simp [sin, toModel, Configured.Family.toModel]

/-- Decoding configured cosine gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_cos (value : Value) :
    toModel (cos value) = Model.cos (toModel value) := by
  simp [cos, toModel, Configured.Family.toModel]

/-- Decoding joint sine/cosine gives both results of the shared model kernel. -/
@[simp, grind =] theorem toModel_sinCos (value : Value) :
    (toModel (sinCos value).1, toModel (sinCos value).2) =
      Model.sinCos (toModel value) := by
  simp [sinCos]

/-- Decoding configured hyperbolic sine gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_sinh (value : Value) :
    toModel (sinh value) = Model.sinh (toModel value) := by
  simp [sinh, toModel, Configured.Family.toModel]

/-- Decoding configured hyperbolic cosine gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_cosh (value : Value) :
    toModel (cosh value) = Model.cosh (toModel value) := by
  simp [cosh, toModel, Configured.Family.toModel]

/-- Decoding configured hyperbolic tangent gives the deterministic model kernel. -/
@[simp, grind =] theorem toModel_tanh (value : Value) :
    toModel (tanh value) = Model.tanh (toModel value) := by
  simp [tanh, toModel, Configured.Family.toModel]

/--
Configured binary values implement the shared elementary-function interface.

This lets generic programs use `MathFunctions.exp`, `MathFunctions.sin`, and the other operations
without knowing the binary descriptor. `sqrt` and `abs` here are the certified operations already
on the default import. The remaining fields are the approximations defined above.
-/
instance : MathFunctions (ExecFloat (Configured.Family format code plan)) where
  exp := fun value => exp value
  tanh := tanh
  cosh := cosh
  sqrt := ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sqrt
  abs := ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.abs
  log := fun value => log value
  pi := ofModel (Model.pi format)
  cos := cos
  sin := sin
  sinh := sinh

/-! ## Certified results -/

section Certify

/-- Decoding a certified exponential gives the model kernel's result or failure. -/
@[simp] theorem map_toModel_exp_certify (value : Value) (budget : Certified.Options) :
    (exp value (certify := true) (budget := budget)).map toModel =
      Certified.exp (toModel value) budget := by
  cases h : Certified.exp (toModel value) budget <;> simp [exp, h, Except.map]

/-- Decoding a certified logarithm gives the model kernel's result or failure. -/
@[simp] theorem map_toModel_log_certify (value : Value) (budget : Certified.Options) :
    (log value (certify := true) (budget := budget)).map toModel =
      Certified.log (toModel value) budget := by
  cases h : Certified.log (toModel value) budget <;> simp [log, h, Except.map]

/-- Decoding a certified power gives the model kernel's result or failure. -/
@[simp] theorem map_toModel_pow_certify (base exponent : Value) (budget : Certified.Options) :
    (pow base exponent (certify := true) (budget := budget)).map toModel =
      Certified.pow (toModel base) (toModel exponent) budget := by
  cases h : Certified.pow (toModel base) (toModel exponent) budget <;>
    simp [pow, h, Except.map]

/-- Decoding `expMinus1` gives the model kernel's result or failure. -/
@[simp] theorem map_toModel_expMinus1 (value : Value) (budget : Certified.Options) :
    (expMinus1 value budget).map toModel = Certified.expMinus1 (toModel value) budget := by
  cases h : Certified.expMinus1 (toModel value) budget <;> simp [expMinus1, h, Except.map]

/-- Decoding `logPlus1` gives the model kernel's result or failure. -/
@[simp] theorem map_toModel_logPlus1 (value : Value) (budget : Certified.Options) :
    (logPlus1 value budget).map toModel = Certified.logPlus1 (toModel value) budget := by
  cases h : Certified.logPlus1 (toModel value) budget <;> simp [logPlus1, h, Except.map]

/-- A certified exponential is finite. -/
theorem isFinite_of_exp_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : exp value (certify := true) (budget := budget) = Except.ok result) :
    isFinite result = true :=
  Certified.isFinite_of_exp_eq_ok (by rw [← map_toModel_exp_certify value budget, hresult]; rfl)

/-- A certified exponential is the nearest-even rounding of the real exponential. -/
theorem toReal_of_exp_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : exp value (certify := true) (budget := budget) = Except.ok result) :
    toReal result = Model.roundAt format (Real.exp (toReal value)) :=
  Certified.toReal_of_exp_eq_ok (by rw [← map_toModel_exp_certify value budget, hresult]; rfl)

/-- A certified logarithm is finite. -/
theorem isFinite_of_log_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : log value (certify := true) (budget := budget) = Except.ok result) :
    isFinite result = true :=
  Certified.isFinite_of_log_eq_ok (by rw [← map_toModel_log_certify value budget, hresult]; rfl)

/-- A certified logarithm is the nearest-even rounding of the real logarithm. -/
theorem toReal_of_log_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : log value (certify := true) (budget := budget) = Except.ok result) :
    toReal result = Model.roundAt format (Real.log (toReal value)) :=
  Certified.toReal_of_log_eq_ok (by rw [← map_toModel_log_certify value budget, hresult]; rfl)

/-- A certified power is finite. -/
theorem isFinite_of_pow_eq_ok {base exponent result : Value} {budget : Certified.Options}
    (hresult : pow base exponent (certify := true) (budget := budget) = Except.ok result) :
    isFinite result = true :=
  Certified.isFinite_of_pow_eq_ok
    (by rw [← map_toModel_pow_certify base exponent budget, hresult]; rfl)

/--
A certified power is the nearest-even rounding of the real power `toReal base ^ toReal exponent`
(`Real.rpow`, since the base of a certified power is positive).
-/
theorem toReal_of_pow_eq_ok {base exponent result : Value} {budget : Certified.Options}
    (hresult : pow base exponent (certify := true) (budget := budget) = Except.ok result) :
    toReal result = Model.roundAt format (toReal base ^ toReal exponent) :=
  Certified.toReal_of_pow_eq_ok
    (by rw [← map_toModel_pow_certify base exponent budget, hresult]; rfl)

/-- A certified `expMinus1` result is finite. -/
theorem isFinite_of_expMinus1_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : expMinus1 value budget = Except.ok result) :
    isFinite result = true :=
  Certified.isFinite_of_expMinus1_eq_ok (by rw [← map_toModel_expMinus1 value budget, hresult]; rfl)

/-- A certified `expMinus1` result is one nearest-even rounding of `Real.exp x - 1`. -/
theorem toReal_of_expMinus1_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : expMinus1 value budget = Except.ok result) :
    toReal result = Model.roundAt format (Real.exp (toReal value) - 1) :=
  Certified.toReal_of_expMinus1_eq_ok (by rw [← map_toModel_expMinus1 value budget, hresult]; rfl)

/-- A certified `logPlus1` result is finite. -/
theorem isFinite_of_logPlus1_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : logPlus1 value budget = Except.ok result) :
    isFinite result = true :=
  Certified.isFinite_of_logPlus1_eq_ok (by rw [← map_toModel_logPlus1 value budget, hresult]; rfl)

/-- A certified `logPlus1` result is one nearest-even rounding of `Real.log (1 + x)`. -/
theorem toReal_of_logPlus1_eq_ok {value result : Value} {budget : Certified.Options}
    (hresult : logPlus1 value budget = Except.ok result) :
    toReal result = Model.roundAt format (Real.log (1 + toReal value)) :=
  Certified.toReal_of_logPlus1_eq_ok (by rw [← map_toModel_logPlus1 value budget, hresult]; rfl)

end Certify

end FloatLib.Floats.ExecFloat.Binary
