/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.PowerProof
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public meta import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Extension

/-!
# Opt-in transcendentals for configured binary values

This module gives `ExecFloat.Binary` deterministic `exp`, `log`, `sin`, `cos`, `sinCos`, `sinh`,
`cosh` and `tanh` approximations, the floating-point power `pow`, and the `MathFunctions`
instance. The approximations carry no general real-error bound. They use nearest-even arithmetic
and IEEE-style exceptional values, and the lifting theorems below carry the model results through
packing. `pow` is `Model.pow`, which is correctly rounded in the cases its documentation states
and approximate otherwise.

Two other namespaces hold functions with different result types and guarantees.
`ExecFloat.Binary.Certified` has certified searches for `exp`, `log`, `pow`, `expMinus1` and
`logPlus1`. Each refines rational enclosures of the real function within its `budget` and returns
`Except Certified.Failure Value`. That is a result proved finite and equal to nearest-even
rounding of the real function, or the reason there is none (an unsupported format, a nonfinite
input, a domain or range failure, or a search that did not settle). A search can fail on a valid
input, and it never falls back to the approximation. `Certified.expMinus1` and
`Certified.logPlus1` form `exp x - 1` and `log (1 + x)` before rounding, so they keep small
results near zero.

The module also imports `Configured.CorrectlyRounded`, whose `CorrectlyRounded.exp`, `log`,
`expMinus1`, `logPlus1` and `expMul` always return a value. For an IEEE descriptor and a finite
input in the domain, a finite result is the nearest-even rounding of the real function. A
non-finite input is outside that statement: `exp (-∞)` is a finite zero. `sin`, `cos`, `sinCos`,
`sinh`, `cosh` and `tanh` exist only as approximations.

Since the `MathFunctions` instance uses the approximation kernels, generic code that should get
the correctly rounded `exp` and `log` on IEEE descriptors has to opt in. There are two ways. After
`open scoped FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`, the instance in
that scope is `CorrectlyRounded.mathFunctions`. A library that builds its own dictionary passes
`CorrectlyRounded.mathFunctions` by name, for example as the `MathFunctions` parent of its own
class instance. `CorrectlyRounded.mathFunctions_exp_of_isIEEE` and `mathFunctions_log_of_isIEEE`
then identify its `exp` and `log` with `CorrectlyRounded.exp` and `CorrectlyRounded.log`, whose
theorems apply. Either way `sin`, `cos`, `sinh`, `cosh` and `tanh` stay the approximations, and a
descriptor other than IEEE keeps the approximate `exp` and `log`.

```lean
ExecFloat.Binary.Certified.exp x
ExecFloat.Binary.Certified.pow x y (budget := { maxAttempts := 32 })
```

Sine and cosine reduce their arguments by the Payne-Hanek reduction of
`Numerics.Enclosure.ArgumentReduction`, reading at most `2^21` bits of `2 / pi`. In a format with
at most 524,258 fraction bits, every finite argument below `2^(2^20)` stays within that limit.
Arguments that would need more bits, such as the largest ones of a 31-bit exponent field, give the
format's invalid result, and so do reductions whose permitted windows are all rejected. These APIs
return no IEEE status flags. The optional Arb adapter supports directed rounding through an
external library.

With `import FloatLib`, binary elementary functions stay opt-in. Certified `sqrt` and `abs`, the
`MathFunctions` class, and its host `Float` and real instances are available by default.

Finally, the module registers the default instance with `roundoff`: its methods decode through the
model functions, and a finite value has a finite absolute value.
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
An approximation to `eˣ` in the configured binary format, with no general error bound.
`Certified.exp` is the certified search, which can fail, and `CorrectlyRounded.exp` the correctly
rounded exponential.
-/
@[inline] def exp (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp value

/--
An approximation to the natural logarithm in the configured binary format, with no general error
bound. `Certified.log` is the certified search, which can fail, and `CorrectlyRounded.log` the
correctly rounded logarithm.
-/
@[inline] def log (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.log value

/--
The power `base ^ exponent` by `Model.pow`, with no general error bound.

Zeros, infinities and NaNs get their IEEE 754 special cases. For an IEEE descriptor, a finite
result for a nonzero base and an integral exponent is correctly rounded, and a positive base with
any other exponent runs the certified search first. A certified range failure gives positive
overflow, and other failures fall back to `exp (exponent * log base)`. `Certified.pow` runs only
the search, for a finite positive base and a finite exponent, and returns its failure instead
of falling back.
-/
@[inline] def pow (base exponent : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.pow base exponent

/-- A deterministic approximation to sine, with no general error bound. -/
@[inline] def sin
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sin value

/-- A deterministic approximation to cosine, with no general error bound. -/
@[inline] def cos
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cos value

/--
Approximate sine and cosine together, with no general error bound, sharing argument reduction
before repacking both results.
-/
@[inline] def sinCos
    (value : Value) : Value × Value :=
  let result := Model.sinCos (toModel value)
  (ofModel result.1, ofModel result.2)

/-- A deterministic approximation to hyperbolic sine, with no general error bound. -/
@[inline] def sinh
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sinh value

/-- A deterministic approximation to hyperbolic cosine, with no general error bound. -/
@[inline] def cosh
    (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.cosh value

/-- A deterministic approximation to hyperbolic tangent, with no general error bound. -/
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
`CorrectlyRounded.mathFunctions` is the same dictionary with correctly rounded `exp` and `log`.
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

namespace CorrectlyRounded

/--
The `MathFunctions` dictionary with correctly rounded `exp` and `log`. For an IEEE descriptor
they are `CorrectlyRounded.exp` and `CorrectlyRounded.log` with the default budget, and otherwise
the approximation kernels. The other fields are those of the default instance: `sqrt` and `abs`
are the certified operations, `pi` is `Model.pi`, and `sin`, `cos`, `sinh`, `cosh`, and `tanh`
are the approximations. Pass it where a dictionary is expected, or select it as the instance
with `open scoped FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`.
-/
@[instance_reducible] def mathFunctions :
    MathFunctions (ExecFloat (Configured.Family format code plan)) where
  exp := fun value =>
    if format.isIEEE then CorrectlyRounded.exp value else ExecFloat.Binary.exp value
  tanh := ExecFloat.Binary.tanh
  cosh := ExecFloat.Binary.cosh
  sqrt := ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.sqrt
  abs := ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.abs
  log := fun value =>
    if format.isIEEE then CorrectlyRounded.log value else ExecFloat.Binary.log value
  pi := ofModel (Model.pi format)
  cos := ExecFloat.Binary.cos
  sin := ExecFloat.Binary.sin
  sinh := ExecFloat.Binary.sinh

/-- For an IEEE descriptor, the `exp` of `mathFunctions` is the correctly rounded exponential. -/
theorem mathFunctions_exp_of_isIEEE (value : Value)
    (hformat : format.isIEEE = true := by ieee_format) :
    MathFunctions.exp (self := mathFunctions) value = CorrectlyRounded.exp value :=
  ite_eq_left hformat

/-- For an IEEE descriptor, the `log` of `mathFunctions` is the correctly rounded logarithm. -/
theorem mathFunctions_log_of_isIEEE (value : Value)
    (hformat : format.isIEEE = true := by ieee_format) :
    MathFunctions.log (self := mathFunctions) value = CorrectlyRounded.log value :=
  ite_eq_left hformat

end CorrectlyRounded

/-- The absolute value that this module's `MathFunctions` instance computes keeps a configured
value finite. -/
theorem isFinite_abs {value : Value} (hvalue : isFinite value = true) :
    isFinite (MathFunctions.abs value) = true := by
  have decoded : toModel (MathFunctions.abs value) = Model.abs (toModel value) :=
    ModelCodec.decode_liftUnary Model.abs value
  change Model.isFinite (toModel (MathFunctions.abs value)) = true
  rw [decoded, Model.isFinite_abs]
  exact hvalue

attribute [roundoff_rule] isFinite_abs

/-! ## Certified searches -/

namespace Certified

/--
Certify the exponential in the configured binary format, searching within `budget`: a finite
result equal to nearest-even rounding of `eˣ`, or the `Certified.Failure` that prevented one. A
search can fail on a valid input, and it never falls back to an approximation.
-/
@[inline] def exp (value : Value) (budget : Certified.Budget := {}) :
    Except Certified.Failure Value :=
  (Model.Transcendentals.Certified.exp (toModel value) budget).map ofModel

/--
Certify the natural logarithm in the configured binary format, searching within `budget`: a
finite result equal to nearest-even rounding of the real logarithm, or the `Certified.Failure`
that prevented one. A search can fail on a valid input, and it never falls back to an
approximation.
-/
@[inline] def log (value : Value) (budget : Certified.Budget := {}) :
    Except Certified.Failure Value :=
  (Model.Transcendentals.Certified.log (toModel value) budget).map ofModel

/--
Certify `base ^ exponent` for a finite positive base and a finite exponent, searching within
`budget`: a finite result equal to nearest-even rounding of the real power, or the
`Certified.Failure` that prevented one. Unlike the plain `pow`, it has no fallback.
-/
@[inline] def pow (base exponent : Value) (budget : Certified.Budget := {}) :
    Except Certified.Failure Value :=
  (Model.Transcendentals.Certified.pow (toModel base) (toModel exponent) budget).map ofModel

/--
Certify `exp x - 1` with one final rounding, preserving signed zero, searching within `budget`:
a finite nearest-even result or the `Certified.Failure` that prevented one.
`CorrectlyRounded.expMinus1` always returns a value.
-/
@[inline] def expMinus1 (value : Value) (budget : Certified.Budget := {}) :
    Except Certified.Failure Value :=
  (Model.Transcendentals.Certified.expMinus1 (toModel value) budget).map ofModel

/--
Certify `log (1 + x)` with one final rounding, preserving signed zero, searching within `budget`:
a finite nearest-even result or the `Certified.Failure` that prevented one.
`CorrectlyRounded.logPlus1` always returns a value.
-/
@[inline] def logPlus1 (value : Value) (budget : Certified.Budget := {}) :
    Except Certified.Failure Value :=
  (Model.Transcendentals.Certified.logPlus1 (toModel value) budget).map ofModel

/-- Decoding a certified exponential gives the model search's result or failure. -/
@[simp] theorem map_toModel_exp (value : Value) (budget : Certified.Budget) :
    (Certified.exp value budget).map toModel =
      Model.Transcendentals.Certified.exp (toModel value) budget := by
  cases h : Model.Transcendentals.Certified.exp (toModel value) budget <;>
    simp [Certified.exp, h, Except.map]

/-- Decoding a certified logarithm gives the model search's result or failure. -/
@[simp] theorem map_toModel_log (value : Value) (budget : Certified.Budget) :
    (Certified.log value budget).map toModel =
      Model.Transcendentals.Certified.log (toModel value) budget := by
  cases h : Model.Transcendentals.Certified.log (toModel value) budget <;>
    simp [Certified.log, h, Except.map]

/-- Decoding a certified power gives the model search's result or failure. -/
@[simp] theorem map_toModel_pow (base exponent : Value) (budget : Certified.Budget) :
    (Certified.pow base exponent budget).map toModel =
      Model.Transcendentals.Certified.pow (toModel base) (toModel exponent) budget := by
  cases h : Model.Transcendentals.Certified.pow (toModel base) (toModel exponent) budget <;>
    simp [Certified.pow, h, Except.map]

/-- Decoding a certified `expMinus1` gives the model search's result or failure. -/
@[simp] theorem map_toModel_expMinus1 (value : Value) (budget : Certified.Budget) :
    (Certified.expMinus1 value budget).map toModel =
      Model.Transcendentals.Certified.expMinus1 (toModel value) budget := by
  cases h : Model.Transcendentals.Certified.expMinus1 (toModel value) budget <;>
    simp [Certified.expMinus1, h, Except.map]

/-- Decoding a certified `logPlus1` gives the model search's result or failure. -/
@[simp] theorem map_toModel_logPlus1 (value : Value) (budget : Certified.Budget) :
    (Certified.logPlus1 value budget).map toModel =
      Model.Transcendentals.Certified.logPlus1 (toModel value) budget := by
  cases h : Model.Transcendentals.Certified.logPlus1 (toModel value) budget <;>
    simp [Certified.logPlus1, h, Except.map]

/-- A certified exponential is finite. -/
theorem isFinite_of_exp_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.exp value budget = Except.ok result) :
    isFinite result = true :=
  Model.Transcendentals.Certified.isFinite_of_exp_eq_ok
    (by rw [← map_toModel_exp value budget, hresult]; rfl)

/-- A certified exponential is the nearest-even rounding of the real exponential. -/
theorem toReal_of_exp_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.exp value budget = Except.ok result) :
    toReal result = Model.roundAt format (Real.exp (toReal value)) :=
  Model.Transcendentals.Certified.toReal_of_exp_eq_ok
    (by rw [← map_toModel_exp value budget, hresult]; rfl)

/-- A certified logarithm is finite. -/
theorem isFinite_of_log_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.log value budget = Except.ok result) :
    isFinite result = true :=
  Model.Transcendentals.Certified.isFinite_of_log_eq_ok
    (by rw [← map_toModel_log value budget, hresult]; rfl)

/-- A certified logarithm is the nearest-even rounding of the real logarithm. -/
theorem toReal_of_log_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.log value budget = Except.ok result) :
    toReal result = Model.roundAt format (Real.log (toReal value)) :=
  Model.Transcendentals.Certified.toReal_of_log_eq_ok
    (by rw [← map_toModel_log value budget, hresult]; rfl)

/-- A certified power is finite. -/
theorem isFinite_of_pow_eq_ok {base exponent result : Value} {budget : Certified.Budget}
    (hresult : Certified.pow base exponent budget = Except.ok result) :
    isFinite result = true :=
  Model.Transcendentals.Certified.isFinite_of_pow_eq_ok
    (by rw [← map_toModel_pow base exponent budget, hresult]; rfl)

/--
A certified power is the nearest-even rounding of the real power `toReal base ^ toReal exponent`
(`Real.rpow`, since the base of a certified power is positive).
-/
theorem toReal_of_pow_eq_ok {base exponent result : Value} {budget : Certified.Budget}
    (hresult : Certified.pow base exponent budget = Except.ok result) :
    toReal result = Model.roundAt format (toReal base ^ toReal exponent) :=
  Model.Transcendentals.Certified.toReal_of_pow_eq_ok
    (by rw [← map_toModel_pow base exponent budget, hresult]; rfl)

/-- A certified `expMinus1` result is finite. -/
theorem isFinite_of_expMinus1_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.expMinus1 value budget = Except.ok result) :
    isFinite result = true :=
  Model.Transcendentals.Certified.isFinite_of_expMinus1_eq_ok
    (by rw [← map_toModel_expMinus1 value budget, hresult]; rfl)

/-- A certified `expMinus1` result is one nearest-even rounding of `Real.exp x - 1`. -/
theorem toReal_of_expMinus1_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.expMinus1 value budget = Except.ok result) :
    toReal result = Model.roundAt format (Real.exp (toReal value) - 1) :=
  Model.Transcendentals.Certified.toReal_of_expMinus1_eq_ok
    (by rw [← map_toModel_expMinus1 value budget, hresult]; rfl)

/-- A certified `logPlus1` result is finite. -/
theorem isFinite_of_logPlus1_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.logPlus1 value budget = Except.ok result) :
    isFinite result = true :=
  Model.Transcendentals.Certified.isFinite_of_logPlus1_eq_ok
    (by rw [← map_toModel_logPlus1 value budget, hresult]; rfl)

/-- A certified `logPlus1` result is one nearest-even rounding of `Real.log (1 + x)`. -/
theorem toReal_of_logPlus1_eq_ok {value result : Value} {budget : Certified.Budget}
    (hresult : Certified.logPlus1 value budget = Except.ok result) :
    toReal result = Model.roundAt format (Real.log (1 + toReal value)) :=
  Model.Transcendentals.Certified.toReal_of_logPlus1_eq_ok
    (by rw [← map_toModel_logPlus1 value budget, hresult]; rfl)

end Certified

end FloatLib.Floats.ExecFloat.Binary

namespace FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath

open FloatLib.Numerics FloatLib.Floats

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
    [ExecFloat.ModelCodec plan (Model format) code]

/--
Make `ExecFloat.Binary.CorrectlyRounded.mathFunctions` the `MathFunctions` instance of configured
binary values, so generic code gets the correctly rounded `exp` and `log` on IEEE descriptors.
-/
scoped instance (priority := high) configured :
    MathFunctions (ExecFloat (Configured.Family format code plan)) :=
  ExecFloat.Binary.CorrectlyRounded.mathFunctions

end FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

/-- The configured `MathFunctions` for `roundoff`: its methods decode through the model
functions. A method gets the contract of a correctly rounded primitive when its selected
implementation unfolds to that primitive's call, or through a registered implementation equality
(`Extension.bridges`). `CorrectlyRounded.mathFunctions` selects the primitive only for an IEEE
descriptor, so a client that uses it registers `CorrectlyRounded.mathFunctions_exp_of_isIEEE` and
`mathFunctions_log_of_isIEEE` itself as bridges. -/
def mathFunctions : Extension where
  decodingRewrites := #[``ExecFloat.Binary.toModel_exp, ``ExecFloat.Binary.toModel_log]
  decodeLemmas := #[``ExecFloat.Binary.toModel_exp, ``ExecFloat.Binary.toModel_log,
    ``ExecFloat.Binary.toModel_pow]

attribute [roundoff_extension] mathFunctions

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
