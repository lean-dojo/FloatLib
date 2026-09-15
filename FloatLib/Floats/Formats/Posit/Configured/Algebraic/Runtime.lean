/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.Power.Runtime
public import FloatLib.Floats.Formats.Posit.Algebraic.Root.Runtime
public import FloatLib.Floats.Formats.Posit.Algebraic.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured posit algebraic functions

These functions use the exact rational algebraic kernels through the selected carrier's model
codec. Storage selection does not introduce additional rounding. NaR and invalid real domains
have the same behavior as the model operations.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/-- Reciprocal square root, rounded once; nonpositive inputs and NaR produce NaR. -/
@[inline] def rSqrt (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.rSqrt value

/-- Euclidean hypotenuse, rounded once after an exact sum of squares; NaR propagates. -/
@[inline] def hypot (left right : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.hypot left right

/-- Fused triple multiplication, with one final rounding and NaR propagation. -/
@[inline] def fMM (left right third : Value) : Value :=
  ModelCodec.liftTernary (Model := Model format) (plan := plan) Model.fMM left right third

/--
Integer root, rounded once, taking the signed real root for odd degrees. Degree zero, even
roots of negative inputs, negative-degree roots of zero, and NaR inputs produce NaR.
-/
@[inline] def rootN (value : Value) (degree : Int) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun x => Model.rootN x degree) value

/-- Fixed integer power, rounded once; NaR and zero to negative powers produce NaR. -/
@[inline] def powInt (value : Value) (exponent : Int) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun x => Model.powInt x exponent) value

/--
Compound `(1 + x) ^ n`, rounding only the final result. NaR propagates, and `x = -1` with
negative exponent produces NaR. Exponent zero gives one on every finite input.
-/
@[inline] def compound (value : Value) (exponent : Int) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan)
    (fun x => Model.compound x exponent) value

end ExecFloat.Posit
end FloatLib.Floats
