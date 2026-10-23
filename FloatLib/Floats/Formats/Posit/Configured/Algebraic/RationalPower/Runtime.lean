/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Algebraic.RationalPower.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Value.Runtime

/-!
# Configured once-rounded powers and exponentials

These codec adapters forward to the exactly rounded model implementations of `pow`, `exp2`,
`exp10`, and their fused minus-one forms. Carrier selection adds no rounding.

The model kernels decide equality with a rounding boundary exactly and separate the other cases
with certified logarithm enclosures. They raise the base's root to the exponent's numerator only by
exponentiation capped against the boundary, so large exponents create no large integers. Small
integer exponents use exact rational arithmetic before the single final rounding.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

local notation "Value" =>
  FloatLib.Floats.ExecFloat (Configured.Family format code plan)

/--
Exactly rounded power. NaR propagates, zero requires a positive exponent, and negative
bases require integral exponents.
-/
@[inline] def pow (base exponent : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.pow base exponent

/-- Exactly rounded base-two exponential. NaR propagates. -/
@[inline] def exp2 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp2 value

/-- Exactly rounded base-ten exponential. NaR propagates. -/
@[inline] def exp10 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp10 value

/-- Base-two exponential minus one, rounded once after the subtraction. NaR propagates. -/
@[inline] def exp2Minus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp2Minus1 value

/-- Base-ten exponential minus one, rounded once after the subtraction. NaR propagates. -/
@[inline] def exp10Minus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp10Minus1 value

end ExecFloat.Posit
end FloatLib.Floats
