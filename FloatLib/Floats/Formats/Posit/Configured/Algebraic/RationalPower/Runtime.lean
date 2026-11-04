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

Configured `pow`, `exp2`, `exp10`, and their fused minus-one forms are codec adapters over the
correctly rounded model implementations, and choosing a carrier adds no rounding.

Most of the work happens in the model kernels. They decide exactly whether the result sits on a
rounding boundary, and when it doesn't, certified logarithm enclosures tell the cases apart. The
base's root is raised to the exponent's numerator only by exponentiation capped against the
boundary, so a large exponent never builds a large integer. Small integer exponents use exact
rational arithmetic before the single final rounding.
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
Correctly rounded power. NaR propagates, zero requires a positive exponent, and negative
bases require integral exponents.
-/
@[inline] def pow (base exponent : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.pow base exponent

/-- Correctly rounded base-two exponential. NaR propagates. -/
@[inline] def exp2 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp2 value

/-- Correctly rounded base-ten exponential. NaR propagates. -/
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
