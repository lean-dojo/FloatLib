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

Certified logarithm enclosures decide boundary comparisons before exact algebraic fallback.
Small integer exponents use direct exact rational arithmetic before the single final rounding.
Fallback cost depends on the numerical numerator and denominator of the decoded exponent;
there is no resource-bound completion guarantee.
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
bases require integral exponents. Inconclusive enclosures use exact comparison fallback.
-/
@[inline] def pow (base exponent : Value) : Value :=
  ModelCodec.liftBinary (Model := Model format) (plan := plan) Model.pow base exponent

/--
Exactly rounded base-two exponential; NaR propagates. Hard fallback cases can be expensive.
-/
@[inline] def exp2 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp2 value

/--
Exactly rounded base-ten exponential; NaR propagates. Hard fallback cases can be expensive.
-/
@[inline] def exp10 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp10 value

/-- Base-two exponential minus one, with a single rounding after subtraction; NaR propagates. -/
@[inline] def exp2Minus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp2Minus1 value

/-- Base-ten exponential minus one, with a single rounding after subtraction; NaR propagates. -/
@[inline] def exp10Minus1 (value : Value) : Value :=
  ModelCodec.liftUnary (Model := Model format) (plan := plan) Model.exp10Minus1 value

end ExecFloat.Posit
end FloatLib.Floats
