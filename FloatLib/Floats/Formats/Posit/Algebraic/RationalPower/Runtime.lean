/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Runtime

/-!
# Once-rounded powers with rational exponents

Powers are compared with rational posit boundaries by `RationalPower.compare`. It decides
equality with a boundary exactly, from the exact-root classification of the power and capped
exponentiation, and separates every other boundary with logarithm enclosures of increasing
degree. No boundary is raised to a power, and the base's root is raised to the exponent's
numerator only by capped exponentiation, which stops once a partial power exceeds the boundary's
numerator or denominator. Large exponent numerators and denominators create no large integers.
A negative base with an integral exponent uses the same magnitude comparison and takes its sign
from the exponent's parity. Integer exponents of magnitude at most the posit width use exact
rational exponentiation, so simple integer powers do not pay for logarithm intervals.

The minus-one exponentials compare the power with `candidate + 1`. Thus subtraction is fused:
the power is never first rounded to a posit, even when the result is very close to zero.

NaR propagates. Zero to a nonpositive exponent produces NaR. A negative base requires an integral
exponent, because every other dyadic exponent gives a nonreal power. Finite posit exponents are
dyadic, so this condition covers the real domain for negative posit bases.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 4.1, 5.1, 5.5 and 5.6 (including footnote 10),
  <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/--
Round a positive-base rational power using exact comparisons with rational boundaries.
The real semantics require `0 < base`. Small integer exponents are evaluated exactly, and other
exponents use the exact rational-power comparator.
-/
@[noinline] def roundPositiveRatPower (format : Format) (base exponent : Rat) : Model format :=
  if exponent.den = 1 ∧ exponent.num.natAbs ≤ format.bits then
    roundRat format (base ^ exponent.num)
  else
    ComparisonRounding.round format (FloatLib.Numerics.RationalPower.compare base exponent)

/--
Round an exact rational power once. Negative bases require integral exponents, and zero
requires a positive exponent. A negative base rounds its magnitude and restores the sign.
-/
@[noinline] def roundRatPower (format : Format) (base exponent : Rat) : Model format :=
  if base = 0 then
    if 0 < exponent then zero format else nar format
  else if base = 1 then
    roundRat format 1
  else if base < 0 then
    if exponent.den = 1 then
      let magnitude := roundPositiveRatPower format (-base) exponent
      if exponent.num % 2 = 0 then magnitude else neg magnitude
    else nar format
  else
    roundPositiveRatPower format base exponent

/--
General posit power with one final rounding and standard NaR propagation. Boundary comparisons
are exact.
-/
@[inline] def pow {format : Format} (base exponent : Model format) : Model format :=
  match base.toRat?, exponent.toRat? with
  | some b, some e => roundRatPower format b e
  | _, _ => nar format

/-- Base-two exponential, rounded once using exact rational-power comparisons. -/
@[inline] def exp2 {format : Format} (value : Model format) : Model format :=
  match value.toRat? with
  | some e => roundRatPower format 2 e
  | none => nar format

/-- Base-ten exponential, rounded once using exact rational-power comparisons. -/
@[inline] def exp10 {format : Format} (value : Model format) : Model format :=
  match value.toRat? with
  | some e => roundRatPower format 10 e
  | none => nar format

/--
Round a positive-base power minus one with a single signed rounding.
The real semantics require `0 < base`. Shifting the candidates by one keeps the cancellation
exact.
Small integer exponents use exact rational exponentiation and subtraction before rounding.
-/
@[noinline] def roundRatPowerMinusOne (format : Format) (base exponent : Rat) : Model format :=
  if exponent.den = 1 ∧ exponent.num.natAbs ≤ format.bits then
    roundRat format (base ^ exponent.num - 1)
  else
    ComparisonRounding.roundSigned format
      (fun candidate => FloatLib.Numerics.RationalPower.compare base exponent (candidate + 1))

/-- Base-two exponential minus one, with fused subtraction and NaR propagation. -/
@[inline] def exp2Minus1 {format : Format} (value : Model format) : Model format :=
  match value.toRat? with
  | some e => roundRatPowerMinusOne format 2 e
  | none => nar format

/-- Base-ten exponential minus one, with fused subtraction and NaR propagation. -/
@[inline] def exp10Minus1 {format : Format} (value : Model format) : Model format :=
  match value.toRat? with
  | some e => roundRatPowerMinusOne format 10 e
  | none => nar format

end FloatLib.Floats.Formats.Posit.Model
