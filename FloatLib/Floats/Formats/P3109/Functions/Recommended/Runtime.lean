/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Functions.Runtime

/-!
# The functions of IEEE 754-2019 clause 9.2 that the P3109 report does not list

The P3109 interim report v4.1 has the natural and base-two exponentials and logarithms, the
trigonometric and hyperbolic functions, `Sqrt`, `RSqrt` and `Hypot`. IEEE 754-2019 §9.2
recommends more: `exp10`, `exp2m1`, `exp10m1`, `log10`, `log2p1`, `log10p1`, `rootn`, `pown`,
`pow`, `powr` and `compound`. This module gives them for every P3109 format, as FloatLib
extensions outside the report: `Exp10`, `Exp2MinusOne`, `Exp10MinusOne`, `Log10`,
`Log2OnePlus`, `Log10OnePlus`, `Rootn`, `Cbrt`, `Pown`, `Pow`, `Powr` and `Compound`.

They are built as the functions of the report are. Exact dispatch on the closed operands
produces a finite `FunctionExpr`, an infinity or NaN, and `projectFunction` compares a finite
expression exactly at every rounding threshold of the destination, in every rounding mode and
saturation mode, with independent source and target formats. No intermediate value is rounded.

The special cases follow IEEE 754-2019 §9.2.1 under the conventions of the report: there is
one zero and one NaN, a NaN operand gives NaN, and a pole at zero gives NaN, as `Recip` and
`RSqrt` give at zero, because the sign of the infinity would depend on a sign that the zero
does not have. So `Pown`, `Rootn`, `Pow` and `Powr` of zero with a finite negative exponent or
degree are NaN, and so is `Compound` of -1 with a negative exponent. The logarithms send the
zero of their argument to negative infinity, as `Log`, `Log2` and `LogOnePlus` do.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Functions

/--
The exponential in a base above one, `base ^ x`, or `base ^ x - 1` with `minusOne`: zero or -1
at negative infinity and positive infinity at positive infinity.
-/
def exponential (base : Rat) (hbase : 1 < base) (minusOne : Bool) :
    NumericalValue Rat → NumericalValue FunctionExpr
  | .finite argument =>
      let power := FunctionExpr.power base argument (zero_le_one.trans hbase.le)
      .finite (if minusOne then .affine 1 (-1) power else power)
  | .infinity negative =>
      if negative then .finite (.rational (if minusOne then -1 else 0)) else .infinity false
  | .exceptional _ => .exceptional .nan

/--
The logarithm in a base above one of `x + offset`: negative infinity where `x + offset` is
zero, NaN below it and at negative infinity, and positive infinity at positive infinity.
-/
def logarithmIn (base : Rat) (hbase : 1 < base) (offset : Rat) :
    NumericalValue Rat → NumericalValue FunctionExpr
  | .finite argument =>
      if hpositive : 0 < argument + offset then
        .finite (.logb base (argument + offset) hbase hpositive)
      else if argument + offset = 0 then .infinity true
      else .exceptional .nan
  | .infinity negative => if negative then .exceptional .nan else .infinity false
  | .exceptional _ => .exceptional .nan

/--
The real root of degree `degree`, the reciprocal root for a negative degree. Degree zero and a
negative operand with an even degree are NaN. Zero gives zero for a positive degree and NaN for
a negative one, and an infinity gives an infinity for a positive degree and zero for a negative
one.
-/
def root (degree : Int) : NumericalValue Rat → NumericalValue FunctionExpr
  | .finite argument =>
      if degree = 0 then .exceptional .nan
      else if argument = 0 then
        if 0 < degree then .finite (.rational 0) else .exceptional .nan
      else if hpositive : 0 < argument then
        .finite (.power argument (1 / (degree : Rat)) hpositive.le)
      else if degree % 2 = 0 then .exceptional .nan
      else
        .finite (.affine (-1) 0
          (.power (-argument) (1 / (degree : Rat)) (neg_nonneg.mpr (le_of_not_gt hpositive))))
  | .infinity negative =>
      if degree = 0 then .exceptional .nan
      else if negative ∧ degree % 2 = 0 then .exceptional .nan
      else if degree < 0 then .finite (.rational 0)
      else .infinity negative
  | .exceptional _ => .exceptional .nan

/--
The integer power `x ^ exponent`: one for the exponent zero, the exact rational power of a
nonzero finite operand, zero at zero for a positive exponent and NaN for a negative one, and at
an infinity the infinity of the sign of the power for a positive exponent and zero for a
negative one.
-/
def integerPower (exponent : Int) : NumericalValue Rat → NumericalValue FunctionExpr
  | .finite argument =>
      if exponent = 0 then .finite (.rational 1)
      else if argument = 0 then
        if 0 < exponent then .finite (.rational 0) else .exceptional .nan
      else .finite (.rational (argument ^ exponent))
  | .infinity negative =>
      if exponent = 0 then .finite (.rational 1)
      else if exponent < 0 then .finite (.rational 0)
      else .infinity (negative && exponent % 2 != 0)
  | .exceptional _ => .exceptional .nan

/--
The power `x ^ y` of IEEE 754-2019 §9.2.1 on closed operands. A finite negative base needs an
integral exponent. An infinite exponent gives one for a base of magnitude one, and zero or
positive infinity as the magnitude of the base is below or above one.
-/
def power : NumericalValue Rat → NumericalValue Rat → NumericalValue FunctionExpr
  | .exceptional _, _ | _, .exceptional _ => .exceptional .nan
  | .finite base, .finite exponent =>
      if exponent = 0 then .finite (.rational 1)
      else if base = 0 then
        if 0 < exponent then .finite (.rational 0) else .exceptional .nan
      else if hpositive : 0 < base then .finite (.power base exponent hpositive.le)
      else if exponent.den = 1 then
        let magnitude :=
          FunctionExpr.power (-base) exponent (neg_nonneg.mpr (le_of_not_gt hpositive))
        .finite (if exponent.num % 2 = 0 then magnitude else .affine (-1) 0 magnitude)
      else .exceptional .nan
  | .finite base, .infinity negative =>
      if |base| = 1 then .finite (.rational 1)
      else if decide (1 < |base|) = !negative then .infinity false
      else .finite (.rational 0)
  | .infinity negative, .finite exponent =>
      if exponent = 0 then .finite (.rational 1)
      else if exponent < 0 then .finite (.rational 0)
      else .infinity (negative && decide (exponent.den = 1) && exponent.num % 2 != 0)
  | .infinity _, .infinity negative =>
      if negative then .finite (.rational 0) else .infinity false

/--
The power `x ^ y` as `exp (y * log x)` (IEEE 754-2019 `powr`) on closed operands: a negative
base is NaN, and so are zero to the power zero, an infinity to the power zero and one to an
infinite power.
-/
def positivePower : NumericalValue Rat → NumericalValue Rat → NumericalValue FunctionExpr
  | .exceptional _, _ | _, .exceptional _ => .exceptional .nan
  | .finite base, .finite exponent =>
      if hpositive : 0 < base then .finite (.power base exponent hpositive.le)
      else if base = 0 ∧ 0 < exponent then .finite (.rational 0)
      else .exceptional .nan
  | .finite base, .infinity negative =>
      if base < 0 ∨ base = 1 then .exceptional .nan
      else if decide (1 < base) = !negative then .infinity false
      else .finite (.rational 0)
  | .infinity negative, .finite exponent =>
      if negative ∨ exponent = 0 then .exceptional .nan
      else if 0 < exponent then .infinity false
      else .finite (.rational 0)
  | .infinity negative, .infinity exponentNegative =>
      if negative then .exceptional .nan
      else if exponentNegative then .finite (.rational 0)
      else .infinity false

/--
The compound interest `(1 + x) ^ exponent` of IEEE 754-2019 §9.2.1 on a closed operand: NaN
below -1, and at -1 zero for a positive exponent, one for the exponent zero and NaN for a
negative one.
-/
def compound (exponent : Int) : NumericalValue Rat → NumericalValue FunctionExpr
  | .finite argument =>
      if argument < -1 then .exceptional .nan
      else if argument = -1 then
        if exponent = 0 then .finite (.rational 1)
        else if 0 < exponent then .finite (.rational 0)
        else .exceptional .nan
      else .finite (.rational ((1 + argument) ^ exponent))
  | .infinity negative =>
      if negative then .exceptional .nan
      else if exponent = 0 then .finite (.rational 1)
      else if 0 < exponent then .infinity false
      else .finite (.rational 0)
  | .exceptional _ => .exceptional .nan

end FloatLib.Floats.Formats.P3109.Functions

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

variable {format : Format}

/-- IEEE 754-2019 §9.2 `exp10`: the exact `10 ^ x`, projected once into `target`. -/
@[inline] def Exp10 (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.exponential 10 (by decide) false input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `exp2m1`: the exact `2 ^ x - 1`, projected once into `target`. -/
@[inline] def Exp2MinusOne (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.exponential 2 (by decide) true input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `exp10m1`: the exact `10 ^ x - 1`, projected once into `target`. -/
@[inline] def Exp10MinusOne (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.exponential 10 (by decide) true input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `log10`: the base-ten logarithm, zero to negative infinity and
negatives to NaN. -/
@[inline] def Log10 (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.logarithmIn 10 (by decide) 0 input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `log2p1`: the base-two logarithm of the exact `1 + x`. -/
@[inline] def Log2OnePlus (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.logarithmIn 2 (by decide) 1 input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `log10p1`: the base-ten logarithm of the exact `1 + x`. -/
@[inline] def Log10OnePlus (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.logarithmIn 10 (by decide) 1 input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `rootn`: the real root of degree `degree`, the reciprocal root for a
negative degree, projected once into `target`. -/
@[inline] def Rootn (input : ExecFloat.P3109 format) (degree : Int) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.root degree input.toClosedRat) mode saturation

/-- The cube root, `Rootn` of degree three: defined for every finite operand. -/
@[inline] def Cbrt (input : ExecFloat.P3109 format) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  Rootn input 3 target mode saturation

/-- IEEE 754-2019 §9.2 `pown`: the exact integer power `x ^ exponent`, projected once into
`target`. -/
@[inline] def Pown (input : ExecFloat.P3109 format) (exponent : Int) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.integerPower exponent input.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `pow`: the exact `x ^ y`, with independent formats of the base, the
exponent and the result, projected once into `target`. -/
@[inline] def Pow {exponentFormat : Format} (base : ExecFloat.P3109 format)
    (exponent : ExecFloat.P3109 exponentFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.power base.toClosedRat exponent.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `powr`: the exact `x ^ y` as `exp (y * log x)`, for a nonnegative base,
projected once into `target`. -/
@[inline] def Powr {exponentFormat : Format} (base : ExecFloat.P3109 format)
    (exponent : ExecFloat.P3109 exponentFormat) (target : Format := format)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 target :=
  projectFunction (Functions.positivePower base.toClosedRat exponent.toClosedRat) mode saturation

/-- IEEE 754-2019 §9.2 `compound`: the exact `(1 + x) ^ exponent`, projected once into
`target`. -/
@[inline] def Compound (input : ExecFloat.P3109 format) (exponent : Int)
    (target : Format := format) (mode : RoundingMode := .nearest)
    (saturation : SaturationMode := .none) : ExecFloat.P3109 target :=
  projectFunction (Functions.compound exponent input.toClosedRat) mode saturation

end FloatLib.Floats.ExecFloat.P3109
