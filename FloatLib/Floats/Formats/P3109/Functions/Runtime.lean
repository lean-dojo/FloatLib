/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Projection.Comparison.Runtime
public meta import FloatLib.Tactic.P3109Functions
public import FloatLib.Floats.Formats.P3109.Arithmetic.Runtime
public import FloatLib.Numerics.Exact.Functions.Runtime

/-!
# P3109 closed elementary functions

P3109 interim report v4.1 (14 September 2026), §§4.10.9–4.10.16,
unapproved draft. Exact domain dispatch produces finite function expressions,
infinities or NaN. A finite expression is compared exactly at every destination
rounding threshold. Source and target formats remain independent.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Functions

/-- Unary elementary operations of P3109 interim report v4.1 §§4.10.9–4.10.13. -/
inductive Unary where
  /-- Natural logarithm, §4.10.9. -/
  | log
  /-- Base-two logarithm, §4.10.9. -/
  | log2
  /-- Natural logarithm after exact addition of one, §4.10.9. -/
  | logOnePlus
  /-- Exponential, §4.10.9. -/
  | exp
  /-- Base-two exponential, §4.10.9. -/
  | exp2
  /-- Exponential followed by exact subtraction of one, §4.10.9. -/
  | expMinusOne
  /-- Radian sine, §4.10.10. -/
  | sin
  /-- Radian cosine, §4.10.10. -/
  | cos
  /-- Radian tangent, §4.10.10. -/
  | tan
  /-- Principal inverse sine, §4.10.10. -/
  | arcSin
  /-- Principal inverse cosine, §4.10.10. -/
  | arcCos
  /-- Principal inverse tangent, §4.10.10. -/
  | arcTan
  /-- Hyperbolic sine, §4.10.11. -/
  | sinh
  /-- Hyperbolic cosine, §4.10.11. -/
  | cosh
  /-- Hyperbolic tangent, §4.10.11. -/
  | tanh
  /-- Inverse hyperbolic sine, §4.10.11. -/
  | arcSinh
  /-- Nonnegative inverse hyperbolic cosine, §4.10.11. -/
  | arcCosh
  /-- Inverse hyperbolic tangent, §4.10.11. -/
  | arcTanh
  /-- Pi-scaled sine, §4.10.12. -/
  | sinPi
  /-- Pi-scaled cosine, §4.10.12. -/
  | cosPi
  /-- Pi-scaled tangent, with signed infinities at poles, §4.10.12. -/
  | tanPi
  /-- Principal inverse sine divided by π, §4.10.12. -/
  | arcSinPi
  /-- Principal inverse cosine divided by π, §4.10.12. -/
  | arcCosPi
  /-- Principal inverse tangent divided by π, §4.10.12. -/
  | arcTanPi
  /-- Natural logarithm of one plus the exponential, §4.10.13. -/
  | softplus
  deriving DecidableEq, Repr

/-- Reconstruct a `Unary` constructor from its constructor index. -/
add_decl_doc Unary.ofNat_ctorIdx

/-- A rational multiple of π, or its coefficient for a pi-scaled function. -/
def angle (piScaled : Bool) (multiple : Rat) : FunctionExpr :=
  if piScaled then .rational multiple else .affine multiple 0 (.arg (-1) 0 false)

/-- Shared logarithm domain: zero is negative infinity and a negative argument is NaN. -/
def logarithm (baseTwo : Bool) (argument : Rat) : NumericalValue FunctionExpr :=
  if hpositive : 0 < argument then
    .finite (if baseTwo then .logb 2 argument (by decide) hpositive
      else .log argument hpositive)
  else if argument = 0 then .infinity true
  else .exceptional (.nan)

/-- Check the common closed unit domain before constructing inverse sine or cosine. -/
def onUnit (inside : (argument : Rat) → -1 ≤ argument → argument ≤ 1 → FunctionExpr)
    (argument : Rat) : NumericalValue FunctionExpr :=
  if hlower : -1 ≤ argument then
    if hupper : argument ≤ 1 then .finite (inside argument hlower hupper)
    else .exceptional (.nan)
  else .exceptional (.nan)

/-- Exact finite-input cases, including the report's tangent poles and inverse-function
    endpoints. -/
def finiteUnary (operation : Unary) (argument : Rat) : NumericalValue FunctionExpr :=
  match operation with
  | .log => logarithm false argument
  | .log2 => logarithm true argument
  | .logOnePlus => logarithm false (argument + 1)
  | .exp => .finite (.exp argument)
  | .exp2 => .finite (.power 2 argument (by decide))
  | .expMinusOne => .finite (.affine 1 (-1) (.exp argument))
  | .sin => .finite (.sin argument)
  | .cos => .finite (.cos argument)
  | .tan => .finite (.tan argument)
  | .arcSin => onUnit FunctionExpr.arcsin argument
  | .arcCos => onUnit FunctionExpr.arccos argument
  | .arcTan => .finite (.arctan argument)
  | .sinh => .finite (.sinh argument)
  | .cosh => .finite (.cosh argument)
  | .tanh => .finite (.tanh argument)
  | .arcSinh => .finite (.arsinh argument)
  | .arcCosh =>
      if h : 1 ≤ argument then .finite (.arcosh argument h) else .exceptional (.nan)
  | .arcTanh =>
      if hlower : -1 < argument then
        if hupper : argument < 1 then .finite (.artanh argument hlower hupper)
        else if argument = 1 then .infinity false else .exceptional (.nan)
      else if argument = -1 then .infinity true else .exceptional (.nan)
  | .sinPi => .finite (.sinPi argument)
  | .cosPi => .finite (.cosPi argument)
  | .tanPi =>
      if Int.fract argument = 1 / 2 then .infinity (Int.floor argument % 2 != 0)
      else .finite (.tanPi argument)
  | .arcSinPi => onUnit FunctionExpr.arcsinPi argument
  | .arcCosPi => onUnit FunctionExpr.arccosPi argument
  | .arcTanPi => .finite (.arctanPi argument)
  | .softplus => .finite (.softplus argument)

/-- The report's infinite-input cases, before destination saturation. -/
def infiniteUnary (operation : Unary) (negative : Bool) : NumericalValue FunctionExpr :=
  match operation with
  | .log | .log2 | .logOnePlus | .arcCosh =>
      if negative then .exceptional (.nan) else .infinity false
  | .exp | .exp2 | .softplus => if negative then .finite (.rational 0) else .infinity false
  | .expMinusOne => if negative then .finite (.rational (-1)) else .infinity false
  | .sinh | .arcSinh => .infinity negative
  | .cosh => .infinity false
  | .tanh => .finite (.rational (if negative then -1 else 1))
  | .arcTan => .finite (angle false (if negative then -1 / 2 else 1 / 2))
  | .arcTanPi => .finite (angle true (if negative then -1 / 2 else 1 / 2))
  | _ => .exceptional (.nan)

/-- Closed unary evaluation preserves exact function expressions until the single final
    projection. -/
def unary (operation : Unary) : NumericalValue Rat → NumericalValue FunctionExpr
  | .finite value => finiteUnary operation value
  | .infinity negative => infiniteUnary operation negative
  | .exceptional _ => .exceptional (.nan)

/-- P3109 interim report v4.1, §§4.10.15–4.10.16: inverse tangent takes arguments in report
    order `(y,x)`. -/
def arcTan2 (piScaled : Bool) :
    NumericalValue Rat → NumericalValue Rat → NumericalValue FunctionExpr
  | .exceptional _, _ | _, .exceptional _ => .exceptional (.nan)
  | .infinity _, .infinity _ => .exceptional (.nan)
  | .infinity negative, .finite _ =>
      .finite (angle piScaled (if negative then -1 / 2 else 1 / 2))
  | .finite y, .infinity negative =>
      .finite (if negative then angle piScaled (if y < 0 then -1 else 1)
        else .rational 0)
  | .finite y, .finite x =>
      if x = 0 ∧ y = 0 then .exceptional (.nan) else .finite (.arg x y piScaled)

/-- Evaluate finite expressions by exact comparisons, then apply the report's saturation policy. -/
def value (format : Format) (policy : ProjectionPolicy)
    (expression : NumericalValue FunctionExpr) : NumericalValue Numerics.Dyadic :=
  format.saturate policy.saturation policy.rounding
    (expression.map (fun expr =>
      ComparisonRounding.rounded format policy.rounding (expr.prepare 8).compare))

/-- Encode a once-rounded closed elementary expression in an arbitrary P3109 descriptor.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§4.7.3 and 4.10.8–4.10.16.
-/
def code (format : Format) (policy : ProjectionPolicy)
    (expression : NumericalValue FunctionExpr) : BitVec format.bitWidth :=
  BitVec.ofNat format.bitWidth (Format.Internal.encodeDatumNat format (value format policy
    expression))

end FloatLib.Floats.Formats.P3109.Functions

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109

/-- Project an exact finite function expression, infinity or NaN by P3109 interim report v4.1
    §§4.7–4.8. -/
@[inline] def projectFunction {format : Format} (expression : NumericalValue FunctionExpr)
    (mode : RoundingMode := .nearest) (saturation : SaturationMode := .none) :
    ExecFloat.P3109 format :=
  ExecFloat.Codebook.ofCode (Functions.code format { rounding := mode, saturation } expression)


/-- P3109 interim report v4.1 §4.10.9: natural logarithm, zero to negative infinity and
    negatives to NaN. -/
unary_function Log := Functions.Unary.log
/-- P3109 interim report v4.1 §4.10.9: base-two logarithm with the logarithm's closed-domain
    rules. -/
unary_function Log2 := Functions.Unary.log2
/-- P3109 interim report v4.1 §4.10.9: logarithm of the exact sum with one, rounded once. -/
unary_function LogOnePlus := Functions.Unary.logOnePlus
/-- P3109 interim report v4.1 §4.10.9: exact exponential followed by destination projection. -/
unary_function Exp := Functions.Unary.exp
/-- P3109 interim report v4.1 §4.10.9: exact base-two exponential followed by destination
    projection. -/
unary_function Exp2 := Functions.Unary.exp2
/-- P3109 interim report v4.1 §4.10.9: exponential minus one, with no intermediate rounding. -/
unary_function ExpMinusOne := Functions.Unary.expMinusOne
/-- P3109 interim report v4.1 §4.10.10: radian sine; infinite inputs are NaN. -/
unary_function Sin := Functions.Unary.sin
/-- P3109 interim report v4.1 §4.10.10: radian cosine; infinite inputs are NaN. -/
unary_function Cos := Functions.Unary.cos
/-- P3109 interim report v4.1 §4.10.10: radian tangent; infinite inputs are NaN. -/
unary_function Tan := Functions.Unary.tan
/-- P3109 interim report v4.1 §4.10.10: principal inverse sine, rejecting arguments outside the
    unit interval. -/
unary_function ArcSin := Functions.Unary.arcSin
/-- P3109 interim report v4.1 §4.10.10: principal inverse cosine, rejecting arguments outside
    the unit interval. -/
unary_function ArcCos := Functions.Unary.arcCos
/-- P3109 interim report v4.1 §4.10.10: principal inverse tangent, with infinite inputs mapped
    to ±π/2. -/
unary_function ArcTan := Functions.Unary.arcTan
/-- P3109 interim report v4.1 §4.10.11: hyperbolic sine, preserving signed infinite inputs. -/
unary_function Sinh := Functions.Unary.sinh
/-- P3109 interim report v4.1 §4.10.11: hyperbolic cosine, mapping both infinite inputs to
    positive infinity. -/
unary_function Cosh := Functions.Unary.cosh
/-- P3109 interim report v4.1 §4.10.11: hyperbolic tangent, mapping infinite inputs to ±1. -/
unary_function Tanh := Functions.Unary.tanh
/-- P3109 interim report v4.1 §4.10.11: inverse hyperbolic sine, preserving signed infinite
    inputs. -/
unary_function ArcSinh := Functions.Unary.arcSinh
/-- P3109 interim report v4.1 §4.10.11: nonnegative inverse hyperbolic cosine, with domain at
    least one. -/
unary_function ArcCosh := Functions.Unary.arcCosh
/-- P3109 interim report v4.1 §4.10.11: inverse hyperbolic tangent, with signed infinities at ±1. -/
unary_function ArcTanh := Functions.Unary.arcTanh
/-- P3109 interim report v4.1 §4.10.12: sine of the exact pi-scaled argument, rounded once. -/
unary_function SinPi := Functions.Unary.sinPi
/-- P3109 interim report v4.1 §4.10.12: cosine of the exact pi-scaled argument, rounded once. -/
unary_function CosPi := Functions.Unary.cosPi
/-- P3109 interim report v4.1 §4.10.12: pi-scaled tangent, with sine-signed infinities at
    half-integer poles. -/
unary_function TanPi := Functions.Unary.tanPi
/-- P3109 interim report v4.1 §4.10.12: principal inverse sine divided by π before projection. -/
unary_function ArcSinPi := Functions.Unary.arcSinPi
/-- P3109 interim report v4.1 §4.10.12: principal inverse cosine divided by π before projection. -/
unary_function ArcCosPi := Functions.Unary.arcCosPi
/-- P3109 interim report v4.1 §4.10.12: principal inverse tangent divided by π before projection. -/
unary_function ArcTanPi := Functions.Unary.arcTanPi
/-- P3109 interim report v4.1 §4.10.13: logarithm of one plus the exponential, with one final
    projection. -/
unary_function Softplus := Functions.Unary.softplus


/-- P3109 interim report v4.1 §4.10.15: principal argument of `(x,y)`; origin and two infinities
    are NaN. -/
binary_angle ArcTan2 := false
/-- P3109 interim report v4.1 §4.10.16: two-coordinate inverse tangent divided by π before
    projection. -/
binary_angle ArcTan2Pi := true

end FloatLib.Floats.ExecFloat.P3109
