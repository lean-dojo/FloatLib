/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Hyperbolic.Runtime
public import FloatLib.Numerics.Exact.RationalPower.Runtime
public import FloatLib.Numerics.Exact.Softplus.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Runtime

/-!
# Exact function expressions with rational arguments

These expressions reuse the certified numerical comparators. Their constructors
carry the real-domain conditions required by inverse functions. Rational affine
transformations compose exact comparisons without an intermediate rounding.
A format chooses its exceptional cases outside this finite expression language.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Finite elementary values and rational affine transformations, with checked real domains. -/
inductive FunctionExpr where
  /-- An exact rational constant. -/
  | rational (value : Rat)
  /-- The exponential of a rational argument. -/
  | exp (argument : Rat)
  /-- The natural logarithm of a positive rational argument. -/
  | log (argument : Rat) (positive : 0 < argument)
  /-- A nonnegative rational base to a rational exponent, using the total real power. -/
  | power (base exponent : Rat) (nonnegative : 0 ≤ base)
  /-- Logarithm in a rational base greater than one. -/
  | logb (base argument : Rat) (base_gt_one : 1 < base) (positive : 0 < argument)
  /-- Natural logarithm of one plus the exponential, evaluated without intermediate rounding. -/
  | softplus (argument : Rat)
  /-- Sine in radians. -/
  | sin (argument : Rat)
  /-- Cosine in radians. -/
  | cos (argument : Rat)
  /-- Tangent in radians. Rational arguments cannot be nonzero half-integer multiples of π. -/
  | tan (argument : Rat)
  /-- Principal inverse sine on its real domain. -/
  | arcsin (argument : Rat) (lower : -1 ≤ argument) (upper : argument ≤ 1)
  /-- Principal inverse cosine on its real domain. -/
  | arccos (argument : Rat) (lower : -1 ≤ argument) (upper : argument ≤ 1)
  /-- Principal inverse tangent in radians. -/
  | arctan (argument : Rat)
  /-- Sine with the rational argument measured in units of π. -/
  | sinPi (argument : Rat)
  /-- Cosine with the rational argument measured in units of π. -/
  | cosPi (argument : Rat)
  /-- Totalized pi-scaled tangent; format wrappers must handle poles before using it. -/
  | tanPi (argument : Rat)
  /-- Principal inverse sine divided by π. -/
  | arcsinPi (argument : Rat) (lower : -1 ≤ argument) (upper : argument ≤ 1)
  /-- Principal inverse cosine divided by π. -/
  | arccosPi (argument : Rat) (lower : -1 ≤ argument) (upper : argument ≤ 1)
  /-- Principal inverse tangent divided by π. -/
  | arctanPi (argument : Rat)
  /-- Hyperbolic sine. -/
  | sinh (argument : Rat)
  /-- Hyperbolic cosine. -/
  | cosh (argument : Rat)
  /-- Hyperbolic tangent. -/
  | tanh (argument : Rat)
  /-- Inverse hyperbolic sine. -/
  | arsinh (argument : Rat)
  /-- Nonnegative inverse hyperbolic cosine. -/
  | arcosh (argument : Rat) (lower : 1 ≤ argument)
  /-- Inverse hyperbolic tangent on its open real domain. -/
  | artanh (argument : Rat) (lower : -1 < argument) (upper : argument < 1)
  /-- Principal argument of `x+i*y`, optionally divided by π; the origin has value zero. -/
  | arg (x y : Rat) (piScaled : Bool)
  /-- Exact `scale * value + offset`, without rounding its child. -/
  | affine (scale offset : Rat) (value : FunctionExpr)

namespace FunctionExpr

/-- Prepare shared comparison data; the cache depth never limits adaptive refinement. -/
def prepare (levels : Nat) : FunctionExpr → Enclosure.Comparison.Prepared
  | .rational value => .direct (cmp value)
  | .exp argument => ElementaryComparison.prepareExp argument levels
  | .log argument h => ElementaryComparison.prepareLog argument levels h
  | .power base exponent _ => .direct (RationalPower.compare base exponent)
  | .logb base argument _ _ =>
      .direct (fun boundary => (RationalPower.compare base boundary argument).swap)
  | .softplus argument => .direct (Softplus.compare argument)
  | .sin argument => TrigonometricComparison.prepareSin argument levels
  | .cos argument => TrigonometricComparison.prepareCos argument levels
  | .tan argument => TrigonometricComparison.prepareTan argument levels
  | .arcsin argument _ _ => TrigonometricComparison.prepareArcsin argument levels
  | .arccos argument _ _ => TrigonometricComparison.prepareArccos argument levels
  | .arctan argument => TrigonometricComparison.prepareArctan argument levels
  | .sinPi argument => TrigonometricComparison.prepareSinPi argument levels
  | .cosPi argument => TrigonometricComparison.prepareCosPi argument levels
  | .tanPi argument => TrigonometricComparison.prepareTanPi argument levels
  | .arcsinPi argument _ _ => TrigonometricComparison.prepareArcsinPi argument levels
  | .arccosPi argument _ _ => TrigonometricComparison.prepareArccosPi argument levels
  | .arctanPi argument => TrigonometricComparison.prepareArctanPi argument levels
  | .sinh argument => .direct (HyperbolicComparison.compareSinh argument)
  | .cosh argument => .direct (HyperbolicComparison.compareCosh argument)
  | .tanh argument => .direct (HyperbolicComparison.compareTanh argument)
  | .arsinh argument => HyperbolicComparison.prepareArsinh argument levels
  | .arcosh argument _ => HyperbolicComparison.prepareArcosh argument levels
  | .artanh argument lower upper =>
      HyperbolicComparison.prepareArtanh argument levels lower upper
  | .arg x y piScaled =>
      if piScaled then TrigonometricComparison.prepareAtan2Pi x y levels
      else TrigonometricComparison.prepareAtan2 x y levels
  | .affine scale offset value =>
      if scale = 0 then .direct (cmp offset)
      else
        let child := value.prepare levels
        .direct (fun boundary =>
          let ordering := child.compare ((boundary - offset) / scale)
          if scale < 0 then ordering.swap else ordering)

end FunctionExpr
end FloatLib.Numerics
