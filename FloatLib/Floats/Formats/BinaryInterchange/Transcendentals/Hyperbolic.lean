/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.ExpLog
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime

/-!
# Format-generic executable hyperbolic functions

`sinh`, `cosh`, and `tanh` are built from exact dyadics, exact rationals, and the configured
exponential kernel, so the same algorithms elaborate for arbitrary binary descriptors.

The small-argument branches evaluate the polynomial stored in `Config.sinhCoeffsAsc` exactly.
For generated configurations, `Config.sinhTerms` selects its length from the destination fraction
width using a Taylor-tail target; binary32's coefficient table has one additional term.
`sinh` rounds the polynomial once. `cosh` integrates it exactly before one final rational rounding.
`tanh` approximates `s / sqrt (1 + s^2)`, where `s` is the truncated `sinh` value, using an integer
square root with `tanhGuardBits` extra bits. Larger arguments use dyadic approximations from the
exponential polynomial, combined before destination rounding. Bounded alignment preserves the
sign of tiny contributions at rounding midpoints. These algorithms have no proved general
real-error or ULP bound yet.

The provider entry points inspect the decoded input exponent before requesting approximation data.
For nonzero inputs with leading exponent below `-(fracWidth + 2)`, `sinh` and `tanh` return the
input and `cosh` returns one. Large inputs return the rounded limit of `tanh`, or the descriptor's
native overflow result for `sinh` and `cosh`. These conservative magnitude branches bypass even
caller-supplied approximation coefficients and avoid huge fixed-point conversions for extreme
inputs. The remaining inputs are compared with the destination's rounded encoding of `1/2`
to choose between the polynomial and exponential branches. The lower-level polynomial and dyadic
helpers do not apply these magnitude guards.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Transcendentals

/-- Exact dyadic multiplication without rounding. -/
@[inline] def mulDyadic (left right : Numerics.Dyadic) : Numerics.Dyadic :=
  { negative := Bool.xor left.negative right.negative
    significand := left.significand * right.significand
    exponent := left.exponent + right.exponent }

/-- Embed an integer as an exact dyadic. -/
@[inline] def dyadicOfInt (value : Int) : Numerics.Dyadic :=
  { negative := value < 0
    significand := value.natAbs
    exponent := 0 }

/-- Exact dyadic one. -/
@[inline] def oneDyadic : Numerics.Dyadic :=
  { negative := false, significand := 1, exponent := 0 }

/-- Exact dyadic zero. -/
@[inline] def zeroDyadic : Numerics.Dyadic :=
  { negative := false, significand := 0, exponent := 0 }

/--
Evaluate ascending integer coefficients as an exact polynomial in a dyadic argument.

An empty coefficient list evaluates to zero.
-/
def evalDyadicPolyAsc
    (coefficients : List Int) (value : Numerics.Dyadic) : Numerics.Dyadic :=
  let step (state : Numerics.Dyadic × Numerics.Dyadic)
      (coefficient : Int) : Numerics.Dyadic × Numerics.Dyadic :=
    let power := state.1
    let accumulator := state.2
    let term := mulDyadic (dyadicOfInt coefficient) power
    (mulDyadic power value, addDyadic accumulator term)
  (coefficients.foldl step (oneDyadic, zeroDyadic)).2

/--
Round `value / denominator` to the destination format for a positive denominator.
A zero numerator preserves its sign; a zero denominator with nonzero numerator gives `invalidResult`.
-/
def roundDyadicDivNat
    (fmt : FloatFormat) (value : Numerics.Dyadic) (denominator : Nat) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundRatScaled fmt value.negative value.significand denominator value.exponent

/-- Round a nonnegative natural number directly into the destination format. -/
@[inline] def ofNat (fmt : FloatFormat) (value : Nat) : Model fmt :=
  roundDyadic fmt { negative := false, significand := value, exponent := 0 }

/--
Exact numerator of the truncated odd Taylor series of `sinh` at a dyadic argument.

For the Taylor data supplied by `Config`, dividing by `config.sinhDenominator` gives
`x + x^3/3! + ...`, truncated to `config.sinhCoeffsAsc.length` terms. A custom configuration
instead evaluates its supplied odd polynomial.
-/
def sinhSeriesNumerator (config : Config) (exact : Numerics.Dyadic) : Numerics.Dyadic :=
  mulDyadic exact (evalDyadicPolyAsc config.sinhCoeffsAsc (mulDyadic exact exact))

/-- Evaluate the truncated `sinh` series at a finite input and round once. -/
def sinhTaylorSmallWith {fmt : FloatFormat}
    (config : Config) (x : Model fmt) : Model fmt :=
  match toDyadic? x with
  | none => invalidResult fmt
  | some exact =>
      roundDyadicDivNat fmt (sinhSeriesNumerator config exact) config.sinhDenominator

/--
Evaluate the integral of the configured `sinh` polynomial, with constant term one.

If the odd coefficients are `aᵢ / D`, the even coefficients after the constant are
`aᵢ / ((2*i+2)*D)`. Multiplying by `(2*n)!`, where `n` is the coefficient count, makes every
coefficient integral without assuming divisibility properties of a caller-supplied configuration.
Keeping this polynomial exact retains the quartic correction at near-one rounding midpoints.
-/
def coshTaylorSmallWith {fmt : FloatFormat}
    (config : Config) (x : Model fmt) : Model fmt :=
  match toDyadic? x with
  | none => invalidResult fmt
  | some exact =>
      let factor := Config.factorial (2 * config.sinhCoeffsAsc.length)
      let denominator := config.sinhDenominator * factor
      let coefficients := Int.ofNat denominator ::
        config.sinhCoeffsAsc.mapIdx fun index coefficient =>
          coefficient * Int.ofNat (factor / (2 * index + 2))
      let numerator := evalDyadicPolyAsc coefficients (mulDyadic exact exact)
      roundDyadicDivNat fmt numerator denominator

/-- Extra bits carried by the integer square root in the small-argument `tanh` branch. -/
def tanhGuardBits : Nat := 8

/--
Approximate `tanh` for small arguments from a truncated `sinh` series.

The real identity is `tanh x = sinh x / sqrt (1 + sinh x ^ 2)`. Substituting the truncated
series gives an approximation whose magnitude is `a / sqrt b`, after clearing powers of two
from its numerator and denominator. The implementation computes
`q = floor (sqrt (a^2 * 4^k / b))`, restores the input sign, and rounds `q * 2^(-k)` once.
The choice of `k` gives the square-root calculation extra working bits controlled by
`tanhGuardBits`; a real-error or ULP bound for the complete calculation remains unproved.
-/
def tanhTaylorSmallWith {fmt : FloatFormat}
    (config : Config) (x : Model fmt) : Model fmt :=
  match toDyadic? x with
  | none => invalidResult fmt
  | some exact =>
      let numerator := sinhSeriesNumerator config exact
      let squaredDenominator := config.sinhDenominator * config.sinhDenominator
      let (a, b) : Nat × Nat :=
        match numerator.exponent with
        | .ofNat shift =>
            let a := numerator.significand * pow2 shift
            (a, squaredDenominator + a * a)
        | .negSucc shift =>
            let a := numerator.significand
            (a, squaredDenominator * pow2 (2 * (shift + 1)) + a * a)
      if a == 0 then
        zero fmt exact.negative
      else
        let k := fmt.fracWidth + tanhGuardBits + (Nat.log2 b + 1) / 2 + 1 - Nat.log2 a
        let q := Nat.sqrt (a * a * pow2 (2 * k) / b)
        roundDyadic fmt { negative := exact.negative, significand := q, exponent := -(Int.ofNat k) }

/-- Keep the exponential polynomial's dyadic result until its caller finishes the operation. -/
def expDyadicWith (config : Config) (exact : Numerics.Dyadic) : Numerics.Dyadic :=
  let fixed := config.fixed
  let xFixed := fixed.ofDyadic exact
  let yFixed := fixed.mul xFixed config.invLn2Fixed
  let exponent := FixedPoint.roundDivPow2Even yFixed fixed
  let remainder := yFixed - exponent * fixed.one
  let polynomial := fixed.evalPolyDesc config.exp2PolyCoeffsDesc remainder
  if polynomial ≤ 0 then
    zeroDyadic
  else
    { negative := false
      significand := polynomial.natAbs
      exponent := exponent - fixed.scaleInt }

/-- Classify an exponential-derived dyadic before asking the destination rounder to align it. -/
def roundExpDyadic (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    let leadingExponent := Int.ofNat (Nat.log2 value.significand) + value.exponent
    if leadingExponent > fmt.maxNormalExponent then
      nativeOverflow fmt value.negative
    else if leadingExponent < fmt.minSubnormalExponent - 1 then
      zero fmt value.negative
    else
      roundDyadic fmt value

/--
Combine dyadics for one destination rounding without allocating their entire exponent gap.

A sufficiently small addend is replaced by a signed sticky contribution below the destination's
rounding bits. Its sign still resolves a midpoint in the larger operand. Otherwise exact alignment
shifts by at most a significand's bit length plus `fmt.fracWidth + 3`.
-/
def addExpDyadics (fmt : FloatFormat) (left right : Numerics.Dyadic) :
    Numerics.Dyadic :=
  if left.significand == 0 || right.significand == 0 then
    addDyadic left right
  else
    let guard := fmt.fracWidth + 3
    if left.exponent - right.exponent > Int.ofNat (Nat.log2 right.significand + guard) then
      addDyadic left
        { right with significand := 1, exponent := left.exponent - Int.ofNat guard }
    else if right.exponent - left.exponent >
        Int.ofNat (Nat.log2 left.significand + guard) then
      addDyadic
        { left with significand := 1, exponent := right.exponent - Int.ofNat guard } right
    else
      addDyadic left right

/--
Approximate `exp x * scale` for a finite input, scaling before destination-format rounding.

The range reduction and polynomial are the same as in `expWithProvider`. Scaling the dyadic before
classifying its range retains the upper finite interval when `scale = 1/2`.
-/
def expMulDyadicWith {fmt : FloatFormat}
    (config : Config) (x : Model fmt) (scale : Numerics.Dyadic) : Model fmt :=
  match toDyadic? x with
  | none => invalidResult fmt
  | some exact => roundExpDyadic fmt (mulDyadic (expDyadicWith config exact) scale)

/-- Combine both scaled exponential approximations before the hyperbolic result is rounded. -/
def hyperbolicSumWith (fmt : FloatFormat) (config : Config)
    (exact scale : Numerics.Dyadic) (subtract : Bool) : Model fmt :=
  let forward := mulDyadic (expDyadicWith config exact) scale
  let backward := mulDyadic (expDyadicWith config exact.neg) scale
  let backward := if subtract then backward.neg else backward
  roundExpDyadic fmt (addExpDyadics fmt forward backward)

/--
Form `(exp (2*x) - 1) / (exp (2*x) + 1)` before destination rounding.

Doubling the decoded argument avoids an intermediate overflow. Outside the quotient's transition
range, return its rounded limit before aligning with one; the remaining shifts are bounded by the
polynomial's bit length and the destination precision.
-/
def tanhExpWith (fmt : FloatFormat) (config : Config) (exact : Numerics.Dyadic) :
    Model fmt :=
  let exponential := expDyadicWith config { exact with exponent := exact.exponent + 1 }
  if exponential.significand == 0 then
    negOne fmt
  else
    let leadingExponent :=
      Int.ofNat (Nat.log2 exponential.significand) + exponential.exponent
    let limit := Int.ofNat (fmt.fracWidth + 3)
    if leadingExponent > limit then
      posOne fmt
    else if leadingExponent < -limit then
      negOne fmt
    else
      let (numerator, denominator) : Nat × Nat :=
        match exponential.exponent with
        | .ofNat shift => (exponential.significand * pow2 shift, 1)
        | .negSucc shift => (exponential.significand, pow2 (shift + 1))
      let difference := Int.ofNat numerator - Int.ofNat denominator
      roundRat fmt (difference < 0) difference.natAbs (numerator + denominator)

end Transcendentals

/--
Evaluate the exponential branch used by `sinhWithProvider`.

The provider passes the destination's rounded encoding of `1/2`. Its decoded dyadic value scales
each exponential before their difference is rounded, avoiding an intermediate destination-format
rounding of either exponential.
-/
@[noinline] def sinhLarge {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config)
    (x half : Model fmt) : Model fmt :=
  let config := getConfig ()
  match toDyadic? half with
  | some scale =>
      match toDyadic? x with
      | some exact => Transcendentals.hyperbolicSumWith fmt config exact scale true
      | none => invalidResult fmt
  | none => mul (sub (expWith config x) (expWith config (neg x))) half

/--
Evaluate hyperbolic sine with a delayed configuration provider.

Tiny inputs return unchanged before configuration generation. A decoded leading exponent above
`log2 (abs maxNormalExponent + 2)` implies magnitude greater than `abs maxNormalExponent + 2`,
where the result overflows; use the descriptor's overflow policy without evaluating an exponential.
The remaining inputs below the encoded half use the exact truncated series; larger inputs combine
dyadic exponential approximations scaled by that encoded half before rounding.
-/
def sinhWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config) (x : Model fmt) : Model fmt :=
  match chooseNaN1 x with
  | some nan => nan
  | none =>
      if isInf x then
        x
      else if isZero x then
        x
      else
        match toDyadic? x with
        | none => invalidResult fmt
        | some exact =>
            let leadingExponent := Int.ofNat (Nat.log2 exact.significand) + exact.exponent
            if leadingExponent < -(Int.ofNat (fmt.fracWidth + 2)) then
              x
            else if leadingExponent >
                Int.ofNat (Nat.log2 (fmt.maxNormalExponent.natAbs + 2)) then
              nativeOverflow fmt exact.negative
            else
              let half := roundDyadic fmt
                { negative := false, significand := 1, exponent := -1 }
              match compare (abs x) half with
              | some .lt => Transcendentals.sinhTaylorSmallWith (getConfig ()) x
              | _ => sinhLarge getConfig x half

/--
Evaluate hyperbolic cosine with a delayed configuration provider.

Tiny inputs return one and sufficiently large inputs return the descriptor's positive overflow
result before configuration generation, using the same input bounds as `sinhWithProvider`.
The remaining inputs below the encoded half use an exact even polynomial. Larger finite inputs
add dyadic approximations of `exp x / 2` and `exp (-x) / 2` before rounding.
-/
def coshWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config) (x : Model fmt) : Model fmt :=
  match chooseNaN1 x with
  | some nan => nan
  | none =>
      if isInf x then
        nativeOverflow fmt false
      else if isZero x then
        roundDyadic fmt Transcendentals.oneDyadic
      else
        match toDyadic? x with
        | none => invalidResult fmt
        | some exact =>
            let leadingExponent := Int.ofNat (Nat.log2 exact.significand) + exact.exponent
            if leadingExponent < -(Int.ofNat (fmt.fracWidth + 2)) then
              roundDyadic fmt Transcendentals.oneDyadic
            else if leadingExponent >
                Int.ofNat (Nat.log2 (fmt.maxNormalExponent.natAbs + 2)) then
              nativeOverflow fmt false
            else
              let config := getConfig ()
              let half : Numerics.Dyadic :=
                { negative := false, significand := 1, exponent := -1 }
              match compare (abs x) (roundDyadic fmt half) with
              | some .lt => Transcendentals.coshTaylorSmallWith config x
              | _ => Transcendentals.hyperbolicSumWith fmt config exact half false

/--
Evaluate hyperbolic tangent with a provider called only after special values and magnitude guards.

Tiny inputs return unchanged. A decoded leading exponent above `log2 (fracWidth + 3)` implies
`|x| > fracWidth + 3`, well past the nearest-even transition to signed one. Returning that limit
before fixed-point conversion also avoids allocating an integer proportional to a huge input.
-/
def tanhWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config) (x : Model fmt) : Model fmt :=
  match chooseNaN1 x with
  | some nan => nan
  | none =>
      if isInf x then
        if signBit x then negOne fmt else posOne fmt
      else if isZero x then
        x
      else
        match toDyadic? x with
        | none => invalidResult fmt
        | some exact =>
            let leadingExponent := Int.ofNat (Nat.log2 exact.significand) + exact.exponent
            if leadingExponent < -(Int.ofNat (fmt.fracWidth + 2)) then
              x
            else if leadingExponent > Int.ofNat (Nat.log2 (fmt.fracWidth + 3)) then
              let one := roundDyadic fmt Transcendentals.oneDyadic
              if exact.negative then neg one else one
            else
              let half := roundDyadic fmt
                { negative := false, significand := 1, exponent := -1 }
              let magnitude := abs x
              match compare magnitude half with
              | some .lt =>
                  Transcendentals.tanhTaylorSmallWith (getConfig ()) x
              | _ =>
                  let config := getConfig ()
                  let raw := Transcendentals.tanhExpWith fmt config { exact with negative := false }
                  let boundary := Transcendentals.tanhTaylorSmallWith config half
                  let positive :=
                    match compare raw boundary with
                    | some .lt => boundary
                    | _ => raw
                  if exact.negative then neg positive else positive

/-- Deterministic hyperbolic sine using the configured exponential kernel. -/
def sinhWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  sinhWithProvider (fun _ => config) x

/-- Deterministic hyperbolic cosine using the configured exponential kernel. -/
def coshWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  coshWithProvider (fun _ => config) x

/--
Deterministic hyperbolic tangent.

After the magnitude guards, small inputs substitute a truncated `sinh` series into
`s / sqrt (1 + s^2)`. Larger finite inputs round the rational quotient formed from the
dyadic approximation to `exp (2 * |x|)`, then clamp it from below to the small-branch value at the
encoded half. The sign is restored after this comparison.
-/
def tanhWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  tanhWithProvider (fun _ => config) x

/-- Hyperbolic sine using the default configuration for the destination format. -/
@[inline] def sinh {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  sinhWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

/-- Hyperbolic cosine using the default configuration for the destination format. -/
@[inline] def cosh {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  coshWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

/-- Hyperbolic tangent using the default configuration for the destination format. -/
@[inline] def tanh {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  tanhWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

end Model
end FloatLib.Floats.Formats.BinaryInterchange
