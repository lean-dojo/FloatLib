/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Config
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Format-generic executable exponential and logarithm

`expWith` and `logWith` take their approximation data as an argument. The convenience operations
`exp` and `log` select `Config.forFormat`. Their finite results are deterministic approximations,
and accuracy bounds need their own certificates.
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
A zero numerator preserves its sign, and a zero denominator with nonzero numerator gives
`invalidResult`.
-/
def roundDyadicDivNat
    (fmt : FloatFormat) (value : Numerics.Dyadic) (denominator : Nat) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundRatScaled fmt value.negative value.significand denominator value.exponent

/-- Bits kept beyond twice the destination precision by the small-argument exponential. -/
def expGuardBits : Nat := 32

/--
Degree of the Taylor polynomial of `exp` for an argument below `2^(-magnitude)`, with
`magnitude ≥ 1`.

Returns the first `n` with `2^(magnitude * (n + 1)) * (n + 1)! ≥ 2^target`, so the first
omitted term `x^(n+1)/(n+1)!` is below `2^(-target)`. The fuel `target` exceeds the point where
the power of two alone reaches the target.
-/
def expTaylorDegree (target magnitude : Nat) : Nat :=
  go target 1
where
  /-- Search upward from `count`, with `fuel` remaining steps. -/
  go : Nat → Nat → Nat
    | 0, count => count
    | fuel + 1, count =>
        if Model.pow2 target ≤
            Model.pow2 (magnitude * (count + 1)) * Config.factorial (count + 1) then
          count
        else
          go fuel (count + 1)

/-- Exact common-denominator coefficients of `sum k in [0, terms], x^k/k!`, as `(terms!, coefficients)`. -/
def expTaylorData (terms : Nat) : Nat × List Int :=
  let denominator := Config.factorial terms
  (denominator, (List.range (terms + 1)).map fun index =>
    Int.ofNat (denominator / Config.factorial index))

/--
Reduce `x / log 2` to the nearest integer `n` and a remainder in `[-1/2, 1/2]` at `config.fixed`
fractional bits, so that `exp x = 2^n * 2^remainder`.

`x / log 2` carries the error of `1 / log 2` times `|x|`. For `|x| ≥ 1` the reduction therefore
runs at `bits |x|` more fractional bits, with `log 2` from the shared constants cache
(`Numerics.Enclosure.Constants.ln2Faithful`, within one unit), which keeps the remainder accurate
at `config.fixed` bits for every argument. Smaller arguments use the configured reciprocal.
-/
def expReduce (config : Config) (exact : Numerics.Dyadic) : Int × Int :=
  let fixed := config.fixed
  let extra := (Int.ofNat (Nat.log2 exact.significand) + exact.exponent + 1).toNat
  if exact.significand == 0 || extra == 0 then
    let yFixed := fixed.mul (fixed.ofDyadic exact) config.invLn2Fixed
    let exponent := FixedPoint.roundDivPow2Even yFixed fixed
    (exponent, yFixed - exponent * fixed.one)
  else
    let wide : FixedPoint := fixed + extra
    let invLn2 := wide.div wide.one (Numerics.Enclosure.Constants.ln2Faithful wide)
    let yFixed := wide.mul (wide.ofDyadic exact) invLn2
    let exponent := FixedPoint.roundDivPow2Even yFixed wide
    (exponent, FixedPoint.roundDivPow2Even (yFixed - exponent * wide.one) extra)

/--
Evaluate the first `terms` terms of
`t + t^3/3 + t^5/5 + ...`
in a fixed-point context.
-/
def atanhSeries (fixed : FixedPoint) (t : Int) (terms : Nat) : Int :=
  let tSquared := fixed.mul t t
  let step (state : Int × Int) (index : Nat) : Int × Int :=
    let term := state.1
    let denominator := 2 * index + 1
    let accumulator := state.2 + fixed.divByNat term denominator
    (fixed.mul term tSquared, accumulator)
  ((List.range terms).foldl step (t, 0)).2

end Transcendentals

/--
Evaluate exponential using a delayed configuration provider.

The provider is called only for a finite input that is neither tiny nor beyond the overflow and
underflow bounds, so generated configurations are not constructed for NaNs, infinities, or those
arguments. Below `2^-(p+1)` the nearest result is one. Two kinds of argument below one half
evaluate `sum x^k/k!` exactly with enough terms for `2p + expGuardBits` bits and round once: one
whose bits extend below the fixed-point scale, which conversion would round so that neighbouring
inputs share a result; and one whose `x^2/2` is within `2^15` of the fixed-point resolution, since
near zero `exp x` can sit just `x^2/2` off a rounding midpoint. Every other argument uses the
configured fixed-point path.
-/
def expWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config) (x : Model fmt) : Model fmt :=
  if isNaN x then
    quietNaN x
  else if isInf x then
    if signBit x then zero fmt false else nativeOverflow fmt false
  else
    match toDyadic? x with
    | none => invalidResult fmt
    | some exact =>
        let leading := Int.ofNat (Nat.log2 exact.significand) + exact.exponent
        if exact.significand == 0 || leading < -(Int.ofNat (fmt.fracWidth + 2)) then
          posOne fmt
        else
          -- Beyond `2 + max |emax| |minSubnormalExponent|` the result is certainly an overflow or
          -- a zero; deciding that first avoids a fixed-point conversion proportional to `x`.
          let bound := Nat.max (fmt.maxNormalExponent.natAbs + 2)
            (fmt.minSubnormalExponent.natAbs + 2)
          if leading ≥ Int.ofNat (Nat.log2 bound + 1) then
            if exact.negative then zero fmt false else nativeOverflow fmt false
          else
            let config := getConfig ()
            let fixed := config.fixed
            if leading < -1 &&
                (exact.exponent + Int.ofNat fixed < 0 || 2 * leading + Int.ofNat fixed < 16) then
              let terms := Transcendentals.expTaylorDegree
                (2 * (fmt.fracWidth + 1) + Transcendentals.expGuardBits) (-(leading + 1)).toNat
              let (denominator, coefficients) := Transcendentals.expTaylorData terms
              Transcendentals.roundDyadicDivNat fmt
                (Transcendentals.evalDyadicPolyAsc coefficients exact) denominator
            else
              let (exponent, remainder) := Transcendentals.expReduce config exact
              let polynomial := fixed.evalPolyDesc config.exp2PolyCoeffsDesc remainder
              if polynomial ≤ 0 then
                zero fmt false
              else
                let resultExponent := exponent - fixed.scaleInt
                let leadingExponent :=
                  Int.ofNat (Nat.log2 polynomial.natAbs) + resultExponent
                if leadingExponent > fmt.maxNormalExponent then
                  nativeOverflow fmt false
                else if leadingExponent < fmt.minSubnormalExponent - 1 then
                  zero fmt false
                else
                  roundDyadic fmt
                    { negative := false
                      significand := polynomial.natAbs
                      exponent := resultExponent }

/--
Evaluate logarithm using a delayed configuration provider.

The provider is called only for a finite positive input.
-/
def logWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config) (x : Model fmt) : Model fmt :=
  if isNaN x then
    quietNaN x
  else if isInf x then
    if signBit x then invalidResult fmt else nativeOverflow fmt false
  else if isZero x then
    nativeOverflow fmt true
  else if signBit x then
    invalidResult fmt
  else
    match toDyadic? x with
    | none => invalidResult fmt
    | some exact =>
        if exact.significand == 0 then
          nativeOverflow fmt true
        else
          let config := getConfig ()
          let leading := Nat.log2 exact.significand
          -- Center the significand in [3/4, 3/2), so values near one need no subtraction
          -- of independently approximated logarithms.
          let shift := if 2 * exact.significand ≥ 3 * pow2 leading then 1 else 0
          let exponent := Int.ofNat leading + exact.exponent + shift
          -- Near one, the quadratic correction can land on a rounding midpoint.
          -- Keep the cubic term as well as the small result before destination rounding.
          let fixed :=
            if exponent == 0 then config.fixed + 2 * (fmt.fracWidth + 1) else config.fixed
          let normalized := fixed.ofDyadic
            { negative := false
              significand := exact.significand
              exponent := exact.exponent - exponent }
          let t := fixed.div (normalized - fixed.one) (normalized + fixed.one)
          let logMantissa := 2 * Transcendentals.atanhSeries fixed t config.logTerms
          let logValue := logMantissa + exponent * config.ln2Fixed
          roundDyadic fmt (fixed.toDyadic logValue)

/--
Deterministic exponential using range reduction and a fixed-point polynomial.

NaNs are quieted and infinities use the destination format's native overflow and zero policies.
-/
def expWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  expWithProvider (fun _ => config) x

/--
Deterministic natural logarithm using centered dyadic normalization and an odd atanh series.

Inputs near one use additional working precision and avoid a logarithmic subtraction.
Special values follow the destination format's native overflow and invalid-result policies.
-/
def logWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  logWithProvider (fun _ => config) x

/-- Exponential using the default configuration for the destination format. -/
@[inline] def exp {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  expWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

/-- Natural logarithm using the default configuration for the destination format. -/
@[inline] def log {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  logWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

end Model
end FloatLib.Floats.Formats.BinaryInterchange
