/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Config
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.RoundDyadicImpl.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode

/-!
# Format-generic executable exponential and logarithm

`expWith` and `logWith` execute against explicit approximation data. The convenience operations
`exp` and `log` select `Config.forFormat`. Their finite results are deterministic approximations;
accuracy bounds require separate certificates.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Transcendentals

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

The provider is called only for a finite input, so generated configurations are not constructed for
NaNs or infinities.
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
        let config := getConfig ()
        let fixed := config.fixed
        let xFixed := fixed.ofDyadic exact
        let yFixed := fixed.mul xFixed config.invLn2Fixed
        let exponent := Transcendentals.FixedPoint.roundDivPow2Even yFixed fixed
        let remainder := yFixed - exponent * fixed.one
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
Deterministic exponential using range reduction and an explicit fixed-point polynomial.

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
