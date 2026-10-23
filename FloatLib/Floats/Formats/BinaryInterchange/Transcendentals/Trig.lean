/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Hyperbolic
public import FloatLib.Numerics.Enclosure.Trigonometric.ArgumentReduction.Runtime

/-!
# Format-generic executable sine and cosine

Finite arguments of at least three quarters are reduced modulo `pi / 2` by the Payne-Hanek window
reduction of `Numerics.Enclosure.ArgumentReduction`, which reads a window of the cached `2 / pi` at
the cache level the argument's exponent needs. With `p` the destination precision, the reduction
keeps `p + 32` relative bits of the remainder: it doubles its window, at most four times and only
while the window stays within the cache level `trigReductionLevelLimit`, until its proved error is
below `2^-(p + 32)` of the remainder. When no permitted window is accepted, sine and cosine give the
format's invalid result. Multiplying the accepted remainder by the cached `pi / 2` and truncating to
`p + 40` significant bits gives the reduced argument. Smaller arguments are their own reduced
argument. The sine and cosine of the reduced argument are evaluated from exact common-denominator
Taylor polynomials, with as many terms as the argument's exponent needs. The quadrant and the sign
of the argument are applied to these exact values, and each result is rounded once to `Model fmt`.

The reduction reads at most level `trigReductionLevelLimit` of the cache, `2^21` bits of `2 / pi`.
For an argument `m * 2^e` whose significand has `k` bits, the first window has
`2 k + fracWidth + 53` bits and stays within that level when `max e 0 + 2 k + fracWidth + 59` is at
most `2^21`. A format argument has `k ≤ fracWidth + 1`, so in a format with at most 524,258
fraction bits every finite argument below `2^(2^20)` qualifies, and with the conventional bias that
covers every exponent field of at most 21 bits. Arguments whose first window needs a higher level,
such as the largest ones of a 31-bit exponent field, give the format's invalid result.

For leading exponents below `-(fracWidth + 2)`, the provider returns the input and one, preserving
tiny sine results without converting them to the fixed-point reduction scale. The reduction error is
proved (`Numerics.Enclosure.ArgumentReduction.QuarterTurns.Reduces.abs_sin_sub_rotate_le`), but the
truncation, the Taylor remainder and the final rounding are not, so the kernels are deterministic
approximations without a whole-algorithm accuracy or correct-rounding certificate.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Transcendentals

/-- Bits kept beyond the destination precision by trigonometric argument reduction. -/
def trigGuardBits : Nat := 32

/-- Window doublings allowed after the first attempt of trigonometric reduction. -/
def trigReductionFuel : Nat := 4

/--
Highest level of the constants cache that trigonometric reduction reads: `levelBits 15 = 2^21` bits
of `2 / pi`, computed in a few seconds on first use and then cached. Each further level would take
more than twice as long. A reduction whose first window needs a higher level gives the invalid
result, and later attempts use only the doublings whose windows stay within this level
(`Numerics.Enclosure.ArgumentReduction.fuelWithin?`). For `ieee 31 23` the first window stays within
it for every argument below `2^2097046`.
-/
def trigReductionLevelLimit : Nat := 15

/--
A dyadic numerator over a denominator, kept exact until its single rounding. The kernels take the
denominators from the Taylor data of their configuration, which are positive in the built-in
configurations `Config.binary32` and `Config.generatedWith`.
-/
structure DyadicRatio where
  /-- The exact numerator. -/
  numerator : Numerics.Dyadic
  /-- The denominator, positive for the built-in configurations. -/
  denominator : Nat

/-- Negation changes the sign of the numerator. -/
instance : Neg DyadicRatio where
  neg value := { value with numerator := value.numerator.neg }

/-- Round a ratio once to the destination format. -/
def DyadicRatio.round (fmt : FloatFormat) (value : DyadicRatio) : Model fmt :=
  roundDyadicDivNat fmt value.numerator value.denominator

/--
The number of sine terms for a relative remainder below `2^-target` at an argument below
`2^-magnitude`: the first `n ≥ 1` with `2^target ≤ 2^(2 n magnitude) * (2 n + 1)!`, so the first
omitted term `|x|^(2n+1) / (2n+1)!` is below `2^-target |x|`. One term suffices once
`2 magnitude ≥ target`. Otherwise the search keeps that product as it goes and stops after
`target` steps, where `(2 n + 1)! ≥ 2^(2 n)` alone exceeds the target.
-/
def trigTaylorTerms (target magnitude : Nat) : Nat :=
  if target ≤ 2 * magnitude then
    1
  else
    let step := 2 ^ (2 * magnitude)
    go (2 ^ target) step target 1 (step * 6)
where
  /--
  Search upward from `count`, whose product is `bound`, for a product of at least `threshold`;
  each term multiplies the product by `step` and two factorial factors.
  -/
  go (threshold step : Nat) : Nat → Nat → Nat → Nat
    | 0, count, _ => count
    | fuel + 1, count, bound =>
        if threshold ≤ bound then
          count
        else
          go threshold step fuel (count + 1) (bound * step * ((2 * count + 2) * (2 * count + 3)))

/--
The exact Taylor sums of sine and cosine at a nonzero `value` below one, before division by the
configuration's denominators: the first `terms` coefficients of `config.sinCoeffsAsc` and the first
`terms + 1` of `config.cosCoeffsAsc`, or all of them when the configuration has fewer.

With `|value| < 2^-s` and `terms = trigTaylorTerms (bits + 8) s`, the first omitted terms are below
`2^-(bits + 8) |value|` when the configuration holds at least `terms` sine and `terms + 1` cosine
coefficients. A shorter table omits the terms past its end instead: the pinned binary32 table has
7 sine and 7 cosine coefficients, so at `|value| = pi / 4` its first omitted terms are about
`2^-45 |value|` for the sine and `2^-41` for the cosine.
-/
def sinCosTaylor (config : Config) (terms : Nat) (value : Numerics.Dyadic) :
    DyadicRatio × DyadicRatio :=
  let squared : Numerics.Dyadic :=
    { negative := false
      significand := value.significand * value.significand
      exponent := value.exponent + value.exponent }
  ( { numerator := mulDyadic value (evalDyadicPolyAsc (config.sinCoeffsAsc.take terms) squared)
      denominator := config.sinDenominator }
  , { numerator := evalDyadicPolyAsc (config.cosCoeffsAsc.take (terms + 1)) squared
      denominator := config.cosDenominator } )

/--
Reduce a positive dyadic `m * 2^e` modulo `pi / 2`, keeping `bits` relative bits.

`Numerics.Enclosure.ArgumentReduction.reduce` reduces it with windows from `startWindow p bits`,
with `p` the bit length of `m`, doubling at most `trigReductionFuel` times and only while the
window reads a cache level of at most `trigReductionLevelLimit` (`fuelWithin?`). The fraction of
the accepted reduction times the cached lower bound of `pi / 2` at `bits + 8` bits is truncated to
`bits + 8` significant bits. Returns the quadrant and this reduced argument, or `none` when the
first window would read a level above the limit or no permitted window is accepted.
-/
def reduceQuarterTurns? (bits m : Nat) (e : Int) : Option (Fin 4 × Numerics.Dyadic) :=
  let p := Nat.log2 m + 1
  match Numerics.Enclosure.ArgumentReduction.fuelWithin? e p bits trigReductionLevelLimit
      trigReductionFuel with
  | none => none
  | some fuel =>
      let turns := Numerics.Enclosure.ArgumentReduction.reduce m e p bits fuel
      if turns.accepts bits then
        let precision := bits + 8
        let numerator := turns.argumentNumerator precision
        let drop := (Nat.log2 numerator.natAbs + 1) - precision
        some (turns.quadrant,
          { negative := numerator < 0
            significand := numerator.natAbs >>> drop
            exponent := Int.ofNat drop - Int.ofNat (turns.scale + precision) })
      else
        none

/-- Whether a positive dyadic with significand `m` and leading exponent `leading` is below `3/4`. -/
def belowThreeQuarters (m : Nat) (leading : Int) : Bool :=
  leading < -1 || (leading == -1 && 2 * m < 3 * 2 ^ Nat.log2 m)

/--
Sine of a nonzero dyadic of leading exponent `leading < -(fracWidth + 2)`, with no work
proportional to its exponent.

A value representable in the format is its own nearest result: `x - sin x < x^3/6` is far below
half its unit. Otherwise `sin x` lies strictly between `x - x^3/6` and `x`. When `x^3/6` is below
a quarter of the unit of the last bit of `x`, the only rounding boundary that can lie between
them is `x` itself, so rounding `x` moved a quarter unit toward zero selects the nearest
encoding of `sin x`, also when `x` is a rounding midpoint. A shorter-than-necessary unit gives
an argument with at least about `2 |leading|` bits, whose sine is evaluated from every sine
coefficient of the configuration.
-/
def tinySine (fmt : FloatFormat) (config : Config) (value : Numerics.Dyadic)
    (leading : Int) : Model fmt :=
  let unit := max (leading - Int.ofNat fmt.fracWidth) fmt.minSubnormalExponent
  if unit ≤ value.exponent then
    roundDyadic fmt value
  else if 3 * (leading + 1) ≤ value.exponent then
    roundDyadic fmt
      { value with significand := 4 * value.significand - 1, exponent := value.exponent - 2 }
  else
    (sinCosTaylor config config.sinCoeffsAsc.length value).1.round fmt

/--
Reduce a dyadic argument modulo `pi / 2` and evaluate sine and cosine.

The configuration supplies the Taylor coefficients, and the reduction itself reads the constants
cache of `Numerics.Enclosure.Constants`. Tiny arguments use `tinySine`, and their cosine
`1 - x^2/2` rounds to one. Other arguments below three quarters evaluate the polynomials on the
exact argument, and larger ones are reduced by `reduceQuarterTurns?` with
`fracWidth + 1 + trigGuardBits` relative bits. The polynomials take the terms that
`trigTaylorTerms` asks for at the exponent of the reduced argument. The quadrant and the sign of
the argument are applied before the single
rounding of each result. The format's invalid result means that the reduction would need a cache
level above `trigReductionLevelLimit` or that no permitted window was accepted. For an argument
`m * 2^e` whose significand has `k` bits, the first window stays within the limit when
`max e 0 + 2 k + fracWidth + 59 ≤ 2^21`. The results are deterministic approximations without a
numerical accuracy certificate.
-/
def sinCosScaledWith (fmt : FloatFormat) (config : Config)
    (value : Numerics.Dyadic) : Model fmt × Model fmt :=
  let leading := Int.ofNat (Nat.log2 value.significand) + value.exponent
  if value.significand == 0 then
    (zero fmt value.negative, posOne fmt)
  else if leading < -(Int.ofNat (fmt.fracWidth + 2)) then
    (tinySine fmt config value leading, posOne fmt)
  else
    let bits := fmt.fracWidth + 1 + trigGuardBits
    let reduced :=
      if belowThreeQuarters value.significand leading then
        some (0, { value with negative := false })
      else
        reduceQuarterTurns? bits value.significand value.exponent
    match reduced with
    | none => (invalidResult fmt, invalidResult fmt)
    | some (quadrant, argument) =>
        let magnitude := (-1 - Int.ofNat (Nat.log2 argument.significand) - argument.exponent).toNat
        let taylor := sinCosTaylor config (trigTaylorTerms (bits + 8) magnitude) argument
        let rotated := Numerics.Enclosure.ArgumentReduction.rotate quadrant taylor.1 taylor.2
        ((if value.negative then -rotated.1 else rotated.1).round fmt, rotated.2.round fmt)

end Transcendentals

/--
Evaluate sine and cosine with a delayed configuration provider.

The provider is called only for finite, nonzero inputs outside the tiny-argument branch.
Exceptional inputs keep their ordinary encoded results: NaNs are quieted and infinities give the
format's invalid result.
-/
def sinCosWithProvider {fmt : FloatFormat}
    (getConfig : Unit → Transcendentals.Config)
    (x : Model fmt) : Model fmt × Model fmt :=
  if isNaN x then
    let quiet := quietNaN x
    (quiet, quiet)
  else if isInf x then
    (invalidResult fmt, invalidResult fmt)
  else if isZero x then
    (x, posOne fmt)
  else
    match toDyadic? x with
    | none => (invalidResult fmt, invalidResult fmt)
    | some exact =>
        let leadingExponent := Int.ofNat (Nat.log2 exact.significand) + exact.exponent
        if leadingExponent < -(Int.ofNat (fmt.fracWidth + 2)) then
          (x, posOne fmt)
        else
          Transcendentals.sinCosScaledWith fmt (getConfig ()) exact

/-- Joint deterministic sine/cosine evaluation with the given approximation data. -/
def sinCosWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt × Model fmt :=
  sinCosWithProvider (fun _ => config) x

/-- Deterministic sine with the given approximation data. -/
@[inline] def sinWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  (sinCosWith config x).1

/-- Deterministic cosine with the given approximation data. -/
@[inline] def cosWith {fmt : FloatFormat}
    (config : Transcendentals.Config) (x : Model fmt) : Model fmt :=
  (sinCosWith config x).2

/-- Joint sine/cosine evaluation using the default configuration. -/
@[inline] def sinCos {fmt : FloatFormat} (x : Model fmt) : Model fmt × Model fmt :=
  sinCosWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x

/-- Sine using the default configuration. -/
@[inline] def sin {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  (sinCosWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x).1

/-- Cosine using the default configuration. -/
@[inline] def cos {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  (sinCosWithProvider (fun _ => Transcendentals.Config.forFormat fmt) x).2

end Model
end FloatLib.Floats.Formats.BinaryInterchange
