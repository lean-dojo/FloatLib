/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Comparison.Runtime

/-!
# Exact comparison rounding in every rounding direction

`AlgebraicRounding.round` rounds a magnitude to nearest-even from an exact comparison oracle.
`roundSigned` does the same for a signed real and every `IEEERoundingMode`: the five
rounding-direction attributes of IEEE 754-2019, clause 4.3, and rounding away from zero.

The oracle orders the real against every rational. Its answer at zero gives the sign, and the
searches of `AlgebraicRounding` then locate the binade of the magnitude and its truncated
significand with two bits below the last place of the destination. One more comparison says whether
the truncation is exact. The two extra bits and that flag are the guard and sticky bits of the
magnitude on the destination grid, and the direction rounds the magnitude from them with
`IEEERoundingMode.magnitudeRounding`. A rounded magnitude beyond the largest finite value takes
the overflow result of IEEE 754-2019, clause 7.4.

`AlgebraicRounding.Proof` and `DirectedProof` state the real contracts. Nothing here depends on
the width of the format.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding

/--
Deliver the magnitude `mantissa * 2 ^ exponent`, which the caller has already rounded to the grid
of `fmt`, with the sign `sign`.

A magnitude beyond the largest finite value takes the overflow result of the direction `mode`
(IEEE 754-2019, clause 7.4): the native overflow value when the direction rounds that sign away
from zero or to nearest, and the largest finite value otherwise. A zero magnitude is the zero of
that sign.
-/
def packGrid (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool) (mantissa : Nat)
    (exponent : Int) : Model fmt :=
  if mantissa = 0 then zero fmt sign
  else if Numerics.Dyadic.Internal.compareScalable (maxFiniteDyadic fmt)
      (Numerics.Dyadic.mk false mantissa exponent) = .lt then
    directedOverflow fmt sign (mode.overflowRoundsMagnitudeUp sign)
  else roundRatScaled fmt sign mantissa 1 exponent

/--
Round a magnitude located on the grid of `fmt` in the direction `mode`.

`mantissa` is the integer part of the magnitude in units of `2 ^ exponent`, the spacing of the
grid at that magnitude. `guard` says that the remainder is at least half a unit, and `sticky` that
it is neither zero nor exactly half.
-/
def roundLocated (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool) (mantissa : Nat)
    (exponent : Int) (guard sticky : Bool) : Model fmt :=
  let rule := mode.magnitudeRounding sign
  packGrid fmt mode sign
    (if rule.increment (mantissa % 2 == 1) guard sticky then mantissa + 1 else mantissa) exponent

/--
Round a nonzero magnitude given by an exact comparison oracle, in the direction `mode` and with
the sign `sign`.

A magnitude at or beyond `2 ^ upperExponent` overflows. One below half the least subnormal lies
strictly between zero and that midpoint. Every other magnitude gets the truncated significand of
`truncatedMantissa`, whose two low bits and exactness are its guard and sticky bits.
-/
def roundMagnitude (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (compare : Rat → Ordering) : Model fmt :=
  let bounds := powerBounds fmt compare
  if bounds.compare compare (upperExponent fmt) ≠ .lt then
    directedOverflow fmt sign (mode.overflowRoundsMagnitudeUp sign)
  else if bounds.compare compare (lowerExponent fmt) = .lt then
    roundLocated fmt mode sign 0 fmt.minSubnormalExponent false true
  else
    let exponent := certificateExponent fmt (binade fmt compare)
    let mantissa := truncatedMantissa fmt compare exponent
    let exact := compare ((mantissa : Rat) * powerOfTwo exponent) == .eq
    roundLocated fmt mode sign (mantissa / 4) (exponent + 2) (decide (2 ≤ mantissa % 4))
      (mantissa % 2 == 1 || !exact)

/--
Round a real number given by an exact comparison oracle, in the direction `mode`.

`compare boundary` orders the real against the rational `boundary`. A real equal to zero gives the
zero with the sign `zeroSign`, in every direction: the caller knows which zero an exact zero
result is. A negative real rounds its magnitude with the mirrored oracle.
-/
def roundSigned (fmt : FloatFormat) (mode : IEEERoundingMode) (compare : Rat → Ordering)
    (zeroSign : Bool := false) : Model fmt :=
  match compare 0 with
  | .eq => zero fmt zeroSign
  | .gt => roundMagnitude fmt mode false compare
  | .lt => roundMagnitude fmt mode true (fun boundary => (compare (-boundary)).swap)

end FloatLib.Floats.Formats.BinaryInterchange.Model.AlgebraicRounding
