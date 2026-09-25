/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.ExpLog
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Runtime

/-!
# Executable floating-point powers

`Model.pow` provides one deterministic power policy for every `FloatFormat`. For an IEEE descriptor,
a finite nonzero base and a finite integral exponent give a correctly rounded result whenever
that result is finite: its decoded value is nearest-even rounding of the exact power, as for
`Model.powInt`. Small exact powers are computed by `powInt` itself. Larger ones
use directed enclosures of `|x|^n` built by binary exponentiation at a working precision derived
from the format. Repeated squaring stops once the enclosure lies beyond the overflow threshold or
below half the least subnormal, so the exponent is never expanded into an integer when the
answer is already an overflow or a zero. An enclosure whose endpoints round to different values
is refined at a higher precision, and exact evaluation remains the last resort.

Integer exponents are classified directly from their dyadic representation. The classifier records
sign, parity, and an optional bounded magnitude without constructing an integer whose bit length is
controlled by the floating-point exponent field. This is essential for formats with wide exponent
fields.

Non-integral exponents use the generic `exp` and `log` kernels. That path is approximate; this
module does not prove correct rounding for real exponentiation. `Operations.PowerProof` proves the
integral case under the IEEE and finiteness hypotheses above.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

namespace Power

/-- Largest integer magnitude that `classifyInteger?` records in `smallMagnitude?`. -/
def smallPowLimit : Nat := 256

/--
Information needed to evaluate a finite integral floating-point exponent.

`smallMagnitude?` is populated exactly when the magnitude is at most `smallPowLimit`.
-/
structure IntegerExponent where
  /-- Whether the nonzero integer is negative. -/
  negative : Bool
  /-- Whether its magnitude is odd. -/
  odd : Bool
  /-- Its magnitude when small enough for direct evaluation. -/
  smallMagnitude? : Option Nat
  deriving Repr, DecidableEq

/-- Return a magnitude when it is within the direct evaluation limit. -/
@[inline] def smallMagnitude (magnitude : Nat) : Option Nat :=
  if magnitude ≤ smallPowLimit then some magnitude else none

/--
Classify a finite dyadic as an integer.

For a nonnegative dyadic exponent, the left shift is bounded by `log₂ smallPowLimit`; the shifted
magnitude is then checked against the limit. For a negative exponent, divisibility is checked
only when the right shift is no greater than the significand's leading bit index.
-/
def classifyIntegerDyadic? (value : Numerics.Dyadic) : Option IntegerExponent :=
  if value.significand == 0 then
    some { negative := false, odd := false, smallMagnitude? := some 0 }
  else
    match value.exponent with
    | .ofNat shift =>
        let odd := shift == 0 && value.significand % 2 == 1
        let small? :=
          if shift ≤ Nat.log2 smallPowLimit then
            smallMagnitude (Nat.shiftLeft value.significand shift)
          else
            none
        some { negative := value.negative, odd, smallMagnitude? := small? }
    | .negSucc shift =>
        let denominatorShift := shift + 1
        if Nat.log2 value.significand < denominatorShift then
          none
        else
          let magnitude := Nat.shiftRight value.significand denominatorShift
          if Nat.shiftLeft magnitude denominatorShift == value.significand then
            some
              { negative := value.negative
                odd := magnitude % 2 == 1
                smallMagnitude? := smallMagnitude magnitude }
          else
            none

/-- Classify an executable finite value as an integer exponent. -/
@[inline] def classifyInteger? {fmt : FloatFormat}
    (value : Model fmt) : Option IntegerExponent :=
  (toDyadic? value).bind classifyIntegerDyadic?

/--
Repeated rounded multiplication with recurrence `p₀ = 1`, `pₙ₊₁ = base * pₙ`.

Each step rounds, so this is not the correctly rounded power; `pow` uses `integerPower?`.
-/
def powNatLinear {fmt : FloatFormat} (base : Model fmt) : Nat → Model fmt
  | 0 => posOne fmt
  | exponent + 1 => mul base (powNatLinear base exponent)

/--
Evaluate the former direct integer-power path. Callers select magnitudes at most `smallPowLimit`.

For a finite nonzero base `s * 2^e`, a negative exponent of magnitude `n` is rounded from
`(1 / s^n) * 2^(-e*n)`. Only the significand is raised to a power, so the denominator's size is
bounded by the input precision and `smallPowLimit`, independently of the exponent range.
Exceptional bases retain the division and multiplication policies of the format. Positive
exponents round at every step; `pow` now uses `integerPower?`.
-/
@[deprecated "use `Power.integerPower?`" (since := "2026-09-24"), inline]
def powSmallInteger {fmt : FloatFormat}
    (base : Model fmt) (metadata : IntegerExponent) (magnitude : Nat) : Model fmt :=
  if metadata.negative then
    match toDyadic? base with
    | some exact =>
        if exact.significand == 0 then
          div (posOne fmt) (powNatLinear base magnitude)
        else
          roundRatScaled fmt (exact.negative && magnitude % 2 == 1)
            1 (exact.significand ^ magnitude) (-(exact.exponent * Int.ofNat magnitude))
    | none => div (posOne fmt) (powNatLinear base magnitude)
  else
    powNatLinear base magnitude

set_option linter.deprecated false in
/--
Evaluate the former integer-power branch before the negative-base sign rule.

Large magnitudes use the deterministic general path `exp (b * log |a|)`. `pow` now uses
`integerPower?` instead.
-/
@[deprecated "use `Power.integerPower?`" (since := "2026-09-24")] def powIntegerDet {fmt : FloatFormat}
    (base exponent : Model fmt) (metadata : IntegerExponent) : Model fmt :=
  match metadata.smallMagnitude? with
  | some magnitude => powSmallInteger base metadata magnitude
  | none => exp (mul exponent (log (abs base)))

/-! ## Correctly rounded integral exponents -/

/--
A nonnegative dyadic `mantissa * 2^exponent`, used as one endpoint of a power enclosure.

Only the mantissa and the exponent are stored; the value is never materialized as a rational
while its exponent may be far outside the destination range.
-/
structure Endpoint where
  /-- Natural significand. -/
  mantissa : Nat
  /-- Power-of-two scale. -/
  exponent : Int
  deriving Repr, DecidableEq

namespace Endpoint

/-- Exact rational value of an endpoint. -/
@[inline] def toRat (x : Endpoint) : Rat := (x.mantissa : Rat) * 2 ^ x.exponent

/-- The endpoint with value one. -/
@[inline] def one : Endpoint := ⟨1, 0⟩

/-- Exact product of two endpoints. -/
@[inline] def mul (x y : Endpoint) : Endpoint :=
  ⟨x.mantissa * y.mantissa, x.exponent + y.exponent⟩

/-- Number of low mantissa bits above a budget of `precision` significant bits. -/
@[inline] def excess (precision : Nat) (x : Endpoint) : Nat :=
  (Nat.log2 x.mantissa + 1) - precision

/-- Truncate toward zero to at most `precision` significant bits. -/
@[inline] def truncDown (precision : Nat) (x : Endpoint) : Endpoint :=
  let shift := excess precision x
  ⟨x.mantissa >>> shift, x.exponent + shift⟩

/-- Truncate away from zero to at most `precision` significant bits, plus a possible carry. -/
@[inline] def truncUp (precision : Nat) (x : Endpoint) : Endpoint :=
  let shift := excess precision x
  let kept := x.mantissa >>> shift
  ⟨if kept <<< shift == x.mantissa then kept else kept + 1, x.exponent + shift⟩

/-- A sufficient test for `2^bound ≤ x`, read from the leading bit. -/
@[inline] def geTwoPow (x : Endpoint) (bound : Int) : Bool :=
  x.mantissa != 0 && decide (bound ≤ (Nat.log2 x.mantissa : Int) + x.exponent)

/-- A sufficient test for `x ≤ 2^bound`, read from the leading bit. -/
@[inline] def leTwoPow (x : Endpoint) (bound : Int) : Bool :=
  decide ((Nat.log2 x.mantissa : Int) + 1 + x.exponent ≤ bound)

end Endpoint

/--
Directed enclosure of `base ^ exponent` by binary exponentiation.

The first component is rounded down and the second up at every product, each to at most
`precision` significant bits.
-/
def powBounds (precision : Nat) (base : Endpoint) (exponent : Nat) : Endpoint × Endpoint :=
  if exponent = 0 then (Endpoint.one, Endpoint.one)
  else
    let half := powBounds precision base (exponent / 2)
    let lower := Endpoint.truncDown precision (half.1.mul half.1)
    let upper := Endpoint.truncUp precision (half.2.mul half.2)
    if exponent % 2 = 1 then
      (Endpoint.truncDown precision (lower.mul base), Endpoint.truncUp precision (upper.mul base))
    else (lower, upper)
termination_by exponent
decreasing_by omega

/-- Result of repeated squaring of an enclosure against the destination range. -/
inductive Screen where
  /-- The exact power is at least `2 ^ above`. -/
  | above
  /-- The exact power is at most `2 ^ below`. -/
  | below
  /-- The exact power lies between the two endpoints. -/
  | bounds (lower upper : Endpoint)
  deriving Repr, DecidableEq

/--
Square an enclosure `remaining` times, stopping early once it lies beyond `2 ^ above` (with
`above ≥ 0`) or below `2 ^ below` (with `below ≤ 0`). Both regions are closed under squaring,
so an early stop also decides every further squaring.
-/
def squareScreen (precision : Nat) (above below : Int) :
    Nat → Endpoint → Endpoint → Screen
  | remaining, lower, upper =>
    if lower.geTwoPow (max above 0) then .above
    else if upper.leTwoPow (min below 0) then .below
    else
      match remaining with
      | 0 => .bounds lower upper
      | remaining + 1 =>
          squareScreen precision above below remaining
            (Endpoint.truncDown precision (lower.mul lower))
            (Endpoint.truncUp precision (upper.mul upper))

/--
Accept a signed rational enclosure `[lower, upper]` when both endpoints round to the same
finite value.
-/
@[inline] def roundEnclosure? (fmt : FloatFormat) (lower upper : Rat) : Option (Model fmt) :=
  let low := roundAlgebraicRat fmt lower
  if isFinite low = true ∧ low = roundAlgebraicRat fmt upper then some low else none

/-- Working precisions tried in turn: a first guess from the format, then three doublings. -/
@[inline] def workingPrecisions (fmt : FloatFormat) : List Nat :=
  let first := 2 * (fmt.fracWidth + 1) + 2 * (Nat.log2 (AlgebraicRounding.exponentSpan fmt) + 1) + 64
  [first, 2 * first, 4 * first, 8 * first]

/--
One enclosure attempt for `(base ^ (magnitude * 2^shift)) ^ (±1)` at a fixed precision.

`reciprocal` selects the negative exponent and `negative` the sign of the result. Screening
returns an overflow or a signed zero; otherwise both enclosure endpoints must round to the same
finite value. For an IEEE descriptor, every finite result is nearest-even rounding of the exact
target. Every other outcome is `none`.
-/
def attempt (fmt : FloatFormat) (precision : Nat) (negative reciprocal : Bool)
    (base : Endpoint) (magnitude shift : Nat) : Option (Model fmt) :=
  let upperBound := AlgebraicRounding.upperExponent fmt
  let lowerBound := AlgebraicRounding.lowerExponent fmt
  let above := if reciprocal then -lowerBound else upperBound
  let below := if reciprocal then -upperBound else lowerBound
  let cap := precision + 2 * (Nat.log2 (AlgebraicRounding.exponentSpan fmt) + 1) + 16
  let start := powBounds precision base magnitude
  match squareScreen precision above below (min shift cap) start.1 start.2 with
  | .above => some (if reciprocal then zero fmt negative else nativeOverflow fmt negative)
  | .below => some (if reciprocal then nativeOverflow fmt negative else zero fmt negative)
  | .bounds lower upper =>
      if cap < shift || lower.mantissa = 0 || !upper.leTwoPow (max above 0 + 1) ||
          !lower.geTwoPow (min below 0 - 1) then none
      else
        let low := if reciprocal then upper.toRat⁻¹ else lower.toRat
        let high := if reciprocal then lower.toRat⁻¹ else upper.toRat
        if negative then roundEnclosure? fmt (-high) (-low) else roundEnclosure? fmt low high

/-- The integer `(-1)^negative * magnitude * 2^shift`, materialized only for `powInt`. -/
@[inline] def integralValue (negative : Bool) (magnitude shift : Nat) : Int :=
  if negative then -((magnitude <<< shift : Nat) : Int) else ((magnitude <<< shift : Nat) : Int)

/-- Exact results are computed through `powInt` while their exact size is below this bit count. -/
def exactBitBudget : Nat := 65536

/--
Decompose an integral dyadic as `±magnitude * 2^shift`, returning `none` for a non-integer.
The sign is the dyadic's sign field.
-/
def integralParts? (value : Numerics.Dyadic) : Option (Nat × Nat) :=
  match value.exponent with
  | .ofNat shift => some (value.significand, shift)
  | .negSucc shift =>
      let magnitude := value.significand >>> (shift + 1)
      if magnitude <<< (shift + 1) == value.significand then some (magnitude, 0) else none

/--
Integer power of a finite nonzero base with dyadic representation `b`, for the integer
`(-1)^negativeExponent * magnitude * 2^shift`. For an IEEE descriptor, a finite result is
correctly rounded.

Small exact results use `powInt`. A base of magnitude one gives a signed one. Otherwise
directed enclosures are refined through `workingPrecisions`; if none decides the result,
`powInt` computes it exactly. `exactBudget` bounds the exact work in the first case.
-/
def integerPowerWith {fmt : FloatFormat} (exactBudget : Nat) (base : Model fmt)
    (b : Numerics.Dyadic) (negativeExponent : Bool) (magnitude shift : Nat) : Model fmt :=
  let odd := shift == 0 && magnitude % 2 == 1
  let negative := b.negative && odd
  if shift ≤ 64 &&
      (magnitude <<< shift) * (Nat.log2 b.significand + 1 + b.exponent.natAbs) ≤ exactBudget then
    powInt base (integralValue negativeExponent magnitude shift)
  else if b.significand == 1 <<< Nat.log2 b.significand &&
      (Nat.log2 b.significand : Int) + b.exponent == 0 then
    roundAlgebraicRat fmt (if negative then -1 else 1)
  else
    let endpoint : Endpoint := ⟨b.significand, b.exponent⟩
    match (workingPrecisions fmt).findSome? fun precision =>
        attempt fmt precision negative negativeExponent endpoint magnitude shift with
    | some result => result
    | none => powInt base (integralValue negativeExponent magnitude shift)

/--
Power of a finite base by a finite integral exponent, or `none` when either input is nonfinite
or the exponent is not an integer. For an IEEE descriptor and a nonzero base, a finite result is
nearest-even rounding of the exact real power.
-/
def integerPower? {fmt : FloatFormat} (base exponent : Model fmt) : Option (Model fmt) :=
  match toDyadic? base, toDyadic? exponent with
  | some b, some y =>
      (integralParts? y).map fun parts =>
        integerPowerWith exactBitBudget base b y.negative parts.1 parts.2
  | _, _ => none

end Power

/--
Deterministic executable floating-point exponentiation.

The special cases and branch order are explicit:

* `x^(+-0) = 1`, including a NaN base;
* `1^y = 1` except for a signaling-NaN exponent;
* infinite exponents are classified by `|x|` relative to one;
* signed zero and infinite bases give a zero or an overflow, negative exactly for a negative base
  and an odd integer exponent;
* a finite nonzero base with a finite integral exponent uses `Power.integerPower?`; for an IEEE
  descriptor, a finite result is correctly rounded;
* otherwise a finite negative base is invalid, and a positive one uses `exp (y * log x)`.
-/
def pow {fmt : FloatFormat} (base exponent : Model fmt) : Model fmt :=
  if isZero exponent then
    posOne fmt
  else if compare base (posOne fmt) = some .eq && !isSNaN exponent then
    posOne fmt
  else
    match chooseNaN2 base exponent with
    | some nan => nan
    | none =>
        if compare exponent (posOne fmt) = some .eq then
          base
        else if isInf exponent then
          match compare (abs base) (posOne fmt) with
          | some .lt =>
              if signBit exponent then nativeOverflow fmt false else zero fmt false
          | some .eq => posOne fmt
          | some .gt =>
              if signBit exponent then zero fmt false else nativeOverflow fmt false
          | none => invalidResult fmt
        else
          match compare base (zero fmt false) with
          | some .eq =>
              match Power.classifyInteger? exponent with
              | some metadata =>
                  match compare exponent (zero fmt false) with
                  | some .lt =>
                      nativeOverflow fmt (signBit base && metadata.odd)
                  | some .gt =>
                      zero fmt (signBit base && metadata.odd)
                  | _ => zero fmt false
              | none =>
                  match compare exponent (zero fmt false) with
                  | some .lt => nativeOverflow fmt false
                  | _ => zero fmt false
          | _ =>
              if isInf base then
                let negative :=
                  signBit base && (Power.classifyInteger? exponent).any (·.odd)
                match compare exponent (zero fmt false) with
                | some .lt => zero fmt negative
                | _ => nativeOverflow fmt negative
              else
                match Power.integerPower? base exponent with
                | some result => result
                | none =>
                    if signBit base then invalidResult fmt
                    else exp (mul exponent (log base))

end Model
end FloatLib.Floats.Formats.BinaryInterchange
