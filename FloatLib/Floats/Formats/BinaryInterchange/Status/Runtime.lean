/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
public import FloatLib.Numerics.IEEEStatus

/-!
# IEEE exception status for format-parameterized `Model`

The value operations are pure and take their rounding mode as an argument. This module pairs
their results with the five IEEE exception indicators and a ternary value. Tininess is detected
after rounding, and underflow is raised exactly when a tiny result is inexact.

Overflow is classified from the precision-rounded result with an unbounded exponent range, as in
IEEE 754-2019 §7.4 and the GNU MPFR manual's exception definition:
<https://doi.org/10.1109/IEEESTD.2019.8766229> and
<https://www.mpfr.org/mpfr-current/mpfr.html#Exceptions>.

The ternary value follows MPFR's return-value convention
(<https://www.mpfr.org/mpfr-current/mpfr.html#Rounding-Modes>): it compares the delivered value
with the exact result, so `.lt` means the delivered value is below it. Each producer computes it
by an exact comparison with the exact witness its status uses, and integral rounding compares with
its input, as `mpfr_rint` does. For the producers built on `dyadicRoundingOutcome` and
`rationalRoundingOutcomeScaled`, compiled code makes that comparison once and, below the overflow
threshold, reads the inexact flag from it (`dyadicRoundingOutcome_eq_internal`,
`rationalRoundingOutcomeScaled_eq_internal`). Square root reads `inexact` from its own squared-root
comparison (`sqrt_inexact_iff`). Only integral rounding computes `inexact` apart from its
ternary value.

The arithmetic producers are the status kernels `Model.Internal.Status.add` through
`Model.Internal.Status.sqrt`, and user code calls them as `Model.add x y (status := true)` and its
siblings in `Arithmetic.Runtime`. Results without an exact real counterpart have fixed
conventions, documented at `IEEEOutcome.ternary`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
A format-parameterized executable value paired with its IEEE exception status and its ternary
value.
-/
structure IEEEOutcome (fmt : FloatFormat) where
  /-- Delivered floating-point result. -/
  value : Model fmt
  /-- Exception indicators raised while computing `value`. -/
  status : Numerics.IEEEStatus
  /--
  The delivered value compared with the exact result, as MPFR's ternary value: `.lt` when the
  delivered value is below the exact result, `.eq` when they are equal, `.gt` when it is above.

  Results that have no exact real counterpart follow fixed conventions. A NaN from a NaN operand
  or an invalid operation, an exceptional placeholder such as the positive zero that a fully
  finite format delivers for an invalid operation, and an infinity that is itself the exact result
  all have `.eq`. A finite exact value delivered as an overflow infinity has `.gt` when it is
  positive and `.lt` when it is negative. The NaN that replaces the infinity in a format without
  one gets the same value by convention. An exact infinity delivered as a saturated finite value
  has `.lt` for `+∞` and `.gt` for `-∞`, and so, by convention, has an exact infinity delivered as
  that overflow NaN. These NaN conventions do not order the NaN itself.

  The structure does not tie inexactness to a nonzero ternary value. A saturated integral
  rounding can return its own input with `inexact` raised, and a division by zero that delivers a
  saturated value raises only `divideByZero`, so any relation between the two holds only for
  particular operations.
  -/
  ternary : Ordering
  deriving DecidableEq

/--
The default outcome is an exact `+0` with a clear status: its value is the default all-zero word
and its ternary value is `.eq`.
-/
instance {fmt : FloatFormat} : Inhabited (IEEEOutcome fmt) where
  default := { value := default, status := .clear, ternary := .eq }

/--
Pair a value with the ternary value `.eq` and a status that is clear or raises only invalid
operation.

Exceptional arithmetic paths use it for NaNs, exact infinities and placeholders, whose
`IEEEOutcome.ternary` convention is `.eq`, and for exact finite results such as an exact zero sum.
The constructor proves nothing about exactness. For a remainder, `remainder_exact` proves it on
IEEE descriptors.
-/
@[inline] def outcomeWithInvalid {fmt : FloatFormat}
    (value : Model fmt) (invalid : Bool) : IEEEOutcome fmt :=
  { value
    status := if invalid then { invalid := true } else .clear
    ternary := .eq }

/-- Whether a finite rounded result is zero or subnormal. -/
@[inline] def isTinyAfterRounding {fmt : FloatFormat} (x : Model fmt) : Bool :=
  isFinite x && expField x == 0

/-- Exact positive value of the smallest normal number in `fmt`. -/
def minNormalDyadic (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := pow2 fmt.fracWidth
    exponent := fmt.minSubnormalExponent }

/--
Largest positive number below `minNormalDyadic fmt` on the format's precision grid with an
unbounded exponent range. Its distance from the smallest normal is half one subnormal step.
-/
def underflowPredecessor (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := 2 * pow2 fmt.fracWidth - 1
    exponent := fmt.minSubnormalExponent - 1 }

/--
Positive boundary used by after-rounding tininess detection.

Tininess after rounding is determined by first rounding to the destination precision with an
unbounded exponent range. Immediately below the smallest normal value, that unbounded grid has
half the subnormal spacing, so the midpoint between `minNormal` and its predecessor is one quarter
of a subnormal step below `minNormal`. Both nearest modes take the midpoint itself to `minNormal`,
whose significand is even and whose magnitude is the larger one, so it is not tiny.
-/
def underflowMidpoint (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := 4 * pow2 fmt.fracWidth - 1
    exponent := fmt.minSubnormalExponent - 2 }

/--
Whether a dyadic result is tiny after rounding to the destination precision with an unbounded
exponent range.

Most tiny results show up as zero or subnormal encodings. A result delivered as `minNormal`
needs a mode-sensitive boundary:

* both nearest modes use the midpoint between `minNormal` and its unbounded-grid predecessor,
  which itself rounds to `minNormal`;
* a direction that rounds the magnitude up is tiny up to and including that predecessor;
* a direction that truncates the magnitude is tiny for every magnitude strictly below `minNormal`.
-/
def dyadicIsTinyAfterRounding (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (rounded : Model fmt) : Bool :=
  if isTinyAfterRounding rounded then
    true
  else
    let magnitude := { exact with negative := false }
    match mode with
    | .nearest | .nearestAway =>
        cmpDyadic magnitude (underflowMidpoint fmt) == .lt
    | .towardZero =>
        cmpDyadic magnitude (minNormalDyadic fmt) == .lt
    | .up | .down | .away =>
        if mode.roundsAwayFromZero exact.negative then
          cmpDyadic magnitude (underflowPredecessor fmt) != .gt
        else
          cmpDyadic magnitude (minNormalDyadic fmt) == .lt

/-- Exact positive dyadic value of the largest finite number in `fmt`. -/
def maxFiniteDyadic (fmt : FloatFormat) : Numerics.Dyadic :=
  { negative := false
    significand := pow2 fmt.fracWidth + fmt.maxFiniteFracField
    exponent := fmt.maxNormalExponent - Int.ofNat fmt.fracWidth }

/-- Whether an exact dyadic magnitude exceeds the finite range of `fmt`. -/
def dyadicMagnitudeOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  cmpDyadic { exact with negative := false } (maxFiniteDyadic fmt) == .gt

/--
Positive midpoint between the largest finite value and the next magnitude on the same binary grid.

Nearest-even overflow is decided at this boundary. The midpoint itself overflows exactly when the
largest finite significand is odd, because the conceptual next significand is then even.
-/
def overflowMidpoint (fmt : FloatFormat) : Numerics.Dyadic :=
  let maximum := maxFiniteDyadic fmt
  { negative := false
    significand := 2 * maximum.significand + 1
    exponent := maximum.exponent - 1 }

/-- First grid magnitude beyond the largest finite value. -/
def overflowLimit (fmt : FloatFormat) : Numerics.Dyadic :=
  let maximum := maxFiniteDyadic fmt
  { negative := false
    significand := maximum.significand + 1
    exponent := maximum.exponent }

/-- Whether the largest finite significand is odd. -/
@[inline] def maxFiniteMantissaOdd (fmt : FloatFormat) : Bool :=
  (maxFiniteDyadic fmt).significand % 2 == 1

/-- Whether nearest-even rounding of an exact dyadic magnitude signals overflow. -/
def dyadicNearestEvenOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  match cmpDyadic { exact with negative := false } (overflowMidpoint fmt) with
  | .gt => true
  | .eq => maxFiniteMantissaOdd fmt
  | .lt => false

/--
Whether nearest-away rounding of an exact dyadic magnitude signals overflow.

Nearest-away rounding is decided at the same top finite midpoint as nearest-even rounding, but the
midpoint itself always overflows: a tie rounds away from zero whatever the parity of the largest
finite significand.
-/
def dyadicNearestAwayOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  cmpDyadic { exact with negative := false } (overflowMidpoint fmt) != .lt

/-- Whether truncating an exact dyadic magnitude still exceeds the finite range. -/
def dyadicTruncationOverflows (fmt : FloatFormat) (exact : Numerics.Dyadic) : Bool :=
  cmpDyadic { exact with negative := false } (overflowLimit fmt) != .lt

/--
Whether rounding an exact dyadic signals overflow.

The nearest modes use the top finite midpoint, which overflows under nearest-away rounding and
under nearest-even rounding only when the largest finite significand is odd. A directed mode that
increases the magnitude overflows above `maxFinite`, while a mode that decreases the magnitude
overflows only from `overflowLimit` on. For conventional IEEE encodings, that limit starts the next
binade. For
encodings that reserve a terminal fraction pattern, it can lie within the same binade.
-/
def dyadicRoundingOverflows (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) : Bool :=
  match mode with
  | .nearest => dyadicNearestEvenOverflows fmt exact
  | .nearestAway => dyadicNearestAwayOverflows fmt exact
  | .towardZero => dyadicTruncationOverflows fmt exact
  | .up =>
      if exact.negative then
        dyadicTruncationOverflows fmt exact
      else
        dyadicMagnitudeOverflows fmt exact
  | .down =>
      if exact.negative then
        dyadicMagnitudeOverflows fmt exact
      else
        dyadicTruncationOverflows fmt exact
  | .away => dyadicMagnitudeOverflows fmt exact

/--
Classify rounding an exact dyadic to `rounded` under `mode`.

Finite results use the proof-guided exact decoder. An exceptional `rounded` argument is classified
as overflow or invalid, never as a clear status.
-/
def dyadicRoundingStatus (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (rounded : Model fmt) : Numerics.IEEEStatus :=
  if dyadicRoundingOverflows fmt mode exact then
    { overflow := true, inexact := true }
  else if hfinite : isFinite rounded = true then
    let actual := finiteDyadic rounded hfinite
    let inexact := cmpDyadic exact actual != .eq
    { underflow := dyadicIsTinyAfterRounding fmt mode exact rounded && inexact
      inexact := inexact }
  else if isInf rounded then
    { overflow := true, inexact := true }
  else
    { invalid := true }

/--
Ternary value of delivering `rounded` for the exact dyadic result `exact`.

A finite delivery is compared exactly with `exact` by `cmpDyadic`, the bounded comparison that
`dyadicRoundingStatus` uses for inexactness. A non-finite delivery stands for the overflow of a
finite exact value and gets the sign of `exact`: `.gt` for a positive and `.lt` for a negative
value. For an infinity this is the order, and for the NaN that replaces the infinity in a format
without one it is the convention of `IEEEOutcome.ternary`.
-/
def dyadicTernary {fmt : FloatFormat} (exact : Numerics.Dyadic) (rounded : Model fmt) :
    Ordering :=
  if hfinite : isFinite rounded = true then
    cmpDyadic (finiteDyadic rounded hfinite) exact
  else if exact.negative then
    .lt
  else
    .gt

/--
The outcome of delivering `value` for the exact dyadic result `exact`.

Its status is `dyadicRoundingStatus` and its ternary value is `dyadicTernary`. Compiled code uses
`Internal.Status.dyadicRoundingOutcome`, which builds the same record with one comparison of the
delivered value against `exact`.
-/
def dyadicRoundingOutcome (fmt : FloatFormat) (mode : IEEERoundingMode) (exact : Numerics.Dyadic)
    (value : Model fmt) : IEEEOutcome fmt :=
  { value
    status := dyadicRoundingStatus fmt mode exact value
    ternary := dyadicTernary exact value }

/--
The status and the ternary value of delivering `value` for `exact`, from one comparison.

A finite delivery is decoded once and compared with `exact` once, and that comparison is the
ternary value of `dyadicTernary`. In the finite branch without overflow, inexactness is its
difference from `.eq`: `dyadicRoundingStatus` compares in the other orientation, and the two tests
agree by `cmpDyadic_swap`. The overflow test still comes first in the status and raises `inexact`
by itself, the non-finite branch is that of `dyadicRoundingStatus` and `dyadicTernary`, and
tininess is computed only for an inexact result.
-/
def Internal.Status.dyadicRoundingClassification (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) : Numerics.IEEEStatus × Ordering :=
  if hfinite : isFinite value = true then
    let ternary := cmpDyadic (finiteDyadic value hfinite) exact
    let status : Numerics.IEEEStatus :=
      if dyadicRoundingOverflows fmt mode exact then
        { overflow := true, inexact := true }
      else
        let inexact := ternary != .eq
        { underflow := if inexact then dyadicIsTinyAfterRounding fmt mode exact value else false
          inexact }
    (status, ternary)
  else
    let status : Numerics.IEEEStatus :=
      if dyadicRoundingOverflows fmt mode exact then
        { overflow := true, inexact := true }
      else if isInf value then
        { overflow := true, inexact := true }
      else
        { invalid := true }
    (status, if exact.negative then .lt else .gt)

/--
Compiled form of `dyadicRoundingOutcome`, built from one
`Internal.Status.dyadicRoundingClassification` call.

The record is built outside every branch, so a caller that keeps only the value lets the compiler
drop the classification call altogether. Classification is a separate function for the same
reason: its branches, inlined into such a caller, would survive as dead tests.
-/
@[inline] def Internal.Status.dyadicRoundingOutcome (fmt : FloatFormat) (mode : IEEERoundingMode)
    (exact : Numerics.Dyadic) (value : Model fmt) : IEEEOutcome fmt :=
  let classification := Internal.Status.dyadicRoundingClassification fmt mode exact value
  { value, status := classification.1, ternary := classification.2 }

/--
Compiled code builds every dyadic rounding outcome with one delivered-versus-exact comparison on
the finite branch.

The equality holds for every exact value and every delivered value, finite or not. It is
registered before every producer in this module and in importing modules, so each of them is
compiled with the shared comparison.
-/
@[csimp] theorem dyadicRoundingOutcome_eq_internal :
    @dyadicRoundingOutcome = @Internal.Status.dyadicRoundingOutcome := by
  funext fmt mode exact value
  unfold dyadicRoundingOutcome Internal.Status.dyadicRoundingOutcome
    Internal.Status.dyadicRoundingClassification
    dyadicRoundingStatus dyadicTernary
  by_cases hfinite : isFinite value = true
  · simp only [dite_eq_left hfinite, IEEEOutcome.mk.injEq, true_and]
    generalize finiteDyadic value hfinite = actual
    have hcomparison : (cmpDyadic exact actual != .eq) = (cmpDyadic actual exact != .eq) := by
      rw [← cmpDyadic_swap exact]
      cases cmpDyadic exact actual <;> rfl
    refine ⟨?_, trivial⟩
    split
    · rfl
    · rw [hcomparison]
      cases cmpDyadic actual exact != .eq <;> simp
  · simp only [dite_eq_right hfinite]

/--
Ternary value of delivering `value` when the exact result is the infinity with sign `negative`.

The infinity itself has `.eq`. Any other delivery has `.lt` for `+∞` and `.gt` for `-∞`. For the
saturated finite value of a fully finite format this is the order, and for the NaN that a format
without infinities returns instead it is the convention of `IEEEOutcome.ternary`, chosen so that
the value agrees with the overflow and inexact flags that casts and reductions raise there.
-/
def exactInfinityTernary {fmt : FloatFormat} (negative : Bool) (value : Model fmt) :
    Ordering :=
  if isInf value && signBit value == negative then
    .eq
  else if negative then
    .gt
  else
    .lt

/-- Exact equality between `(numerator / denominator) * 2^exponent` and a signed dyadic. -/
def rationalEqualsDyadicScaled (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (value : Numerics.Dyadic) : Bool :=
  Numerics.RationalBinary.compareDyadicScaled? sign numerator denominator exponent value == some .eq

/-- Whether a positive scaled rational magnitude exceeds the finite range of `fmt`. -/
def rationalMagnitudeOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  if denominator == 0 || numerator == 0 then
    false
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    let maximumExponent := fmt.maxNormalExponent
    if totalExponent < maximumExponent then
      false
    else if totalExponent > maximumExponent then
      true
    else
      let maximum := maxFiniteDyadic fmt
      let scaled :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator
          (denominator * maximum.significand) (exponent - maximum.exponent)
      scaled.1 > scaled.2

/-- Whether nearest-even rounding of a positive scaled rational signals overflow. -/
def rationalNearestEvenOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  match Numerics.RationalBinary.compareDyadicScaled? false numerator denominator exponent
      (overflowMidpoint fmt) with
  | some .gt => true
  | some .eq => maxFiniteMantissaOdd fmt
  | some .lt | none => false

/--
Whether nearest-away rounding of a positive scaled rational signals overflow.

As for dyadics, the top finite midpoint itself overflows whatever the parity of the largest finite
significand.
-/
def rationalNearestAwayOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  match Numerics.RationalBinary.compareDyadicScaled? false numerator denominator exponent
      (overflowMidpoint fmt) with
  | some .gt | some .eq => true
  | some .lt | none => false

/-- Whether truncating a scaled rational magnitude still exceeds the finite range. -/
def rationalTruncationOverflowsScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  match Numerics.RationalBinary.compareDyadicScaled? false numerator denominator exponent
      (overflowLimit fmt) with
  | some .gt | some .eq => true
  | some .lt | none => false

/--
Whether rounding an exact signed scaled rational signals overflow.

The nearest modes use the top finite midpoint, as for dyadics. The sign determines whether an
infinity-directed mode increases or decreases magnitude. Magnitude-increasing rounding, rounding
away from zero included, overflows above `maxFinite`, while truncating rounding uses
`overflowLimit`.
-/
def rationalRoundingOverflowsScaled (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) (numerator denominator : Nat) (exponent : Int) : Bool :=
  match mode with
  | .nearest => rationalNearestEvenOverflowsScaled fmt numerator denominator exponent
  | .nearestAway => rationalNearestAwayOverflowsScaled fmt numerator denominator exponent
  | .towardZero =>
      rationalTruncationOverflowsScaled fmt numerator denominator exponent
  | .up =>
      if sign then
        rationalTruncationOverflowsScaled fmt numerator denominator exponent
      else
        rationalMagnitudeOverflowsScaled fmt numerator denominator exponent
  | .down =>
      if sign then
        rationalMagnitudeOverflowsScaled fmt numerator denominator exponent
      else
        rationalTruncationOverflowsScaled fmt numerator denominator exponent
  | .away =>
      rationalMagnitudeOverflowsScaled fmt numerator denominator exponent

/-- Whether rounding an exact rational signals overflow. -/
def rationalRoundingOverflows (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) (numerator denominator : Nat) : Bool :=
  rationalRoundingOverflowsScaled fmt mode sign numerator denominator 0

/--
Whether a scaled rational result is tiny after rounding to the destination precision with an
unbounded exponent range.

As with dyadics, an encoded zero or subnormal is tiny. A result delivered as `minNormal` uses the
nearest midpoint, the unbounded-grid predecessor, or `minNormal` itself according to the rounding
direction and sign.
-/
def rationalIsTinyAfterRoundingScaled (fmt : FloatFormat) (mode : IEEERoundingMode)
    (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (rounded : Model fmt) : Bool :=
  if isTinyAfterRounding rounded then
    true
  else
    let boundary :=
      match mode with
      | .nearest | .nearestAway => underflowMidpoint fmt
      | .towardZero => minNormalDyadic fmt
      | .up | .down | .away =>
          if mode.roundsAwayFromZero sign then
            underflowPredecessor fmt
          else
            minNormalDyadic fmt
    match Numerics.RationalBinary.compareDyadicScaled?
        false numerator denominator exponent boundary with
    | some .lt => true
    | some .eq => mode.roundsAwayFromZero sign
    | some .gt | none => false

/--
Classify rounding an exact scaled signed rational to `rounded` under `mode`.

For a nonzero denominator, finite results are compared with the exact rational. Exceptional
results are classified as overflow or invalid, as in `dyadicRoundingStatus`. Division handles a
zero denominator before calling this classifier.
-/
def rationalRoundingStatusScaled (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (rounded : Model fmt) : Numerics.IEEEStatus :=
  if rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent then
    { overflow := true, inexact := true }
  else if hfinite : isFinite rounded = true then
    let actual := finiteDyadic rounded hfinite
    let inexact :=
      !(rationalEqualsDyadicScaled sign numerator denominator exponent actual)
    { underflow :=
        rationalIsTinyAfterRoundingScaled fmt mode sign numerator denominator exponent rounded &&
          inexact
      inexact := inexact }
  else if isInf rounded then
    { overflow := true, inexact := true }
  else
    { invalid := true }

/--
Ternary value of delivering `rounded` for the exact signed rational
`±(numerator / denominator) * 2^exponent`, where `sign` is the sign.

A finite delivery is compared exactly with the rational by `compareDyadicScaled?`, the comparison
that `rationalRoundingStatusScaled` uses for inexactness, with its orientation reversed: that
comparator orders the rational before the delivered value. A non-finite delivery gets the sign,
as in `dyadicTernary`. With a zero denominator, which no operation passes, a finite delivery gives
`.eq`.
-/
def rationalTernaryScaled {fmt : FloatFormat} (sign : Bool) (numerator denominator : Nat)
    (exponent : Int) (rounded : Model fmt) : Ordering :=
  if hfinite : isFinite rounded = true then
    match Numerics.RationalBinary.compareDyadicScaled? sign numerator denominator exponent
        (finiteDyadic rounded hfinite) with
    | some order => order.swap
    | none => .eq
  else if sign then
    .lt
  else
    .gt

/--
The outcome of delivering `value` for the exact signed rational
`±(numerator / denominator) * 2^exponent`, where `sign` is the sign.

Its status is `rationalRoundingStatusScaled` and its ternary value is `rationalTernaryScaled`.
Compiled code uses `Internal.Status.rationalRoundingOutcomeScaled`, which builds the same record
with one comparison of the delivered value against the rational.
-/
def rationalRoundingOutcomeScaled (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) (value : Model fmt) : IEEEOutcome fmt :=
  { value
    status := rationalRoundingStatusScaled fmt mode sign numerator denominator exponent value
    ternary := rationalTernaryScaled sign numerator denominator exponent value }

/--
The status and the ternary value of delivering `value` for the exact scaled rational, from one
comparison.

A finite delivery is decoded once and compared with the rational by `compareDyadicScaled?` once.
Inexactness is whether that comparison differs from `some .eq`, as in
`rationalRoundingStatusScaled`, and the ternary value reverses its orientation, as in
`rationalTernaryScaled`. Inexactness is not read off the ternary value: with a zero denominator the
comparator returns `none`, which is inexact and still has the ternary value `.eq`. The overflow
test still comes first in the status, the non-finite branch is that of both classifiers, and
tininess is computed only for an inexact result.
-/
def Internal.Status.rationalRoundingClassificationScaled (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    Numerics.IEEEStatus × Ordering :=
  if hfinite : isFinite value = true then
    let comparison :=
      Numerics.RationalBinary.compareDyadicScaled? sign numerator denominator exponent
        (finiteDyadic value hfinite)
    let ternary : Ordering :=
      match comparison with
      | some order => order.swap
      | none => .eq
    let status : Numerics.IEEEStatus :=
      if rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent then
        { overflow := true, inexact := true }
      else
        let inexact := !(comparison == some .eq)
        { underflow :=
            if inexact then
              rationalIsTinyAfterRoundingScaled fmt mode sign numerator denominator exponent value
            else
              false
          inexact }
    (status, ternary)
  else
    let status : Numerics.IEEEStatus :=
      if rationalRoundingOverflowsScaled fmt mode sign numerator denominator exponent then
        { overflow := true, inexact := true }
      else if isInf value then
        { overflow := true, inexact := true }
      else
        { invalid := true }
    (status, if sign then .lt else .gt)

/--
Compiled form of `rationalRoundingOutcomeScaled`, built from one
`Internal.Status.rationalRoundingClassificationScaled` call.

As for `Internal.Status.dyadicRoundingOutcome`, the record is built outside every branch, so a
caller that keeps only the value lets the compiler drop the classification call altogether.
-/
@[inline] def Internal.Status.rationalRoundingOutcomeScaled (fmt : FloatFormat)
    (mode : IEEERoundingMode) (sign : Bool) (numerator denominator : Nat) (exponent : Int)
    (value : Model fmt) :
    IEEEOutcome fmt :=
  let classification :=
    Internal.Status.rationalRoundingClassificationScaled fmt mode sign numerator denominator
      exponent value
  { value, status := classification.1, ternary := classification.2 }

/--
Compiled code builds every scaled rational rounding outcome with one delivered-versus-exact
comparison on the finite branch.

The equality holds for every numerator and denominator, a zero denominator included, and every
delivered value. It is registered before every producer in this module and in importing modules,
so each of them is compiled with the shared comparison.
-/
@[csimp] theorem rationalRoundingOutcomeScaled_eq_internal :
    @rationalRoundingOutcomeScaled = @Internal.Status.rationalRoundingOutcomeScaled := by
  funext fmt mode sign numerator denominator exponent value
  unfold rationalRoundingOutcomeScaled Internal.Status.rationalRoundingOutcomeScaled
    Internal.Status.rationalRoundingClassificationScaled rationalRoundingStatusScaled
    rationalTernaryScaled rationalEqualsDyadicScaled
  by_cases hfinite : isFinite value = true
  · simp only [dite_eq_left hfinite, IEEEOutcome.mk.injEq, true_and]
    generalize finiteDyadic value hfinite = actual
    generalize Numerics.RationalBinary.compareDyadicScaled? sign numerator denominator exponent
      actual = comparison
    refine ⟨?_, trivial⟩
    split
    · rfl
    · cases !(comparison == some .eq) <;> simp
  · simp only [dite_eq_right hfinite]

namespace Internal.Status

/--
Addition in rounding direction `mode`, with IEEE exception status and ternary value: the kernel
of `Model.add x y (mode := mode) (status := true)`.

Finite operands compare the delivered value with their exact dyadic sum. An infinite or NaN
operand gives an exact infinity or a NaN, with the ternary value `.eq`.
-/
def add {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      let exact := Model.addDyadic dx dy
      let value := Directed.add mode x y
      Model.dyadicRoundingOutcome fmt mode exact value
  | _, _ =>
      let value := Directed.add mode x y
      let hasNaN := isNaN x || isNaN y
      let generatedInvalid := isInf x && isInf y && Model.signBit x != Model.signBit y
      let invalid := isSNaN x || isSNaN y || (!hasNaN && generatedInvalid)
      outcomeWithInvalid value invalid

/--
Subtraction in rounding direction `mode`, with IEEE exception status and ternary value: the
kernel of `Model.sub x y (mode := mode) (status := true)`.
-/
def sub {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  add x (neg y) mode

/--
Multiplication in rounding direction `mode`, with IEEE exception status and ternary value: the
kernel of `Model.mul x y (mode := mode) (status := true)`.

Finite operands compare the delivered value with their exact dyadic product. An infinite or NaN
operand gives an exact infinity or a NaN, with the ternary value `.eq`.
-/
def mul {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      let exact : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let value := Directed.mul mode x y
      Model.dyadicRoundingOutcome fmt mode exact value
  | _, _ =>
      let value := Directed.mul mode x y
      let hasNaN := isNaN x || isNaN y
      let generatedInvalid := (isInf x && isZero y) || (isInf y && isZero x)
      let invalid := isSNaN x || isSNaN y || (!hasNaN && generatedInvalid)
      outcomeWithInvalid value invalid

/--
Division in rounding direction `mode`, with IEEE exception status and ternary value: the kernel
of `Model.div x y (mode := mode) (status := true)`.

A finite nonzero quotient compares the delivered value with the exact rational quotient. A finite
nonzero value over zero has an exact infinity, so the ternary value is `exactInfinityTernary` of
the delivered overflow result. Zero over a nonzero finite value is exact, and invalid or NaN
operands give the ternary value `.eq`.
-/
def div {fmt : FloatFormat} (x y : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  match toDyadic? x, toDyadic? y with
  | some dx, some dy =>
      let sign := Bool.xor dx.negative dy.negative
      if dy.significand == 0 then
        if dx.significand == 0 then
          outcomeWithInvalid (invalidResult fmt) true
        else
          let value := nativeOverflow fmt sign
          { value
            status := { divideByZero := true }
            ternary := exactInfinityTernary sign value }
      else if dx.significand == 0 then
        { value := zero fmt sign, status := .clear, ternary := .eq }
      else
        let exponentDifference := dx.exponent - dy.exponent
        let value :=
          Internal.Directed.roundRatScaled fmt mode sign dx.significand dy.significand
            exponentDifference
        Model.rationalRoundingOutcomeScaled fmt mode sign dx.significand dy.significand
          exponentDifference value
  | _, _ =>
      let value := Directed.div mode x y
      let hasNaN := isNaN x || isNaN y
      let generatedInvalid := isInf x && isInf y
      let invalid := isSNaN x || isSNaN y || (!hasNaN && generatedInvalid)
      outcomeWithInvalid value invalid

/--
Fused multiply-add in rounding direction `mode`, with IEEE exception status and ternary value:
the kernel of `Model.fma x y z (mode := mode) (status := true)`.

Finite operands compare the delivered value with the exact dyadic `x * y + z`. An infinite or NaN
operand gives an exact infinity or a NaN, with the ternary value `.eq`.

IEEE 754-2019 Section 7.2 leaves it implementation defined whether `fma(0, ∞, c)` signals invalid
when `c` is a quiet NaN. This implementation signals invalid for that case: the invalid product
`0 × ∞` is reported whether or not the addend is a quiet NaN, whereas `add` and `mul` only
report an operand-generated invalid operation when no operand is a NaN.
-/
def fma {fmt : FloatFormat} (x y z : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  match toDyadic? x, toDyadic? y, toDyadic? z with
  | some dx, some dy, some dz =>
      let product : Numerics.Dyadic :=
        { negative := Bool.xor dx.negative dy.negative
          significand := dx.significand * dy.significand
          exponent := dx.exponent + dy.exponent }
      let exact := Model.addDyadic product dz
      let value := Directed.fma mode x y z
      Model.dyadicRoundingOutcome fmt mode exact value
  | _, _, _ =>
      let value := Directed.fma mode x y z
      let hasNaN := isNaN x || isNaN y || isNaN z
      let invalidProduct := (isInf x || isInf y) && (isZero x || isZero y)
      let productIsInf := (isInf x || isInf y) && !(isZero x || isZero y)
      let oppositeInfiniteAddend :=
        productIsInf && isInf z && Model.signBit z != Bool.xor (Model.signBit x) (Model.signBit y)
      let invalid :=
        isSNaN x || isSNaN y || isSNaN z ||
          invalidProduct || (!hasNaN && oppositeInfiniteAddend)
      outcomeWithInvalid value invalid

end Internal.Status

/--
Ternary value of delivering `rounded` for the square root of the nonnegative dyadic `radicand`.

For nonnegative `a` and `b`, `a < √b` holds exactly when `a * a < b`, and likewise for equality.
So the delivery, which is the rounded root, is decoded once and squared exactly, and the square is
compared with `radicand`: the comparison is exact and never evaluates the square root of
`radicand`. It is meaningful only for a nonnegative radicand and a nonnegative delivery, which
`Internal.Status.sqrt` ensures before calling it. A non-finite delivery gets `.gt`, the overflow
convention of `dyadicTernary` for a positive exact value.
-/
@[specialize fmt] def dyadicSqrtTernary {fmt : FloatFormat} (radicand : Numerics.Dyadic)
    (rounded : Model fmt) : Ordering :=
  match toDyadic? rounded with
  | some actual =>
      let square : Numerics.Dyadic :=
        { negative := false
          significand := actual.significand * actual.significand
          exponent := actual.exponent + actual.exponent }
      cmpDyadic square radicand
  | none => .gt

/--
Whether the square root of the dyadic `radicand`, taken as a magnitude, lies below the
after-rounding tininess boundary of `mode`.

The boundaries are those of `dyadicIsTinyAfterRounding`: the underflow midpoint for both nearest
modes, `minNormal` for the directions that truncate a positive value, and the unbounded-grid
predecessor for the directions that round it up. On nonnegative values, comparing `√radicand` with
a positive boundary is equivalent to comparing `radicand` with its square, so the radicand is
compared with the squared boundary and no approximate square root enters the test.
-/
@[specialize fmt] def dyadicSqrtIsTinyAfterRounding (fmt : FloatFormat)
    (mode : IEEERoundingMode) (radicand : Numerics.Dyadic) : Bool :=
  let boundary :=
    match mode with
    | .nearest | .nearestAway => underflowMidpoint fmt
    | .towardZero | .down => minNormalDyadic fmt
    | .up | .away => underflowPredecessor fmt
  let boundarySquared : Numerics.Dyadic :=
    { negative := false
      significand := boundary.significand * boundary.significand
      exponent := boundary.exponent + boundary.exponent }
  match cmpDyadic { radicand with negative := false } boundarySquared with
  | .lt => true
  | .eq => mode.roundsAwayFromZero false
  | .gt => false

namespace Internal.Status

/--
Square root in rounding direction `mode`, with IEEE exception status and ternary value: the
kernel of `Model.sqrt x (mode := mode) (status := true)`.

A NaN raises invalid only when it is signaling. Among the other inputs with a set sign bit, a
zero raises nothing and every other value raises invalid. An input with a clear sign bit is
decoded once: `+∞` and `+0` raise nothing, and a positive finite input compares the delivered root
through its exact square with `dyadicSqrtTernary`. That comparison is the ternary value, and
the result is inexact exactly when it is not `.eq`, that is, when the delivered value is not the
real square root (`sqrt_inexact_iff`). Tininess is tested only for an inexact result:
a zero or subnormal delivery is tiny, and otherwise `dyadicSqrtIsTinyAfterRounding`
decides. That comparison is skipped when `fmt.fracWidth + 1 < fmt.exponentBias`, because then the
least positive radicand already exceeds the square of every boundary
(`dyadicSqrtIsTinyAfterRounding_eq_false`). NaNs, zeros, `+∞`, and the invalid square
root of a negative value have the ternary value `.eq`. `sqrt_status_of_toDyadic` and its
siblings restate the outcome case by case.

A module that calls it with a closed format compiles a copy specialized to that descriptor term by
`@[specialize fmt]` (calls that spell the same descriptor alike share it), and other callers run the
compiled generic body.
-/
@[specialize fmt] def sqrt {fmt : FloatFormat} (x : Model fmt)
    (mode : IEEERoundingMode) : IEEEOutcome fmt :=
  let value := Directed.sqrt mode x
  if Model.signBit x then
    if isNaN x then
      outcomeWithInvalid value (isSNaN x)
    else
      outcomeWithInvalid value (!isZero x)
  else
    match toDyadic? x with
    | none => outcomeWithInvalid value (isSNaN x)
    | some exact =>
        if exact.significand == 0 then
          outcomeWithInvalid value false
        else
          let ternary := dyadicSqrtTernary exact value
          let inexact := ternary != .eq
          let underflow :=
            if inexact then
              if isTinyAfterRounding value then
                true
              else if fmt.fracWidth + 1 < fmt.exponentBias then
                false
              else
                dyadicSqrtIsTinyAfterRounding fmt mode exact
            else
              false
          { value
            status := { underflow, inexact }
            ternary }

end Internal.Status

end Model
end FloatLib.Floats.Formats.BinaryInterchange
