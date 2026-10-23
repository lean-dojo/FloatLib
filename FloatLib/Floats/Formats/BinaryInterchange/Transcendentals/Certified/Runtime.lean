/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Decode
public import FloatLib.Numerics.Enclosure.Constants.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Numerics.Exact.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
public import FloatLib.Numerics.Enclosure.Elementary.LogTable.Runtime
public import FloatLib.Numerics.Enclosure.Refinement

/-!
# Certified binary exponential, logarithm, and power by enclosure refinement

Exact input decoding and outward-rounded binary-grid enclosures feed a nearest-even endpoint
check. Refinement increases the Taylor degree while the interval shrinks rapidly, and increases
the working precision when that progress stalls. The cases `exp 0 = 1` and `log 1 = 0` use point
enclosures.

Exponential uses format-derived rational argument bounds to skip impossible underflow and overflow
checks. Beyond these bounds, total logarithm-based comparisons handle extreme inputs. These
comparisons terminate independently of the options, which bound the direct enclosure search.
Every accepted result has a finite real-rounding certificate. A call that does not certify a result
returns a `Failure` saying why: an unsupported descriptor, a nonfinite input, an argument outside
the function's domain, a result beyond the finite range, or a search that did not settle.

The power `a ^ b` of a positive base is `exp (b * log a)`. Writing `a = s * 2 ^ e` with `s` near
one, an enclosure of `t = b * log a` settles underflow and rejects overflow. It also gives an
integer `k` near `t / log 2`, from its lower endpoint and a 52-bit approximation of `1 / log 2`,
and any integer is sound. Refinement then encloses `exp (t - k * log 2)` from enclosures of `log s`
and `log 2`, and rounds both endpoints times `2 ^ k` without forming that power. The
exponential's working precision is independent of `|t|`, and the argument grid grows only with
the bit lengths of `b` and `b * e`, so a result near the end of a very wide exponent range needs
no work proportional to `|t|`. The logarithms of `2` and of `j / 32` come from the shared constants
cache of `Numerics.Enclosure.Constants`, which keeps the series short. An exact result that is a
rounding boundary generally does not settle and ends `inconclusive`, but one whose reduced argument
is enclosed exactly, such as binary16 `4 ^ -12.5 = 2 ^ -25`, can still settle.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified

open FloatLib.Numerics

/--
Why a certified evaluation returned no result.

An `inconclusive` result makes no claim about whether more refinement would succeed. The other
cases identify a format, input, domain, or finite-range obstruction.
-/
inductive Failure where
  /-- The descriptor is not an IEEE binary format, which the enclosure kernels require. -/
  | unsupportedFormat
  /-- An input is a NaN or an infinity. -/
  | nonfiniteInput
  /--
  The input is outside the supported real domain: the logarithm of a number at most zero,
  `log (1 + x)` for `x ≤ -1`, or a certified power whose base is at most zero.
  -/
  | domain
  /-- The exact result rounds beyond the largest finite value of the format. -/
  | range
  /--
  The search stopped without a certificate: its budget ran out, or the exact result lies on or
  too close to a rounding boundary, or it is a power the search does not settle.
  -/
  | inconclusive
  deriving DecidableEq, Repr

/-- Degree and attempt budget for direct enclosure refinement. -/
structure Options where
  /-- First Taylor degree. Zero is promoted to one before refinement. -/
  initialDegree : Nat := 8
  /-- Maximum enclosure attempts, including retries at higher degree or precision. -/
  maxSteps : Nat := 16
  deriving DecidableEq, Repr

/-- Try successive enclosures, stopping immediately when the endpoints certify one encoding. -/
@[inline] def refine (fmt : FloatFormat) (enclose : Nat → Nat → RationalInterval)
    (degree precision steps : Nat) : Option (Model fmt) :=
  RationalInterval.refine enclose (Enclosure.round? fmt) degree precision steps

/-- The interval from zero to half the least subnormal, including the even tie at zero. -/
def expUnderflowInterval (fmt : FloatFormat) : RationalInterval :=
  ⟨0, (Numerics.Dyadic.mk false 1 (fmt.minSubnormalExponent - 1)).toRat⟩

/-- First power of two above the normal range, used before direct exponential evaluation. -/
def expUpperBound (fmt : FloatFormat) : ℚ :=
  (Numerics.Dyadic.mk false 1 (fmt.maxNormalExponent + 1)).toRat

/--
The least rational that nearest-even rounding sends beyond the largest finite value of an IEEE
descriptor: the largest finite value plus half its ulp.
-/
def overflowThreshold (fmt : FloatFormat) : ℚ :=
  (Numerics.Dyadic.mk false (2 ^ (fmt.fracWidth + 2) - 1)
    (fmt.maxNormalExponent - fmt.fracWidth - 1)).toRat

/-- Argument lower bound that excludes exponential underflow, using `log 2 > 1/2`. -/
@[inline] def expUnderflowArgumentBound (fmt : FloatFormat) : ℚ :=
  ((fmt.minSubnormalExponent - 1 : ℤ) : ℚ) / 2

/-- Argument upper bound below the exponential overflow guard on supported descriptors. -/
@[inline] def expUpperArgumentBound (fmt : FloatFormat) : ℚ :=
  ((fmt.maxNormalExponent + 1 : ℤ) : ℚ) / 2

/-- Accept a certified encoding, or report `failure` when there is none. -/
@[inline] def accept {fmt : FloatFormat} (result : Option (Model fmt)) (failure : Failure) :
    Except Failure (Model fmt) :=
  match result with
  | some value => .ok value
  | none => .error failure

/--
The failure of an exhausted exponential search: `range` when `exp argument - shift` reaches the
overflow threshold, and `inconclusive` otherwise. The coarse argument screen avoids constructing
the threshold when overflow is already excluded: an IEEE format has `emax ≥ 1`, and
`exp (emax / 2) < 2^emax` lies below its largest finite value.
-/
def expSearchFailure (fmt : FloatFormat) (argument shift : ℚ) : Failure :=
  if fmt.isIEEE = true ∧ 0 ≤ shift ∧ argument ≤ (fmt.maxNormalExponent : ℚ) / 2 then
    .inconclusive
  else if ElementaryComparison.compareExp argument (overflowThreshold fmt + shift) = .lt then
    .inconclusive
  else .range

/-- Round the exponential of an exact rational if the enclosure budget certifies a finite result. -/
@[inline] def expRat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else if argument = 0 then accept (Enclosure.round? fmt (RationalInterval.point 1)) .inconclusive
  else if argument < expUnderflowArgumentBound fmt ∧
      ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
    accept (Enclosure.round? fmt (expUnderflowInterval fmt)) .inconclusive
  else if expUpperArgumentBound fmt < argument ∧
      ElementaryComparison.compareExp argument (expUpperBound fmt) ≠ .lt then .error .range
  else
    let degree := max 1 options.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
      (fmt.fracWidth + 1) argument degree
    let search := refine fmt (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument)
      degree precision options.maxSteps
    -- The exact overflow comparison runs only after an exhausted search.
    accept search (if search.isSome then .inconclusive else expSearchFailure fmt argument 0)

/-- Certify a finite rounded logarithm of a positive rational, rejecting other arguments. -/
@[inline] def logRat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else if argument ≤ 0 then .error .domain
  else if argument = 1 then accept (Enclosure.round? fmt (RationalInterval.point 0)) .inconclusive
  else
    let degree := max 1 options.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.logPrecision
      (fmt.fracWidth + 1) argument degree
    accept (refine fmt (FloatLib.Numerics.Enclosure.BinaryGrid.log argument)
      degree precision options.maxSteps) .inconclusive

/--
Certify `exp argument - 1`, subtracting one from the exact rational enclosure before rounding.

This retains small results that would be lost by rounding the exponential to one first.
The same comparison shortcut as `expRat` handles very negative arguments without constructing
their exponential. Unsupported descriptors, overflow, and an exhausted budget are failures.
-/
@[inline] def expMinus1Rat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else if argument = 0 then
    accept (Enclosure.round? fmt (RationalInterval.point 0)) .inconclusive
  else if argument < expUnderflowArgumentBound fmt ∧
      ElementaryComparison.compareExp argument (expUnderflowInterval fmt).hi ≠ .gt then
    accept (Enclosure.round? fmt ((expUnderflowInterval fmt).sub (RationalInterval.point 1)))
      .inconclusive
  else if expUpperArgumentBound fmt < argument ∧
      ElementaryComparison.compareExp argument (expUpperBound fmt + 1) ≠ .lt then .error .range
  else
    let degree := max 1 options.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
      (fmt.fracWidth + 1) argument degree true
    let search := refine fmt
      (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument
        degree precision).sub (RationalInterval.point 1))
      degree precision options.maxSteps
    accept search (if search.isSome then .inconclusive else expSearchFailure fmt argument 1)

/--
Certify `log (1 + argument)`, forming the sum exactly before enclosing the logarithm.

In particular, a small nonzero argument is not lost by rounding `1 + argument` to one.
Arguments at or below `-1` are a domain failure, and the other failures are those of `logRat`.
-/
@[inline] def logPlus1Rat (fmt : FloatFormat) (argument : ℚ) (options : Options := {}) :
    Except Failure (Model fmt) :=
  logRat fmt (1 + argument) options

/-! ## Real powers -/

/--
An upper bound on the number of bits of `|value|` above the binary point, read from the bit
lengths of its numerator and denominator: `|value| < 2 ^ magnitudeBits value`.
-/
@[inline] def magnitudeBits (value : ℚ) : Nat :=
  value.num.natAbs.log2 + 1 - value.den.log2

/--
Enclose `log value` for a positive rational on the grid of `precision` fractional bits.

With `j` the integer nearest `32 * value`, `log value = log (j / 32) + log (32 * value / j)`: the
first term comes from the cached table `BinaryGrid.Internal.logTable`, and for `value` in
`[3/4, 3/2)` the second argument lies within `1/48` of one, so its series needs about a third of the
terms. Values below `3/4` use the first table entry, since the index saturates at zero. Values from
about `3/2` up, and grids finer than the table's, use `BinaryGrid.logUnreduced` directly. The
identity holds for every positive `j`, so the choice affects the work only.
-/
def logReduced (value : ℚ) (precision : Nat) : Interval Int :=
  let numerator := value.num.natAbs
  let index := (64 * numerator + value.den) / (2 * value.den) - 24
  match FloatLib.Numerics.Enclosure.BinaryGrid.logTableAt? index precision with
  | some entry =>
      Interval.BinaryGrid.add entry
        (FloatLib.Numerics.Enclosure.BinaryGrid.logUnreduced
          (mkRat (32 * numerator) (value.den * (index + 24))) precision)
  | none => FloatLib.Numerics.Enclosure.BinaryGrid.logUnreduced value precision

/--
Enclose `exponent * log s + multiple * log 2` on one grid, from enclosures `logScaled` of `log s`
and `logTwo` of `log 2` on that grid.
-/
def powArgument (logScaled logTwo : Interval Int) (exponent multiple : ℚ) : Interval Int :=
  Interval.BinaryGrid.add (FloatLib.Numerics.Enclosure.BinaryGrid.scaleRat logScaled exponent)
    (FloatLib.Numerics.Enclosure.BinaryGrid.scaleRat logTwo multiple)

/--
Enclose `exp x` for every `x` in `argument` from one exponential enclosure at its lower end.

For a width `w ≤ 1`, `exp (lo + w) ≤ exp lo * (1 + 2 * w)`. A wider argument evaluates the
exponential at its upper end as well.
-/
def expInterval (argument : RationalInterval) (degree precision : Nat) : RationalInterval :=
  let lower := FloatLib.Numerics.Enclosure.BinaryGrid.exp argument.lo degree precision
  let width := argument.hi - argument.lo
  if width ≤ 1 then ⟨lower.lo, lower.hi * (1 + 2 * width)⟩
  else ⟨lower.lo, (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument.hi degree precision).hi⟩

/--
Enclose `exp r` from enclosures `reduced grid` of `r` on grids of `grid` fractional bits.

The argument is taken on the grid of `precision + extraBits` fractional bits.
-/
def expReduced (reduced : Nat → Interval Int) (extraBits : Nat) (degree precision : Nat) :
    RationalInterval :=
  let grid := precision + extraBits
  expInterval (FloatLib.Numerics.Enclosure.BinaryGrid.toRationalInterval grid (reduced grid))
    degree precision

/-- A rational above `log 2`, from `log 2 < 0.6931471808`. -/
def logTwoUpper : ℚ := 6931471808 / 10000000000

/--
Round `(scaled * 2 ^ binaryExponent) ^ exponent` for a positive rational `scaled` if the
enclosure budget certifies a finite result.

An overflow evident from `exponent * binaryExponent` alone fails as `range` before any logarithm.
An enclosure of `t = exponent * log (scaled * 2 ^ binaryExponent)` on the first grid settles a
result below half the least subnormal as `+0`, by rounding `[0, 1]` times
`2 ^ (minSubnormalExponent - 1)` without forming that power. It fails as `range` for a result at
least `2 ^ (maxNormalExponent + 1)`, comparing `t` with the same grid's enclosure of `log 2`.
Otherwise refinement encloses `exp (t - k * log 2)` for an integer `k` near `t / log 2`, reusing
the first enclosure of `t` in its first attempt, and accepts when both endpoints times `2 ^ k`
round to the same finite encoding. The options' degree applies to the exponential, while the
logarithm series take their degrees from the grid. Unsupported descriptors, nonpositive `scaled`,
overflow, and an exhausted budget are failures. A result within a rounding step of the overflow
threshold also ends the search as `inconclusive`.
-/
def powRatScaled (fmt : FloatFormat) (scaled : ℚ) (binaryExponent : ℤ) (exponent : ℚ)
    (options : Options := {}) : Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else if scaled ≤ 0 then .error .domain
  else if exponent = 0 then accept (Enclosure.round? fmt (RationalInterval.point 1)) .inconclusive
  else
    let product := exponent * binaryExponent
    -- For `scaled` in `[1/2, 2)`, `|log₂ scaled| ≤ 1`, so `t / log 2 ≥ product - |exponent|`.
    if 1 / 2 ≤ scaled ∧ scaled < 2 ∧
        ((fmt.maxNormalExponent + 1 : ℤ) : ℚ) + |exponent| ≤ product then .error .range
    else
      let degree := max 1 options.initialDegree
      let precision :=
        FloatLib.Numerics.Enclosure.BinaryGrid.workingPrecision (fmt.fracWidth + 1) degree
      let extraBits := max (magnitudeBits exponent) (magnitudeBits product) + 1
      let firstGrid := precision + extraBits
      let logTwo := Numerics.Enclosure.Constants.ln2Grid firstGrid
      let argument := powArgument (logReduced scaled firstGrid) logTwo exponent product
      if FloatLib.Numerics.Interval.BinaryGrid.toRat firstGrid argument.hi ≤
          ((fmt.minSubnormalExponent - 1 : ℤ) : ℚ) * logTwoUpper then
        accept (Enclosure.roundScaled? fmt ⟨0, 1⟩ (fmt.minSubnormalExponent - 1)) .inconclusive
      -- Both sides are on the first grid, and `t ≥ (maxNormalExponent + 1) * log 2` overflows.
      else if (fmt.maxNormalExponent + 1) * logTwo.hi ≤ argument.lo then .error .range
      else
        -- An integer near `t / log 2` from the lower endpoint, with `1 / log 2` taken as
        -- `6497320848556798 / 2 ^ 52`. Any integer is sound.
        let scale : ℤ :=
          (argument.lo * 6497320848556798 + (1 : ℤ) <<< (firstGrid + 51)) >>> (firstGrid + 52)
        let multiple := product - scale
        let reduced := fun grid =>
          if grid = firstGrid then
            Interval.BinaryGrid.sub argument
              (FloatLib.Numerics.Enclosure.BinaryGrid.scaleRat logTwo scale)
          else
            powArgument (logReduced scaled grid) (Numerics.Enclosure.Constants.ln2Grid grid)
              exponent multiple
        accept (RationalInterval.refine (expReduced reduced extraBits)
          (fun interval => Enclosure.roundScaled? fmt interval scale) degree precision
          options.maxSteps) .inconclusive

/-- Write a positive rational as `scaled * 2 ^ exponent` with `scaled` in `[3/4, 3/2)`. -/
def splitTwoPow (value : ℚ) : ℚ × ℤ :=
  let exponent := Numerics.RationalBinary.floorLog2 value.num.natAbs value.den
  let scaled := value / 2 ^ exponent
  if scaled < 3 / 2 then (scaled, exponent) else (scaled / 2, exponent + 1)

/--
Round `base ^ exponent` for exact rationals with a positive base if the enclosure budget
certifies a finite result. Nonpositive bases, unsupported descriptors, overflow, and an exhausted
budget are failures.
-/
def powRat (fmt : FloatFormat) (base exponent : ℚ) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if base ≤ 0 then .error .domain
  else
    let split := splitTwoPow base
    powRatScaled fmt split.1 split.2 exponent options

/--
An integer `n` with `|exponent * log base| < 2 ^ n` for a positive dyadic base, read from the
stored fields without forming either rational.
-/
def powArgumentExponent (base exponent : Numerics.Dyadic) : ℤ :=
  exponent.exponent + (exponent.significand.log2 + 1 : ℕ) +
    ((base.exponent.natAbs + base.significand.log2 + 1).log2 + 1 : ℕ)

/-- An interval around one that contains `exp t` whenever `|t| < 2 ^ -(fracWidth + 4)`. -/
def powNearOne (fmt : FloatFormat) : RationalInterval :=
  let gap := (Numerics.Dyadic.mk false 1 (-((fmt.fracWidth : ℤ) + 3))).toRat
  ⟨1 - gap, 1 + gap⟩

/--
The failure of a power whose stored exponent field marks an integer exponent too large for the
search: `range` when the power overflows, a base above one with a positive exponent or below one
with a negative exponent, and `inconclusive` otherwise.
-/
def powHugeFailure (base exponent : Numerics.Dyadic) : Failure :=
  let lead : ℤ := (base.significand.log2 : ℤ) + base.exponent
  let above := decide (0 < lead) || (lead == 0 && base.significand != 1 <<< base.significand.log2)
  if exponent.significand != 0 &&
      ((above && !exponent.negative) || (decide (lead < 0) && exponent.negative)) then .range
  else .inconclusive

/-- Certify a finite exponential using exact decoding and outward-rounded enclosures. -/
def exp {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else
    match toRat? input with
    | none => .error .nonfiniteInput
    | some argument => expRat fmt argument options

/-- Certify a finite logarithm. `log 1` returns positive zero. -/
def log {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else
    match toRat? input with
    | none => .error .nonfiniteInput
    | some argument => logRat fmt argument options

/--
Certify `base ^ exponent` for a finite positive base and a finite exponent.

Both inputs are decoded exactly as dyadics, and the base's significand alone is split as
`scaled * 2 ^ e`, so the base's power-of-two scale is never formed. When the stored fields show
`|exponent * log base| < 2 ^ -(fracWidth + 4)` the result rounds to one without forming the
exponent's rational: in a format with a very wide exponent field its denominator can have billions
of bits. An exponent decoded as a dyadic `b` with stored binary exponent
`b.exponent > fracWidth + expWidth + 8` stops before its rational is formed: it is an integer so
large that only a base of one has a finite nonzero rounded power, and `powHugeFailure` reports
whether the power overflows. Once these two checks have bounded its size, the general path forms
the exponent's rational. Non-IEEE descriptors, nonpositive or nonfinite bases, nonfinite exponents,
overflow, and an exhausted budget are failures too.
-/
def pow {fmt : FloatFormat} (base exponent : Model fmt) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else
    match toDyadic? base, toDyadic? exponent with
    | some a, some b =>
        if a.negative || a.significand == 0 then .error .domain
        else if powArgumentExponent a b ≤ -((fmt.fracWidth : ℤ) + 4) then
          accept (Enclosure.round? fmt (powNearOne fmt)) .inconclusive
        else if b.exponent > ((fmt.fracWidth + fmt.expWidth : ℕ) : ℤ) + 8 then
          .error (powHugeFailure a b)
        else
          let split := splitTwoPow a.significand
          powRatScaled fmt split.1 (split.2 + a.exponent) b.toRat options
    | _, _ => .error .nonfiniteInput

/-- Certify `exp x - 1` with one final rounding, preserving either IEEE signed zero. -/
@[inline] def expMinus1 {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else if isZero input then .ok input
  else
    match toRat? input with
    | none => .error .nonfiniteInput
    | some argument => expMinus1Rat fmt argument options

/-- Certify `log (1 + x)` with one final rounding, preserving either IEEE signed zero. -/
@[inline] def logPlus1 {fmt : FloatFormat} (input : Model fmt) (options : Options := {}) :
    Except Failure (Model fmt) :=
  if !fmt.isIEEE then .error .unsupportedFormat
  else if isZero input then .ok input
  else
    match toRat? input with
    | none => .error .nonfiniteInput
    | some argument => logPlus1Rat fmt argument options

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Certified
