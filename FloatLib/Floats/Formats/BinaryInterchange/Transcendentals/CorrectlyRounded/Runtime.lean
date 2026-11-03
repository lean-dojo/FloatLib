/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Algebraic.Rounding.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Certified.Runtime

/-!
# Correctly rounded binary exponential and logarithm for every input

`CorrectlyRounded.exp`, `log`, `expMinus1`, `logPlus1`, and the weighted exponential `expMul`
always return a value. A finite argument first goes to an enclosure search. When the search does
not settle, exact comparisons of the real result with rational candidates decide the rounding
through `AlgebraicRounding.round`, as in `Model.pi`. These comparisons terminate for every
rational boundary, so no budget limits the result. For an IEEE descriptor and a finite input in
the domain, a finite result is the nearest-even rounding of the real function, and any other
result is the infinity with the sign of the real result. A finite input outside the domain never
gives a finite result. NaNs are quieted, and infinities, zeros, and arguments outside the domain
get their IEEE 754 results. A result decided by comparisons, such as an overflow, a subnormal
exponential, or a finite result in a descriptor other than IEEE, compares the real result with
rational rounding candidates. An exponential comparison with a positive boundary becomes the
comparison of the argument with the logarithm of the boundary, and the cases decided exactly,
such as `log 1 = 0` and so `exp 0 = 1`, return without separation. The remaining comparisons
refine rational enclosures of the logarithm until one of them excludes the candidate.
Termination is proved, but the proof bounds neither the number of refinements nor the size of the
rationals.

The exponential and `expMinus1` searches are those of `Certified.expRat` and
`Certified.expMinus1Rat`, and use both fields of the budget. The logarithm search writes its
argument as `s * 2 ^ e` with `s` in `[3/4, 3/2)` and adds the cached table reduction
`Certified.logReduced` of `log s` to `e` times the cached `log 2`, on grids that start at the
destination precision plus guard bits and the bits that cancel when `s` is near one. It uses
`maxAttempts` but not `initialDegree`, which has no effect on `log` and `logPlus1`. `expMul x w`
rounds `exp x * w` once. Its search reduces `x` by a multiple `k` of `log 2` and rounds the
enclosure of `exp (x - k * log 2)` times the significand of `w`, scaled by `2 ^ k` and the
exponent of `w` without forming that power. So for finite operands the product is finite whenever
its rounding is, even when `exp x` alone overflows, and a zero weight with a finite `x` gives the
zero with the weight's sign. NaN operands and `exp (±∞)` follow the IEEE 754 product rules
described at `expMul`, so `expMul (+∞) 0` is invalid.

A descriptor other than IEEE skips the searches, and the comparisons decide every finite result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded

open FloatLib.Numerics

/-! ## Exact comparisons -/

/-- Compare `|exp argument - 1|` with a rational boundary. -/
def compareAbsExpMinus1 (argument boundary : ℚ) : Ordering :=
  if argument < 0 then (ElementaryComparison.compareExp argument (1 - boundary)).swap
  else ElementaryComparison.compareExp argument (boundary + 1)

/-- Compare `|log argument|` with a rational boundary, for a positive argument. -/
def compareAbsLog (argument : ℚ) (hpositive : 0 < argument) (boundary : ℚ) : Ordering :=
  ElementaryComparison.compareLog (max argument argument⁻¹) boundary
    (lt_max_of_lt_left hpositive)

/-- Compare `exp argument * weight` with a rational boundary, for a positive weight. -/
def compareExpMul (argument weight boundary : ℚ) : Ordering :=
  ElementaryComparison.compareExp argument (boundary / weight)

/-! ## Enclosure searches -/

/--
Enclose `log (scaled * 2 ^ binaryExponent)` on the grid of `precision` fractional bits, adding
`binaryExponent` times the cached `log 2` to the table reduction of `log scaled`.
-/
def logEnclosure (scaled : ℚ) (binaryExponent : ℤ) (precision : Nat) : RationalInterval :=
  FloatLib.Numerics.Enclosure.BinaryGrid.toRationalInterval precision
    (Interval.BinaryGrid.add (Certified.logReduced scaled precision)
      (FloatLib.Numerics.Enclosure.BinaryGrid.scaleRat
        (FloatLib.Numerics.Enclosure.Constants.ln2Grid precision) binaryExponent))

/--
The first grid of a logarithm search: the destination precision with guard bits, plus the bits
that cancel in `log scaled` when `scaled` is near one and `binaryExponent` is zero.
-/
def logPrecision (fmt : FloatFormat) (scaled : ℚ) (binaryExponent : ℤ) : Nat :=
  let cancellation :=
    if binaryExponent = 0 then (scaled - 1).den.log2 - (scaled - 1).num.natAbs.log2 else 0
  FloatLib.Numerics.Enclosure.BinaryGrid.workingPrecision (fmt.fracWidth + 1 + cancellation) 0

/--
Round the logarithm of a positive rational if both endpoints of an enclosure select one finite
encoding within `budget.maxAttempts` attempts, refining the grid after each failure. The table
reduction picks its series lengths from the grid, so `budget.initialDegree` is unused. A
descriptor other than IEEE gives `none` at once.
-/
def logSearch (fmt : FloatFormat) (argument : ℚ) (budget : Certified.Budget) :
    Option (Model fmt) :=
  if fmt.isIEEE then
    let split := Certified.splitTwoPow argument
    RationalInterval.refine (fun _ precision => logEnclosure split.1 split.2 precision)
      (Enclosure.round? fmt) 1 (logPrecision fmt split.1 split.2) budget.maxAttempts
  else none

/--
An integer near `argument / log 2`, from the 52-bit approximation `6497320848556798 / 2 ^ 52` of
`1 / log 2`. Any integer is sound.
-/
def logTwoMultiple (argument : ℚ) : ℤ :=
  ⌊argument * 6497320848556798 / 2 ^ 52 + 1 / 2⌋

/--
Enclose `exp (argument - multiple * log 2)`, reading the reduced argument on grids of `precision`
plus `extraBits` fractional bits.
-/
def expReducedEnclosure (argument : ℚ) (multiple : ℤ) (extraBits degree precision : Nat) :
    RationalInterval :=
  Certified.expReduced
    (fun grid => Interval.BinaryGrid.sub (Interval.BinaryGrid.enclose grid argument)
      (FloatLib.Numerics.Enclosure.BinaryGrid.scaleRat
        (FloatLib.Numerics.Enclosure.Constants.ln2Grid grid) multiple))
    extraBits degree precision

/--
Round `exp argument * weight` if the enclosure search settles within `budget.maxAttempts`
attempts.

With `k = logTwoMultiple argument`, the search encloses `exp (argument - k * log 2)` times the
signed significand of `weight`, and rounds it scaled by `2 ^ (k + weight.exponent)`. A product
whose binade is evidently beyond the finite range or below half the least subnormal gives `none`
before any enclosure, as does a descriptor other than IEEE: exact comparisons settle those cases.
-/
def expMulSearch (fmt : FloatFormat) (argument : ℚ) (weight : Numerics.Dyadic)
    (budget : Certified.Budget) : Option (Model fmt) :=
  let multiple := logTwoMultiple argument
  let lead := multiple + weight.exponent + weight.significand.log2
  if fmt.isIEEE ∧ fmt.minSubnormalExponent - 2 ≤ lead ∧ lead ≤ fmt.maxNormalExponent + 1 then
    let degree := max 1 budget.initialDegree
    RationalInterval.refine
      (fun degree precision =>
        (expReducedEnclosure argument multiple (Certified.magnitudeBits multiple + 1) degree
          precision).scale weight.signedSignificand)
      (fun interval => Enclosure.roundScaled? fmt interval (multiple + weight.exponent))
      degree
      (FloatLib.Numerics.Enclosure.BinaryGrid.workingPrecision (fmt.fracWidth + 1) degree)
      budget.maxAttempts
  else none

/-! ## Rational arguments -/

/--
Round `exp argument` for an exact rational: the certified search, then exact comparisons with
the rounding candidates when it returns a failure.
-/
def expRat (fmt : FloatFormat) (argument : ℚ) (budget : Certified.Budget := {}) :
    Model fmt :=
  match Certified.expRat fmt argument budget with
  | .ok result => result
  | .error _ => AlgebraicRounding.round fmt false (ElementaryComparison.compareExp argument)

/--
Round `exp argument - 1` for an exact rational: the certified search, then exact comparisons
when it returns a failure.
-/
def expMinus1Rat (fmt : FloatFormat) (argument : ℚ) (budget : Certified.Budget := {}) :
    Model fmt :=
  match Certified.expMinus1Rat fmt argument budget with
  | .ok result => result
  | .error _ =>
      AlgebraicRounding.round fmt (decide (argument < 0)) (compareAbsExpMinus1 argument)

/--
Round `log argument` for a positive rational: the table-reduced search, then exact comparisons
when it does not settle.
-/
def logRat (fmt : FloatFormat) (argument : ℚ) (hpositive : 0 < argument)
    (budget : Certified.Budget := {}) : Model fmt :=
  match logSearch fmt argument budget with
  | some result => result
  | none =>
      AlgebraicRounding.round fmt (decide (argument < 1)) (compareAbsLog argument hpositive)

/--
Round `exp argument * weight` for an exact rational argument and a nonzero dyadic weight: the
reduced search, then exact comparisons when it does not settle.
-/
def expMulRat (fmt : FloatFormat) (argument : ℚ) (weight : Numerics.Dyadic)
    (budget : Certified.Budget := {}) : Model fmt :=
  match expMulSearch fmt argument weight budget with
  | some result => result
  | none =>
      AlgebraicRounding.round fmt weight.negative (compareExpMul argument |weight.toRat|)

/-! ## Encoded inputs -/

/--
The exponential, correctly rounded for every finite input of an IEEE descriptor.

NaNs are quieted, `+∞` gives `+∞`, and `-∞` gives `+0`.
-/
def exp {fmt : FloatFormat} (input : Model fmt) (budget : Certified.Budget := {}) :
    Model fmt :=
  if isNaN input then quietNaN input
  else if isInf input then if signBit input then zero fmt false else nativeOverflow fmt false
  else
    match toRat? input with
    | some argument => expRat fmt argument budget
    | none => invalidResult fmt

/--
`exp x - 1` with one rounding, correctly rounded for every finite input of an IEEE descriptor.

NaNs are quieted, `+∞` gives `+∞`, `-∞` gives `-1`, and either zero is returned unchanged.
-/
def expMinus1 {fmt : FloatFormat} (input : Model fmt) (budget : Certified.Budget := {}) :
    Model fmt :=
  if isNaN input then quietNaN input
  else if isInf input then if signBit input then negOne fmt else nativeOverflow fmt false
  else if isZero input then input
  else
    match toRat? input with
    | some argument => expMinus1Rat fmt argument budget
    | none => invalidResult fmt

/--
The natural logarithm, correctly rounded for every positive finite input of an IEEE descriptor.

NaNs are quieted, `+∞` gives `+∞`, either zero gives `-∞`, and negative inputs, `-∞` included,
give the invalid result. `budget.initialDegree` has no effect.
-/
def log {fmt : FloatFormat} (input : Model fmt) (budget : Certified.Budget := {}) :
    Model fmt :=
  if isNaN input then quietNaN input
  else if isInf input then if signBit input then invalidResult fmt else nativeOverflow fmt false
  else if isZero input then nativeOverflow fmt true
  else
    match toRat? input with
    | some argument =>
        if hpositive : 0 < argument then logRat fmt argument hpositive budget
        else invalidResult fmt
    | none => invalidResult fmt

/--
`log (1 + x)` with the sum formed exactly, correctly rounded for every finite input above `-1` of
an IEEE descriptor.

NaNs are quieted, `+∞` gives `+∞`, either zero is returned unchanged, `-1` gives `-∞`, and inputs
below `-1`, `-∞` included, give the invalid result. `budget.initialDegree` has no effect.
-/
def logPlus1 {fmt : FloatFormat} (input : Model fmt) (budget : Certified.Budget := {}) :
    Model fmt :=
  if isNaN input then quietNaN input
  else if isInf input then if signBit input then invalidResult fmt else nativeOverflow fmt false
  else if isZero input then input
  else
    match toRat? input with
    | some argument =>
        if hpositive : 0 < 1 + argument then logRat fmt (1 + argument) hpositive budget
        else if argument = -1 then nativeOverflow fmt true
        else invalidResult fmt
    | none => invalidResult fmt

/--
`exp x * w` with one rounding, correctly rounded for all finite inputs of an IEEE descriptor.

The exponential is never rounded on its own, so for finite operands the product is finite
whenever its rounding is, and a finite input times a zero weight is the zero with the weight's
sign. A NaN operand gives that NaN quieted, the input's first. Otherwise `exp (+∞)` times a
nonzero weight is an infinity with the weight's sign, `exp (-∞)` times a finite weight is a zero
with the weight's sign, and the products `∞ * 0` give the invalid result. A finite input times an
infinite weight is an infinity with the weight's sign.
-/
def expMul {fmt : FloatFormat} (input weight : Model fmt) (budget : Certified.Budget := {}) :
    Model fmt :=
  if isNaN input then quietNaN input
  else if isNaN weight then quietNaN weight
  else if isInf input then
    if signBit input then
      if isInf weight then invalidResult fmt else zero fmt (signBit weight)
    else if isZero weight then invalidResult fmt
    else nativeOverflow fmt (signBit weight)
  else if isInf weight then nativeOverflow fmt (signBit weight)
  else if isZero weight then zero fmt (signBit weight)
  else
    match toRat? input, toDyadic? weight with
    | some argument, some factor => expMulRat fmt argument factor budget
    | _, _ => invalidResult fmt

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.CorrectlyRounded
