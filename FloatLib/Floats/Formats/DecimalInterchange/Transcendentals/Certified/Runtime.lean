/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Certified
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Numerics.Exact.Elementary.Runtime
public import FloatLib.Numerics.Enclosure.Elementary.BinaryGridRuntime
public import FloatLib.Numerics.Enclosure.Refinement

/-!
# Certified decimal exp-minus-one and log-plus-one

Computing `exp x - 1` as written loses most of its digits to cancellation when `x` is tiny, and
`log (1 + x)` has the same problem. These kernels use outward-rounded binary-grid enclosures that
keep the cancellation and the small increment, at a precision that follows the decimal
coefficient width. A result is accepted when both rational endpoints round to the same finite
nearest-even decimal datum. While the interval shrinks quickly, refinement raises the Taylor
degree, and when that progress stalls it raises the working precision.

The kernels return `none` for:

* invalid or nonfinite inputs
* logarithm arguments at or below minus one
* overflow
* inconclusive certification

Valid signed zeros keep their sign and quantum. Rational argument bounds skip impossible tail and
overflow checks. The remaining exact exponential comparisons run outside the search, so
`Certified.Budget` bounds the enclosure attempts and not the work they do.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified

open FloatLib.Numerics
open FloatLib.Floats.Certified

/-- Return the first finite endpoint agreement within the supplied attempt budget. -/
@[inline] def refine (f : Format) (enclose : Nat → Nat → RationalInterval)
    (degree precision steps : Nat) : Option Datum :=
  RationalInterval.refine enclose (Enclosure.round? f) degree precision steps

/-- A small positive exponential bound, one tenth of the precision's last place below one. -/
def expMinus1TailBound (f : Format) : ℚ :=
  (10 : ℚ) ^ (-(f.precision : ℤ) - 1)

/-- A narrow interval above minus one for sufficiently negative exponential arguments. -/
def expMinus1TailInterval (f : Format) : RationalInterval :=
  (⟨0, expMinus1TailBound f⟩ : RationalInterval).sub (RationalInterval.point 1)

/-- First power of ten above the finite range, before adding back the subtracted one. -/
def expMinus1UpperBound (f : Format) : ℚ :=
  (10 : ℚ) ^ (f.maxQuantum + (f.precision : ℤ))

/-- Above this argument, the exponential exceeds the negative-tail bound. -/
def expMinus1TailArgumentBound (f : Format) : ℚ :=
  2 * (-(f.precision : ℚ) - 1)

/--
Below this argument, exponential-minus-one cannot reach the upper bound.
The two slopes use `2 < log 10 < 3`, including formats whose upper exponent is negative.
-/
def expMinus1UpperArgumentBound (f : Format) : ℚ :=
  let exponent := f.maxQuantum + (f.precision : ℤ)
  ((if 0 ≤ exponent then 2 * exponent else 3 * exponent : ℤ) : ℚ)

/--
Certify nearest-even rounding of `exp argument - 1` from an exact rational argument.

One is subtracted from the rational enclosure before either endpoint is rounded.
The exact zero and negative-tail branches can succeed even with no refinement attempts.
-/
@[inline] def expMinus1Rat (f : Format) (argument : ℚ) (budget : Budget := {}) : Option Datum :=
  if argument = 0 then
    Enclosure.round? f (RationalInterval.point 0)
  else if argument < expMinus1TailArgumentBound f ∧
      ElementaryComparison.compareExp argument (expMinus1TailBound f) ≠ .gt then
    Enclosure.round? f (expMinus1TailInterval f)
  else if expMinus1UpperArgumentBound f < argument ∧
      ElementaryComparison.compareExp argument (expMinus1UpperBound f + 1) ≠ .lt then
    none
  else
    let degree := max 1 budget.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.expPrecision
      (f.coefficientBound.log2 + 1) argument degree true
    refine f
      (fun degree precision => (FloatLib.Numerics.Enclosure.BinaryGrid.exp argument
        degree precision).sub (RationalInterval.point 1))
      degree precision budget.maxAttempts

/--
Certify nearest-even rounding of `log (1 + argument)` from an exact rational argument.

The addition is exact, so a small nonzero increment is retained. Arguments at or below
minus one return `none`. Exact zero can succeed without any refinement attempts.
-/
@[inline] def logPlus1Rat (f : Format) (argument : ℚ) (budget : Budget := {}) : Option Datum :=
  if argument ≤ -1 then none
  else if argument = 0 then
    Enclosure.round? f (RationalInterval.point 0)
  else
    let shifted := 1 + argument
    let degree := max 1 budget.initialDegree
    let precision := FloatLib.Numerics.Enclosure.BinaryGrid.logPrecision
      (f.coefficientBound.log2 + 1) shifted degree
    refine f (FloatLib.Numerics.Enclosure.BinaryGrid.log shifted)
      degree precision budget.maxAttempts

/-- Certify `exp x - 1` for a valid finite datum, preserving its encoding when it is zero. -/
@[inline] def expMinus1 (f : Format) (input : Datum) (budget : Budget := {}) : Option Datum :=
  if ¬input.Valid f then none
  else if input.isZero then some input
  else
    match input.toRat? with
    | none => none
    | some argument => expMinus1Rat f argument budget

/-- Certify `log (1 + x)` for a valid finite datum, preserving a zero's sign and quantum. -/
@[inline] def logPlus1 (f : Format) (input : Datum) (budget : Budget := {}) : Option Datum :=
  if ¬input.Valid f then none
  else if input.isZero then some input
  else
    match input.toRat? with
    | none => none
    | some argument => logPlus1Rat f argument budget

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified
