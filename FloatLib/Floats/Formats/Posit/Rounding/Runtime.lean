/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Positive.BitRuns
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Trailing
public import FloatLib.Floats.Formats.Posit.Semantics.Positive.Order

/-!
# Executable exact rational-to-posit rounding

The width-generic reference conversion searches the monotone positive encoding with at most
`format.bits` bisection comparisons. Between adjacent `n`-bit codes `U` and `W`, the standard's
exact boundary is the `(n + 1)`-bit posit whose encoding is `U1`; this is not generally the
arithmetic midpoint of the decoded values. A tie at that boundary is resolved by the low bit of
`U`. Negative inputs use whole-word two's-complement symmetry.

This implementation is the executable rounding specification. Packed word and limb kernels are
proved equal to it. Search and round-trip theorems live in `Rounding.Proof`.

The Posit Standard (2022) also gives the extreme intervals explicit behavior: magnitudes above
maxPos saturate to signed maxPos, while every nonzero magnitude below minPos rounds to signed
minPos. Zero is represented exactly.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Section 4, <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, Supercomputing Frontiers and Innovations 9(1),
  2022, <https://doi.org/10.14529/jsfi220102>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/--
Shared bounded bisection over an unsigned code interval.

`accept code` states that `code` is still on the lower side of the target boundary. Separating
the search from the comparison domain lets the exact-rational specification and certified
integer implementations follow literally the same control flow.
-/
@[inline] def lowerCodeByBisection (accept : Nat → Bool) :
    Nat → Nat → Nat → Nat
  | 0, lower, _ => lower
  | fuel + 1, lower, upper =>
      if lower + 1 < upper then
        let middle := (lower + upper) / 2
        if accept middle then
          lowerCodeByBisection accept fuel middle upper
        else
          lowerCodeByBisection accept fuel lower middle
      else
        lower

/--
Greatest candidate code found below an exclusive upper bound.

The initial interval is `[0, signMaskNat)`. Its size is a power of two, so `format.bits` bisections
are sufficient to isolate adjacent codes. Exact rational comparison avoids host-float
double-rounding.
-/
@[inline] def lowerCodeForPositive (format : Format) (target : Rat) : Nat :=
  lowerCodeByBisection
    (fun code => decide (nonnegativeRatAt format code ≤ target))
    format.bits 0 format.signMaskNat

/-- Exact smallest positive value of a posit format. -/
@[inline] def minPositiveRat (format : Format) : Rat :=
  nonnegativeRatAt format 1

/--
Exact standard rounding boundary above an `n`-bit lower code.

If `U` is the lower code, Section 4.1 defines the boundary as the value of the `(n + 1)`-bit word
`U1`. Numerically that word has unsigned code `2 * U + 1`.
-/
@[inline] def roundingThreshold (format : Format) (lowerCode : Nat) : Rat :=
  nonnegativeRatAt format.nextPrecision (2 * lowerCode + 1)

/--
Round a nonnegative exact rational to a nonnegative posit code.

This helper is total, returning zero for nonpositive input. Its intended positive-input behavior
matches Section 4.1 exactly: nonzero underflow selects minPos, overflow selects maxPos, and each
interior interval uses the appended-bit boundary with ties to an even retained low bit.
-/
@[inline] def roundPositiveCode (format : Format) (target : Rat) : Nat :=
  if target ≤ 0 then
    0
  else if target < minPositiveRat format then
    1
  else
    let lower := lowerCodeForPositive format target
    let upper := lower + 1
    if upper < format.signMaskNat then
      let threshold := roundingThreshold format lower
      if target < threshold then
        lower
      else if threshold < target then
        upper
      else if lower % 2 = 0 then
        lower
      else
        upper
    else
      lower

/-- Round a positive rational to a nonnegative posit model. -/
@[inline] def roundPositiveRat (format : Format) (target : Rat) : Model format :=
  ofNatBits (roundPositiveCode format target)

/--
For a nonnegative radicand, the greatest nonnegative code whose squared value does not exceed it.

Comparing squares is enough because positive posit codes are ordered by their unsigned word. It
also keeps square-root rounding fully executable over exact rationals: no approximate real square
root or host floating-point operation enters the specification.
-/
@[inline] def lowerSqrtCode (format : Format) (radicand : Rat) : Nat :=
  lowerCodeByBisection
    (fun code =>
      let value := nonnegativeRatAt format code
      decide (value * value ≤ radicand))
    format.bits 0 format.signMaskNat

/--
Round the nonnegative square root of an exact rational to a nonnegative posit code.

The comparisons square each exact standard threshold. This decides the rounding of irrational
roots without introducing an approximate square-root oracle.
-/
@[inline] def roundSqrtCode (format : Format) (radicand : Rat) : Nat :=
  if radicand ≤ 0 then
    0
  else
    let minPos := minPositiveRat format
    if radicand < minPos * minPos then
      1
    else
      let lower := lowerSqrtCode format radicand
      let lowerValue := nonnegativeRatAt format lower
      if radicand = lowerValue * lowerValue then
        lower
      else
        let upper := lower + 1
        if upper < format.signMaskNat then
          let threshold := roundingThreshold format lower
          let thresholdSquare := threshold * threshold
          if radicand < thresholdSquare then
            lower
          else if thresholdSquare < radicand then
            upper
          else if lower % 2 = 0 then
            lower
          else
            upper
        else
          lower

/-- Round the nonnegative square root of an exact rational using only rational comparisons. -/
@[inline] def roundSqrtRat (format : Format) (radicand : Rat) : Model format :=
  ofNatBits (roundSqrtCode format radicand)

/--
Round an exact rational to the configured posit using the Posit Standard rule.

This conversion does not pass through `Float`, `Float32`, MPFR, or another destination format.
-/
@[inline] def roundRat (format : Format) (value : Rat) : Model format :=
  if value = 0 then
    zero format
  else if value < 0 then
    neg (roundPositiveRat format (-value))
  else
    roundPositiveRat format value


end FloatLib.Floats.Formats.Posit.Model
