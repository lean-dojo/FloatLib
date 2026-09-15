/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Dyadic.Runtime
public import FloatLib.Numerics.Exact.Dyadic.Arithmetic.Runtime

/-!
# Executable rational-free exact posit square-root rounding

A finite posit is dyadic, although its square root need not be. Correct rounding does not require
constructing the root: for `c ≥ 0` and `x ≥ 0`, `c ≤ sqrt x` exactly when `c² ≤ x`.
This module performs every search and threshold decision with shared exact-dyadic multiplication
and comparison. The rational and real-valued refinement theorems live in `SquareRoot.Proof`, so
real numbers do not enter executable kernels.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DyadicSquareRoot

open FloatLib.Numerics

/--
For a nonnegative radicand, the greatest nonnegative code whose squared value does not exceed it.

The standard code interval is searched logarithmically. Squaring a decoded candidate is exact and
does not introduce a host floating-point or real-number oracle.
-/
@[inline] def lowerCode (format : Format) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  Model.lowerCodeByBisection
    (fun code =>
      let value := DyadicRounding.nonnegativeDyadicAt format code
      (value.mul value).isLessOrEqual radicand)
    format.bits 0 format.signMaskNat

/--
Correctly round the nonnegative square root of an exact dyadic radicand.

Zero is recognized from its significand. Positive values use exact squared comparisons for
underflow, the lower-code search, the appended-bit threshold, and the tie-to-even decision.
Arithmetic callers reject negative radicands before calling this helper.
-/
@[inline] def roundCode (format : Format) (radicand : FloatLib.Numerics.Dyadic) : Nat :=
  if radicand.significand == 0 then
    0
  else
    let minPos := DyadicRounding.minPositive format
    let minPosSquare := minPos.mul minPos
    if radicand.isLess minPosSquare then
      1
    else
      let lower := lowerCode format radicand
      let lowerValue := DyadicRounding.nonnegativeDyadicAt format lower
      let lowerSquare := lowerValue.mul lowerValue
      if radicand.isEqual lowerSquare then
        lower
      else
        let upper := lower + 1
        if upper < format.signMaskNat then
          let threshold := DyadicRounding.roundingThreshold format lower
          let thresholdSquare := threshold.mul threshold
          if radicand.isLess thresholdSquare then
            lower
          else if thresholdSquare.isLess radicand then
            upper
          else if lower % 2 = 0 then
            lower
          else
            upper
        else
          lower

/-- Pack the code selected by exact dyadic square-root rounding. -/
@[inline] def round (format : Format) (radicand : FloatLib.Numerics.Dyadic) : Model format :=
  Model.ofNatBits (roundCode format radicand)


end FloatLib.Floats.Formats.Posit.Model.DyadicSquareRoot
