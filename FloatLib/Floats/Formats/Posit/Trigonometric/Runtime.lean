/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Runtime

/-!
# Correctly rounded posit trigonometric operations

Each finite input is decoded exactly. A prepared comparator then compares the mathematical
function value with posit rounding boundaries, sharing its enclosure data across the search.
Only the final result is rounded. Inverse sine and cosine reject inputs outside `[-1, 1]`;
all six operations propagate NaR.

The radian functions and principal branches follow the Posit Standard (2022), §5.5.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Trigonometric

open FloatLib.Numerics.Enclosure.Comparison

/-- Round using a prepared comparator, propagating NaR.
An exact comparator gives the real rounding contract in `evaluate_eq_real`. -/
def evaluate {format : Format} (prepare : Rat → Nat → Prepared)
    (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some argument =>
      ComparisonRounding.roundSigned format
        (prepare argument (format.bits.log2 + 2)).compare

/-- Check the closed real domain of inverse sine or cosine before preparing its comparator. -/
def evaluateUnit {format : Format} (prepare : Rat → Nat → Prepared)
    (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some argument =>
      if -1 ≤ argument ∧ argument ≤ 1 then
        ComparisonRounding.roundSigned format
          (prepare argument (format.bits.log2 + 2)).compare
      else nar format

end Trigonometric

open FloatLib.Numerics.TrigonometricComparison

/-- Correctly rounded sine of a radian argument. NaR propagates. -/
def sin {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareSin value

/-- Correctly rounded cosine of a radian argument. NaR propagates. -/
def cos {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareCos value

/-- Correctly rounded tangent. A finite posit, being rational, is never a radian tangent pole. -/
def tan {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareTan value

/-- Inverse sine on its principal branch `[-π/2, π/2]`; invalid inputs produce NaR. -/
def arcSin {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluateUnit prepareArcsin value

/-- Inverse cosine on its principal branch `[0, π]`; invalid inputs produce NaR. -/
def arcCos {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluateUnit prepareArccos value

/-- Correctly rounded inverse tangent on its principal branch `(-π/2, π/2)`. -/
def arcTan {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareArctan value

end FloatLib.Floats.Formats.Posit.Model
