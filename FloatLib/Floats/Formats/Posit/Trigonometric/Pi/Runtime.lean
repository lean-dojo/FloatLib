/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Pi.Runtime

/-!
# Correctly rounded pi-scaled posit trigonometric functions

In these functions the argument is multiplied by pi exactly, before the final posit rounding, and
rational special values and tangent poles are classified exactly. In the inverse functions, the
exact principal angle is divided by pi and never rounded to a posit first.

These functions follow the Posit Standard (2022), §5.5.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics.TrigonometricComparison

/-- Correctly rounded sine of pi times the input, including exact rational special values. -/
def sinPi {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareSinPi value

/-- Correctly rounded cosine of pi times the input, including exact rational special values. -/
def cosPi {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareCosPi value

/-- Correctly rounded tangent of pi times the input. Half-integer arguments produce NaR. -/
def tanPi {format : Format} (value : Model format) : Model format :=
  match value.toRat? with
  | none => nar format
  | some argument =>
      if Int.fract argument = 1 / 2 then nar format
      else ComparisonRounding.roundSigned format
        (prepareTanPi argument (format.bits.log2 + 2)).compare

/-- Correctly rounded principal inverse sine divided by pi, with real domain `[-1, 1]`. -/
def arcSinPi {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluateUnit prepareArcsinPi value

/-- Correctly rounded principal inverse cosine divided by pi, with real domain `[-1, 1]`. -/
def arcCosPi {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluateUnit prepareArccosPi value

/-- Correctly rounded principal inverse tangent divided by pi. -/
def arcTanPi {format : Format} (value : Model format) : Model format :=
  Trigonometric.evaluate prepareArctanPi value

end FloatLib.Floats.Formats.Posit.Model
