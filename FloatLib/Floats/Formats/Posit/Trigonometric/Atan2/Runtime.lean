/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Trigonometric.Runtime
public import FloatLib.Numerics.Exact.Trigonometric.Atan2.Runtime

/-!
# Correctly rounded two-coordinate posit arctangent

The Posit Standard (2022), §5.5, orders the coordinates as `(x, y)`: the result is the
principal argument of `x + i*y`. The negative real axis has angle pi. NaR propagates,
and the origin produces NaR rather than adopting Mathlib's totalized zero angle.

The pi-scaled variant divides the exact angle by pi before the final rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Trigonometric

open FloatLib.Numerics.Enclosure.Comparison

/-- Decode both coordinates, reject the origin, and round using the supplied comparator.
Its exact argument semantics are the hypothesis of `evaluateArgument_eq_real`. -/
def evaluateArgument {format : Format} (prepare : Rat → Rat → Nat → Prepared)
    (x y : Model format) : Model format :=
  match x.toRat?, y.toRat? with
  | some a, some b =>
      if a = 0 ∧ b = 0 then nar format
      else ComparisonRounding.roundSigned format
        (prepare a b (format.bits.log2 + 2)).compare
  | _, _ => nar format

end Trigonometric

/-- Correctly rounded principal argument of `x + i*y`, in radians; `(0, 0)` produces NaR. -/
def arcTan2 {format : Format} (x y : Model format) : Model format :=
  Trigonometric.evaluateArgument FloatLib.Numerics.TrigonometricComparison.prepareAtan2 x y

/-- Correctly rounded principal argument of `x + i*y` divided by pi; `(0, 0)` produces NaR. -/
def arcTan2Pi {format : Format} (x y : Model format) : Model format :=
  Trigonometric.evaluateArgument FloatLib.Numerics.TrigonometricComparison.prepareAtan2Pi x y

end FloatLib.Floats.Formats.Posit.Model
