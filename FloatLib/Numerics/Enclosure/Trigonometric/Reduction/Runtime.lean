/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Trigonometric.Runtime
public import Mathlib.Data.Rat.Floor

/-!
# Rational period reduction for sine and cosine

An enclosed quarter period supplies an approximate full period in `[4, 8]`. Rounding the
quotient to an integer leaves a rational Taylor argument in `[-4, 4]`. The output radius
includes the accumulated period error, using the global Lipschitz bound of sine and cosine.
Thus the reduction remains valid even when the selected integer changes as precision grows.

The number of series terms need not grow with the magnitude of the reduced argument. The
precision needed in the period still grows with the input magnitude, as expected for range
reduction. All arithmetic here is rational; there is no machine approximation to π.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure

/-- A positive rational approximation to π/4, bounded between one half and one. -/
def trigQuarter (degree : Nat) : ℚ :=
  max (1 / 2) (min 1 (piQuarter degree).lo)

/-- The nearest integer number of approximate full periods, with upward half ties. -/
def trigTurns (x : ℚ) (degree : Nat) : Int :=
  ⌊x / (8 * trigQuarter degree) + 1 / 2⌋

/-- The exact rational remainder after removing the approximate periods. -/
def trigReducedArgument (x : ℚ) (degree : Nat) : ℚ :=
  x - 8 * (trigTurns x degree : ℚ) * trigQuarter degree

/-- Error from replacing true periods by the rational approximate periods. -/
def trigReductionError (x : ℚ) (degree : Nat) : ℚ :=
  8 * |(trigTurns x degree : ℚ)| * ((piQuarter degree).hi - trigQuarter degree)

/-- Combined Taylor and period-reduction error. -/
def trigReducedRadius (x : ℚ) (degree : Nat) : ℚ :=
  trigRadius (trigReducedArgument x degree) degree + trigReductionError x degree

/-- A sine enclosure with a Taylor argument of magnitude at most four. -/
def sinReduced (x : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (RationalInterval.around
    (sinTaylor (trigReducedArgument x degree) degree) (trigReducedRadius x degree))

/-- A cosine enclosure with the same bounded rational period reduction. -/
def cosReduced (x : ℚ) (degree : Nat) : RationalInterval :=
  restrictUnit (RationalInterval.around
    (cosTaylor (trigReducedArgument x degree) degree) (trigReducedRadius x degree))

end FloatLib.Numerics.Enclosure
