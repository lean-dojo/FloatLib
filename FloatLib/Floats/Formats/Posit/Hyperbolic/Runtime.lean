/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Exact.Hyperbolic.Runtime

/-!
# Correctly rounded posit hyperbolic functions

The operations compare their exact real result with rational posit rounding boundaries.
There is no intermediate posit rounding. NaR propagates, and inputs outside an inverse
function's real domain produce NaR.

## Reference

* Posit Standard (2022), §5.5, https://posithub.org/docs/posit_standard-2.pdf
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

namespace Hyperbolic

open FloatLib.Numerics.HyperbolicComparison

/-- Round hyperbolic tangent of an exact rational argument. -/
def tanhRat (format : Format) (argument : Rat) : Model format :=
  ComparisonRounding.roundSigned format (compareTanh argument)

/-- Round inverse hyperbolic tangent, rejecting both endpoints and the exterior domain. -/
def artanhRat (format : Format) (argument : Rat) : Model format :=
  if hlower : -1 < argument then
    if hupper : argument < 1 then
      ComparisonRounding.roundSigned format
        (prepareArtanh argument (format.bits.log2 + 2) hlower hupper).compare
    else nar format
  else nar format

/-- Round hyperbolic sine of an exact rational argument. -/
def sinhRat (format : Format) (argument : Rat) : Model format :=
  ComparisonRounding.roundSigned format (compareSinh argument)

/-- Round hyperbolic cosine of an exact rational argument. -/
def coshRat (format : Format) (argument : Rat) : Model format :=
  ComparisonRounding.roundSigned format (compareCosh argument)

/-- Round inverse hyperbolic sine of an exact rational argument. -/
def arsinhRat (format : Format) (argument : Rat) : Model format :=
  ComparisonRounding.roundSigned format (prepareArsinh argument (format.bits.log2 + 2)).compare

/-- Round inverse hyperbolic cosine on its real domain `[1, ∞)`. -/
def arcoshRat (format : Format) (argument : Rat) : Model format :=
  if 1 ≤ argument then
    ComparisonRounding.roundSigned format (prepareArcosh argument (format.bits.log2 + 2)).compare
  else nar format

/-- Apply a rational hyperbolic operation to a finite posit, propagating NaR. -/
def applyRat {format : Format} (operation : Rat → Model format) (value : Model format) :
    Model format :=
  match value.toRat? with
  | none => nar format
  | some q => operation q

end Hyperbolic

/-- Correctly rounded hyperbolic tangent; NaR propagates. -/
def tanH {format : Format} (value : Model format) : Model format :=
  Hyperbolic.applyRat (Hyperbolic.tanhRat format) value

/-- Correctly rounded inverse hyperbolic tangent, with real domain `-1 < x < 1`. -/
def arcTanH {format : Format} (value : Model format) : Model format :=
  Hyperbolic.applyRat (Hyperbolic.artanhRat format) value

/-- Correctly rounded hyperbolic sine; NaR propagates. -/
def sinH {format : Format} (value : Model format) : Model format :=
  Hyperbolic.applyRat (Hyperbolic.sinhRat format) value

/-- Correctly rounded hyperbolic cosine; NaR propagates. -/
def cosH {format : Format} (value : Model format) : Model format :=
  Hyperbolic.applyRat (Hyperbolic.coshRat format) value

/-- Correctly rounded inverse hyperbolic sine; NaR propagates. -/
def arcSinH {format : Format} (value : Model format) : Model format :=
  Hyperbolic.applyRat (Hyperbolic.arsinhRat format) value

/-- Correctly rounded inverse hyperbolic cosine; inputs below `1` produce NaR. -/
def arcCosH {format : Format} (value : Model format) : Model format :=
  Hyperbolic.applyRat (Hyperbolic.arcoshRat format) value

end FloatLib.Floats.Formats.Posit.Model
