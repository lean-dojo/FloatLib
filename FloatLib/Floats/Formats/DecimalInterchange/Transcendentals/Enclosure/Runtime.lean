/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Queries.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Runtime

/-!
# Finite decimal enclosure acceptance

The acceptance test is short. Round both exact rational endpoints to nearest, ties to even, and
accept only when the two give the same finite datum, returning `none` otherwise. Exact endpoint
results prefer the least representable quantum. `Proof` connects acceptance to real rounding.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure

open FloatLib.Numerics

/-- Nearest-even projection of an exact endpoint, preferring its least representable quantum. -/
def roundEndpoint (f : Format) (value : ℚ) : Datum :=
  (project f .nearest value f.minQuantum).value

/-- Accept if and only if both endpoints round to the same finite decimal datum. -/
def round? (f : Format) (interval : RationalInterval) : Option Datum :=
  let lower := roundEndpoint f interval.lo
  let upper := roundEndpoint f interval.hi
  if lower.isFinite = true ∧ lower = upper then some lower else none

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure
