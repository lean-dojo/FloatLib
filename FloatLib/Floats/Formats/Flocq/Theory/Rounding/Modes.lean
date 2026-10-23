/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Away
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Nearest

/-!
# Rounding directions as integer-rounding rules

`IEEERoundingMode` has six rounding directions: the five rounding-direction attributes of
IEEE 754-2019 (Section 4.3) and rounding away from zero, the `MPFR_RNDA` mode of GNU MPFR. They
are the named rounding modes of the generic float model as well. `roundingFunction` interprets each
direction as a valid integer-rounding rule, so the generic theory of `round` applies to every
direction: `round (roundingFunction mode) x` rounds a real into a generic format.

## References

- IEEE Std 754-2019, "IEEE Standard for Floating-Point Arithmetic", Section 4.3.
- The GNU MPFR Library manual, version 4.2.2, Section 4.4, "Rounding":
  <https://www.mpfr.org/mpfr-current/mpfr.html#Rounding>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

open FloatLib.Floats.Formats.BinaryInterchange.Model (IEEERoundingMode)

/--
The integer-rounding rule of a rounding direction, as used by `round`.

Nearest rounding resolves a tie toward an even integer at the selected scale. Under the usual
Flocq conditions (in particular, excluding the precision-one even-radix corner case), this agrees
with the familiar even canonical-significand description.
-/
noncomputable def roundingFunction : IEEERoundingMode → ℝ → ℤ
  | .nearest => FloatLib.Floats.Formats.Flocq.nearestEven
  | .nearestAway => nearestChoice nearestAwayChoice
  | .towardZero => truncRound
  | .up => ceilRound
  | .down => floorRound
  | .away => awayRound

/-- Every rounding direction satisfies the generic rounding-function laws. -/
instance (mode : IEEERoundingMode) : ValidRnd (roundingFunction mode) := by
  cases mode with
  | nearest =>
      change ValidRnd FloatLib.Floats.Formats.Flocq.nearestEven
      infer_instance
  | nearestAway =>
      change ValidRnd (nearestChoice nearestAwayChoice)
      exact (nearestChoiceValid nearestAwayChoice).toValidRnd
  | towardZero => change ValidRnd truncRound; infer_instance
  | up => change ValidRnd ceilRound; infer_instance
  | down => change ValidRnd floorRound; infer_instance
  | away => change ValidRnd awayRound; exact awayRoundValid

end FloatLib.Floats.Formats.Flocq
