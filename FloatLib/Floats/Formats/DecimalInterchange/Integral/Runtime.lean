/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Quantize.Runtime

/-!
# Decimal integral rounding

IEEE 754-2019 §§5.3.1 and 5.4.1 use the preferred quantum `max(Q(x), 0)`.
Rounding to the integer grid never increases a valid finite coefficient. If the
preferred quantum is representable, the result fits without additional precision
rounding. A custom layout whose maximum quantum is negative cannot store this
preferred quantum; this binding returns invalid through `quantizeMagnitude`.
Both APIs preserve the sign of a successful zero result; the exact variant signals
numerical inexactness.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Arithmetic

/-- Round to an integral decimal value in the supplied rounding direction, signaling inexact.
The mode argument represents the current rounding-direction attribute.
An unrepresentable preferred quantum produces invalid, including on custom layouts. -/
def roundToIntegralExact (f : Format) (mode : RoundingMode) : Datum → Outcome
  | .nan s t p => nanResult f s p t
  | .infinity s => { value := .infinity s }
  | .finite s c q => quantizeMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) (max q 0)

/-- Integral rounding with an explicit direction, without signaling inexact. -/
def roundToIntegral (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  let out := roundToIntegralExact f mode x
  { out with status := { out.status with inexact := false } }

/-- Round to the nearest integral value, choosing the even integer at a tie. -/
abbrev roundToIntegralTiesToEven (f : Format) := roundToIntegral f .nearestEven
/-- Round to the nearest integral value, choosing away from zero at a tie. -/
abbrev roundToIntegralTiesToAway (f : Format) := roundToIntegral f .nearestAway
/-- Round to an integral value toward zero, without signaling inexact. -/
abbrev roundToIntegralTowardZero (f : Format) := roundToIntegral f .towardZero
/-- Round to an integral value toward positive infinity, without signaling inexact. -/
abbrev roundToIntegralTowardPositive (f : Format) := roundToIntegral f .towardPositive
/-- Round to an integral value toward negative infinity, without signaling inexact. -/
abbrev roundToIntegralTowardNegative (f : Format) := roundToIntegral f .towardNegative

end FloatLib.Floats.Formats.DecimalInterchange.Arithmetic
