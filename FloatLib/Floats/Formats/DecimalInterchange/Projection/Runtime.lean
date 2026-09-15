/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Scale
public import FloatLib.Floats.Formats.DecimalInterchange.Cohort.Runtime
public import FloatLib.Numerics.Exact.RadixText.Precision
public import FloatLib.Numerics.IEEEStatus

/-!
# Cohort-aware rational projection

Precision rounding precedes the overflow test (IEEE 754-2019 §7.4). Decimal
tininess is detected before rounding (§7.5), and the underflow flag requires
both tininess and inexactness. Exact results select the cohort member closest
to the preferred quantum (§5.2).
The magnitude interface requires a nonnegative input; `project` handles either
sign and receives the sign of an exact zero separately.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- The shared IEEE exception indicators, also used by binary arithmetic. -/
abbrev Status := Numerics.IEEEStatus

/-- A decimal result with the exceptions raised by this operation. -/
structure Outcome where
  /-- The delivered decimal datum. -/
  value : Datum
  /-- Exceptions raised while computing the datum. -/
  status : Status := {}
  deriving DecidableEq, Repr

/-- Least positive normal value, independent of the chosen cohort. -/
def Format.minNormal (f : Format) : ℚ :=
  (10 : ℚ) ^ (f.precision - 1) * (10 : ℚ) ^ f.minQuantum

/-- Greatest finite magnitude and its largest-quantum representation. -/
def Format.maxFinite (f : Format) (negative : Bool) : Datum :=
  .finite negative (f.coefficientBound - 1) f.maxQuantum

/-- Precision-rounded coefficient and exponent with an unbounded upper exponent.
The only possible carry is exactly `10 ^ precision`. -/
def roundedPair (f : Format) (mode : RoundingMode) (negative : Bool) (magnitude : ℚ) :
    Nat × Int :=
  let q := roundingQuantum f magnitude
  let c := mode.roundAt negative magnitude q
  Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ c q

/-- Whether overflow delivers an infinity rather than the greatest finite value. -/
def RoundingMode.overflowToInfinity (mode : RoundingMode) (negative : Bool) : Bool :=
  match mode with
  | .nearestEven | .nearestAway => true
  | .towardZero => false
  | .towardPositive => !negative
  | .towardNegative => negative

/-- Project a nonnegative rational magnitude, retaining the supplied sign even at zero.
Exact zero selects its cohort directly, without allocating powers for rounding or tininess. -/
def projectMagnitude (f : Format) (mode : RoundingMode) (negative : Bool)
    (magnitude : ℚ) (preferred : Int) : Outcome :=
  if magnitude = 0 then
    { value := preferredCohort f negative 0 f.minQuantum preferred }
  else
    let result := roundedPair f mode negative magnitude
    if f.maxQuantum < result.2 then
      { value := if mode.overflowToInfinity negative then .infinity negative
          else f.maxFinite negative
        status := { overflow := true, inexact := true } }
    else
      let inexact := decide ((result.1 : ℚ) * (10 : ℚ) ^ result.2 ≠ magnitude)
      { value := if inexact then .finite negative result.1 result.2
          else preferredCohort f negative result.1 result.2 preferred
        status :=
          { inexact := inexact
            underflow := decide (magnitude < f.minNormal) && inexact } }

/-- Round an exact rational value with an operation's preferred quantum.
`negativeZero` is consulted only when the exact input equals zero. -/
def project (f : Format) (mode : RoundingMode) (value : ℚ) (preferred : Int)
    (negativeZero : Bool := false) : Outcome :=
  projectMagnitude f mode (if value = 0 then negativeZero else decide (value < 0))
    |value| preferred

end FloatLib.Floats.Formats.DecimalInterchange
