/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Kernels.IntegerRoot.Runtime

/-!
# Decimal integer-degree roots by exact power comparisons

The integer root brackets the scaled coefficient. Comparing the radicand with
the power of the exact midpoint decides nearest rounding, including ties.
Precision, degree, and intermediate integers are unbounded.

Negative degrees invert the exact rational radicand before root rounding.
Negative nonzero operands require an odd degree. Signed zeros follow the same
odd-degree sign rule; a negative degree at zero raises divide-by-zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Decimal grid shift for a root of positive integer degree. -/
def rootScaleShift (precision degree : Nat) (scaledRadicand : ℚ) : Nat :=
  Nat.log 10 ⌊scaledRadicand⌋₊ / degree + 1 - precision

/-- Smallest coefficient grid which fits the exact nonnegative root. -/
def rootQuantum (f : Format) (degree : Nat) (radicand : ℚ) : Int :=
  f.minQuantum +
    (rootScaleShift f.precision degree
      (radicand / (10 : ℚ) ^ ((degree : Int) * f.minQuantum)) : Int)

/-- Integer floor of a nonnegative rational's positive-degree root. -/
def rootFloor (degree : Nat) (radicand : ℚ) : Nat :=
  Numerics.IntegerRoot.root degree ⌊radicand⌋₊

/-- Exact decision between adjacent coefficients, with directed rounding respecting sign. -/
def RoundingMode.rootIncrement (mode : RoundingMode) (negative : Bool)
    (degree lower : Nat) (radicand : ℚ) : Bool :=
  match mode with
  | .nearestEven =>
      decide ((2 * (lower : ℚ) + 1) ^ degree < 2 ^ degree * radicand ∨
        ((2 * (lower : ℚ) + 1) ^ degree = 2 ^ degree * radicand ∧ lower % 2 = 1))
  | .nearestAway => decide ((2 * (lower : ℚ) + 1) ^ degree ≤ 2 ^ degree * radicand)
  | .towardPositive => !negative && decide ((lower : ℚ) ^ degree < radicand)
  | .towardNegative => negative && decide ((lower : ℚ) ^ degree < radicand)
  | .towardZero => false

/-- Round a nonnegative root magnitude on the integer grid. -/
def RoundingMode.rootRound (mode : RoundingMode) (negative : Bool)
    (degree : Nat) (radicand : ℚ) : Nat :=
  let lower := rootFloor degree radicand
  if mode.rootIncrement negative degree lower radicand then lower + 1 else lower

/-- Rounded root coefficient and quantum, after an exact power-of-ten carry. -/
def rootPair (f : Format) (mode : RoundingMode) (negative : Bool)
    (degree : Nat) (radicand : ℚ) : Nat × Int :=
  let q := rootQuantum f degree radicand
  let c := mode.rootRound negative degree (radicand / (10 : ℚ) ^ ((degree : Int) * q))
  Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ c q

/-- Round a positive-degree root of a nonnegative rational magnitude.
Only the final root can raise overflow or underflow. Exact results retain the
preferred cohort, and inexactness is decided by an exact power equality. -/
def rootMagnitude (f : Format) (mode : RoundingMode) (negative : Bool)
    (degree : Nat) (radicand : ℚ) (preferred : Int) : Outcome :=
  let result := rootPair f mode negative degree radicand
  if f.maxQuantum < result.2 then
    { value := if mode.overflowToInfinity negative then .infinity negative
        else f.maxFinite negative
      status := { overflow := true, inexact := true } }
  else
    let inexact := decide (((result.1 : ℚ) * (10 : ℚ) ^ result.2) ^ degree ≠ radicand)
    { value := if inexact then .finite negative result.1 result.2
        else preferredCohort f negative result.1 result.2 preferred
      status :=
        { inexact := inexact
          underflow := decide (radicand < f.minNormal ^ degree) && inexact } }

/-- Integer-degree root with one final rounding. Degree zero is invalid for numeric
operands; input NaNs retain the usual decimal propagation. For an exact finite
result, the preferred quantum is the floor of the signed operand quantum divided
by the positive degree magnitude. -/
def Arithmetic.rootN (f : Format) (mode : RoundingMode) : Datum → Int → Outcome
  | .nan s t p, _ => nanResult f s p t
  | .infinity s, n =>
      if n = 0 then invalidResult
      else if s && decide (n % 2 = 0) then invalidResult
      else if n < 0 then
        projectMagnitude f mode (s && decide (n % 2 = 1)) 0 f.minQuantum
      else { value := .infinity (s && decide (n % 2 = 1)) }
  | .finite s c q, n =>
      if n = 0 then invalidResult
      else
        let negative := s && decide (n % 2 = 1)
        let preferred := (if n < 0 then -q else q) / (n.natAbs : Int)
        if c = 0 then
          if n < 0 then
            { value := .infinity negative, status := { divideByZero := true } }
          else projectMagnitude f mode negative 0 preferred
        else if s && decide (n % 2 = 0) then invalidResult
        else
          let magnitude := (c : ℚ) * (10 : ℚ) ^ q
          rootMagnitude f mode negative n.natAbs
            (if n < 0 then magnitude⁻¹ else magnitude) preferred

end FloatLib.Floats.Formats.DecimalInterchange
