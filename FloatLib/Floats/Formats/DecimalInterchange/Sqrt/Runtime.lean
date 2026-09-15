/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import Mathlib.Data.Nat.Sqrt

/-!
# Decimal square root by exact squared comparisons

An integer square root brackets the scaled result. Comparing the radicand
with the squared midpoint decides nearest rounding exactly, including ties.
All decisions use integer and rational arithmetic.

The preferred exponent is the floor of half the operand quantum
(IEEE 754-2019 §5.4.1). Negative zero survives, while a negative nonzero
operand raises invalid (§§6.3, 7.2).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Decimal scale shift for a square root, computed without evaluating a real square root. -/
def sqrtScaleShift (precision : Nat) (scaledRadicand : ℚ) : Nat :=
  Nat.log 10 ⌊scaledRadicand⌋₊ / 2 + 1 - precision

/-- Smallest coefficient grid which fits the exact square root. -/
def sqrtQuantum (f : Format) (radicand : ℚ) : Int :=
  f.minQuantum +
    (sqrtScaleShift f.precision (radicand / (10 : ℚ) ^ (2 * f.minQuantum)) : Int)

/-- Integer floor of a nonnegative rational's square root. -/
def sqrtFloor (radicand : ℚ) : Nat := Nat.sqrt ⌊radicand⌋₊

/-- Decide the upper adjacent integer by exact comparison with a squared midpoint. -/
def RoundingMode.sqrtIncrement (mode : RoundingMode) (lower : Nat)
    (radicand : ℚ) : Bool :=
  match mode with
  | .nearestEven =>
      decide ((2 * (lower : ℚ) + 1) ^ 2 < 4 * radicand ∨
        ((2 * (lower : ℚ) + 1) ^ 2 = 4 * radicand ∧ lower % 2 = 1))
  | .nearestAway => decide ((2 * (lower : ℚ) + 1) ^ 2 ≤ 4 * radicand)
  | .towardPositive => decide ((lower : ℚ) ^ 2 < radicand)
  | .towardZero | .towardNegative => false

/-- Round a nonnegative square root on the integer grid. -/
def RoundingMode.sqrtRound (mode : RoundingMode) (radicand : ℚ) : Nat :=
  let lower := sqrtFloor radicand
  if mode.sqrtIncrement lower radicand then lower + 1 else lower

/-- Rounded coefficient and quantum; an exact power-of-ten carry loses no value. -/
def sqrtPair (f : Format) (mode : RoundingMode) (radicand : ℚ) : Nat × Int :=
  let q := sqrtQuantum f radicand
  let c := mode.sqrtRound (radicand / (10 : ℚ) ^ (2 * q))
  Numerics.RadixText.carry 10 ⟨f.precision, f.precision_pos⟩ c q

/-- Round the square root of a nonnegative rational, selecting the preferred
cohort member when the result is exact. -/
def sqrtMagnitude (f : Format) (mode : RoundingMode) (radicand : ℚ)
    (preferred : Int) : Outcome :=
  let result := sqrtPair f mode radicand
  if f.maxQuantum < result.2 then
    { value := if mode.overflowToInfinity false then .infinity false else f.maxFinite false
      status := { overflow := true, inexact := true } }
  else
    let inexact := decide (((result.1 : ℚ) * (10 : ℚ) ^ result.2) ^ 2 ≠ radicand)
    { value := if inexact then .finite false result.1 result.2
        else preferredCohort f false result.1 result.2 preferred
      status :=
        { inexact := inexact
          underflow := decide (radicand < f.minNormal ^ 2) && inexact } }

/-- Square root in all five rounding modes, including signed zeros and NaN diagnostics. -/
def Arithmetic.sqrt (f : Format) (mode : RoundingMode) : Datum → Outcome
  | .nan s t p => nanResult f s p t
  | .infinity s => if s then invalidResult else { value := .infinity false }
  | .finite s c q =>
      if c = 0 then projectMagnitude f mode s 0 (q / 2)
      else if s then invalidResult
      else sqrtMagnitude f mode ((c : ℚ) * (10 : ℚ) ^ q) (q / 2)

end FloatLib.Floats.Formats.DecimalInterchange
