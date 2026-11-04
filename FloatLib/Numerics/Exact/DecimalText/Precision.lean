/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Exact.DecimalText.Runtime
public import FloatLib.Numerics.Exact.RadixText.Precision

/-!
# Requested precision for external decimal text

Writing a value with a requested number of significant digits needs a digit grid and a decade carry,
and both depend only on an exact decimal value. Rounding is the caller's part: it supplies the
signed magnitude-to-integer rounding function, and this module makes no choice of source format,
exponent bounds, cohort policy, or exception handling, so it works the same for decimal datums and
for terminating decimal expansions of dyadics.

There's no width cap on the requested precision. Zero uses adjusted exponent zero, which gives
quantum `1-p` at precision `p`, and the sign is preserved, signed zero included.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- Exact representation and a requested significant-digit count are distinct output modes. -/
inductive Precision where
  /-- Every digit of the exact value. Nothing is rounded, so the rounding direction is unused. -/
  | exact
  /-- This many significant digits, rounded once in the caller's rounding direction. -/
  | significant (digits : ℕ+)
  deriving DecidableEq, Repr

/-- Decimal position of the last requested digit. -/
def significantQuantum (coefficient : Nat) (quantum : Int) (digits : ℕ+) : Int :=
  RadixText.significantQuantum 10 coefficient quantum digits

/-- Round on a decimal grid with the caller's magnitude-to-integer rounding function. -/
def roundDecimal (roundMagnitude : Bool → ℚ → Nat) (value : Decimal) (quantum : Int) :
    Decimal :=
  { negative := value.negative
    significand := RadixText.roundCoefficient 10 roundMagnitude value.negative
      value.significand value.exponent quantum
    exponent := quantum }

/-- Carry into a new decade without adding an extra significant digit. -/
def carryDecimal (digits : ℕ+) (value : Decimal) : Decimal :=
  let result := RadixText.carry 10 digits value.significand value.exponent
  { negative := value.negative, significand := result.1, exponent := result.2 }

/-- One rounding at the requested significant-digit grid, followed by a value-preserving carry. -/
def significantDecimal (roundMagnitude : Bool → ℚ → Nat) (value : Decimal) (digits : ℕ+) :
    Decimal :=
  carryDecimal digits
    (roundDecimal roundMagnitude value (significantQuantum value.significand value.exponent digits))

end FloatLib.Numerics.DecimalText
