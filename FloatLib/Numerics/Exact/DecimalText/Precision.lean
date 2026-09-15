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

The digit grid and decade carry depend only on an exact decimal value. A caller
supplies the signed magnitude-to-integer rounding function; this module makes no
choice of source format, exponent bounds, cohort policy, or exception handling.
It applies equally to decimal datums and terminating decimal expansions of dyadics.

Requested precision has no width cap. Zero uses adjusted exponent zero, hence
quantum `1-p` at precision `p`. Sign preservation includes signed zero.
-/

@[expose] public section

namespace FloatLib.Numerics.DecimalText

/-- Exact representation and a requested significant-digit count are distinct output modes. -/
inductive Precision where
  | exact
  | significant (digits : ℕ+)

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
