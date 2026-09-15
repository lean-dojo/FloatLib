/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Nat.Log

/-!
# Significant-digit rounding on an arbitrary radix grid

Decimal and hexadecimal output share the grid calculation, one integer rounding,
and carry. The radix and rounding callback are explicit; there are no format
widths or exponent limits here. Meaningful radix semantics require `1 < radix`.
-/

@[expose] public section

namespace FloatLib.Numerics.RadixText

/-- Exponent of the last requested radix digit, with adjusted exponent zero for zero. -/
def significantQuantum (radix coefficient : Nat) (quantum : Int) (digits : ℕ+) : Int :=
  if coefficient = 0 then 1 - (digits : Nat)
  else quantum + ((Nat.log radix coefficient + 1 : Nat) : Int) - (digits : Nat)

/-- Round a coefficient onto another grid using an exact magnitude-rounding callback. -/
def roundCoefficient (radix : Nat) (roundMagnitude : Bool → ℚ → Nat)
    (negative : Bool) (coefficient : Nat) (quantum destination : Int) : Nat :=
  roundMagnitude negative
    ((coefficient : ℚ) * (radix : ℚ) ^ quantum / (radix : ℚ) ^ destination)

/-- Carry a rounded coefficient into the next radix position without changing its value. -/
def carry (radix : Nat) (digits : ℕ+) (coefficient : Nat) (quantum : Int) : Nat × Int :=
  if coefficient = radix ^ (digits : Nat) then
    (radix ^ ((digits : Nat) - 1), quantum + 1)
  else (coefficient, quantum)

/-- One significant-digit rounding, followed by a value-preserving radix carry. -/
def significant (radix : Nat) (roundMagnitude : Bool → ℚ → Nat)
    (negative : Bool) (coefficient : Nat) (quantum : Int) (digits : ℕ+) : Nat × Int :=
  let destination := significantQuantum radix coefficient quantum digits
  carry radix digits
    (roundCoefficient radix roundMagnitude negative coefficient quantum destination) destination

end FloatLib.Numerics.RadixText
