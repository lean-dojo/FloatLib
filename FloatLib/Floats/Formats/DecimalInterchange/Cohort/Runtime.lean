/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Datum

/-!
# Selecting an exact result's cohort

For an exact result, IEEE 754-2019 §5.2 asks for the cohort member nearest the preferred exponent.
We start at the smallest representable exponent and strip trailing zeros one at a time, stopping at
the preferred exponent or at the largest stored quantum. Zero takes a shortcut. Without it, a large
gap between the exponents would mean a long recursion.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Remove at most `fuel` exact trailing coefficient zeros.
The second component counts the removed zeros. -/
def stripTrailing : Nat → Nat → Nat × Nat
  | 0, c => (c, 0)
  | fuel + 1, c =>
      if c = 0 then (0, fuel + 1)
      else if c % 10 = 0 then
        let result := stripTrailing fuel (c / 10)
        (result.1, result.2 + 1)
      else (c, 0)

/-- Raise an exact result's quantum toward its preferred exponent without changing its value.
The input quantum is already the smallest representable one for this coefficient. -/
def preferredCohort (f : Format) (negative : Bool) (c : Nat) (q preferred : Int) : Datum :=
  let fuel := (min preferred f.maxQuantum - q).toNat
  let result := stripTrailing fuel c
  .finite negative result.1 (q + (result.2 : Int))

end FloatLib.Floats.Formats.DecimalInterchange
