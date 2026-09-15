/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Format
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Runtime
public import Mathlib.Data.Nat.Log

/-!
# Selecting the decimal rounding grid

Count digits after scaling to the least quantum. This permits exact rational
inputs, including values below the least subnormal. `Nat.log` computes the digit
count from the scaled integer part.
The selected exponent is unbounded above so overflow can be tested *after*
precision rounding, as required by IEEE 754-2019 §7.4.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Number of decimal places to remove from the least-quantum grid. -/
def scaleShift (precision : Nat) (scaled : ℚ) : Nat :=
  Nat.log 10 ⌊scaled⌋₊ + 1 - precision

/-- Least quantum retaining the format's precision, before overflow is handled.
Zero selects the least quantum without constructing its radix power. -/
def roundingQuantum (f : Format) (magnitude : ℚ) : Int :=
  if magnitude = 0 then f.minQuantum
  else f.minQuantum + (scaleShift f.precision (magnitude / (10 : ℚ) ^ f.minQuantum) : Int)

end FloatLib.Floats.Formats.DecimalInterchange
