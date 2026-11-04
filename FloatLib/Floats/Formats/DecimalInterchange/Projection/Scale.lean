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

To pick the rounding grid we scale the input to the least quantum and count digits, with `Nat.log`
on the scaled integer part. That works for any exact rational input, even one below the least
subnormal. The selected exponent has no upper bound, so overflow can be tested *after* precision
rounding, as IEEE 754-2019 §7.4 requires.
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
