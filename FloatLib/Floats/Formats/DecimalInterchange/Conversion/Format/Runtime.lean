/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime

/-!
# Conversion between decimal interchange formats

`Conversion.convertFormat` rounds once to the destination precision and exponent
range. The source quantum is the preferred quantum, including for signed zero.
The operation acts on datums; BID and DPD are independent encoding choices.

NaNs are quieted, with invalid raised exactly for signaling NaNs. A payload that
fits the destination is preserved; an oversized payload becomes zero. The sign
is retained for every exceptional operand and for exact or rounded zero.

## References

* IEEE 754-2019, §§5.2 and 5.4.2, preferred exponents and format conversion;
  §§6.2 and 7, NaN propagation and default exception handling.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

/-- Convert a decimal datum to `target`, using its source quantum as the preferred
quantum. Finite inputs undergo one exact rational projection in any of the five
rounding directions. Signaling NaNs become quiet and raise invalid. -/
def convertFormat (target : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  match x with
  | .finite negative coefficient quantum =>
      project target mode (Datum.finiteValue negative coefficient quantum) quantum negative
  | .infinity negative => { value := .infinity negative }
  | .nan negative signaling payload =>
      Arithmetic.nanResult target negative payload signaling

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
