/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime

/-!
# Once-rounded integer powers and compound

Integer exponentiation happens in the exact rational field, and compound forms `1 + x` exactly
too, so neither that addition nor any intermediate power is rounded to the posit format. Because
the integer exponent is a fixed parameter, exponent zero gives the constant one on every finite
input, a zero base included. That differs from the two-posit `pow` operation, whose two-variable
limit at `(0, 0)` is not unique. Zero to a negative power produces NaR.

## Reference

* [Posit Standard (2022), §§4.2, 5.1, 5.6 and 5.8](https://posithub.org/docs/posit_standard-2.pdf)
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/--
Round an exact rational integer power once. Zero to a negative power produces NaR, and this
domain check is what keeps the total field convention `0⁻¹ = 0` from defining the result.
For the fixed exponent zero, the underlying function is the constant one.
-/
@[inline] def roundIntPower (format : Format) (base : Rat) (exponent : Int) : Model format :=
  if base = 0 ∧ exponent < 0 then nar format else roundRat format (base ^ exponent)

/-- Fixed integer power, rounded once. NaR propagates, and zero to a negative power gives NaR. -/
@[inline] def powInt {format : Format} (value : Model format) (exponent : Int) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => roundIntPower format q exponent

/--
Compound `(1 + x) ^ n`, rounded once. NaR propagates, and `x = -1` with a negative exponent produces
NaR. Exponent zero gives one even at `x = -1`, since the integer parameter is fixed in §5.8. Both
the addition and exponentiation are exact before the final posit rounding.
-/
@[inline] def compound {format : Format} (value : Model format) (exponent : Int) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => roundIntPower format (1 + q) exponent

end FloatLib.Floats.Formats.Posit.Model
