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

Integer exponentiation takes place in the exact rational field. Compound also forms `1 + x`
exactly, so neither that addition nor the intermediate powers are rounded to the posit format.
The integer exponent is fixed: exponent zero gives the constant one on every finite input,
including a zero base. Zero to a negative power produces NaR. This differs from the two-posit
`pow` operation, whose two-variable limit at `(0, 0)` is not unique.

## Reference

* [Posit Standard (2022), §§4.2, 5.1, 5.6 and 5.8](https://posithub.org/docs/posit_standard-2.pdf)
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

/--
Round an exact rational integer power once. Zero to a negative power produces NaR; this
explicit domain check prevents the total field convention `0⁻¹ = 0` from defining the result.
For the fixed exponent zero, the underlying function is the constant one.
-/
@[inline] def roundIntPower (format : Format) (base : Rat) (exponent : Int) : Model format :=
  if base = 0 ∧ exponent < 0 then nar format else roundRat format (base ^ exponent)

/-- Fixed integer power, rounded once. NaR propagates; zero to a negative power produces NaR. -/
@[inline] def powInt {format : Format} (value : Model format) (exponent : Int) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => roundIntPower format q exponent

/--
Compound `(1 + x) ^ n`, rounded once. NaR propagates; `x = -1` with negative exponent produces
NaR. Exponent zero gives one even at `x = -1`, since the integer parameter is fixed in §5.8.
Both the addition and exponentiation are exact before the final posit rounding.
-/
@[inline] def compound {format : Format} (value : Model format) (exponent : Int) : Model format :=
  match value.toRat? with
  | none => nar format
  | some q => roundIntPower format (1 + q) exponent

end FloatLib.Floats.Formats.Posit.Model
