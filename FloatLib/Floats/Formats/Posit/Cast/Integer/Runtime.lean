/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime
public import FloatLib.Numerics.Quantization.Deterministic.Rational
public import FloatLib.Numerics.Representations.FixedInt.Core

/-!
# Posit conversions to and from fixed-width signed integers

These conversions implement the MSB-only sentinel from Section 6.4 of the Posit Standard (2022)
for two's-complement integers of positive width, where the sentinel is `FixedInt.minCode width` and
its signed interpretation is the least representable integer.

From integer to posit, the sentinel is recognized first, and every other integer gets Section 4.1
posit rounding of its exact signed value. From posit to integer, the exact rational value is
rounded to the nearest integer, with ties to even, and then the signed range is checked. Section
6.4 says to check the range after rounding, but it doesn't prescribe an integer tie rule, so ties
to even is our choice. NaR and an out-of-range rounded result both produce the sentinel.

That leaves one corner case. An in-range rounded result equal to the signed minimum has the same
bits as the sentinel, so converting those bits back to a posit gives NaR. These adapters leave the
ordinary numerical interpretation of `FixedInt` alone. Unsigned adapters live in
`Integer.Unsigned`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 4.1 and 6.4, <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics
open FloatLib.Numerics.Representations

/--
Convert a positive-width signed integer to posit, treating its MSB-only word as NaR.
Every other word gets a single Section 4.1 rounding of its signed integer value.
-/
@[inline] def ofFixedInt (format : Format) {width : Nat} (value : FixedInt width)
    (_hwidth : 0 < width := by decide) : Model format :=
  if value = FixedInt.minCode width then nar format
  else roundRat format (value.toInt : Rat)

/--
Round a posit to a positive-width signed integer, using nearest integer with ties to even.
NaR and overflow after rounding produce the MSB-only word. There is no modular wraparound.
-/
@[inline] def toFixedInt {format : Format} (width : Nat) (value : Model format)
    (_hwidth : 0 < width := by decide) : FixedInt width :=
  match value.toRat? with
  | none => FixedInt.minCode width
  | some rational =>
      let rounded := roundRatEven rational
      if FixedInt.InRange width rounded then FixedInt.ofInt rounded
      else FixedInt.minCode width

end FloatLib.Floats.Formats.Posit.Model
