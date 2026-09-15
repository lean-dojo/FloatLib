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

These conversions implement the MSB-only sentinel specified in Section 6.4 of the Posit Standard
(2022) for positive-width two's-complement integers. The sentinel is `FixedInt.minCode width`;
its signed interpretation is the least representable integer.

Integer-to-posit conversion recognizes the sentinel before applying Section 4.1 posit rounding
to the exact signed integer. Posit-to-integer conversion rounds the exact rational value to the
nearest integer, with ties to even, then checks the signed range. Section 6.4 says to check the
range after rounding but does not itself prescribe an integer tie rule; ties to even is the
convention chosen here. NaR and an out-of-range rounded result produce the sentinel.

An in-range rounded result equal to the signed minimum has the same bits as the sentinel.
Converting those bits back to posit therefore produces NaR. These adapters do not change the
ordinary numerical interpretation of `FixedInt`. Unsigned adapters are defined in
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
Every other word undergoes exactly one Section 4.1 rounding of its signed integer value.
-/
@[inline] def ofFixedInt (format : Format) {width : Nat} (value : FixedInt width)
    (_hwidth : 0 < width := by decide) : Model format :=
  if value = FixedInt.minCode width then nar format
  else roundRat format (value.toInt : Rat)

/--
Round a posit to a positive-width signed integer, using nearest integer with ties to even.
NaR and overflow after rounding produce the MSB-only word; no modular wraparound is used.
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
