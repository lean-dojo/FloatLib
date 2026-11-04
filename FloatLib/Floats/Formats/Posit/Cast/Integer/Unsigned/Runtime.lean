/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.Posit.Cast.Integer.Runtime
public import FloatLib.Numerics.Quantization.Integer.Runtime

/-!
# Posit conversions for unsigned integer words

Posit Standard (2022) §6.4 reserves the MSB-only integer word on input for NaR, and that includes
unsigned integer formats, while every other input denotes its unsigned natural-number value and
gets one §4.1 posit rounding.

On output, the exact posit value is rounded to an integer first, and only then is the full
unsigned range checked. NaR and a rounded result outside that range deliver the MSB-only word.
Ties go to the even integer, the same policy as the signed adapter, because §6.4 doesn't specify
an integer tie rule.

Even `2^(width-1)` is a valid unsigned output, but its representation is the sentinel, so converting
that word back produces NaR. Rounding before the range check matters for small negatives. If we
tested the sign of the source in place of the rounded integer, negative fractions that round to zero
would be rejected by mistake.

All widths use the same range-parameterized quantization kernel as decimal integer conversion.
`BitVec` supplies the carrier, so there are no per-width algorithms.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, §§4.1 and 6.4,
  <https://posithub.org/docs/posit_standard-2.pdf>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

open FloatLib.Numerics

/-- Convert an unsigned word, reserving only the MSB-only word for NaR. -/
@[inline] def ofUnsigned (format : Format) {width : Nat} (value : BitVec width)
    (_hwidth : 0 < width := by decide) : Model format :=
  if value = BitVec.intMin width then nar format
  else roundRat format (value.toNat : Rat)

/-- Round first, then check the unsigned range. Failures deliver the MSB-only word. -/
@[inline] def toUnsigned {format : Format} (width : Nat) (value : Model format)
    (_hwidth : 0 < width := by decide) : BitVec width :=
  match value.toRat? with
  | none => BitVec.intMin width
  | some rational =>
      match (IntegerFormat.unsigned width).range.round? roundRatEven rational with
      | none => BitVec.intMin width
      | some integer => BitVec.ofNat width integer.toNat

end FloatLib.Floats.Formats.Posit.Model
