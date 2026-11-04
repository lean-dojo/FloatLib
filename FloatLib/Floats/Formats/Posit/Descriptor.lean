/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Posit format descriptors

A posit has one sign bit and a tapered payload, and the length of its regime field depends on the
encoded value. The Posit Standard (2022) fixes the maximum exponent field at two bits, so you pick
a standard format by its total width alone, as in `{ bits := 32 }`.

We keep the descriptor static in the Lean type. That is what lets the library support arbitrary
widths without storing the width in every runtime value.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 2--4, <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, Supercomputing Frontiers and Innovations 9(1),
  2022, <https://doi.org/10.14529/jsfi220102>.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit

/--
A validated, statically configured Posit Standard encoding, written `{ bits := 32 }`.

With a numeral width `decide` supplies the proof field, and a width below two fails with the
message `a posit format requires bits ≥ 2`. Any other width passes its proof as
`bits_ge_two := h`.
-/
structure Format where
  /-- Total encoded width, including the sign bit. -/
  bits : Nat
  /-- The Posit Standard requires at least two total bits. -/
  bits_ge_two : 2 ≤ bits := by
    first
    | decide
    | fail "a posit format requires bits ≥ 2"
  deriving Repr

namespace Format

/-- Number of encoded bits below the sign bit. -/
@[inline] def payloadBits (format : Format) : Nat :=
  format.bits - 1

/-- Index of the sign bit in least-significant-bit numbering. -/
@[inline] def signIndex (format : Format) : Nat :=
  format.bits - 1

/-- Natural-number bit mask containing only the sign bit. -/
@[inline] def signMaskNat (format : Format) : Nat :=
  2 ^ format.signIndex

/-- Unsigned encoding of the exact posit value one. -/
@[inline] def oneCodeNat (format : Format) : Nat :=
  2 ^ (format.payloadBits - 1)

/-- Modulus of the exact-width unsigned encoding. -/
@[inline] def modulus (format : Format) : Nat :=
  2 ^ format.bits

/-- Maximum number of exponent bits available after the regime terminator. -/
@[inline] def exponentBits (_format : Format) : Nat :=
  2

/-- Binary exponent contributed by one unit of regime value. -/
@[inline] def regimeExponentStep (_format : Format) : Nat :=
  4

/-- One regime unit contributes `2 ^ exponentBits` to the decoded binary exponent. -/
@[simp] theorem regimeExponentStep_eq_two_pow_exponentBits (format : Format) :
    format.regimeExponentStep = 2 ^ format.exponentBits := by
  rfl

/--
The same standardized posit family at one additional bit of precision.

Section 4.1 of the standard defines an `n`-bit rounding boundary using an `(n + 1)`-bit posit.
So this transformation is part of the exact rounding definition itself, and it isn't an
implementation convenience.
-/
@[inline] def nextPrecision (format : Format) : Format where
  bits := format.bits + 1
  bits_ge_two := Nat.le_trans format.bits_ge_two (Nat.le_succ format.bits)

/-- Adding one encoded bit adds exactly one bit to the tapered payload. -/
@[simp] theorem nextPrecision_payloadBits (format : Format) :
    format.nextPrecision.payloadBits = format.payloadBits + 1 := by
  change format.bits + 1 - 1 = (format.bits - 1) + 1
  have hbits := format.bits_ge_two
  omega

/-- Adding one encoded bit shifts the sign mask left by one place. -/
@[simp] theorem nextPrecision_signMaskNat (format : Format) :
    format.nextPrecision.signMaskNat = 2 * format.signMaskNat := by
  unfold signMaskNat signIndex
  change
    2 ^ (format.bits + 1 - 1) =
      2 * 2 ^ (format.bits - 1)
  have hbits := format.bits_ge_two
  rw [show format.bits + 1 - 1 = (format.bits - 1) + 1 by omega,
    Nat.pow_succ]
  omega

/-- Every valid posit has at least one payload bit. -/
theorem payloadBits_pos (format : Format) : 0 < format.payloadBits := by
  unfold payloadBits
  have := format.bits_ge_two
  omega

/-- The unique sign-bit mask is nonzero. -/
theorem signMaskNat_pos (format : Format) :
    0 < format.signMaskNat := by
  exact Nat.two_pow_pos format.signIndex

/-- At least the codes zero and one lie below the sign-bit boundary. -/
theorem one_lt_signMaskNat (format : Format) :
    1 < format.signMaskNat := by
  apply Nat.one_lt_two_pow
  unfold signIndex
  have hbits := format.bits_ge_two
  omega

/-- The exact-one encoding is nonzero. -/
theorem oneCodeNat_pos (format : Format) :
    0 < format.oneCodeNat :=
  Nat.two_pow_pos _

/-- The exact-one encoding lies in the positive finite half of the word space. -/
theorem oneCodeNat_lt_signMaskNat (format : Format) :
    format.oneCodeNat < format.signMaskNat := by
  unfold oneCodeNat signMaskNat signIndex
  have hpayload : 0 < format.payloadBits :=
    format.payloadBits_pos
  have hsame : format.payloadBits = format.bits - 1 := rfl
  rw [← hsame]
  exact Nat.pow_lt_pow_right (by decide)
    (Nat.sub_one_lt (Nat.ne_of_gt hpayload))

/-- The sign bit is strictly below the exact-width modulus. -/
theorem signMaskNat_lt_modulus (format : Format) :
    format.signMaskNat < format.modulus := by
  unfold signMaskNat signIndex modulus
  have hbits : 0 < format.bits := lt_of_lt_of_le (by decide) format.bits_ge_two
  exact Nat.pow_lt_pow_right (by decide) (Nat.sub_one_lt (Nat.ne_of_gt hbits))

/-- The complete unsigned modulus is twice the mask containing the sign bit. -/
theorem modulus_eq_two_mul_signMaskNat (format : Format) :
    format.modulus = 2 * format.signMaskNat := by
  have hbits : 0 < format.bits :=
    lt_of_lt_of_le (by decide) format.bits_ge_two
  have hindex : format.signIndex + 1 = format.bits := by
    simp [signIndex,
      Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hbits))]
  unfold modulus signMaskNat
  rw [← hindex, Nat.pow_succ]
  omega

end Format
end FloatLib.Floats.Formats.Posit
