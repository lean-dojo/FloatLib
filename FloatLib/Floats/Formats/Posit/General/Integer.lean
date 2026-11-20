/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Arithmetic
public import FloatLib.Floats.Formats.Posit.KernelPath.Integer

/-!
# Posits with any number of exponent bits: conversions to integers

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. `KernelPath.toSigned`
and `KernelPath.toUnsigned` are the words of the conversions of §6.4 to a signed and to an
unsigned integer of `w` bits. This module states them on values, for every number `p ≥ 1` of
payload bits and every number `es` of exponent bits:

* `nearestNat_fields`: the integer that the conversions read from the fields of a positive
  magnitude code is the nearest integer of its value, ties to even.
* `toSigned_of_lt`, `toSigned_of_gt`: a positive encoding gives that integer `n` when it is
  below `2 ^ (w - 1)`, and a negative one the two's complement of `n` in `w` bits when `n` is at
  most `2 ^ (w - 1)`. Outside the range the result is the word with only its most significant
  bit set, as for NaR (`toSigned_nar`), and zero gives zero (`toSigned_zero`).
* `toUnsigned_of_lt`, `toUnsigned_of_gt`, `toUnsigned_nar`, `toUnsigned_zero`: the same for an
  unsigned integer, where a positive encoding gives `n` below `2 ^ w` and a negative one gives
  zero only when it rounds to zero.

The conversion from an integer is the rounding of a ratio with the denominator one
(`ofRatio_isRoundedTo`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Numerics FloatLib.Numerics.Kernel FloatLib.Floats.Formats.Posit.KernelPath

/-- The integer that the conversions read from the fields of a positive magnitude code is the
nearest integer of its value, ties to even, for every number of exponent bits. -/
theorem nearestNat_fields {p es m : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    nearestNat (significand es m (tailLength p m)) (exponent p es m (tailLength p m))
        (bias p es) = (roundRatEven (value p es m)).toNat := by
  rw [value_eq_fields hp hm0 hm, nearestNat_eq, Int.toNat_natCast]

/-- The conversion of NaR to a signed integer is the word with only its most significant bit
set. -/
theorem toSigned_nar (p es w : ℕ) : toSigned p es w (2 ^ p) = 2 ^ (w - 1) := by
  unfold toSigned nar
  kernel_notation
  rw [ite_eq_left trivial]

/-- The conversion of zero to a signed integer is zero. -/
theorem toSigned_zero (p es w : ℕ) : toSigned p es w 0 = 0 := by
  unfold toSigned nar
  kernel_notation
  rw [ite_eq_right (Nat.two_pow_pos p).ne, ite_eq_left trivial]

/--
Posit Standard (2022), §6.4, for every number of exponent bits: a positive encoding converts to
the nearest integer of its value, ties to even, when that integer is below `2 ^ (w - 1)`, and to
the word with only its most significant bit set otherwise.
-/
theorem toSigned_of_lt {p es a : ℕ} (w : ℕ) (hp : 0 < p) (ha0 : 0 < a) (ha : a < 2 ^ p) :
    toSigned p es w a =
      if (roundRatEven (value p es a)).toNat + 1 ≤ 2 ^ (w - 1) then
        (roundRatEven (value p es a)).toNat
      else 2 ^ (w - 1) := by
  have hm : magnitude p a = a := by rw [magnitude_eq_ite, ite_eq_right (Nat.not_le.mpr ha)]
  unfold toSigned nar
  kernel_notation
  rw [ite_eq_right (Nat.ne_of_lt ha), ite_eq_right ha0.ne', ite_eq_right (Nat.not_le.mpr ha), hm,
    nearestNat_fields hp ha0 ha]

/--
Posit Standard (2022), §6.4, for every number of exponent bits: a negative encoding converts to
the two's complement in `w` bits of the nearest integer `n` of its magnitude, ties to even, when
`n` is at most `2 ^ (w - 1)`, and to the word with only its most significant bit set otherwise.
-/
theorem toSigned_of_gt {p es a : ℕ} (w : ℕ) (hp : 0 < p) (ha : 2 ^ p < a)
    (ha' : a < 2 ^ (p + 1)) :
    toSigned p es w a =
      if (roundRatEven (value p es (2 ^ (p + 1) - a))).toNat ≤ 2 ^ (w - 1) then
        (2 ^ w - (roundRatEven (value p es (2 ^ (p + 1) - a))).toNat) % 2 ^ w
      else 2 ^ (w - 1) := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hm : magnitude p a = 2 ^ (p + 1) - a := by rw [magnitude_eq_ite, ite_eq_left ha.le]
  unfold toSigned nar
  kernel_notation
  rw [ite_eq_right (Nat.ne_of_gt ha), ite_eq_right (by omega), ite_eq_left ha.le, hm,
    nearestNat_fields hp (by omega) (by omega)]

/-- The conversion of NaR to an unsigned integer is the word with only its most significant bit
set. -/
theorem toUnsigned_nar (p es w : ℕ) : toUnsigned p es w (2 ^ p) = 2 ^ (w - 1) := by
  unfold toUnsigned nar
  kernel_notation
  rw [ite_eq_left trivial]

/-- The conversion of zero to an unsigned integer is zero. -/
theorem toUnsigned_zero (p es w : ℕ) : toUnsigned p es w 0 = 0 := by
  unfold toUnsigned nar
  kernel_notation
  rw [ite_eq_right (Nat.two_pow_pos p).ne, ite_eq_left trivial]

/--
Posit Standard (2022), §6.4, for every number of exponent bits: a positive encoding converts to
the nearest integer of its value, ties to even, when that integer is below `2 ^ w`, and to the
word with only its most significant bit set otherwise.
-/
theorem toUnsigned_of_lt {p es a : ℕ} (w : ℕ) (hp : 0 < p) (ha0 : 0 < a) (ha : a < 2 ^ p) :
    toUnsigned p es w a =
      if (roundRatEven (value p es a)).toNat + 1 ≤ 2 ^ w then
        (roundRatEven (value p es a)).toNat
      else 2 ^ (w - 1) := by
  have hm : magnitude p a = a := by rw [magnitude_eq_ite, ite_eq_right (Nat.not_le.mpr ha)]
  unfold toUnsigned nar
  kernel_notation
  rw [ite_eq_right (Nat.ne_of_lt ha), ite_eq_right ha0.ne', ite_eq_right (Nat.not_le.mpr ha), hm,
    nearestNat_fields hp ha0 ha]

/--
Posit Standard (2022), §6.4, for every number of exponent bits: a negative encoding converts to
zero when the nearest integer of its magnitude is zero, and to the word with only its most
significant bit set otherwise.
-/
theorem toUnsigned_of_gt {p es a : ℕ} (w : ℕ) (hp : 0 < p) (ha : 2 ^ p < a)
    (ha' : a < 2 ^ (p + 1)) :
    toUnsigned p es w a =
      if (roundRatEven (value p es (2 ^ (p + 1) - a))).toNat = 0 then 0 else 2 ^ (w - 1) := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hm : magnitude p a = 2 ^ (p + 1) - a := by rw [magnitude_eq_ite, ite_eq_left ha.le]
  unfold toUnsigned nar
  kernel_notation
  rw [ite_eq_right (Nat.ne_of_gt ha), ite_eq_right (by omega), ite_eq_left ha.le, hm,
    nearestNat_fields hp (by omega) (by omega)]

end FloatLib.Floats.Formats.Posit.General
