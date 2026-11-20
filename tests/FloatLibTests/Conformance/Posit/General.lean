/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit
public import FloatLib.Tactic.FloatDecide

/-!
# Posits with exponent sizes other than two, checked by the kernel

The Posit Standard (2022) fixes two exponent bits, and `Posit.General` proves the operations of
`Posit.KernelPath.Core` for every number of them. The expected encodings below are those of
SoftPosit, whose 8-bit posits have no exponent bit and whose 16-bit posits have one
(`tests/oracles/posit_general.py` makes the full comparison). Lean's kernel evaluates each
operation on the natural-number encodings.

The last section applies the theorems of `Posit.General` to explicit encodings, so that their
premises are seen to hold: the value of an encoding, the rounding of a sum, a quotient and a
square root, and the uniqueness that turns a rounding into an equation.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Posit.General

open FloatLib.Floats.Formats.Posit FloatLib.Floats.Formats.Posit.KernelPath
open FloatLib.Floats.Formats.Posit.General

/-! ## Eight bits, no exponent bit -/

-- Sum, difference, product and quotient of four pairs of encodings.
example : [add 7 0 0x40 0x40, sub 7 0 0x40 0x40, mul 7 0 0x40 0x40, div 7 0 0x40 0x40] =
    [0x60, 0x00, 0x40, 0x40] := by decide +kernel

example : [add 7 0 0x35 0x6b, sub 7 0 0x35 0x6b, mul 7 0 0x35 0x6b, div 7 0 0x35 0x6b] =
    [0x70, 0x9c, 0x66, 0x10] := by decide +kernel

-- The least positive value and the greatest: both saturate.
example : [add 7 0 0x01 0x7f, sub 7 0 0x01 0x7f, mul 7 0 0x01 0x7f, div 7 0 0x01 0x7f] =
    [0x7f, 0x81, 0x40, 0x01] := by decide +kernel

-- Negative operands.
example : [add 7 0 0xc3 0x2a, sub 7 0 0xc3 0x2a, mul 7 0 0xc3 0x2a, div 7 0 0xc3 0x2a] =
    [0xed, 0xac, 0xd8, 0xb2] := by decide +kernel

example : [add 7 0 0x13 0xee, sub 7 0 0x13 0xee, mul 7 0 0x13 0xee, div 7 0 0x13 0xee] =
    [0x01, 0x25, 0xfb, 0xbe] := by decide +kernel

-- Square roots, with NaR for a negative operand, and fused multiply-adds with the addend 0x55.
example : [sqrt 7 0 0x40, sqrt 7 0 0x35, sqrt 7 0 0x01, sqrt 7 0 0xc3, sqrt 7 0 0x7f,
    sqrt 7 0 0x13] = [0x40, 0x3a, 0x08, 0x80, 0x78, 0x23] := by decide +kernel

example : [fma 7 0 0x40 0x40 0x55, fma 7 0 0x35 0x6b 0x55, fma 7 0 0x01 0x7f 0x55,
    fma 7 0 0xc3 0x2a 0x55, fma 7 0 0x7f 0x7f 0x55, fma 7 0 0x13 0xee 0x55] =
    [0x65, 0x71, 0x65, 0x41, 0x7f, 0x52] := by decide +kernel

-- The order, and the conversion to 16 bits with one exponent bit.
example : [lt 7 0x40 0x40, lt 7 0x35 0x6b, lt 7 0xc3 0x2a, lt 7 0x13 0xee, lt 7 0x80 0x13] =
    [false, true, true, false, true] := by decide +kernel

example : [KernelPath.cast 7 0 15 1 0x40, KernelPath.cast 7 0 15 1 0x35,
    KernelPath.cast 7 0 15 1 0x01, KernelPath.cast 7 0 15 1 0xc3, KernelPath.cast 7 0 15 1 0x13,
    KernelPath.cast 7 0 15 1 0x80] = [0x4000, 0x3a80, 0x0800, 0xc180, 0x2300, 0x8000] := by
  decide +kernel

/-! ## Sixteen bits, one exponent bit -/

example : [add 15 1 0x4000 0x5000, sub 15 1 0x4000 0x5000, mul 15 1 0x4000 0x5000,
    div 15 1 0x4000 0x5000] = [0x5800, 0xc000, 0x5000, 0x3000] := by decide +kernel

example : [add 15 1 0x3555 0x6aaa, sub 15 1 0x3555 0x6aaa, mul 15 1 0x3555 0x6aaa,
    div 15 1 0x3555 0x6aaa] = [0x6b55, 0x9601, 0x6638, 0x1000] := by decide +kernel

example : [add 15 1 0x0001 0x7fff, sub 15 1 0x0001 0x7fff, mul 15 1 0x0001 0x7fff,
    div 15 1 0x0001 0x7fff] = [0x7fff, 0x8001, 0x4000, 0x0001] := by decide +kernel

example : [add 15 1 0xc333 0x2aaa, sub 15 1 0xc333 0x2aaa, mul 15 1 0xc333 0x2aaa,
    div 15 1 0xc333 0x2aaa] = [0xd110, 0xbaef, 0xd800, 0xaeb8] := by decide +kernel

example : [add 15 1 0x1234 0xedcb, sub 15 1 0x1234 0xedcb, mul 15 1 0x1234 0xedcb,
    div 15 1 0x1234 0xedcb] = [0xffa0, 0x1a34, 0xfabf, 0xc003] := by decide +kernel

example : [sqrt 15 1 0x4000, sqrt 15 1 0x3555, sqrt 15 1 0x0001, sqrt 15 1 0xc333,
    sqrt 15 1 0x1234] = [0x4000, 0x3a21, 0x0080, 0x8000, 0x2212] := by decide +kernel

example : [fma 15 1 0x4000 0x5000 0x5555, fma 15 1 0x3555 0x6aaa 0x5555,
    fma 15 1 0x0001 0x7fff 0x5555, fma 15 1 0xc333 0x2aaa 0x5555,
    fma 15 1 0x1234 0xedcb 0x5555] = [0x6155, 0x69c7, 0x5d55, 0x5255, 0x5548] := by
  decide +kernel

-- Conversions to 8 bits with no exponent bit and to 32 bits with two.
example : [KernelPath.cast 15 1 7 0 0x4000, KernelPath.cast 15 1 7 0 0x3555,
    KernelPath.cast 15 1 7 0 0x0001, KernelPath.cast 15 1 7 0 0xc333,
    KernelPath.cast 15 1 7 0 0x1234] = [0x40, 0x2b, 0x01, 0xc6, 0x05] := by decide +kernel

example : [KernelPath.cast 15 1 31 2 0x4000, KernelPath.cast 15 1 31 2 0x3555,
    KernelPath.cast 15 1 31 2 0x0001, KernelPath.cast 15 1 31 2 0xc333,
    KernelPath.cast 15 1 31 2 0x1234] =
    [0x40000000, 0x3aaa8000, 0x00800000, 0xc1998000, 0x22340000] := by decide +kernel

/-! ## Conversions to integers, and the flat forms -/

-- The greatest eight-bit value with no exponent bit is 64, and minus it is the two's complement
-- of 64 in 32 bits. NaR gives the word with only its most significant bit set.
example : [toSigned 7 0 32 0x7f, toSigned 7 0 32 0x81, toSigned 7 0 32 0x50,
    toSigned 7 0 32 0x80, toUnsigned 7 0 32 0x7f, toUnsigned 7 0 32 0x81] =
    [64, 4294967232, 2, 2147483648, 64, 2147483648] := by decide +kernel

-- With one exponent bit, the 16-bit encoding 0x7000 is 16 and the greatest value is `2 ^ 28`.
example : [toSigned 15 1 32 0x7000, toSigned 15 1 64 0x7fff, toUnsigned 15 1 32 0x3000] =
    [16, 268435456, 0] := by decide +kernel

-- `float_decide` evaluates the staged operations through their flat forms, for every number of
-- exponent bits.
example : add 7 0 0x35 0x6b = 0x70 ∧ div 15 1 0x3555 0x6aaa = 0x1000 ∧
    sqrt 31 3 0x35555555 = 982003548 := by
  float_decide

/-! ## The theorems on explicit encodings -/

/-- With no exponent bit, the eight-bit code 0x40 has the significand 32 at the exponent `-5`:
the value one. -/
private theorem value_one : value 7 0 0x40 = 1 := by
  rw [value_eq_fields (by decide) (by decide) (by decide)]
  have h : significand 0 0x40 (tailLength 7 0x40) = 32 ∧
      exponent 7 0 0x40 (tailLength 7 0x40) + 5 = bias 7 0 := by decide +kernel
  have he : ((exponent 7 0 0x40 (tailLength 7 0x40) : ℕ) : ℤ) - ((bias 7 0 : ℕ) : ℤ) = -5 := by
    omega
  rw [h.1, he]
  norm_num

-- The encoding 0x40 has the value one.
example : toRat? 7 0 0x40 = some 1 := by
  rw [toRat?_of_lt (by decide) (by decide), value_one]

-- `1 + 1` is rounded to the encoding that `add` returns, and that encoding is 0x60.
example : IsRoundedTo 7 0 (1 + 1) 0x60 := by
  have h1 : toRat? 7 0 0x40 = some 1 := by
    rw [toRat?_of_lt (by decide) (by decide), value_one]
  have h := add_isRoundedTo (es := 0) (p := 7) (by decide) (by decide) (by decide) h1 h1
  rwa [show add 7 0 0x40 0x40 = 0x60 by decide +kernel] at h

-- Every rational has a rounding in every format, and only one.
example (q : ℚ) : ∃ a, IsRoundedTo 5 3 q a ∧ ∀ b, IsRoundedTo 5 3 q b → b = a := by
  obtain ⟨a, ha⟩ := exists_isRoundedTo 3 (by decide : 0 < 5) q
  exact ⟨a, ha, fun b hb => hb.unique ha⟩

-- The quotient of two encodings with values is the rounding of the quotient of the values, in
-- a format with three exponent bits.
example {a b : ℕ} {x y : ℚ} (ha : a < 2 ^ 12) (hb : b < 2 ^ 12) (hx : toRat? 11 3 a = some x)
    (hy : toRat? 11 3 b = some y) (hb0 : b ≠ 0) : IsRoundedTo 11 3 (x / y) (div 11 3 a b) :=
  div_isRoundedTo (by decide) ha hb hx hy hb0

-- The square root of a positive encoding, stated on squares, with four exponent bits.
example {a : ℕ} (ha0 : 0 < a) (ha : a < 2 ^ 9) :
    IsRoundedSqrt 9 4 (value 9 4 a) (sqrt 9 4 a) :=
  sqrt_isRoundedSqrt (by decide) ha0 ha

-- At two exponent bits the general rule is the rule of the standard's model.
example (q : ℚ) :
    IsRoundedTo 7 2 q (Model.roundRat ({ bits := 8 } : Format) q).toNatBits :=
  roundRat_isRoundedTo { bits := 8 } q

-- NaR is absorbing in every operation, for every number of exponent bits, and a quotient by
-- zero is NaR.
example (es a b : ℕ) :
    add 7 es (2 ^ 7) b = 2 ^ 7 ∧ sub 7 es a (2 ^ 7) = 2 ^ 7 ∧ mul 7 es (2 ^ 7) b = 2 ^ 7 ∧
      div 7 es a 0 = 2 ^ 7 ∧ fma 7 es a b (2 ^ 7) = 2 ^ 7 ∧
      KernelPath.cast 7 es 15 1 (2 ^ 7) = 2 ^ 15 :=
  ⟨add_nar es (.inl rfl), sub_nar es (.inr rfl), mul_nar es (.inl rfl),
    div_nar es (.inr (.inr rfl)), fma_nar es (.inr (.inr rfl)), cast_nar 7 es 15 1⟩

-- A difference, a fused multiply-add and a conversion to another format are rounded once, with
-- three exponent bits, and a rounding is never NaR.
example {a b c : ℕ} {x y z : ℚ} (ha : a < 2 ^ 12) (hb : b < 2 ^ 12) (hc : c < 2 ^ 12)
    (hx : toRat? 11 3 a = some x) (hy : toRat? 11 3 b = some y) (hz : toRat? 11 3 c = some z) :
    IsRoundedTo 11 3 (x - y) (sub 11 3 a b) ∧ IsRoundedTo 11 3 (x * y + z) (fma 11 3 a b c) ∧
      IsRoundedTo 15 1 x (KernelPath.cast 11 3 15 1 a) ∧ sub 11 3 a b ≠ 2 ^ 11 :=
  ⟨sub_isRoundedTo (by decide) ha hb hx hy, fma_isRoundedTo (by decide) ha hb hc hx hy hz,
    cast_isRoundedTo (by decide) (by decide) ha hx,
    (sub_isRoundedTo (by decide) ha hb hx hy).ne_nar⟩

-- NaR is below every other encoding, and no encoding is below it.
example {b : ℕ} (hb : b < 2 ^ 8) (hnar : b ≠ 2 ^ 7) :
    lt 7 (2 ^ 7) b = true ∧ lt 7 b (2 ^ 7) = false ∧ le 7 (2 ^ 7) b = true ∧
      le 7 b (2 ^ 7) = false :=
  ⟨lt_nar_left hb hnar, lt_nar_right 7 b, le_nar_left 7 b, le_nar_right hb hnar⟩

-- The next encoding is above an encoding with none in between, and the prior one is one step
-- below in the order.
example {a : ℕ} (ha : a < 2 ^ 8) (h : signedKey 7 a + 1 < 2 ^ 8) (c : ℕ) :
    lt 7 a (next 7 a) = true ∧ ¬(lt 7 a c = true ∧ lt 7 c (next 7 a) = true) :=
  ⟨lt_next ha h, not_lt_and_lt_next ha h c⟩

example {a : ℕ} (ha : a < 2 ^ 8) (h : 0 < signedKey 7 a) :
    signedKey 7 (prior 7 a) = signedKey 7 a - 1 :=
  signedKey_prior ha h

-- The conversions to integers at zero and at NaR, for every number of exponent bits and every
-- width of the integer.
example (es w : ℕ) :
    toSigned 7 es w 0 = 0 ∧ toUnsigned 7 es w 0 = 0 ∧ toSigned 7 es w (2 ^ 7) = 2 ^ (w - 1) :=
  ⟨toSigned_zero 7 es w, toUnsigned_zero 7 es w, toSigned_nar 7 es w⟩

-- The conversions of a positive and of a negative encoding round the value to the nearest
-- integer, ties to even, and saturate: the hypotheses hold for 0x50 and 0x81 above.
example :=
  And.intro (toSigned_of_lt (p := 7) (es := 0) (a := 0x50) 32 (by decide) (by decide) (by decide))
    (toUnsigned_of_lt (p := 7) (es := 0) (a := 0x50) 32 (by decide) (by decide) (by decide))

example :=
  And.intro (toSigned_of_gt (p := 7) (es := 0) (a := 0x81) 32 (by decide) (by decide) (by decide))
    (toUnsigned_of_gt (p := 7) (es := 0) (a := 0x81) 32 (by decide) (by decide) (by decide))

-- A rounding of a positive number is a rounded square root of its square, with four exponent
-- bits.
example {r : ℚ} {c : ℕ} (hr : 0 < r) (h : IsRounded 9 4 r c) : IsRoundedSqrt 9 4 (r ^ 2) c :=
  isRoundedSqrt_sq (by decide) hr h

-- At two exponent bits the value of an encoding is the value of the standard's model.
example (x : Model ({ bits := 16 } : Format)) : toRat? 15 2 x.toNatBits = x.toRat? :=
  toRat?_toNatBits x

end FloatLibTests.Conformance.Posit.General
