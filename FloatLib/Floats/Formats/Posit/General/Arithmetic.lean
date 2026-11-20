/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Spec
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Posits with any number of exponent bits: sums, products, signs and conversions

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. The operations of
`Posit.KernelPath.Core` take the number `es` of exponent bits as a parameter. This module proves
that the ones with an exact dyadic result return the encoding that the specification of
`General.Spec` names, for every number `p ≥ 1` of payload bits, every `es` and all operands,
zero, NaR and both signs included:

* `toRat?_eq_dyadic`: an encoding that is neither zero nor NaR has the value
  `(-1) ^ sign * significand * 2 ^ (exponent - bias)` of the fields that the kernel reads.
* `add_isRoundedTo`, `sub_isRoundedTo`, `mul_isRoundedTo`, `fma_isRoundedTo`: the result is the
  rounding of the exact sum, difference, product and `x * y + z` of the values (Posit Standard
  (2022), §5.4 and §4.1 with `2 ^ es` in place of `4`; the fused operation is a FloatLib
  extension). `add_nar`, `sub_nar`, `mul_nar`, `fma_nar`: NaR propagates.
* `toRat?_neg`, `toRat?_abs`, `neg_nar`, `abs_nar`: negation and the absolute value are exact,
  and they fix NaR.
* `cast_isRoundedTo`, `cast_nar`: the conversion to a format with other numbers of payload bits
  and of exponent bits returns the rounding of the value in the destination.

`General.Quotient` has division, the square root and the rounding of a ratio.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Numerics.Kernel FloatLib.Floats.Formats.Posit.KernelPath

/-! ## Encodings and their fields -/

/-- The dyadic number with the sign bit `s`, the significand `M` and the exponent `E` biased by
`bK * 2 ^ es`: `(-1) ^ s * M * 2 ^ (E - bK * 2 ^ es)`. -/
def dyadic (es bK s M E : ℕ) : ℚ :=
  signFactor s * ((M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es))

/-- The sign bit of an encoding below the modulus: zero below the sign bit and one from it on. -/
theorem div_two_pow_eq {p a : ℕ} (ha : a < 2 ^ (p + 1)) :
    a / 2 ^ p = if a < 2 ^ p then 0 else 1 := by
  have := Nat.two_pow_pos p
  rw [pow_succ] at ha
  split_ifs with h
  · exact Nat.div_eq_of_lt h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-- The sign bit of an encoding below the modulus is zero or one. -/
theorem div_two_pow_le_one {p a : ℕ} (ha : a < 2 ^ (p + 1)) : a / 2 ^ p ≤ 1 := by
  rw [div_two_pow_eq ha]
  split_ifs <;> omega

/-- The magnitude of an encoding: itself below the sign bit and its two's complement in
`p + 1` bits from the sign bit on. -/
theorem magnitude_eq_ite (p a : ℕ) :
    magnitude p a = if 2 ^ p ≤ a then 2 ^ (p + 1) - a else a := by
  unfold magnitude nar
  kernel_notation

/-- The magnitude of an encoding that is neither zero nor NaR is a positive magnitude code. -/
theorem magnitude_bounds {p a : ℕ} (ha : a < 2 ^ (p + 1)) (ha0 : a ≠ 0) (hnar : a ≠ 2 ^ p) :
    0 < magnitude p a ∧ magnitude p a < 2 ^ p := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  rw [magnitude_eq_ite]
  split_ifs <;> omega

/-- The exponent bias is the regime bias times `2 ^ es`, as integers. -/
theorem bias_cast (p es : ℕ) : ((bias p es : ℕ) : ℤ) = ((regimeBias p : ℕ) : ℤ) * 2 ^ es := by
  have h : regimeBias p = 8 * (p + 1) := rfl
  rw [bias_eq_mul, h]
  push_cast
  ring

/--
The value of an encoding that is neither zero nor NaR is the dyadic number of the fields that
the kernel reads from its magnitude, with the sign of the encoding.
-/
theorem toRat?_eq_dyadic {p es a : ℕ} (hp : 0 < p) (ha : a < 2 ^ (p + 1)) (ha0 : a ≠ 0)
    (hnar : a ≠ 2 ^ p) :
    toRat? p es a =
      some (dyadic es (regimeBias p) (a / 2 ^ p)
        (significand es (magnitude p a) (tailLength p (magnitude p a)))
        (exponent p es (magnitude p a) (tailLength p (magnitude p a)))) := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  rw [div_two_pow_eq ha, magnitude_eq_ite]
  unfold dyadic signFactor
  rcases Nat.lt_or_gt_of_ne hnar with hlt | hgt
  · rw [toRat?_of_lt ha0 hlt, ite_eq_left hlt, ite_eq_right (Nat.not_le.mpr hlt), ite_eq_left rfl,
      one_mul, value_eq_fields hp (Nat.pos_of_ne_zero ha0) hlt, bias_cast]
  · rw [toRat?_of_gt hgt, ite_eq_right (show ¬a < 2 ^ p by omega),
      ite_eq_left (show 2 ^ p ≤ a from hgt.le), value_eq_fields hp (by omega) (by omega),
      bias_cast, ite_eq_right Nat.one_ne_zero, neg_one_mul]

/-! ## The rounding of a signed sum -/

/-- Aligning a significand to the smaller of two exponents keeps its value. -/
private theorem align (m e e' : ℕ) (c : ℤ) :
    ((m * 2 ^ (e - e') : ℕ) : ℚ) * 2 ^ (((min e e' : ℕ) : ℤ) - c) =
      (m : ℚ) * 2 ^ ((e : ℤ) - c) := by
  rcases le_total e e' with h | h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, Nat.mul_one, min_eq_left h]
  · have hexp : (e : ℤ) - c = ((e - e' : ℕ) : ℤ) + ((e' : ℤ) - c) := by omega
    rw [min_eq_right h, hexp, zpow_add₀ two_ne_zero, zpow_natCast]
    push_cast
    ring

/-- Two different sign bits have opposite sign factors. -/
private theorem signFactor_of_ne {s₁ s₂ : ℕ} (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1) (h : s₁ ≠ s₂) :
    signFactor s₂ = -signFactor s₁ := by
  unfold signFactor
  rcases (by omega : (s₁ = 0 ∧ s₂ = 1) ∨ (s₁ = 1 ∧ s₂ = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num

/--
`sumFields` returns the rounding of the exact sum of two nonzero dyadic numbers with a common
exponent bias, for every number of payload bits, every number of exponent bits and both signs.
-/
theorem sumFields_isRoundedTo {p es bK s₁ m₁ e₁ s₂ m₂ e₂ : ℕ} (hp : 0 < p) (h₁ : m₁ ≠ 0)
    (h₂ : m₂ ≠ 0) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1) :
    IsRoundedTo p es (dyadic es bK s₁ m₁ e₁ + dyadic es bK s₂ m₂ e₂)
      (sumFields p es bK s₁ m₁ e₁ s₂ m₂ e₂) := by
  have hA := align m₁ e₁ e₂ ((bK : ℤ) * 2 ^ es)
  have hB := align m₂ e₂ e₁ ((bK : ℤ) * 2 ^ es)
  rw [Nat.min_comm] at hB
  have hA0 : m₁ * 2 ^ (e₁ - e₂) ≠ 0 := Nat.mul_ne_zero h₁ (Nat.two_pow_pos _).ne'
  have hB0 : m₂ * 2 ^ (e₂ - e₁) ≠ 0 := Nat.mul_ne_zero h₂ (Nat.two_pow_pos _).ne'
  unfold sumFields
  kernel_notation
  have hsum : dyadic es bK s₁ m₁ e₁ + dyadic es bK s₂ m₂ e₂ =
      signFactor s₁ * (((m₁ * 2 ^ (e₁ - e₂) : ℕ) : ℚ) *
          2 ^ (((min e₁ e₂ : ℕ) : ℤ) - (bK : ℤ) * 2 ^ es)) +
        signFactor s₂ * (((m₂ * 2 ^ (e₂ - e₁) : ℕ) : ℚ) *
          2 ^ (((min e₁ e₂ : ℕ) : ℤ) - (bK : ℤ) * 2 ^ es)) := by
    unfold dyadic
    rw [hA, hB]
  rw [hsum]
  generalize m₁ * 2 ^ (e₁ - e₂) = A at hA0 ⊢
  generalize m₂ * 2 ^ (e₂ - e₁) = B at hB0 ⊢
  generalize min e₁ e₂ = E
  by_cases hs : s₁ = s₂
  · subst hs
    rw [ite_eq_left rfl]
    have h := withSign_encode_isRoundedTo (es := es) (bK := bK) (E := E) s₁ hp
      (show A + B ≠ 0 by omega)
    have hval : signFactor s₁ * ((A : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) +
        signFactor s₁ * ((B : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) =
        signFactor s₁ * (((A + B : ℕ) : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) := by
      push_cast
      ring
    rwa [hval]
  · rw [ite_eq_right hs, signFactor_of_ne hs₁ hs₂ hs]
    by_cases hle : B ≤ A
    · rw [ite_eq_left hle]
      by_cases heq : A = B
      · subst heq
        rw [ite_eq_left rfl]
        have hval : signFactor s₁ * ((A : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) +
            -signFactor s₁ * ((A : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) = 0 := by ring
        rw [hval]
        exact isRoundedTo_zero p es
      · rw [ite_eq_right heq]
        have h := withSign_encode_isRoundedTo (es := es) (bK := bK) (E := E) s₁ hp
          (show A - B ≠ 0 by omega)
        have hval : signFactor s₁ * ((A : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) +
            -signFactor s₁ * ((B : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) =
            signFactor s₁ * (((A - B : ℕ) : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) := by
          rw [Nat.cast_sub hle]
          ring
        rwa [hval]
    · rw [ite_eq_right hle]
      have h := withSign_encode_isRoundedTo (es := es) (bK := bK) (E := E) s₂ hp
        (show B - A ≠ 0 by omega)
      have hval : signFactor s₁ * ((A : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) +
          -signFactor s₁ * ((B : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) =
          signFactor s₂ * (((B - A : ℕ) : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) := by
        rw [signFactor_of_ne hs₁ hs₂ hs, Nat.cast_sub (Nat.le_of_not_le hle)]
        ring
      rwa [hval]

/-! ## Negation and the absolute value -/

/-- The negation of an encoding below the modulus: zero for zero, and the two's complement in
`p + 1` bits otherwise. -/
theorem neg_eq_ite {p a : ℕ} (ha : a < 2 ^ (p + 1)) :
    neg p a = if a = 0 then 0 else 2 ^ (p + 1) - a := by
  have := Nat.two_pow_pos (p + 1)
  unfold neg
  kernel_notation
  rw [Nat.and_two_pow_sub_one_eq_mod]
  split_ifs with h
  · subst h
    simp
  · exact Nat.mod_eq_of_lt (by omega)

/-- The negation of an encoding below the modulus is below the modulus. -/
theorem neg_lt {p a : ℕ} (ha : a < 2 ^ (p + 1)) : neg p a < 2 ^ (p + 1) := by
  have := Nat.two_pow_pos (p + 1)
  rw [neg_eq_ite ha]
  split_ifs <;> omega

/-- The negation of NaR is NaR. -/
theorem neg_nar (p : ℕ) : neg p (2 ^ p) = 2 ^ p := by
  have := Nat.two_pow_pos p
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  rw [neg_eq_ite (by omega), ite_eq_right (by omega)]
  omega

/-- Negation is exact: the negated encoding has the negated value, for every number of exponent
bits (Posit Standard (2022), §5.2). -/
theorem toRat?_neg {p es a : ℕ} {x : ℚ} (ha : a < 2 ^ (p + 1)) (h : toRat? p es a = some x) :
    toRat? p es (neg p a) = some (-x) := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hnar := ne_nar_of_toRat? h
  rw [neg_eq_ite ha]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at h
    simp only [Option.some.injEq] at h
    rw [ite_eq_left rfl, toRat?_zero, ← h, neg_zero]
  rw [ite_eq_right ha0]
  rcases Nat.lt_or_gt_of_ne hnar with hlt | hgt
  · rw [toRat?_of_lt ha0 hlt] at h
    simp only [Option.some.injEq] at h
    rw [toRat?_of_gt (by omega), ← h, show 2 ^ (p + 1) - (2 ^ (p + 1) - a) = a by omega]
  · rw [toRat?_of_gt hgt] at h
    simp only [Option.some.injEq] at h
    rw [toRat?_of_lt (by omega) (by omega), ← h, neg_neg]

/-- The absolute value of an encoding: itself below the sign bit, and its negation from the sign
bit on. -/
theorem abs_eq_ite (p a : ℕ) : KernelPath.abs p a = if 2 ^ p ≤ a then neg p a else a := by
  unfold KernelPath.abs nar
  kernel_notation

/-- The absolute value of NaR is NaR. -/
theorem abs_nar (p : ℕ) : KernelPath.abs p (2 ^ p) = 2 ^ p := by
  rw [abs_eq_ite, ite_eq_left le_rfl, neg_nar]

/-- The absolute value is exact: its encoding has the absolute value of the value, for every
number of exponent bits (Posit Standard (2022), §5.2). -/
theorem toRat?_abs {p es a : ℕ} {x : ℚ} (ha : a < 2 ^ (p + 1)) (h : toRat? p es a = some x) :
    toRat? p es (KernelPath.abs p a) = some |x| := by
  have hnar := ne_nar_of_toRat? h
  rw [abs_eq_ite]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at h
    simp only [Option.some.injEq] at h
    rw [ite_eq_right (by have := Nat.two_pow_pos p; omega), toRat?_zero, ← h, abs_zero]
  rcases Nat.lt_or_gt_of_ne hnar with hlt | hgt
  · rw [ite_eq_right (Nat.not_le.mpr hlt)]
    rw [toRat?_of_lt ha0 hlt] at h ⊢
    simp only [Option.some.injEq] at h
    rw [← h, abs_of_pos (value_pos p es a)]
  · rw [ite_eq_left hgt.le, toRat?_neg ha h]
    rw [toRat?_of_gt hgt] at h
    simp only [Option.some.injEq] at h
    rw [← h, abs_neg, abs_of_pos (value_pos _ _ _), neg_neg]

/-! ## Addition and subtraction -/

/-- NaR propagates through addition. -/
theorem add_nar {p a b : ℕ} (es : ℕ) (h : a = 2 ^ p ∨ b = 2 ^ p) : add p es a b = 2 ^ p := by
  unfold add nar
  kernel_notation
  rw [ite_eq_left (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h)]

/--
Posit Standard (2022), §5.4 and §4.1, for every number of exponent bits: `add` on two encodings
with values returns the rounding of the exact sum of the values, for all operands and signs.
-/
theorem add_isRoundedTo {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y) :
    IsRoundedTo p es (x + y) (add p es a b) := by
  have hna := ne_nar_of_toRat? hx
  have hnb := ne_nar_of_toRat? hy
  unfold add sumFinite nar
  kernel_notation
  rw [ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; tauto)]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at hx
    simp only [Option.some.injEq] at hx
    rw [ite_eq_left rfl, ← hx, zero_add]
    exact isRoundedTo_toRat? hp hb hy
  rw [ite_eq_right ha0]
  by_cases hb0 : b = 0
  · subst hb0
    rw [toRat?_zero] at hy
    simp only [Option.some.injEq] at hy
    rw [ite_eq_left rfl, ← hy, add_zero]
    exact isRoundedTo_toRat? hp ha hx
  rw [ite_eq_right hb0]
  rw [toRat?_eq_dyadic hp ha ha0 hna] at hx
  rw [toRat?_eq_dyadic hp hb hb0 hnb] at hy
  simp only [Option.some.injEq] at hx hy
  rw [← hx, ← hy]
  exact sumFields_isRoundedTo hp (significand_ne_zero _ _ _) (significand_ne_zero _ _ _)
    (div_two_pow_le_one ha) (div_two_pow_le_one hb)

/-- NaR propagates through subtraction. -/
theorem sub_nar {p a b : ℕ} (es : ℕ) (h : a = 2 ^ p ∨ b = 2 ^ p) : sub p es a b = 2 ^ p := by
  unfold sub nar
  kernel_notation
  rw [ite_eq_left (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h)]

/-- Flipping a sign bit negates a dyadic number. -/
private theorem dyadic_flip (es bK M E : ℕ) {s : ℕ} (hs : s ≤ 1) :
    dyadic es bK (1 - s) M E = -dyadic es bK s M E := by
  unfold dyadic signFactor
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> norm_num

/--
Posit Standard (2022), §5.4 and §4.1, for every number of exponent bits: `sub` on two encodings
with values returns the rounding of the exact difference of the values, for all operands and
signs.
-/
theorem sub_isRoundedTo {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y) :
    IsRoundedTo p es (x - y) (sub p es a b) := by
  have hna := ne_nar_of_toRat? hx
  have hnb := ne_nar_of_toRat? hy
  unfold sub sumFinite nar
  kernel_notation
  rw [ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; tauto)]
  by_cases hb0 : b = 0
  · subst hb0
    rw [toRat?_zero] at hy
    simp only [Option.some.injEq] at hy
    rw [ite_eq_left rfl, ← hy, sub_zero]
    exact isRoundedTo_toRat? hp ha hx
  rw [ite_eq_right hb0]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at hx
    simp only [Option.some.injEq] at hx
    rw [ite_eq_left rfl, ← hx, zero_sub]
    exact isRoundedTo_toRat? hp (neg_lt hb) (toRat?_neg hb hy)
  rw [ite_eq_right ha0]
  rw [toRat?_eq_dyadic hp ha ha0 hna] at hx
  rw [toRat?_eq_dyadic hp hb hb0 hnb] at hy
  simp only [Option.some.injEq] at hx hy
  rw [← hx, ← hy, sub_eq_add_neg, ← dyadic_flip es _ _ _ (div_two_pow_le_one hb)]
  exact sumFields_isRoundedTo hp (significand_ne_zero _ _ _) (significand_ne_zero _ _ _)
    (div_two_pow_le_one ha) (Nat.sub_le 1 _)

/-! ## Multiplication and the fused operation -/

/-- NaR propagates through multiplication. -/
theorem mul_nar {p a b : ℕ} (es : ℕ) (h : a = 2 ^ p ∨ b = 2 ^ p) : mul p es a b = 2 ^ p := by
  unfold mul nar
  kernel_notation
  rw [ite_eq_left (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h)]

/-- The exclusive or of two sign bits has the product of their sign factors. -/
theorem signFactor_xor {s₁ s₂ : ℕ} (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1) :
    signFactor (s₁ ^^^ s₂) = signFactor s₁ * signFactor s₂ := by
  unfold signFactor
  rcases (by omega : s₁ = 0 ∨ s₁ = 1) with rfl | rfl <;>
    rcases (by omega : s₂ = 0 ∨ s₂ = 1) with rfl | rfl <;> norm_num

/-- The exclusive or of two sign bits is a sign bit. -/
theorem xor_le_one {s₁ s₂ : ℕ} (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1) : s₁ ^^^ s₂ ≤ 1 := by
  rcases (by omega : s₁ = 0 ∨ s₁ = 1) with rfl | rfl <;>
    rcases (by omega : s₂ = 0 ∨ s₂ = 1) with rfl | rfl <;> decide

/-- The product of two dyadic numbers with the bias `bK` is the dyadic number of the product of
the significands at the sum of the exponents, with the bias `2 * bK`. -/
private theorem dyadic_mul (es bK : ℕ) {s₁ s₂ : ℕ} (M₁ E₁ M₂ E₂ : ℕ) (hs₁ : s₁ ≤ 1)
    (hs₂ : s₂ ≤ 1) :
    dyadic es bK s₁ M₁ E₁ * dyadic es bK s₂ M₂ E₂ =
      dyadic es (2 * bK) (s₁ ^^^ s₂) (M₁ * M₂) (E₁ + E₂) := by
  unfold dyadic
  rw [signFactor_xor hs₁ hs₂]
  have hexp : (((E₁ + E₂ : ℕ) : ℤ) - ((2 * bK : ℕ) : ℤ) * 2 ^ es) =
      ((E₁ : ℤ) - (bK : ℤ) * 2 ^ es) + ((E₂ : ℤ) - (bK : ℤ) * 2 ^ es) := by
    push_cast
    ring
  rw [hexp, zpow_add₀ two_ne_zero]
  push_cast
  ring

/--
Posit Standard (2022), §5.4 and §4.1, for every number of exponent bits: `mul` on two encodings
with values returns the rounding of the exact product of the values, for all operands and
signs.
-/
theorem mul_isRoundedTo {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y) :
    IsRoundedTo p es (x * y) (mul p es a b) := by
  have hna := ne_nar_of_toRat? hx
  have hnb := ne_nar_of_toRat? hy
  unfold mul nar
  kernel_notation
  rw [ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; tauto)]
  by_cases h0 : a = 0 ∨ b = 0
  · rw [ite_eq_left (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h0)]
    have hzero : x * y = 0 := by
      rcases h0 with rfl | rfl
      · rw [toRat?_zero] at hx
        simp only [Option.some.injEq] at hx
        rw [← hx, zero_mul]
      · rw [toRat?_zero] at hy
        simp only [Option.some.injEq] at hy
        rw [← hy, mul_zero]
    rw [hzero]
    exact isRoundedTo_zero p es
  rw [ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h0)]
  have ha0 : a ≠ 0 := fun h => h0 (Or.inl h)
  have hb0 : b ≠ 0 := fun h => h0 (Or.inr h)
  rw [toRat?_eq_dyadic hp ha ha0 hna] at hx
  rw [toRat?_eq_dyadic hp hb hb0 hnb] at hy
  simp only [Option.some.injEq] at hx hy
  rw [← hx, ← hy, dyadic_mul es _ _ _ _ _ (div_two_pow_le_one ha) (div_two_pow_le_one hb)]
  exact withSign_encode_isRoundedTo _ hp
    (Nat.mul_ne_zero (significand_ne_zero _ _ _) (significand_ne_zero _ _ _))

/-- NaR propagates through the fused multiply-add. -/
theorem fma_nar {p a b c : ℕ} (es : ℕ) (h : a = 2 ^ p ∨ b = 2 ^ p ∨ c = 2 ^ p) :
    fma p es a b c = 2 ^ p := by
  unfold fma nar
  kernel_notation
  rw [ite_eq_left (by
    rw [Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
    exact h)]

/-- Raising the exponent by the bias of the format doubles the regime bias of a dyadic number. -/
private theorem dyadic_add_bias (p es s M E : ℕ) :
    dyadic es (2 * regimeBias p) s M (E + bias p es) = dyadic es (regimeBias p) s M E := by
  unfold dyadic
  have hexp : (((E + bias p es : ℕ) : ℤ) - ((2 * regimeBias p : ℕ) : ℤ) * 2 ^ es) =
      (E : ℤ) - ((regimeBias p : ℕ) : ℤ) * 2 ^ es := by
    rw [Nat.cast_add, bias_cast]
    push_cast
    ring
  rw [hexp]

/--
The fused multiply-add for every number of exponent bits, a FloatLib extension rounded by the
rule of the Posit Standard (2022), §4.1: `fma` on three encodings with values returns the
rounding of the exact `x * y + z`, for all operands and signs.
-/
theorem fma_isRoundedTo {p es a b c : ℕ} {x y z : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hc : c < 2 ^ (p + 1)) (hx : toRat? p es a = some x)
    (hy : toRat? p es b = some y) (hz : toRat? p es c = some z) :
    IsRoundedTo p es (x * y + z) (fma p es a b c) := by
  have hna := ne_nar_of_toRat? hx
  have hnb := ne_nar_of_toRat? hy
  have hnc := ne_nar_of_toRat? hz
  have hmul := mul_isRoundedTo hp ha hb hx hy
  unfold fma nar
  kernel_notation
  rw [ite_eq_right (by
    rw [Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
    tauto)]
  by_cases h0 : a = 0 ∨ b = 0
  · rw [ite_eq_left (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h0)]
    have hzero : x * y = 0 := by
      rcases h0 with rfl | rfl
      · rw [toRat?_zero] at hx
        simp only [Option.some.injEq] at hx
        rw [← hx, zero_mul]
      · rw [toRat?_zero] at hy
        simp only [Option.some.injEq] at hy
        rw [← hy, mul_zero]
    rw [hzero, zero_add]
    exact isRoundedTo_toRat? hp hc hz
  rw [ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; exact h0)]
  by_cases hc0 : c = 0
  · subst hc0
    rw [toRat?_zero] at hz
    simp only [Option.some.injEq] at hz
    rw [ite_eq_left rfl, ← hz, add_zero]
    exact hmul
  rw [ite_eq_right hc0]
  have ha0 : a ≠ 0 := fun h => h0 (Or.inl h)
  have hb0 : b ≠ 0 := fun h => h0 (Or.inr h)
  rw [toRat?_eq_dyadic hp ha ha0 hna] at hx
  rw [toRat?_eq_dyadic hp hb hb0 hnb] at hy
  rw [toRat?_eq_dyadic hp hc hc0 hnc] at hz
  simp only [Option.some.injEq] at hx hy hz
  rw [← hx, ← hy, ← hz, dyadic_mul es _ _ _ _ _ (div_two_pow_le_one ha) (div_two_pow_le_one hb),
    ← dyadic_add_bias p es]
  exact sumFields_isRoundedTo hp
    (Nat.mul_ne_zero (significand_ne_zero _ _ _) (significand_ne_zero _ _ _))
    (significand_ne_zero _ _ _) (xor_le_one (div_two_pow_le_one ha) (div_two_pow_le_one hb))
    (div_two_pow_le_one hc)

/-! ## Change of format -/

/-- The conversion of NaR is NaR. -/
theorem cast_nar (p es q es' : ℕ) : KernelPath.cast p es q es' (2 ^ p) = 2 ^ q := by
  unfold KernelPath.cast nar
  kernel_notation
  rw [ite_eq_left trivial]

/--
The conversion between two formats, each with any number of payload bits and of exponent bits
(Posit Standard (2022), §6.1 for `es = 2`): `cast` on an encoding with a value returns the
rounding of that value in the destination, for every operand and sign.
-/
theorem cast_isRoundedTo {p es q es' a : ℕ} {x : ℚ} (hp : 0 < p) (hq : 0 < q)
    (ha : a < 2 ^ (p + 1)) (hx : toRat? p es a = some x) :
    IsRoundedTo q es' x (KernelPath.cast p es q es' a) := by
  have hna := ne_nar_of_toRat? hx
  unfold KernelPath.cast nar
  kernel_notation
  rw [ite_eq_right hna]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at hx
    simp only [Option.some.injEq] at hx
    rw [ite_eq_left rfl, ← hx]
    exact isRoundedTo_zero q es'
  rw [ite_eq_right ha0]
  rw [toRat?_eq_dyadic hp ha ha0 hna] at hx
  simp only [Option.some.injEq] at hx
  rw [← hx]
  have h := withSign_encode_isRoundedTo (es := es') (bK := bias p es / 2 ^ es' + 1)
    (M := significand es (magnitude p a) (tailLength p (magnitude p a)))
    (E := exponent p es (magnitude p a) (tailLength p (magnitude p a)) +
      (bias p es / 2 ^ es' + 1) * 2 ^ es' - bias p es) (a / 2 ^ p) hq
    (significand_ne_zero _ _ _)
  have : bias p es < (bias p es / 2 ^ es' + 1) * 2 ^ es' := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add (Nat.two_pow_pos es')
  have hexp : ((exponent p es (magnitude p a) (tailLength p (magnitude p a)) +
        (bias p es / 2 ^ es' + 1) * 2 ^ es' - bias p es : ℕ) : ℤ) -
      ((bias p es / 2 ^ es' + 1 : ℕ) : ℤ) * 2 ^ es' =
      (exponent p es (magnitude p a) (tailLength p (magnitude p a)) : ℤ) -
        ((regimeBias p : ℕ) : ℤ) * 2 ^ es := by
    have hcast : (((bias p es / 2 ^ es' + 1) * 2 ^ es' : ℕ) : ℤ) =
        ((bias p es / 2 ^ es' + 1 : ℕ) : ℤ) * 2 ^ es' := by
      push_cast
      ring
    rw [← hcast, ← bias_cast]
    omega
  rw [hexp] at h
  exact h

end FloatLib.Floats.Formats.Posit.General
