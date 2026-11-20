/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Spec
import Mathlib.Tactic.Linarith

/-!
# Posits with any number of exponent bits: order and neighbours

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. The comparisons and
the neighbours of `Posit.KernelPath.Core` work on the encodings alone. This module proves what
they mean on values, for every number `p ≥ 1` of payload bits and every number `es` of exponent
bits:

* `toRat?_lt_iff_signedKey`: the comparison key orders the encodings as their values.
* `lt_iff`, `le_iff`: `lt` and `le` on two encodings with values are the strict and the weak
  comparison of the values (Posit Standard (2022), §5.3). `lt_nar_left`, `lt_nar_right`,
  `le_nar_left`, `le_nar_right`: NaR is below every other encoding and equal to itself.
* `signedKey_next`, `signedKey_prior`, `lt_next`, `not_lt_and_lt_next`: `next` and `prior` are
  the successor and the predecessor in that order, so no encoding lies strictly between an
  encoding and its `next` (§5.2).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Numerics.Kernel FloatLib.Floats.Formats.Posit.KernelPath

/-- An encoding with a value is zero, positive or negative, with its value and its comparison
key in each case. -/
private theorem classify {p es a : ℕ} {x : ℚ} (ha : a < 2 ^ (p + 1))
    (hx : toRat? p es a = some x) :
    (a = 0 ∧ x = 0 ∧ signedKey p a = 2 ^ p) ∨
      (0 < a ∧ a < 2 ^ p ∧ x = value p es a ∧ signedKey p a = a + 2 ^ p) ∨
        (2 ^ p < a ∧ x = -value p es (2 ^ (p + 1) - a) ∧ signedKey p a = a - 2 ^ p) := by
  have hpos := Nat.two_pow_pos p
  have hnar := ne_nar_of_toRat? hx
  rw [signedKey_eq ha]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at hx
    simp only [Option.some.injEq] at hx
    exact Or.inl ⟨rfl, hx.symm, by rw [ite_eq_left hpos, Nat.zero_add]⟩
  rcases Nat.lt_or_gt_of_ne hnar with hlt | hgt
  · rw [toRat?_of_lt ha0 hlt] at hx
    simp only [Option.some.injEq] at hx
    exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero ha0, hlt, hx.symm, by rw [ite_eq_left hlt]⟩)
  · rw [toRat?_of_gt hgt] at hx
    simp only [Option.some.injEq] at hx
    exact Or.inr (Or.inr ⟨hgt, hx.symm, by rw [ite_eq_right (Nat.not_lt.mpr hgt.le)]⟩)

/-- The comparison key orders the encodings with a value as their values, for every number of
exponent bits. -/
theorem toRat?_lt_iff_signedKey {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y) :
    x < y ↔ signedKey p a < signedKey p b := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have := Nat.two_pow_pos p
  rcases classify ha hx with ⟨rfl, rfl, hka⟩ | ⟨ha0, halt, rfl, hka⟩ | ⟨hagt, rfl, hka⟩ <;>
    rcases classify hb hy with ⟨rfl, rfl, hkb⟩ | ⟨hb0, hblt, rfl, hkb⟩ | ⟨hbgt, rfl, hkb⟩
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · rw [hka, hkb]
    exact iff_of_true (value_pos p es b) (by omega)
  · rw [hka, hkb]
    exact iff_of_false (not_lt.mpr (neg_nonpos.mpr (value_pos _ _ _).le)) (by omega)
  · rw [hka, hkb]
    exact iff_of_false (not_lt.mpr (value_pos p es a).le) (by omega)
  · rw [hka, hkb, value_lt_value_iff hp ha0 halt hb0 hblt]
    omega
  · rw [hka, hkb]
    exact iff_of_false
      (not_lt.mpr ((neg_nonpos.mpr (value_pos _ _ _).le).trans (value_pos p es a).le)) (by omega)
  · rw [hka, hkb]
    exact iff_of_true (neg_lt_zero.mpr (value_pos _ _ _)) (by omega)
  · rw [hka, hkb]
    exact iff_of_true ((neg_lt_zero.mpr (value_pos _ _ _)).trans (value_pos p es b)) (by omega)
  · rw [hka, hkb, neg_lt_neg_iff,
      value_lt_value_iff hp (by omega) (by omega) (by omega) (by omega)]
    omega

/-- The comparison key of NaR is zero, the least key. -/
theorem signedKey_nar (p : ℕ) : signedKey p (2 ^ p) = 0 := by
  have := Nat.two_pow_pos p
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  rw [signedKey_eq (by omega), ite_eq_right (lt_irrefl _), Nat.sub_self]

/-- The comparison key of every encoding other than NaR is positive. -/
theorem signedKey_pos {p a : ℕ} (ha : a < 2 ^ (p + 1)) (hnar : a ≠ 2 ^ p) :
    0 < signedKey p a := by
  have := Nat.two_pow_pos p
  rw [signedKey_eq ha]
  split_ifs <;> omega

/-- `lt` compares the comparison keys strictly. -/
theorem lt_eq_decide (p a b : ℕ) : lt p a b = decide (signedKey p a < signedKey p b) := by
  unfold lt
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]
  exact Nat.succ_le_iff

/-- `le` compares the comparison keys. -/
theorem le_eq_decide (p a b : ℕ) : le p a b = decide (signedKey p a ≤ signedKey p b) := by
  unfold le
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_eq]

/-- Posit Standard (2022), §5.3, for every number of exponent bits: `lt` on two encodings with
values is the strict comparison of the values. -/
theorem lt_iff {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y) :
    lt p a b = true ↔ x < y := by
  rw [lt_eq_decide, decide_eq_true_eq, toRat?_lt_iff_signedKey hp ha hb hx hy]

/-- Posit Standard (2022), §5.3, for every number of exponent bits: `le` on two encodings with
values is the comparison of the values. -/
theorem le_iff {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y) :
    le p a b = true ↔ x ≤ y := by
  rw [le_eq_decide, decide_eq_true_eq, ← not_lt, ← not_lt,
    toRat?_lt_iff_signedKey hp hb ha hy hx]

/-- NaR is below every other encoding. -/
theorem lt_nar_left {p b : ℕ} (hb : b < 2 ^ (p + 1)) (hnar : b ≠ 2 ^ p) :
    lt p (2 ^ p) b = true := by
  rw [lt_eq_decide, decide_eq_true_eq, signedKey_nar]
  exact signedKey_pos hb hnar

/-- No encoding is below NaR. -/
theorem lt_nar_right (p a : ℕ) : lt p a (2 ^ p) = false := by
  rw [lt_eq_decide, signedKey_nar]
  exact decide_eq_false (Nat.not_lt_zero _)

/-- NaR is at most every encoding, itself included. -/
theorem le_nar_left (p b : ℕ) : le p (2 ^ p) b = true := by
  rw [le_eq_decide, decide_eq_true_eq, signedKey_nar]
  exact Nat.zero_le _

/-- An encoding other than NaR is not at most NaR. -/
theorem le_nar_right {p a : ℕ} (ha : a < 2 ^ (p + 1)) (hnar : a ≠ 2 ^ p) :
    le p a (2 ^ p) = false := by
  rw [le_eq_decide, signedKey_nar]
  exact decide_eq_false (Nat.not_le.mpr (signedKey_pos ha hnar))

/-! ## Neighbours -/

/-- `next` is an encoding below the modulus. -/
theorem next_lt (p a : ℕ) : next p a < 2 ^ (p + 1) := by
  unfold next
  kernel_notation
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- `prior` is an encoding below the modulus. -/
theorem prior_lt (p a : ℕ) : prior p a < 2 ^ (p + 1) := by
  unfold prior
  kernel_notation
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- `next` adds one to the comparison key: it is the successor in the order of the encodings,
for every encoding but the greatest. -/
theorem signedKey_next {p a : ℕ} (ha : a < 2 ^ (p + 1)) (h : signedKey p a + 1 < 2 ^ (p + 1)) :
    signedKey p (next p a) = signedKey p a + 1 := by
  have := Nat.two_pow_pos p
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hn := next_lt p a
  have hna : next p a = if a + 1 = 2 ^ (p + 1) then 0 else a + 1 := by
    unfold next
    kernel_notation
    split_ifs with h1
    · rw [h1, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [signedKey_eq ha] at h ⊢
  rw [signedKey_eq hn, hna]
  split_ifs at h ⊢ <;> omega

/-- `prior` subtracts one from the comparison key: it is the predecessor in the order of the
encodings, for every encoding but NaR. -/
theorem signedKey_prior {p a : ℕ} (ha : a < 2 ^ (p + 1)) (h : 0 < signedKey p a) :
    signedKey p (prior p a) = signedKey p a - 1 := by
  have := Nat.two_pow_pos p
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hn := prior_lt p a
  have hna : prior p a = if a = 0 then 2 ^ (p + 1) - 1 else a - 1 := by
    unfold prior
    kernel_notation
    split_ifs with h1
    · rw [h1, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    · rw [show a + 2 ^ (p + 1) - 1 = a - 1 + 2 ^ (p + 1) by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  rw [signedKey_eq ha] at h ⊢
  rw [signedKey_eq hn, hna]
  split_ifs at h ⊢ <;> omega

/-- An encoding is below its `next`, for every encoding but the greatest (Posit Standard (2022),
§5.2). -/
theorem lt_next {p a : ℕ} (ha : a < 2 ^ (p + 1)) (h : signedKey p a + 1 < 2 ^ (p + 1)) :
    lt p a (next p a) = true := by
  rw [lt_eq_decide, decide_eq_true_eq, signedKey_next ha h]
  exact Nat.lt_succ_self _

/-- No encoding lies strictly between an encoding and its `next`. -/
theorem not_lt_and_lt_next {p a : ℕ} (ha : a < 2 ^ (p + 1))
    (h : signedKey p a + 1 < 2 ^ (p + 1)) (c : ℕ) :
    ¬(lt p a c = true ∧ lt p c (next p a) = true) := by
  rw [lt_eq_decide, lt_eq_decide, decide_eq_true_eq, decide_eq_true_eq, signedKey_next ha h]
  omega

end FloatLib.Floats.Formats.Posit.General
