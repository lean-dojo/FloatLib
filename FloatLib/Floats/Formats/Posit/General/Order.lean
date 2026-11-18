/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.KernelPath.Core
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Field.Power
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Posits with any number of exponent bits: values and positions

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2` exponent bits. This
module has the two coordinate maps of a tapered format with `es` exponent bits and their order,
with no reference to a width or to an encoding.

A positive value is given by its regime `k : ℤ` and its tail `a : ℚ`, `0 ≤ a < 2 ^ es`: the
exponent field plus the fraction.

* `taper a = 2 ^ ⌊a⌋ * (1 + fract a)` is the value of a tail: the piecewise linear interpolation
  of `2 ^ a` between the integers. `taper_strictMono`: it is strictly increasing.
* `val es k a = 2 ^ (k * 2 ^ es) * taper a` is the value with regime `k` and tail `a`
  (Posit Standard (2022), §3.2.2 with `2 ^ es` in place of `4`).
* `pos p es k a` is the position of that value on the scale of the codes with `p` payload bits:
  the number whose binary expansion is the regime run, its terminator, the exponent field and
  the fraction, with the binary point after `p` bits. A value that a code represents has that
  code as its position (`General.pos_code`), and a value between two codes has a position between
  them.
* `val_lt_val`, `pos_lt_pos`: both maps are strictly increasing in the lexicographic order of
  `(k, a)`, so `pos_lt_pos_iff` and `pos_eq_pos_iff`: positions are ordered exactly as values,
  for every `es` and every width.
* `pos_succ`: one more payload bit doubles every position.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

/-- The value of a tail: `2 ^ ⌊a⌋ * (1 + fract a)`, the exponent field `⌊a⌋` and the fraction
`fract a`. -/
def taper (a : ℚ) : ℚ := 2 ^ ⌊a⌋ * (1 + Int.fract a)

/-- The value of a tail is positive. -/
theorem taper_pos (a : ℚ) : 0 < taper a :=
  mul_pos (zpow_pos two_pos _)
    (add_pos_of_pos_of_nonneg zero_lt_one (Int.fract_nonneg a))

/-- A tail at or above an integer has a value at or above that power of two. -/
theorem zpow_le_taper {n : ℤ} {a : ℚ} (h : (n : ℚ) ≤ a) : (2 : ℚ) ^ n ≤ taper a := by
  have hn : n ≤ ⌊a⌋ := Int.le_floor.mpr h
  have h1 : (2 : ℚ) ^ n ≤ 2 ^ ⌊a⌋ := zpow_le_zpow_right₀ one_le_two hn
  exact h1.trans (le_mul_of_one_le_right (zpow_pos two_pos _).le
    (le_add_of_nonneg_right (Int.fract_nonneg a)))

/-- A tail below an integer has a value below that power of two. -/
theorem taper_lt_zpow {n : ℤ} {a : ℚ} (h : a < (n : ℚ)) : taper a < 2 ^ n := by
  have hn : ⌊a⌋ + 1 ≤ n := Int.floor_lt.mpr h
  have h2 : (0 : ℚ) < 2 ^ ⌊a⌋ := zpow_pos two_pos _
  calc taper a < 2 ^ ⌊a⌋ * 2 :=
        mul_lt_mul_of_pos_left
          (by simpa only [one_add_one_eq_two] using add_lt_add_right (Int.fract_lt_one a) 1) h2
    _ = 2 ^ (⌊a⌋ + 1) := by rw [zpow_add₀ two_ne_zero, zpow_one]
    _ ≤ 2 ^ n := zpow_le_zpow_right₀ one_le_two hn

/-- The value of a tail is strictly increasing. -/
theorem taper_strictMono : StrictMono taper := by
  intro a b hab
  rcases (Int.floor_mono hab.le).lt_or_eq with hlt | heq
  · calc taper a < 2 ^ (⌊a⌋ + 1) :=
          taper_lt_zpow (by push_cast; exact Int.lt_floor_add_one a)
      _ ≤ 2 ^ ⌊b⌋ := zpow_le_zpow_right₀ one_le_two hlt
      _ ≤ taper b := zpow_le_taper (Int.floor_le b)
  · have ha := Int.self_sub_floor a
    have hb := Int.self_sub_floor b
    have hfract : Int.fract a < Int.fract b := by
      rw [← ha, ← hb, heq]
      exact sub_lt_sub_right hab _
    unfold taper
    rw [heq]
    exact mul_lt_mul_of_pos_left (add_lt_add_right hfract 1) (zpow_pos two_pos _)

/-- The value with regime `k` and tail `a` in a format with `es` exponent bits. -/
def val (es : ℕ) (k : ℤ) (a : ℚ) : ℚ := 2 ^ (k * 2 ^ es) * taper a

/-- Every value is positive. -/
theorem val_pos (es : ℕ) (k : ℤ) (a : ℚ) : 0 < val es k a :=
  mul_pos (zpow_pos two_pos _) (taper_pos a)

/-- Values are strictly increasing in the lexicographic order of the regime and the tail. -/
theorem val_lt_val {es : ℕ} {k k' : ℤ} {a a' : ℚ} (ha : a < 2 ^ es) (ha' : 0 ≤ a')
    (h : k < k' ∨ k = k' ∧ a < a') : val es k a < val es k' a' := by
  rcases h with hk | ⟨rfl, haa⟩
  · have h1 : taper a < 2 ^ ((2 : ℤ) ^ es) := taper_lt_zpow (by push_cast; exact ha)
    have h2 : (1 : ℚ) ≤ taper a' := by
      have := zpow_le_taper (n := 0) (a := a') (by simpa using ha')
      simpa using this
    have h3 : (0 : ℚ) < 2 ^ (k * 2 ^ es) := zpow_pos two_pos _
    have h4 : (0 : ℚ) < 2 ^ (k' * 2 ^ es) := zpow_pos two_pos _
    have hexp : k * 2 ^ es + 2 ^ es ≤ k' * 2 ^ es := by
      simpa only [add_mul, one_mul] using
        mul_le_mul_of_nonneg_right (show k + 1 ≤ k' by omega)
          (pow_pos (show (0 : ℤ) < 2 by decide) es).le
    calc val es k a < 2 ^ (k * 2 ^ es) * 2 ^ ((2 : ℤ) ^ es) := mul_lt_mul_of_pos_left h1 h3
      _ = 2 ^ (k * 2 ^ es + 2 ^ es) := (zpow_add₀ two_ne_zero _ _).symm
      _ ≤ 2 ^ (k' * 2 ^ es) := zpow_le_zpow_right₀ one_le_two hexp
      _ ≤ val es k' a' := le_mul_of_one_le_right h4.le h2
  · exact mul_lt_mul_of_pos_left (taper_strictMono haa) (zpow_pos two_pos _)

/--
The position of the value with regime `k` and tail `a` on the scale of the codes with `p` payload
bits. A negative regime `k` is a run of `-k` zeros and a one: the position is
`2 ^ (p + k - 1) * (1 + a / 2 ^ es)`. A regime `k ≥ 0` is a run of `k + 1` ones and a zero: the
position is `2 ^ p - 2 ^ (p - 1 - k) * (1 - a / 2 ^ (es + 1))`.
-/
def pos (p es : ℕ) (k : ℤ) (a : ℚ) : ℚ :=
  if k < 0 then 2 ^ ((p : ℤ) + k - 1) * (1 + a / 2 ^ es)
  else 2 ^ (p : ℤ) - 2 ^ ((p : ℤ) - 1 - k) * (1 - a / 2 ^ (es + 1))

/-- One more payload bit doubles every position. -/
theorem pos_succ (p es : ℕ) (k : ℤ) (a : ℚ) : pos (p + 1) es k a = 2 * pos p es k a := by
  unfold pos
  have e1 : ((p + 1 : ℕ) : ℤ) + k - 1 = ((p : ℤ) + k - 1) + 1 := by push_cast; ring
  have e2 : ((p + 1 : ℕ) : ℤ) = (p : ℤ) + 1 := by push_cast; ring
  have e3 : ((p + 1 : ℕ) : ℤ) - 1 - k = ((p : ℤ) - 1 - k) + 1 := by push_cast; ring
  split_ifs
  · rw [e1, zpow_add₀ two_ne_zero, zpow_one]
    ring
  · rw [e3, e2, zpow_add₀ two_ne_zero, zpow_add₀ two_ne_zero, zpow_one]
    ring

/-- Positions are strictly increasing in the lexicographic order of the regime and the tail. -/
theorem pos_lt_pos {p es : ℕ} {k k' : ℤ} {a a' : ℚ} (ha : a < 2 ^ es)
    (ha'0 : 0 ≤ a') (h : k < k' ∨ k = k' ∧ a < a') :
    pos p es k a < pos p es k' a' := by
  have hes : (0 : ℚ) < 2 ^ es := by positivity
  have hu1 : a / 2 ^ es < 1 := (div_lt_one hes).mpr ha
  have hu0' : 0 ≤ a' / 2 ^ es := div_nonneg ha'0 hes.le
  have hhalf : ∀ b : ℚ, b / 2 ^ (es + 1) = b / 2 ^ es / 2 := fun b => by
    rw [pow_succ, div_mul_eq_div_div]
  unfold pos
  rw [hhalf a, hhalf a']
  by_cases hk : k < 0
  · by_cases hk' : k' < 0
    · rw [ite_eq_left hk, ite_eq_left hk']
      rcases h with hlt | ⟨rfl, haa⟩
      · have h3 : (0 : ℚ) < 2 ^ ((p : ℤ) + k - 1) := zpow_pos two_pos _
        have h4 : (0 : ℚ) < 2 ^ ((p : ℤ) + k' - 1) := zpow_pos two_pos _
        have hle : (2 : ℚ) ^ ((p : ℤ) + k - 1 + 1) ≤ 2 ^ ((p : ℤ) + k' - 1) :=
          zpow_le_zpow_right₀ one_le_two (by omega)
        rw [zpow_add₀ two_ne_zero, zpow_one] at hle
        nlinarith
      · have h3 : (0 : ℚ) < 2 ^ ((p : ℤ) + k - 1) := zpow_pos two_pos _
        have hdiv : a / 2 ^ es < a' / 2 ^ es := div_lt_div_of_pos_right haa hes
        nlinarith
    · rw [ite_eq_left hk, ite_eq_right hk']
      have h3 : (0 : ℚ) < 2 ^ ((p : ℤ) + k - 1) := zpow_pos two_pos _
      have h4 : (0 : ℚ) < 2 ^ ((p : ℤ) - 1 - k') := zpow_pos two_pos _
      have hle : (2 : ℚ) ^ ((p : ℤ) + k - 1 + 1) ≤ 2 ^ ((p : ℤ) - 1) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      rw [zpow_add₀ two_ne_zero, zpow_one] at hle
      have hle' : (2 : ℚ) ^ ((p : ℤ) - 1 - k') ≤ 2 ^ ((p : ℤ) - 1) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      have hp : (2 : ℚ) ^ (p : ℤ) = 2 ^ ((p : ℤ) - 1) * 2 := by
        rw [← zpow_add_one₀ two_ne_zero]
        congr 1
        ring
      nlinarith
  · have hk' : ¬ k' < 0 := by
      rcases h with hlt | ⟨rfl, _⟩
      · omega
      · exact hk
    rw [ite_eq_right hk, ite_eq_right hk']
    rcases h with hlt | ⟨rfl, haa⟩
    · have h4 : (0 : ℚ) < 2 ^ ((p : ℤ) - 1 - k') := zpow_pos two_pos _
      have hle : (2 : ℚ) ^ ((p : ℤ) - 1 - k' + 1) ≤ 2 ^ ((p : ℤ) - 1 - k) :=
        zpow_le_zpow_right₀ one_le_two (by omega)
      rw [zpow_add₀ two_ne_zero, zpow_one] at hle
      nlinarith
    · have h3 : (0 : ℚ) < 2 ^ ((p : ℤ) - 1 - k) := zpow_pos two_pos _
      have hdiv : a / 2 ^ es < a' / 2 ^ es := div_lt_div_of_pos_right haa hes
      nlinarith

/-- Two pairs of a regime and a tail are equal, or one is before the other. -/
theorem lex_trichotomy (k k' : ℤ) (a a' : ℚ) :
    (k < k' ∨ k = k' ∧ a < a') ∨ (k = k' ∧ a = a') ∨ (k' < k ∨ k' = k ∧ a' < a) := by
  rcases lt_trichotomy k k' with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases lt_trichotomy a a' with h' | h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inl ⟨h, h'⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨h.symm, h'⟩))
  · exact Or.inr (Or.inr (Or.inl h))

/-- Positions are ordered as values are: for tails in `[0, 2 ^ es)`, one position is below
another exactly when its value is. -/
theorem pos_lt_pos_iff {p es : ℕ} {k k' : ℤ} {a a' : ℚ} (ha0 : 0 ≤ a) (ha : a < 2 ^ es)
    (ha'0 : 0 ≤ a') (ha' : a' < 2 ^ es) :
    pos p es k a < pos p es k' a' ↔ val es k a < val es k' a' := by
  rcases lex_trichotomy k k' a a' with h | ⟨rfl, rfl⟩ | h
  · exact iff_of_true (pos_lt_pos ha ha'0 h) (val_lt_val ha ha'0 h)
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)
  · exact iff_of_false (not_lt.mpr (pos_lt_pos ha' ha0 h).le)
      (not_lt.mpr (val_lt_val ha' ha0 h).le)

/-- Two values with tails in `[0, 2 ^ es)` have the same position exactly when they are equal. -/
theorem pos_eq_pos_iff {p es : ℕ} {k k' : ℤ} {a a' : ℚ} (ha0 : 0 ≤ a) (ha : a < 2 ^ es)
    (ha'0 : 0 ≤ a') (ha' : a' < 2 ^ es) :
    pos p es k a = pos p es k' a' ↔ val es k a = val es k' a' := by
  rcases lex_trichotomy k k' a a' with h | ⟨rfl, rfl⟩ | h
  · exact iff_of_false (pos_lt_pos ha ha'0 h).ne (val_lt_val ha ha'0 h).ne
  · exact iff_of_true rfl rfl
  · exact iff_of_false (pos_lt_pos ha' ha0 h).ne' (val_lt_val ha' ha0 h).ne'

end FloatLib.Floats.Formats.Posit.General
