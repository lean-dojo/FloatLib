/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Arithmetic
public import FloatLib.Numerics.ShiftRightJam.Proof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Posits with any number of exponent bits: quotients and ratios

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. A quotient is not a
dyadic number, so `KernelPath.quotient` rounds a truncated quotient of at least `p + 1` bits
with the remainder recorded in its low bit (`KernelPath.jam`). This module proves that this is
the rounding of the exact quotient, for every number `p ≥ 1` of payload bits and every number
`es` of exponent bits:

* `value_succ_even`: the values of the format with one more payload bit that lie in the binade
  of `2 ^ t` are even multiples of `2 ^ (t - p)`. So no rounding boundary falls strictly between
  two neighbours of a number with `p + 1` significant bits.
* `SameSide p es x x'`: `x` and `x'` compare alike with every such value, and then the rounding
  rule gives them the same code (`IsRounded.of_sameSide`).
* `sameSide_jam`: a number `(q + θ) * 2 ^ e` with `2 ^ p ≤ q` and `0 < θ < 1` is on the same
  side of every boundary as `(q ||| 1) * 2 ^ e`.
* `quotient_isRounded`: `quotient` returns the rounding of the exact quotient of two natural
  numbers at the given exponent.
* `div_isRoundedTo`, `div_nar`: `div` returns the rounding of the exact quotient of the values,
  and NaR for a NaR operand or a zero divisor (Posit Standard (2022), §5.4 and §4.1 with
  `2 ^ es` in place of `4`).
* `ofRatio_isRoundedTo`: `ofRatio` returns the rounding of `± num / den`, which is how a literal
  is rounded. With it every rational has a rounding (`exists_isRoundedTo`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Numerics.Kernel FloatLib.Floats.Formats.Posit.KernelPath

/-! ## The values of one binade -/

/-- A positive number lies in one binade. -/
private theorem binade_unique {v : ℚ} {a b : ℤ} (ha : (2 : ℚ) ^ a ≤ v) (ha' : v < 2 ^ (a + 1))
    (hb : (2 : ℚ) ^ b ≤ v) (hb' : v < 2 ^ (b + 1)) : a = b := by
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp (lt_of_le_of_lt ha hb')
  have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp (lt_of_le_of_lt hb ha')
  omega

/--
The values of the format with `p + 1` payload bits in the binade of `2 ^ t` are even multiples
of `2 ^ (t - p)`: a code of that format has at most `p - 1` fraction bits.
-/
theorem value_succ_even {p es n : ℕ} {t : ℤ} (hp : 0 < p) (hn0 : 0 < n) (hn : n < 2 ^ (p + 1))
    (hlo : (2 : ℚ) ^ t ≤ value (p + 1) es n) (hhi : value (p + 1) es n < 2 ^ (t + 1)) :
    ∃ k : ℕ, value (p + 1) es n = ((2 * k : ℕ) : ℚ) * 2 ^ (t - (p : ℤ)) := by
  have : tailLength (p + 1) n ≤ p := by
    rcases code_cases (Nat.succ_pos p) hn0 hn with h | h
    · exact h.2.2.1
    · exact h.2.1
  have hv := value_eq_fields (es := es) (Nat.succ_pos p) hn0 hn
  rw [significand_eq] at hv
  generalize hfb : tailLength (p + 1) n - 1 - es = fb at hv
  generalize ((exponent (p + 1) es n (tailLength (p + 1) n) : ℕ) : ℤ) -
    ((bias (p + 1) es : ℕ) : ℤ) = X at hv
  have : fb ≤ p - 1 := by omega
  have := Nat.mod_lt n (Nat.two_pow_pos fb)
  have hsig1 : ((2 : ℚ) ^ fb) ≤ ((2 ^ fb + n % 2 ^ fb : ℕ) : ℚ) := by
    exact_mod_cast Nat.le_add_right (2 ^ fb) (n % 2 ^ fb)
  have hsig2 : ((2 ^ fb + n % 2 ^ fb : ℕ) : ℚ) < (2 : ℚ) ^ (fb + 1) := by
    have : 2 ^ fb + n % 2 ^ fb < 2 ^ (fb + 1) := by
      rw [pow_succ]
      omega
    exact_mod_cast this
  have hXpos : (0 : ℚ) < 2 ^ X := zpow_pos two_pos X
  have hbin1 : (2 : ℚ) ^ ((fb : ℤ) + X) ≤ value (p + 1) es n := by
    rw [hv, zpow_add₀ two_ne_zero, zpow_natCast]
    exact mul_le_mul_of_nonneg_right hsig1 hXpos.le
  have hbin2 : value (p + 1) es n < (2 : ℚ) ^ ((fb : ℤ) + X + 1) := by
    rw [hv, show (fb : ℤ) + X + 1 = ((fb + 1 : ℕ) : ℤ) + X by push_cast; ring,
      zpow_add₀ two_ne_zero, zpow_natCast]
    exact mul_lt_mul_of_pos_right hsig2 hXpos
  have : t = (fb : ℤ) + X := binade_unique hlo hhi hbin1 hbin2
  refine ⟨(2 ^ fb + n % 2 ^ fb) * 2 ^ (p - 1 - fb), ?_⟩
  have hkey : (2 : ℚ) ^ X = 2 ^ (p - 1 - fb) * 2 * 2 ^ (t - (p : ℤ)) := by
    rw [← zpow_natCast (2 : ℚ) (p - 1 - fb), ← zpow_add_one₀ two_ne_zero,
      ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  rw [hv, hkey]
  push_cast
  ring

/-! ## Two numbers on one side of every boundary -/

/-- `x` and `x'` compare alike with the value of every code of the format with one more payload
bit: both below it, both equal to it, or both above it. -/
def SameSide (p es : ℕ) (x x' : ℚ) : Prop :=
  ∀ n, 0 < n → n < 2 ^ (p + 1) →
    (x < value (p + 1) es n ↔ x' < value (p + 1) es n) ∧
      (x = value (p + 1) es n ↔ x' = value (p + 1) es n)

/-- Being on the same side of every boundary is symmetric. -/
theorem SameSide.symm {p es : ℕ} {x x' : ℚ} (h : SameSide p es x x') : SameSide p es x' x :=
  fun n hn0 hn => ⟨(h n hn0 hn).1.symm, (h n hn0 hn).2.symm⟩

/-- Two numbers on the same side of every boundary are at most the same values. -/
theorem SameSide.le_iff {p es : ℕ} {x x' : ℚ} (h : SameSide p es x x') {n : ℕ} (hn0 : 0 < n)
    (hn : n < 2 ^ (p + 1)) : x ≤ value (p + 1) es n ↔ x' ≤ value (p + 1) es n := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, (h n hn0 hn).1, (h n hn0 hn).2]

/-- Two numbers on the same side of every boundary have the same rounding. -/
theorem IsRounded.of_sameSide {p es : ℕ} {x x' : ℚ} {c : ℕ} (hp : 0 < p)
    (hs : SameSide p es x x') (h : IsRounded p es x c) : IsRounded p es x' c := by
  have : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hmin : value p es 1 = value (p + 1) es 2 :=
    (value_succ (es := es) hp Nat.one_pos (by omega)).symm
  have hmax : value p es (2 ^ p - 1) = value (p + 1) es (2 * (2 ^ p - 1)) :=
    (value_succ (es := es) hp (by omega) (by omega)).symm
  have := h.pos
  have := h.lt
  refine ⟨h.pos, h.lt, fun hlo => h.low ?_, fun hhi => h.high ?_, fun hlo hhi => ?_⟩
  · rw [hmin] at hlo ⊢
    exact (hs.le_iff (by omega) (by omega)).mpr hlo
  · rw [hmax] at hhi ⊢
    exact not_lt.mp (mt (hs _ (by omega) (by omega)).1.mp (not_lt.mpr hhi))
  · have hlo' : value p es 1 < x := by
      rw [hmin] at hlo ⊢
      exact not_le.mp (mt (hs.le_iff (by omega) (by omega)).mp (not_le.mpr hlo))
    have hhi' : x < value p es (2 ^ p - 1) := by
      rw [hmax] at hhi ⊢
      exact (hs _ (by omega) (by omega)).1.mpr hhi
    obtain ⟨h1, h2, h3⟩ := h.between hlo' hhi'
    refine ⟨?_, (hs.le_iff (by omega) (by omega)).mp h2, fun hx => h3 ?_⟩
    · exact not_lt.mp (mt (hs _ (by omega) (by omega)).1.mpr (not_lt.mpr h1))
    · rcases hx with hx | hx
      · exact Or.inl ((hs _ (by omega) (by omega)).2.mpr hx)
      · exact Or.inr ((hs _ (by omega) (by omega)).2.mpr hx)

/--
A number with a nonzero part below its unit is on the same side of every rounding boundary as
its truncation with the low bit set: `(q + θ) * 2 ^ e` and `(q ||| 1) * 2 ^ e`, for
`2 ^ p ≤ q` and `0 < θ < 1`. This is what recording a remainder in the low bit relies on.
-/
theorem sameSide_jam {p es q : ℕ} (hp : 0 < p) (hq : 2 ^ p ≤ q) {θ : ℚ} (hθ0 : 0 < θ)
    (hθ1 : θ < 1) (e : ℤ) :
    SameSide p es (((q : ℚ) + θ) * 2 ^ e) (((q ||| 1 : ℕ) : ℚ) * 2 ^ e) := by
  intro n hn0 hn
  have hu : (0 : ℚ) < 2 ^ e := zpow_pos two_pos e
  have hq0 : q ≠ 0 := by
    have := Nat.two_pow_pos p
    omega
  have hL1 : 2 ^ q.log2 ≤ q := Nat.log2_self_le hq0
  have hL2 : q < 2 ^ (q.log2 + 1) := Nat.lt_log2_self
  have hLp : p ≤ q.log2 :=
    Nat.lt_succ_iff.mp ((Nat.pow_lt_pow_iff_right (by decide)).mp (lt_of_le_of_lt hq hL2))
  generalize q.log2 = L at hL1 hL2 hLp
  have hJ := FloatLib.Numerics.or_one_eq q
  generalize q ||| 1 = J at hJ
  have : J % 2 = 1 := by
    rw [hJ]
    split_ifs <;> omega
  have hJle : q ≤ J := by
    rw [hJ]
    split_ifs <;> omega
  have : J ≤ q + 1 := by
    rw [hJ]
    split_ifs <;> omega
  have hmul : ∀ a b : ℚ, a * 2 ^ e < b * 2 ^ e ↔ a < b := fun a b =>
    ⟨fun h => lt_of_mul_lt_mul_right h hu.le, fun h => mul_lt_mul_of_pos_right h hu⟩
  have hmuleq : ∀ a b : ℚ, a * 2 ^ e = b * 2 ^ e ↔ a = b := fun a b =>
    ⟨fun h => mul_right_cancel₀ hu.ne' h, fun h => by rw [h]⟩
  have hLq : ((2 : ℚ) ^ L) ≤ (q : ℚ) := by exact_mod_cast hL1
  have : (q : ℚ) + 1 ≤ 2 ^ (L + 1) := by exact_mod_cast hL2
  have heven : ∀ t : ℤ, (2 : ℚ) ^ t ≤ value (p + 1) es n → value (p + 1) es n < 2 ^ (t + 1) →
      ∃ k : ℕ, value (p + 1) es n = ((2 * k : ℕ) : ℚ) * 2 ^ (t - (p : ℤ)) :=
    fun t h1 h2 => value_succ_even hp hn0 hn h1 h2
  generalize value (p + 1) es n = v at heven ⊢
  rcases lt_or_ge v ((2 : ℚ) ^ ((L : ℤ) + e)) with hlow | hge
  · -- every such value is below both numbers
    have hB : (2 : ℚ) ^ ((L : ℤ) + e) = 2 ^ L * 2 ^ e := by
      rw [zpow_add₀ two_ne_zero, zpow_natCast]
    rw [hB] at hlow
    have hx : v < ((q : ℚ) + θ) * 2 ^ e :=
      hlow.trans_le (mul_le_mul_of_nonneg_right (by linarith) hu.le)
    have hx' : v < (J : ℚ) * 2 ^ e :=
      hlow.trans_le (mul_le_mul_of_nonneg_right
        (hLq.trans (by exact_mod_cast hJle)) hu.le)
    exact ⟨iff_of_false (not_lt.mpr hx.le) (not_lt.mpr hx'.le), iff_of_false hx.ne' hx'.ne'⟩
  rcases le_or_gt ((2 : ℚ) ^ ((L : ℤ) + e + 1)) v with hhigh | hlt
  · -- every such value is above both numbers
    have hB : (2 : ℚ) ^ ((L : ℤ) + e + 1) = 2 ^ (L + 1) * 2 ^ e := by
      rw [show (L : ℤ) + e + 1 = ((L + 1 : ℕ) : ℤ) + e by push_cast; ring,
        zpow_add₀ two_ne_zero, zpow_natCast]
    rw [hB] at hhigh
    have hx : ((q : ℚ) + θ) * 2 ^ e < v :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right (by linarith) hu) hhigh
    have hJlt : J < 2 ^ (L + 1) := by
      have heven : 2 ^ (L + 1) % 2 = 0 := by
        rw [pow_succ]
        omega
      omega
    have hx' : (J : ℚ) * 2 ^ e < v :=
      lt_of_lt_of_le (mul_lt_mul_of_pos_right (by exact_mod_cast hJlt) hu) hhigh
    exact ⟨iff_of_true hx hx', iff_of_false hx.ne hx'.ne⟩
  · -- inside the binade the value is an even multiple of the unit
    obtain ⟨k, hk⟩ := heven _ hge hlt
    have hexp : (2 : ℚ) ^ ((L : ℤ) + e - (p : ℤ)) = 2 ^ (L - p) * 2 ^ e := by
      rw [show (L : ℤ) + e - (p : ℤ) = ((L - p : ℕ) : ℤ) + e by omega, zpow_add₀ two_ne_zero,
        zpow_natCast]
    have hvw : v = ((2 * k * 2 ^ (L - p) : ℕ) : ℚ) * 2 ^ e := by
      rw [hk, hexp]
      push_cast
      ring
    have hweven : (2 * k * 2 ^ (L - p)) % 2 = 0 := by
      rw [Nat.mul_assoc]
      exact Nat.mul_mod_right 2 _
    generalize 2 * k * 2 ^ (L - p) = w at hvw hweven
    rw [hvw, hmul, hmul, hmuleq, hmuleq]
    have key1 : (q : ℚ) + θ < (w : ℚ) ↔ q < w := by
      constructor
      · intro h
        exact_mod_cast (show (q : ℚ) < (w : ℚ) by linarith)
      · intro h
        have : (q : ℚ) + 1 ≤ (w : ℚ) := by exact_mod_cast h
        linarith
    have key2 : (J : ℚ) < (w : ℚ) ↔ q < w := by
      rw [Nat.cast_lt]
      omega
    refine ⟨key1.trans key2.symm, iff_of_false (fun h => ?_) (fun h => ?_)⟩
    · -- an integer strictly between two consecutive integers
      have h1 : (q : ℚ) < (w : ℚ) := by linarith
      have h2 : (w : ℚ) < (q : ℚ) + 1 := by linarith
      have : q < w := by exact_mod_cast h1
      have : w < q + 1 := by exact_mod_cast h2
      omega
    · have : J = w := by exact_mod_cast h
      omega

/-! ## The rounding of a quotient -/

/-- `jam q r` is `q` for a zero remainder and `q` with its low bit set otherwise. -/
theorem jam_eq_ite (q r : ℕ) : jam q r = if r = 0 then q else q ||| 1 := by
  unfold jam
  kernel_notation

/--
`quotient` returns the rounding of the exact quotient, for every number of payload bits and
every number of exponent bits. `m₁` is a natural number of at least `l₁ + 1` bits and `m₂` one
whose leading bit is at `l₂`, and the result is the rounding of
`m₁ / m₂ * 2 ^ (E₀ - l₁ + l₂ - bK * 2 ^ es)`, for every `E₀ ≥ p + 1`.
-/
theorem quotient_isRounded {p es bK m₁ l₁ m₂ l₂ E₀ : ℕ} (hp : 0 < p) (h₁ : 2 ^ l₁ ≤ m₁)
    (h₂ : 2 ^ l₂ ≤ m₂) (h₂' : m₂ < 2 ^ (l₂ + 1)) (hE : p + 1 ≤ E₀) :
    IsRounded p es
      ((m₁ : ℚ) / (m₂ : ℚ) * 2 ^ ((E₀ : ℤ) - (l₁ : ℤ) + (l₂ : ℤ) - (bK : ℤ) * 2 ^ es))
      (quotient p es bK m₁ l₁ m₂ l₂ E₀) := by
  unfold quotient
  kernel_notation
  generalize hc : max l₁ l₂ = c
  have hcl₁ : l₁ ≤ c := by omega
  have hcl₂ : l₂ ≤ c := by omega
  have hN1 : 2 ^ c ≤ m₁ * 2 ^ (c - l₁) :=
    calc 2 ^ c = 2 ^ l₁ * 2 ^ (c - l₁) := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ m₁ * 2 ^ (c - l₁) := Nat.mul_le_mul_right _ h₁
  have hD1 : 2 ^ c ≤ m₂ * 2 ^ (c - l₂) :=
    calc 2 ^ c = 2 ^ l₂ * 2 ^ (c - l₂) := by
          rw [← pow_add]
          congr 1
          omega
      _ ≤ m₂ * 2 ^ (c - l₂) := Nat.mul_le_mul_right _ h₂
  have hD2 : m₂ * 2 ^ (c - l₂) < 2 ^ (c + 1) :=
    calc m₂ * 2 ^ (c - l₂) < 2 ^ (l₂ + 1) * 2 ^ (c - l₂) :=
          Nat.mul_lt_mul_of_pos_right h₂' (Nat.two_pow_pos _)
      _ = 2 ^ (c + 1) := by
          rw [← pow_add]
          congr 1
          omega
  have hm₁ : (m₁ : ℚ) ≠ 0 := by
    have := Nat.two_pow_pos l₁
    exact_mod_cast (show m₁ ≠ 0 by omega)
  have hm₂ : (m₂ : ℚ) ≠ 0 := by
    have := Nat.two_pow_pos l₂
    exact_mod_cast (show m₂ ≠ 0 by omega)
  have hNq : ((m₁ * 2 ^ (c - l₁) : ℕ) : ℚ) = (m₁ : ℚ) * 2 ^ ((c : ℤ) - (l₁ : ℤ)) := by
    rw [show (c : ℤ) - (l₁ : ℤ) = ((c - l₁ : ℕ) : ℤ) by omega, zpow_natCast]
    push_cast
    rfl
  have hDq : ((m₂ * 2 ^ (c - l₂) : ℕ) : ℚ) = (m₂ : ℚ) * 2 ^ ((c : ℤ) - (l₂ : ℤ)) := by
    rw [show (c : ℤ) - (l₂ : ℤ) = ((c - l₂ : ℕ) : ℤ) by omega, zpow_natCast]
    push_cast
    rfl
  generalize m₁ * 2 ^ (c - l₁) = N at hN1 hNq ⊢
  generalize m₂ * 2 ^ (c - l₂) = D at hD1 hD2 hDq ⊢
  have hDpos : 0 < D := lt_of_lt_of_le (Nat.two_pow_pos c) hD1
  have : (D : ℚ) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hsteps : p ≤ (if D ≤ N then p else p + 1) ∧ (if D ≤ N then p else p + 1) ≤ p + 1 := by
    split_ifs <;> omega
  have hq1 : 2 ^ p ≤ N * 2 ^ (if D ≤ N then p else p + 1) / D := by
    rw [Nat.le_div_iff_mul_le hDpos]
    split_ifs with h
    · calc 2 ^ p * D ≤ 2 ^ p * N := Nat.mul_le_mul_left _ h
        _ = N * 2 ^ p := Nat.mul_comm _ _
    · have h2 : D ≤ 2 * N := by
        rw [pow_succ] at hD2
        omega
      calc 2 ^ p * D ≤ 2 ^ p * (2 * N) := Nat.mul_le_mul_left _ h2
        _ = N * 2 ^ (p + 1) := by
            rw [pow_succ]
            ring
  generalize (if D ≤ N then p else p + 1) = steps at hsteps hq1 ⊢
  have hdm : ((N * 2 ^ steps / D : ℕ) : ℚ) + ((N * 2 ^ steps % D : ℕ) : ℚ) / (D : ℚ) =
      (N : ℚ) * 2 ^ steps / (D : ℚ) := by
    have h := Nat.div_add_mod (N * 2 ^ steps) D
    have : (D : ℚ) * ((N * 2 ^ steps / D : ℕ) : ℚ) + ((N * 2 ^ steps % D : ℕ) : ℚ) =
        (N : ℚ) * 2 ^ steps := by exact_mod_cast h
    field_simp
    linarith
  have hval : (m₁ : ℚ) / (m₂ : ℚ) * 2 ^ ((E₀ : ℤ) - (l₁ : ℤ) + (l₂ : ℤ) - (bK : ℤ) * 2 ^ es) =
      (((N * 2 ^ steps / D : ℕ) : ℚ) + ((N * 2 ^ steps % D : ℕ) : ℚ) / (D : ℚ)) *
        2 ^ (((E₀ - steps : ℕ) : ℤ) - (bK : ℤ) * 2 ^ es) := by
    rw [hdm, hNq, hDq]
    generalize (bK : ℤ) * 2 ^ es = B
    have hexp : (E₀ : ℤ) - (l₁ : ℤ) + (l₂ : ℤ) - B =
        ((c : ℤ) - (l₁ : ℤ)) + (steps : ℤ) - ((c : ℤ) - (l₂ : ℤ)) +
          (((E₀ - steps : ℕ) : ℤ) - B) := by omega
    rw [hexp, zpow_add₀ two_ne_zero, zpow_sub₀ two_ne_zero, zpow_add₀ two_ne_zero,
      zpow_natCast]
    field_simp
  rw [hval, jam_eq_ite]
  have hq0 : N * 2 ^ steps / D ≠ 0 := by
    have := Nat.two_pow_pos p
    omega
  by_cases hr : N * 2 ^ steps % D = 0
  · rw [ite_eq_left hr, hr, Nat.cast_zero, zero_div, add_zero]
    exact encode_isRounded hp hq0
  · rw [ite_eq_right hr]
    have hθ0 : (0 : ℚ) < ((N * 2 ^ steps % D : ℕ) : ℚ) / (D : ℚ) :=
      div_pos (by exact_mod_cast Nat.pos_of_ne_zero hr) (by exact_mod_cast hDpos)
    have hθ1 : ((N * 2 ^ steps % D : ℕ) : ℚ) / (D : ℚ) < 1 := by
      rw [div_lt_one (by exact_mod_cast hDpos)]
      exact_mod_cast Nat.mod_lt _ hDpos
    have hJ0 : N * 2 ^ steps / D ||| 1 ≠ 0 := by
      rw [FloatLib.Numerics.or_one_eq]
      split_ifs <;> omega
    exact IsRounded.of_sameSide hp
      (sameSide_jam (es := es) hp hq1 hθ0 hθ1 (((E₀ - steps : ℕ) : ℤ) - (bK : ℤ) * 2 ^ es)).symm
      (encode_isRounded hp hJ0)

/-! ## Division -/

/-- A decoded significand lies in the binade of its number of fraction bits. -/
theorem significand_bounds (es m z : ℕ) :
    2 ^ fractionBits es z ≤ significand es m z ∧
      significand es m z < 2 ^ (fractionBits es z + 1) := by
  have hfb : fractionBits es z = z - 1 - es := by
    unfold fractionBits
    kernel_notation
  have := Nat.mod_lt m (Nat.two_pow_pos (z - 1 - es))
  rw [significand_eq, hfb, pow_succ]
  omega

/--
The biased exponent of the leading bit of a magnitude code, for every number of exponent bits:
`exponent + fractionBits` is within `p` regimes of the bias.
-/
theorem exponent_add_fractionBits_bounds {p es m : ℕ} (hp : 0 < p) (hm0 : 0 < m)
    (hm : m < 2 ^ p) :
    (regimeBias p - p) * 2 ^ es ≤
        exponent p es m (tailLength p m) + fractionBits es (tailLength p m) ∧
      exponent p es m (tailLength p m) + fractionBits es (tailLength p m) <
        (regimeBias p + p) * 2 ^ es := by
  have hfb : fractionBits es (tailLength p m) = tailLength p m - 1 - es := by
    unfold fractionBits
    kernel_notation
  have : regimeBias p = 8 * (p + 1) := rfl
  have hT := Nat.two_pow_pos es
  have hfield : m / 2 ^ (tailLength p m - 1 - es) % 2 ^ min es (tailLength p m - 1) *
      2 ^ (es - min es (tailLength p m - 1)) < 2 ^ es :=
    calc _ < 2 ^ min es (tailLength p m - 1) * 2 ^ (es - min es (tailLength p m - 1)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
      _ = 2 ^ es := by
          rw [← pow_add]
          congr 1
          omega
  rw [exponent_eq, hfb]
  generalize m / 2 ^ (tailLength p m - 1 - es) % 2 ^ min es (tailLength p m - 1) *
    2 ^ (es - min es (tailLength p m - 1)) = f at hfield
  have hK : regimeBias p - p ≤
        (if 2 ^ (p - 1) ≤ m then regimeBias p + p - tailLength p m - 1
          else regimeBias p + tailLength p m - p) ∧
      (if 2 ^ (p - 1) ≤ m then regimeBias p + p - tailLength p m - 1
          else regimeBias p + tailLength p m - p) + 1 ≤ regimeBias p + p ∧
      tailLength p m ≤ p := by
    rcases code_cases hp hm0 hm with ⟨hlt, hz1, hzp, -⟩ | ⟨hge, hzp, -, -⟩
    · rw [ite_eq_right (Nat.not_le.mpr hlt)]
      omega
    · rw [ite_eq_left hge]
      omega
  generalize (if 2 ^ (p - 1) ≤ m then regimeBias p + p - tailLength p m - 1
    else regimeBias p + tailLength p m - p) = K at hK
  obtain ⟨hK1, hK2, hz⟩ := hK
  have : K ≤ K * 2 ^ es := Nat.le_mul_of_pos_right _ hT
  rw [Nat.sub_add_cancel (by omega)]
  have : (regimeBias p - p) * 2 ^ es ≤ K * 2 ^ es := Nat.mul_le_mul_right _ hK1
  have h2 : (K + 1) * 2 ^ es ≤ (regimeBias p + p) * 2 ^ es := Nat.mul_le_mul_right _ hK2
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-- The quotient of two dyadic numbers with one bias: the quotient of the significands at the
difference of the exponents, with the exclusive or of the signs. -/
theorem dyadic_div (es bK : ℕ) {s₁ s₂ : ℕ} (M₁ E₁ M₂ E₂ : ℕ) (hs₁ : s₁ ≤ 1) (hs₂ : s₂ ≤ 1) :
    dyadic es bK s₁ M₁ E₁ / dyadic es bK s₂ M₂ E₂ =
      signFactor (s₁ ^^^ s₂) * ((M₁ : ℚ) / (M₂ : ℚ) * 2 ^ ((E₁ : ℤ) - (E₂ : ℤ))) := by
  unfold dyadic
  rw [signFactor_xor hs₁ hs₂]
  generalize (bK : ℤ) * 2 ^ es = B
  have hexp : (E₁ : ℤ) - (E₂ : ℤ) = ((E₁ : ℤ) - B) - ((E₂ : ℤ) - B) := by ring
  have hinv : (signFactor s₂)⁻¹ = signFactor s₂ := by
    unfold signFactor
    rcases (by omega : s₂ = 0 ∨ s₂ = 1) with rfl | rfl <;> norm_num
  have hP : (2 : ℚ) ^ ((E₁ : ℤ) - (E₂ : ℤ)) =
      2 ^ ((E₁ : ℤ) - B) * (2 ^ ((E₂ : ℤ) - B))⁻¹ := by
    rw [hexp, zpow_sub₀ two_ne_zero, div_eq_mul_inv]
  rw [hP]
  generalize (2 : ℚ) ^ ((E₁ : ℤ) - B) = P₁
  generalize (2 : ℚ) ^ ((E₂ : ℤ) - B) = P₂
  rw [div_eq_mul_inv, mul_inv, hinv, mul_inv, div_eq_mul_inv]
  ring

/-- NaR propagates through division, and a zero divisor gives NaR. -/
theorem div_nar {p a b : ℕ} (es : ℕ) (h : a = 2 ^ p ∨ b = 2 ^ p ∨ b = 0) :
    div p es a b = 2 ^ p := by
  unfold div nar
  kernel_notation
  rw [ite_eq_left (by
    rw [Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
    exact h)]

/--
Posit Standard (2022), §5.4 and §4.1, for every number of exponent bits: `div` on two encodings
with values and a nonzero divisor returns the rounding of the exact quotient of the values, for
all operands and signs.
-/
theorem div_isRoundedTo {p es a b : ℕ} {x y : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (hb : b < 2 ^ (p + 1)) (hx : toRat? p es a = some x) (hy : toRat? p es b = some y)
    (hb0 : b ≠ 0) : IsRoundedTo p es (x / y) (div p es a b) := by
  have hna := ne_nar_of_toRat? hx
  have hnb := ne_nar_of_toRat? hy
  unfold div nar
  kernel_notation
  rw [ite_eq_right (by
    rw [Bool.or_eq_true, Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq, Nat.beq_eq]
    tauto)]
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at hx
    simp only [Option.some.injEq] at hx
    rw [ite_eq_left rfl, ← hx, zero_div]
    exact isRoundedTo_zero p es
  rw [ite_eq_right ha0]
  obtain ⟨hma0, hma⟩ := magnitude_bounds ha ha0 hna
  obtain ⟨hmb0, hmb⟩ := magnitude_bounds hb hb0 hnb
  rw [toRat?_eq_dyadic hp ha ha0 hna] at hx
  rw [toRat?_eq_dyadic hp hb hb0 hnb] at hy
  simp only [Option.some.injEq] at hx hy
  rw [← hx, ← hy, dyadic_div es _ _ _ _ _ (div_two_pow_le_one ha) (div_two_pow_le_one hb)]
  have hEa := exponent_add_fractionBits_bounds (es := es) hp hma0 hma
  have hEb := exponent_add_fractionBits_bounds (es := es) hp hmb0 hmb
  have hsa := significand_bounds es (magnitude p a) (tailLength p (magnitude p a))
  have hsb := significand_bounds es (magnitude p b) (tailLength p (magnitude p b))
  have hbias : bias p es = regimeBias p * 2 ^ es := by
    rw [bias_eq_mul]
    rfl
  have hrb : regimeBias p = 8 * (p + 1) := rfl
  have hT := Nat.two_pow_pos es
  have : p ≤ p * 2 ^ es := Nat.le_mul_of_pos_right _ hT
  have hlow : (regimeBias p - p) * 2 ^ es = 7 * (p * 2 ^ es) + 8 * 2 ^ es := by
    rw [show regimeBias p - p = 7 * p + 8 by omega]
    ring
  have hhigh : (regimeBias p + p) * 2 ^ es = 9 * (p * 2 ^ es) + 8 * 2 ^ es := by
    rw [hrb]
    ring
  have hmid : regimeBias p * 2 ^ es = 8 * (p * 2 ^ es) + 8 * 2 ^ es := by
    rw [hrb]
    ring
  rw [hlow, hhigh] at hEa hEb
  rw [hbias]
  generalize exponent p es (magnitude p a) (tailLength p (magnitude p a)) = Ea at hEa ⊢
  generalize exponent p es (magnitude p b) (tailLength p (magnitude p b)) = Eb at hEb ⊢
  generalize fractionBits es (tailLength p (magnitude p a)) = fa at hEa hsa ⊢
  generalize fractionBits es (tailLength p (magnitude p b)) = fb at hEb hsb ⊢
  have hE : p + 1 ≤ Ea + regimeBias p * 2 ^ es + fa - (Eb + fb) := by
    rw [hmid]
    omega
  have hq := quotient_isRounded (es := es) (bK := regimeBias p) hp hsa.1 hsb.1 hsb.2 hE
  have hexp : ((Ea + regimeBias p * 2 ^ es + fa - (Eb + fb) : ℕ) : ℤ) - (fa : ℤ) + (fb : ℤ) -
      ((regimeBias p : ℕ) : ℤ) * 2 ^ es = (Ea : ℤ) - (Eb : ℤ) := by
    have hcast : ((regimeBias p * 2 ^ es : ℕ) : ℤ) = ((regimeBias p : ℕ) : ℤ) * 2 ^ es := by
      push_cast
      ring
    rw [← hcast]
    rw [hmid] at hE ⊢
    omega
  rw [hexp] at hq
  have hpos : (0 : ℚ) < (significand es (magnitude p a) (tailLength p (magnitude p a)) : ℚ) /
      (significand es (magnitude p b) (tailLength p (magnitude p b)) : ℚ) *
        2 ^ ((Ea : ℤ) - (Eb : ℤ)) :=
    mul_pos (div_pos (by exact_mod_cast Nat.pos_of_ne_zero (significand_ne_zero _ _ _))
      (by exact_mod_cast Nat.pos_of_ne_zero (significand_ne_zero _ _ _))) (zpow_pos two_pos _)
  exact withSign_isRoundedTo _ hpos hq

/-! ## The rounding of a ratio -/

/--
`ofRatio` returns the rounding of the ratio `± num / den` of two natural numbers, for every
number of payload bits, every number of exponent bits, every numerator and every nonzero
denominator. This is the rounding of a literal.
-/
theorem ofRatio_isRoundedTo {p es num den : ℕ} (s : ℕ) (hp : 0 < p) (hden : den ≠ 0) :
    IsRoundedTo p es (signFactor s * ((num : ℚ) / (den : ℚ))) (ofRatio p es s num den) := by
  unfold ofRatio
  kernel_notation
  by_cases hnum : num = 0
  · subst hnum
    rw [ite_eq_left rfl, Nat.cast_zero, zero_div, mul_zero]
    exact isRoundedTo_zero p es
  rw [ite_eq_right hnum, size_eq, size_eq]
  obtain ⟨hn1, -⟩ := size_bounds hnum
  obtain ⟨hd1, hd2⟩ := size_bounds hden
  have hT := Nat.two_pow_pos es
  have hbK : Nat.size den - 1 + (p + 1) <
      ((Nat.size den - 1 + (p + 1)) / 2 ^ es + 1) * 2 ^ es := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_div_mul_add hT
  generalize Nat.size num - 1 = la at hn1 ⊢
  generalize Nat.size den - 1 = lb at hd1 hd2 hbK ⊢
  generalize (lb + (p + 1)) / 2 ^ es + 1 = bK at hbK ⊢
  have hq := quotient_isRounded (es := es) (bK := bK) (E₀ := bK * 2 ^ es + la - lb) hp hn1 hd1
    hd2 (by omega)
  have hexp : ((bK * 2 ^ es + la - lb : ℕ) : ℤ) - (la : ℤ) + (lb : ℤ) - (bK : ℤ) * 2 ^ es = 0 := by
    have hcast : ((bK * 2 ^ es : ℕ) : ℤ) = (bK : ℤ) * 2 ^ es := by
      push_cast
      ring
    rw [← hcast]
    omega
  rw [hexp, zpow_zero, mul_one] at hq
  exact withSign_isRoundedTo s
    (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hnum)
      (by exact_mod_cast Nat.pos_of_ne_zero hden)) hq

/-- Every rational has a rounding in every format with at least one payload bit: the rounding
rule is satisfiable, by the encoding that `ofRatio` computes. -/
theorem exists_isRoundedTo {p : ℕ} (es : ℕ) (hp : 0 < p) (q : ℚ) :
    ∃ a, IsRoundedTo p es q a := by
  refine ⟨ofRatio p es (if q < 0 then 1 else 0) q.num.natAbs q.den, ?_⟩
  have h := ofRatio_isRoundedTo (es := es) (num := q.num.natAbs) (if q < 0 then 1 else 0) hp
    q.den_nz
  have hval : signFactor (if q < 0 then 1 else 0) * ((q.num.natAbs : ℚ) / (q.den : ℚ)) = q := by
    have hq := Rat.num_div_den q
    unfold signFactor
    by_cases hneg : q < 0
    · have hnum : ((q.num.natAbs : ℕ) : ℚ) = -(q.num : ℚ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, abs_of_nonpos (Rat.num_nonpos.mpr hneg.le),
          Int.cast_neg]
      rw [ite_eq_left hneg, ite_eq_right Nat.one_ne_zero, hnum, neg_div, neg_one_mul, neg_neg,
        hq]
    · have hnum : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
        rw [← Int.cast_natCast, Int.natCast_natAbs,
          abs_of_nonneg (Rat.num_nonneg.mpr (not_lt.mp hneg))]
      rw [ite_eq_right hneg, ite_eq_left rfl, hnum, one_mul, hq]
  rwa [hval] at h

end FloatLib.Floats.Formats.Posit.General
