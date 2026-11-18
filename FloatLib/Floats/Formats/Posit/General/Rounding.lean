/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Order
public import FloatLib.Tactic.KernelNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Posits with any number of exponent bits: rounding

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. `KernelPath.encode`
rounds a positive dyadic number to a code of a format with `p` payload bits and `es` exponent
bits. This module proves what it returns, for every `p`, every `es` and every input.

* `IsNearestEven q n`: the natural number `n` is nearest to the rational `q`, and even when `q`
  is halfway between two integers.
* `roundTail_nearest`: `KernelPath.roundTail t base raw w` is nearest-even to
  `base + raw * 2 ^ (t - w)`.
* `regime`, `tail` and `val_dyadic`: the regime and the tail of the value
  `M * 2 ^ (E - bK * 2 ^ es)` as `encode` computes them, and that this pair has that value.
* `encode_of_le`, `encode_of_ge`, `encode_nearest`: `encode` returns the least positive code for
  a regime at or below `-p`, the greatest code for a regime at or above `p - 1`, and otherwise a
  code that is nearest-even to the position of the value (`General.pos`).

With `General.pos_code` (a code's value has the code as its position) and `General.pos_lt_pos_iff`
(positions are ordered as values), this is the rounding rule of the Posit Standard (2022), §4.1,
with `es` exponent bits in place of two: `General.Standard` states it on values.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Numerics.Kernel FloatLib.Floats.Formats.Posit.KernelPath

/-- `n` is a natural number nearest to `q`, and it is even when `q` is halfway between two
integers. -/
def IsNearestEven (q : ℚ) (n : ℕ) : Prop :=
  |(n : ℚ) - q| ≤ 1 / 2 ∧ (|(n : ℚ) - q| = 1 / 2 → Even n)

/-- A natural number is nearest-even to itself. -/
theorem isNearestEven_self (n : ℕ) : IsNearestEven (n : ℚ) n := by
  constructor
  · simp
  · intro h
    simp at h

/-- The nearest-even natural number is unique. -/
theorem IsNearestEven.unique {q : ℚ} {n m : ℕ} (hn : IsNearestEven q n)
    (hm : IsNearestEven q m) : n = m := by
  have h1 := abs_le.mp hn.1
  have h2 := abs_le.mp hm.1
  have hlt : ((n : ℤ) : ℚ) - m < 2 ∧ ((m : ℤ) : ℚ) - n < 2 := by
    constructor <;> push_cast <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hd : (n : ℤ) - m ≤ 1 ∧ (m : ℤ) - n ≤ 1 := by
    constructor
    · have : (((n : ℤ) - m : ℤ) : ℚ) < 2 := by push_cast; exact hlt.1
      exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
    · have : (((m : ℤ) - n : ℤ) : ℚ) < 2 := by push_cast; exact hlt.2
      exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  rcases (by omega : n = m ∨ n = m + 1 ∨ m = n + 1) with h | h | h
  · exact h
  · subst h
    have hq : q = (m : ℚ) + 1 / 2 := by push_cast at h1; linarith [h1.2, h2.1]
    have e1 : Even (m + 1) := hn.2 (by rw [hq]; push_cast; norm_num)
    have e2 : Even m := hm.2 (by rw [hq]; norm_num)
    rw [Nat.even_add_one] at e1
    exact absurd e2 e1
  · subst h
    have hq : q = (n : ℚ) + 1 / 2 := by push_cast at h2; linarith [h2.2, h1.1]
    have e1 : Even (n + 1) := hm.2 (by rw [hq]; push_cast; norm_num)
    have e2 : Even n := hn.2 (by rw [hq]; norm_num)
    rw [Nat.even_add_one] at e1
    exact absurd e2 e1

/--
Rounding by a remainder: with `r < 2 * H`, the number `lower + r / (2 * H)` is nearest-even to
`lower + 1` when `2 * r + lower % 2` exceeds `2 * H`, and to `lower` otherwise.
-/
theorem isNearestEven_of_remainder (lower r H : ℕ) (hH : 0 < H) (hr : r < 2 * H) :
    IsNearestEven ((lower : ℚ) + (r : ℚ) / (2 * H))
      (if 2 * H + 1 ≤ r * 2 + lower % 2 then lower + 1 else lower) := by
  have hHq : (0 : ℚ) < 2 * H := by positivity
  split_ifs with h
  · have hrH : H ≤ r := by omega
    have hfrac : (1 : ℚ) / 2 ≤ (r : ℚ) / (2 * H) := by
      rw [div_le_div_iff₀ two_pos hHq]
      have : ((H : ℕ) : ℚ) ≤ r := by exact_mod_cast hrH
      linarith
    have hfrac1 : (r : ℚ) / (2 * H) < 1 := by
      rw [div_lt_one hHq]
      exact_mod_cast hr
    have habs : |((lower + 1 : ℕ) : ℚ) - ((lower : ℚ) + (r : ℚ) / (2 * H))| =
        1 - (r : ℚ) / (2 * H) := by
      rw [abs_of_nonneg (by push_cast; linarith)]
      push_cast
      ring
    refine ⟨by rw [habs]; linarith, fun htie => ?_⟩
    rw [habs] at htie
    have hrq : (r : ℚ) = H := by
      have h2 : (r : ℚ) / (2 * H) = 1 / 2 := by linarith
      rw [div_eq_iff hHq.ne'] at h2
      linarith
    have hrH' : r = H := by exact_mod_cast hrq
    have : lower % 2 = 1 := by omega
    exact Nat.even_add_one.mpr (Nat.not_even_iff.mpr this)
  · have hrH : r ≤ H := by omega
    have hfrac : (r : ℚ) / (2 * H) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hHq two_pos]
      have : ((r : ℕ) : ℚ) ≤ H := by exact_mod_cast hrH
      linarith
    have hfrac0 : (0 : ℚ) ≤ (r : ℚ) / (2 * H) := by positivity
    have habs : |(lower : ℚ) - ((lower : ℚ) + (r : ℚ) / (2 * H))| = (r : ℚ) / (2 * H) := by
      rw [abs_of_nonpos (by linarith)]
      ring
    refine ⟨by rw [habs]; exact hfrac, fun htie => ?_⟩
    rw [habs] at htie
    have hrq : (r : ℚ) = H := by
      rw [div_eq_iff hHq.ne'] at htie
      linarith
    have hrH' : r = H := by exact_mod_cast hrq
    have : lower % 2 = 0 := by omega
    exact Nat.even_iff.mpr this

/--
`roundTail t base raw w` is nearest-even to `base + raw * 2 ^ (t - w)`: the stream `raw` of `w`
bits read as a number with `t` bits before its binary point, above the code `base`.
-/
theorem roundTail_nearest (t base raw w : ℕ) :
    IsNearestEven ((base : ℚ) + (raw : ℚ) * 2 ^ ((t : ℤ) - (w : ℤ))) (roundTail t base raw w) := by
  unfold roundTail
  kernel_notation
  rw [Nat.and_one_is_mod]
  obtain ⟨s, hs⟩ : ∃ s, w + (t + 1 - w) - t = s + 1 := ⟨w + (t + 1 - w) - t - 1, by omega⟩
  rw [hs]
  generalize t + 1 - w = d at hs
  have hpow : (2 : ℕ) ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ]; ring
  have hspos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hrem : raw * 2 ^ d % 2 ^ (s + 1) < 2 * 2 ^ s := by
    rw [← hpow]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have key := isNearestEven_of_remainder (base + raw * 2 ^ d / 2 ^ (s + 1))
    (raw * 2 ^ d % 2 ^ (s + 1)) (2 ^ s) hspos hrem
  have hval : ((base + raw * 2 ^ d / 2 ^ (s + 1) : ℕ) : ℚ) +
      ((raw * 2 ^ d % 2 ^ (s + 1) : ℕ) : ℚ) / (2 * ((2 ^ s : ℕ) : ℚ)) =
      (base : ℚ) + (raw : ℚ) * 2 ^ ((t : ℤ) - (w : ℤ)) := by
    have hdm := Nat.div_add_mod (raw * 2 ^ d) (2 ^ (s + 1))
    have hdmq : (2 : ℚ) ^ (s + 1) * ((raw * 2 ^ d / 2 ^ (s + 1) : ℕ) : ℚ) +
        ((raw * 2 ^ d % 2 ^ (s + 1) : ℕ) : ℚ) = (raw : ℚ) * 2 ^ d := by
      exact_mod_cast hdm
    have hexp : ((t : ℤ) - (w : ℤ)) = (d : ℤ) - ((s + 1 : ℕ) : ℤ) := by omega
    have h2 : (2 : ℚ) * ((2 ^ s : ℕ) : ℚ) = 2 ^ (s + 1) := by push_cast; rw [pow_succ]; ring
    rw [hexp, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast, h2]
    push_cast
    field_simp
    linarith
  rw [hval] at key
  have hcond : (2 ^ (s + 1) + 1 ≤ raw * 2 ^ d % 2 ^ (s + 1) * 2 ^ 1 +
      (base + raw * 2 ^ d / 2 ^ (s + 1)) % 2) ↔
      (2 * 2 ^ s + 1 ≤ raw * 2 ^ d % 2 ^ (s + 1) * 2 + (base + raw * 2 ^ d / 2 ^ (s + 1)) % 2) := by
    rw [hpow, pow_one]
  simp only [hcond]
  exact key

/-! ## The regime and the tail of a dyadic number -/

/-- The regime of the value `M * 2 ^ (E - bK * 2 ^ es)`, `M ≠ 0`: its binary exponent divided
by `2 ^ es`, rounded down. -/
def regime (es bK M E : ℕ) : ℤ := (((E + (Nat.size M - 1)) / 2 ^ es : ℕ) : ℤ) - (bK : ℤ)

/-- The tail of the value `M * 2 ^ (E - bK * 2 ^ es)`, `M ≠ 0`: the remainder of its binary
exponent modulo `2 ^ es`, plus the fraction of `M` below its leading bit. -/
def tail (es M E : ℕ) : ℚ :=
  (((E + (Nat.size M - 1)) % 2 ^ es : ℕ) : ℚ) +
    ((M - 2 ^ (Nat.size M - 1) : ℕ) : ℚ) / 2 ^ (Nat.size M - 1)

/-- A nonzero natural number lies between the power of two of its leading bit and the next. -/
theorem size_bounds {M : ℕ} (hM : M ≠ 0) :
    2 ^ (Nat.size M - 1) ≤ M ∧ M < 2 ^ (Nat.size M - 1 + 1) := by
  have hpos : 0 < Nat.size M := Nat.size_pos.mpr (Nat.pos_of_ne_zero hM)
  have h1 : Nat.size M - 1 < Nat.size M := by omega
  have h2 : Nat.size M - 1 + 1 = Nat.size M := by omega
  exact ⟨Nat.lt_size.mp h1, by rw [h2]; exact Nat.lt_size_self M⟩

/-- The tail of a dyadic number is not negative. -/
theorem tail_nonneg (es M E : ℕ) : 0 ≤ tail es M E := by
  unfold tail
  positivity

/-- The fraction of a nonzero natural number below its leading bit is less than one. -/
theorem fraction_lt_one {M : ℕ} (hM : M ≠ 0) :
    ((M - 2 ^ (Nat.size M - 1) : ℕ) : ℚ) / 2 ^ (Nat.size M - 1) < 1 := by
  obtain ⟨h1, h2⟩ := size_bounds hM
  rw [div_lt_one (by positivity)]
  have : M - 2 ^ (Nat.size M - 1) < 2 ^ (Nat.size M - 1) := by
    rw [pow_succ] at h2
    omega
  exact_mod_cast this

/-- The tail of a dyadic number is below `2 ^ es`. -/
theorem tail_lt {M : ℕ} (hM : M ≠ 0) (es E : ℕ) : tail es M E < 2 ^ es := by
  have hmod : (E + (Nat.size M - 1)) % 2 ^ es + 1 ≤ 2 ^ es := Nat.mod_lt _ (Nat.two_pow_pos es)
  have hmodq : (((E + (Nat.size M - 1)) % 2 ^ es : ℕ) : ℚ) + 1 ≤ 2 ^ es := by exact_mod_cast hmod
  have hfrac := fraction_lt_one hM
  unfold tail
  linarith

/-- The exponent field of a dyadic number is the integer part of its tail. -/
theorem floor_tail {M : ℕ} (hM : M ≠ 0) (es E : ℕ) :
    ⌊tail es M E⌋ = (((E + (Nat.size M - 1)) % 2 ^ es : ℕ) : ℤ) := by
  have hfrac := fraction_lt_one hM
  have hfrac0 : (0 : ℚ) ≤ ((M - 2 ^ (Nat.size M - 1) : ℕ) : ℚ) / 2 ^ (Nat.size M - 1) := by
    positivity
  rw [Int.floor_eq_iff, Int.cast_natCast]
  unfold tail
  constructor <;> linarith

/-- The pair `regime`, `tail` has the value `M * 2 ^ (E - bK * 2 ^ es)`. -/
theorem val_dyadic {M : ℕ} (hM : M ≠ 0) (es bK E : ℕ) :
    val es (regime es bK M E) (tail es M E) = (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) := by
  obtain ⟨h1, _⟩ := size_bounds hM
  have hfloor := floor_tail hM es E
  have hfract : Int.fract (tail es M E) =
      ((M - 2 ^ (Nat.size M - 1) : ℕ) : ℚ) / 2 ^ (Nat.size M - 1) := by
    rw [← Int.self_sub_floor, hfloor, Int.cast_natCast]
    unfold tail
    ring
  have hdm := Nat.div_add_mod (E + (Nat.size M - 1)) (2 ^ es)
  have hdmz : (2 : ℤ) ^ es * (((E + (Nat.size M - 1)) / 2 ^ es : ℕ) : ℤ) +
      (((E + (Nat.size M - 1)) % 2 ^ es : ℕ) : ℤ) = (E : ℤ) + ((Nat.size M - 1 : ℕ) : ℤ) := by
    exact_mod_cast hdm
  have hexp : regime es bK M E * 2 ^ es + (((E + (Nat.size M - 1)) % 2 ^ es : ℕ) : ℤ) =
      ((E : ℤ) - (bK : ℤ) * 2 ^ es) + ((Nat.size M - 1 : ℕ) : ℤ) := by
    unfold regime
    linarith
  have hcast : (1 : ℚ) + ((M - 2 ^ (Nat.size M - 1) : ℕ) : ℚ) / 2 ^ (Nat.size M - 1) =
      (M : ℚ) / 2 ^ (Nat.size M - 1) := by
    rw [Nat.cast_sub h1]
    push_cast
    field_simp
    ring
  unfold val taper
  rw [hfloor, hfract, ← mul_assoc, ← zpow_add₀ two_ne_zero, hexp, hcast, zpow_add₀ two_ne_zero,
    zpow_natCast]
  field_simp

/-! ## What `encode` returns -/

/-- `encode` as the case analysis on the regime that it performs. -/
theorem encode_eq_ite (p es bK M E : ℕ) :
    encode p es bK M E =
      if bK ≤ (E + (M.size - 1)) / 2 ^ es then
        if p ≤ (E + (M.size - 1)) / 2 ^ es - bK + 1 then 2 ^ p - 1
        else
          roundTail (p - ((E + (M.size - 1)) / 2 ^ es - bK + 1) - 1)
            (2 ^ p - 2 ^ (p - ((E + (M.size - 1)) / 2 ^ es - bK + 1)))
            ((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1)))
            (M.size - 1 + es)
      else
        if p ≤ bK - (E + (M.size - 1)) / 2 ^ es then 1
        else
          roundTail (p - (bK - (E + (M.size - 1)) / 2 ^ es) - 1)
            (2 ^ (p - (bK - (E + (M.size - 1)) / 2 ^ es) - 1))
            ((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1)))
            (M.size - 1 + es) := by
  unfold encode
  kernel_notation
  rw [size_eq]

/-- A value whose regime is at or below `-p` is rounded to the least positive code. -/
theorem encode_of_le {p es bK M E : ℕ} (hp : 0 < p) (h : regime es bK M E ≤ -(p : ℤ)) :
    encode p es bK M E = 1 := by
  rw [encode_eq_ite]
  unfold regime at h
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- A value whose regime is at or above `p - 1` is rounded to the greatest code. -/
theorem encode_of_ge {p es bK M E : ℕ} (hp : 0 < p) (h : (p : ℤ) - 1 ≤ regime es bK M E) :
    encode p es bK M E = 2 ^ p - 1 := by
  rw [encode_eq_ite]
  unfold regime at h
  rw [ite_eq_left (by omega), ite_eq_left (by omega)]

/--
A value whose regime is strictly between `-p` and `p - 1` is rounded to a code that is
nearest-even to its position among the codes with `p` payload bits.
-/
theorem encode_nearest {p es bK M E : ℕ} (hlo : -(p : ℤ) < regime es bK M E)
    (hhi : regime es bK M E < (p : ℤ) - 1) :
    IsNearestEven (pos p es (regime es bK M E) (tail es M E)) (encode p es bK M E) := by
  have hraw : (((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1)) : ℕ) : ℚ) =
      tail es M E * 2 ^ (M.size - 1) := by
    unfold tail
    rw [Nat.cast_add, Nat.cast_mul, add_mul]
    push_cast
    field_simp
  rw [encode_eq_ite]
  unfold regime at hlo hhi ⊢
  generalize (E + (M.size - 1)) / 2 ^ es = K at hlo hhi ⊢
  by_cases hb : bK ≤ K
  · rw [ite_eq_left hb, ite_eq_right (by omega)]
    obtain ⟨z, hz⟩ : ∃ z, p = (K - bK + 1) + (z + 1) := ⟨p - (K - bK + 1) - 1, by omega⟩
    have e1 : (p : ℤ) - 1 - ((K : ℤ) - (bK : ℤ)) = ((z + 1 : ℕ) : ℤ) := by omega
    have e2 : p - (K - bK + 1) = z + 1 := by omega
    have e3 : p - (K - bK + 1) - 1 = z := by omega
    have key := roundTail_nearest z (2 ^ p - 2 ^ (z + 1))
      ((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1))) (M.size - 1 + es)
    rw [e3, e2]
    have hle : 2 ^ (z + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) (by omega)
    have hpos : pos p es ((K : ℤ) - (bK : ℤ)) (tail es M E) =
        ((2 ^ p - 2 ^ (z + 1) : ℕ) : ℚ) +
          (((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1)) : ℕ) : ℚ) *
            2 ^ ((z : ℤ) - ((M.size - 1 + es : ℕ) : ℤ)) := by
      unfold pos
      rw [ite_eq_right (by omega), e1, hraw, Nat.cast_sub hle, zpow_sub₀ two_ne_zero, zpow_natCast,
        zpow_natCast, zpow_natCast, zpow_natCast]
      push_cast
      rw [pow_add, pow_succ, pow_succ]
      field_simp
      ring
    rw [hpos]
    exact key
  · rw [ite_eq_right hb, ite_eq_right (by omega)]
    obtain ⟨t, ht⟩ : ∃ t, p = (bK - K) + (t + 1) := ⟨p - (bK - K) - 1, by omega⟩
    have e1 : (p : ℤ) + ((K : ℤ) - (bK : ℤ)) - 1 = (t : ℤ) := by omega
    have e3 : p - (bK - K) - 1 = t := by omega
    have key := roundTail_nearest t (2 ^ t)
      ((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1))) (M.size - 1 + es)
    rw [e3]
    have hpos : pos p es ((K : ℤ) - (bK : ℤ)) (tail es M E) =
        ((2 ^ t : ℕ) : ℚ) +
          (((E + (M.size - 1)) % 2 ^ es * 2 ^ (M.size - 1) + (M - 2 ^ (M.size - 1)) : ℕ) : ℚ) *
            2 ^ ((t : ℤ) - ((M.size - 1 + es : ℕ) : ℤ)) := by
      unfold pos
      rw [ite_eq_left (by omega), e1, hraw, zpow_sub₀ two_ne_zero, zpow_natCast, zpow_natCast]
      push_cast
      rw [pow_add]
      field_simp
    rw [hpos]
    exact key

end FloatLib.Floats.Formats.Posit.General
