/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Code
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Posits with any number of exponent bits: the rounding rule on values

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. This module states
what `KernelPath.encode` returns in terms of the values of the codes, for every number `p` of
payload bits, every number `es` of exponent bits and every positive dyadic input
`x = M * 2 ^ (E - bK * 2 ^ es)`. It is the rounding rule of the Posit Standard (2022), §4.1, with
`2 ^ es` in place of `4`:

* `encode_range`: the result is a positive magnitude code, never zero and never NaR;
* `encode_value`: a value that a code represents is returned as that code (rule 1);
* `encode_of_le_value_one`, `encode_of_value_max_le`: a value at or below the least positive
  value gives the least positive code, and a value at or above the greatest value gives the
  greatest code (rule 2);
* `encode_between`: otherwise the result `c` satisfies
  `value (p + 1) es (2 * c - 1) ≤ x ≤ value (p + 1) es (2 * c + 1)`, and `c` is even when `x` is
  one of the two bounds. The bounds are the values, in the format with one more payload bit, of
  the two codes next to `2 * c`: the midpoints of rules 3 to 6, with ties to the even code;
* `mul_eq_encode`, `mul_dyadic`, `mul_of_eq_value`: the product of two positive magnitude codes
  is one `encode` of the exact product of their values, the first operation stated for every
  `es`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Floats.Formats.Posit.KernelPath

/-- A value whose regime is at or below `-p` has a position below one. -/
theorem pos_lt_one {p es : ℕ} {k : ℤ} {a : ℚ} (hp : 0 < p) (hk : k ≤ -(p : ℤ))
    (ha : a < 2 ^ es) : pos p es k a < 1 := by
  have hes : (0 : ℚ) < 2 ^ es := by positivity
  have hu : a / 2 ^ es < 1 := (div_lt_one hes).mpr ha
  have h3 : (0 : ℚ) < 2 ^ ((p : ℤ) + k - 1) := zpow_pos two_pos _
  have hle : (2 : ℚ) ^ ((p : ℤ) + k - 1 + 1) ≤ 2 ^ (0 : ℤ) :=
    zpow_le_zpow_right₀ one_le_two (by omega)
  rw [zpow_add₀ two_ne_zero, zpow_one, zpow_zero] at hle
  unfold pos
  rw [ite_eq_left (by omega)]
  nlinarith

/-- A value whose regime is at or above `p - 1` has a position at or above `2 ^ p - 1`. -/
theorem le_pos {p es : ℕ} {k : ℤ} {a : ℚ} (hp : 0 < p) (hk : (p : ℤ) - 1 ≤ k) (ha0 : 0 ≤ a) :
    (2 : ℚ) ^ p - 1 ≤ pos p es k a := by
  have hu0 : 0 ≤ a / 2 ^ (es + 1) := by positivity
  have h4 : (0 : ℚ) < 2 ^ ((p : ℤ) - 1 - k) := zpow_pos two_pos _
  have hle : (2 : ℚ) ^ ((p : ℤ) - 1 - k) ≤ 2 ^ (0 : ℤ) :=
    zpow_le_zpow_right₀ one_le_two (by omega)
  rw [zpow_zero] at hle
  unfold pos
  rw [ite_eq_right (by omega), zpow_natCast]
  nlinarith

/-- A value whose regime is strictly between `-p` and `p - 1` has a position from one up to,
and excluding, `2 ^ p - 1`. -/
theorem pos_interior {p es : ℕ} {k : ℤ} {a : ℚ} (hlo : -(p : ℤ) < k) (hhi : k < (p : ℤ) - 1)
    (ha0 : 0 ≤ a) (ha : a < 2 ^ es) : 1 ≤ pos p es k a ∧ pos p es k a < 2 ^ p - 1 := by
  have hes : (0 : ℚ) < 2 ^ es := by positivity
  have hu0 : 0 ≤ a / 2 ^ es := div_nonneg ha0 hes.le
  have hu1 : a / 2 ^ es < 1 := (div_lt_one hes).mpr ha
  have hhalf : a / 2 ^ (es + 1) = a / 2 ^ es / 2 := by rw [pow_succ, div_mul_eq_div_div]
  have hp1 : (1 : ℚ) ≤ 2 ^ ((p : ℤ) - 1) := by
    have := zpow_le_zpow_right₀ (one_le_two (α := ℚ)) (show (0 : ℤ) ≤ (p : ℤ) - 1 by omega)
    rwa [zpow_zero] at this
  have hp : (2 : ℚ) ^ p = 2 ^ ((p : ℤ) - 1) * 2 := by
    rw [← zpow_natCast, ← zpow_add_one₀ two_ne_zero]
    congr 1
    ring
  unfold pos
  rw [hhalf]
  by_cases hk : k < 0
  · rw [ite_eq_left hk]
    have h3 : (0 : ℚ) < 2 ^ ((p : ℤ) + k - 1) := zpow_pos two_pos _
    have hge : (2 : ℚ) ^ (0 : ℤ) ≤ 2 ^ ((p : ℤ) + k - 1) :=
      zpow_le_zpow_right₀ one_le_two (by omega)
    rw [zpow_zero] at hge
    have hle : (2 : ℚ) ^ ((p : ℤ) + k - 1 + 1) ≤ 2 ^ ((p : ℤ) - 1) :=
      zpow_le_zpow_right₀ one_le_two (by omega)
    rw [zpow_add₀ two_ne_zero, zpow_one] at hle
    constructor <;> nlinarith
  · rw [ite_eq_right hk, zpow_natCast]
    have h4 : (0 : ℚ) < 2 ^ ((p : ℤ) - 1 - k) := zpow_pos two_pos _
    have hle : (2 : ℚ) ^ ((p : ℤ) - 1 - k) ≤ 2 ^ ((p : ℤ) - 1) :=
      zpow_le_zpow_right₀ one_le_two (by omega)
    have hge : (2 : ℚ) ^ (1 : ℤ) ≤ 2 ^ ((p : ℤ) - 1 - k) :=
      zpow_le_zpow_right₀ one_le_two (by omega)
    rw [zpow_one] at hge
    constructor <;> nlinarith

/-- `encode` returns a positive magnitude code: it is never zero and never NaR. -/
theorem encode_range {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0) :
    0 < encode p es bK M E ∧ encode p es bK M E < 2 ^ p := by
  have hone : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  rcases le_or_gt (regime es bK M E) (-(p : ℤ)) with hlo | hlo
  · rw [encode_of_le hp hlo]
    omega
  rcases le_or_gt ((p : ℤ) - 1) (regime es bK M E) with hhi | hhi
  · rw [encode_of_ge hp hhi]
    omega
  · have hn := (encode_nearest (p := p) hlo hhi).1
    have hint := pos_interior hlo hhi (tail_nonneg es M E) (tail_lt hM es E)
    have habs := abs_le.mp hn
    constructor
    · have : (0 : ℚ) < ((encode p es bK M E : ℕ) : ℚ) := by linarith [habs.1, hint.1]
      exact_mod_cast this
    · have : ((encode p es bK M E : ℕ) : ℚ) < ((2 ^ p : ℕ) : ℚ) := by
        push_cast
        linarith [habs.2, hint.2]
      exact_mod_cast this

/-- The position of a dyadic number that is the value of a code is that code. -/
theorem pos_of_eq_value {p es bK M E m : ℕ} (hp : 0 < p) (hM : M ≠ 0) (hm0 : 0 < m)
    (hm : m < 2 ^ p) (hx : (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) = value p es m) :
    pos p es (regime es bK M E) (tail es M E) = (m : ℚ) := by
  have hval : val es (regime es bK M E) (tail es M E) =
      val es (codeRegime p m) (fieldTail es m (tailLength p m)) := by
    rw [val_dyadic hM, hx]
    rfl
  rw [(pos_eq_pos_iff (tail_nonneg es M E) (tail_lt hM es E) (fieldTail_nonneg _ _ _)
    (fieldTail_lt _ _ _)).mpr hval, pos_code hp hm0 hm]

/--
Posit Standard (2022), §4.1, rule 1, for every number of exponent bits: a dyadic number that is
the value of the positive magnitude code `m` is encoded as `m`.
-/
theorem encode_value {p es bK M E m : ℕ} (hp : 0 < p) (hM : M ≠ 0) (hm0 : 0 < m)
    (hm : m < 2 ^ p) (hx : (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) = value p es m) :
    encode p es bK M E = m := by
  have hpos := pos_of_eq_value hp hM hm0 hm hx
  rcases le_or_gt (regime es bK M E) (-(p : ℤ)) with hlo | hlo
  · have h := pos_lt_one hp hlo (tail_lt hM es E)
    rw [hpos] at h
    have : m < 1 := by exact_mod_cast h
    omega
  rcases le_or_gt ((p : ℤ) - 1) (regime es bK M E) with hhi | hhi
  · have h := le_pos (es := es) hp hhi (tail_nonneg es M E)
    rw [hpos] at h
    have : 2 ^ p ≤ m + 1 := by
      have h' : ((2 ^ p : ℕ) : ℚ) ≤ ((m + 1 : ℕ) : ℚ) := by
        push_cast
        linarith
      exact_mod_cast h'
    rw [encode_of_ge hp hhi]
    omega
  · have h := encode_nearest (p := p) hlo hhi
    rw [hpos] at h
    exact h.unique (isNearestEven_self m)

/--
Posit Standard (2022), §4.1, rule 2, for every number of exponent bits: a dyadic number at or
below the least positive value is encoded as the least positive code.
-/
theorem encode_of_le_value_one {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0)
    (hx : (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) ≤ value p es 1) :
    encode p es bK M E = 1 := by
  have hone : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  have hpos : pos p es (regime es bK M E) (tail es M E) ≤ 1 := by
    have h := (pos_lt_pos_iff (p := p) (fieldTail_nonneg es 1 (tailLength p 1))
      (fieldTail_lt es 1 (tailLength p 1)) (tail_nonneg es M E) (tail_lt hM es E)).not.mpr
      (by rw [val_dyadic hM]; exact not_lt.mpr hx)
    rw [pos_code hp Nat.one_pos (by omega)] at h
    simpa using not_lt.mp h
  rcases le_or_gt (regime es bK M E) (-(p : ℤ)) with hlo | hlo
  · exact encode_of_le hp hlo
  rcases le_or_gt ((p : ℤ) - 1) (regime es bK M E) with hhi | hhi
  · have h := le_pos (es := es) hp hhi (tail_nonneg es M E)
    have h2 : ((2 ^ p : ℕ) : ℚ) ≤ ((2 : ℕ) : ℚ) := by
      push_cast
      linarith
    have h3 : 2 ^ p ≤ 2 := by exact_mod_cast h2
    rw [encode_of_ge hp hhi]
    omega
  · have hint := pos_interior hlo hhi (tail_nonneg es M E) (tail_lt hM es E)
    have h := encode_nearest (p := p) hlo hhi
    rw [le_antisymm hpos hint.1] at h
    exact h.unique (by simpa using isNearestEven_self 1)

/--
Posit Standard (2022), §4.1, rule 2, for every number of exponent bits: a dyadic number at or
above the greatest value is encoded as the greatest code.
-/
theorem encode_of_value_max_le {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0)
    (hx : value p es (2 ^ p - 1) ≤ (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) :
    encode p es bK M E = 2 ^ p - 1 := by
  have hone : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  have hpos : (2 : ℚ) ^ p - 1 ≤ pos p es (regime es bK M E) (tail es M E) := by
    have h := (pos_lt_pos_iff (p := p) (tail_nonneg es M E) (tail_lt hM es E)
      (fieldTail_nonneg es (2 ^ p - 1) (tailLength p (2 ^ p - 1)))
      (fieldTail_lt es (2 ^ p - 1) (tailLength p (2 ^ p - 1)))).not.mpr
      (by rw [val_dyadic hM]; exact not_lt.mpr hx)
    rw [pos_code hp (by omega) (by omega), Nat.cast_sub (by omega)] at h
    push_cast at h
    exact not_lt.mp h
  rcases le_or_gt ((p : ℤ) - 1) (regime es bK M E) with hhi | hhi
  · exact encode_of_ge hp hhi
  rcases le_or_gt (regime es bK M E) (-(p : ℤ)) with hlo | hlo
  · have h := pos_lt_one hp hlo (tail_lt hM es E)
    have h2 : ((2 ^ p : ℕ) : ℚ) < ((2 : ℕ) : ℚ) := by
      push_cast
      linarith
    have h3 : 2 ^ p < 2 := by exact_mod_cast h2
    omega
  · have hint := pos_interior hlo hhi (tail_nonneg es M E) (tail_lt hM es E)
    linarith [hint.2]

/--
Posit Standard (2022), §4.1, rules 3 to 6, for every number of exponent bits. For a dyadic
number `x` whose regime is strictly between `-p` and `p - 1`, the code `c` that `encode` returns
satisfies `value (p + 1) es (2 * c - 1) ≤ x ≤ value (p + 1) es (2 * c + 1)`: `x` lies between the
values, in the format with one more payload bit, of the two codes next to `2 * c`. When `x` is
one of these two midpoints, `c` is even.
-/
theorem encode_between {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0)
    (hlo : -(p : ℤ) < regime es bK M E) (hhi : regime es bK M E < (p : ℤ) - 1) :
    value (p + 1) es (2 * encode p es bK M E - 1) ≤
        (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) ∧
      (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) ≤
        value (p + 1) es (2 * encode p es bK M E + 1) ∧
      ((M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) =
          value (p + 1) es (2 * encode p es bK M E - 1) ∨
        (M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es) =
          value (p + 1) es (2 * encode p es bK M E + 1) → Even (encode p es bK M E)) := by
  obtain ⟨hc0, hclt⟩ := encode_range (es := es) (bK := bK) (E := E) hp hM
  have hn := encode_nearest (p := p) hlo hhi
  generalize encode p es bK M E = c at hc0 hclt hn ⊢
  have ht0 := tail_nonneg es M E
  have ht := tail_lt hM es E
  have hdouble := pos_succ p es (regime es bK M E) (tail es M E)
  have hlow : pos (p + 1) es (codeRegime (p + 1) (2 * c - 1))
      (fieldTail es (2 * c - 1) (tailLength (p + 1) (2 * c - 1))) = 2 * (c : ℚ) - 1 := by
    rw [pos_code (Nat.succ_pos p) (by omega) (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  have hhigh : pos (p + 1) es (codeRegime (p + 1) (2 * c + 1))
      (fieldTail es (2 * c + 1) (tailLength (p + 1) (2 * c + 1))) = 2 * (c : ℚ) + 1 := by
    rw [pos_code (Nat.succ_pos p) (by omega) (by omega)]
    push_cast
    ring
  have habs := abs_le.mp hn.1
  rw [← val_dyadic hM]
  refine ⟨?_, ?_, ?_⟩
  · refine not_lt.mp fun hlt => ?_
    have h := (pos_lt_pos_iff (p := p + 1) ht0 ht (fieldTail_nonneg _ _ _)
      (fieldTail_lt _ _ _)).mpr hlt
    rw [hdouble, hlow] at h
    linarith [habs.2]
  · refine not_lt.mp fun hlt => ?_
    have h := (pos_lt_pos_iff (p := p + 1) (fieldTail_nonneg _ _ _) (fieldTail_lt _ _ _) ht0
      ht).mpr hlt
    rw [hdouble, hhigh] at h
    linarith [habs.1]
  · rintro (heq | heq)
    · have h := (pos_eq_pos_iff (p := p + 1) ht0 ht (fieldTail_nonneg _ _ _)
        (fieldTail_lt _ _ _)).mpr heq
      rw [hdouble, hlow] at h
      refine hn.2 ?_
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have h := (pos_eq_pos_iff (p := p + 1) ht0 ht (fieldTail_nonneg _ _ _)
        (fieldTail_lt _ _ _)).mpr heq
      rw [hdouble, hhigh] at h
      refine hn.2 ?_
      rw [abs_of_nonpos (by linarith)]
      linarith

/-! ## Multiplication of positive codes

The first operation whose result is stated for every number of exponent bits: the product of two
positive magnitude codes is one `encode` of the exact product of their values, so every theorem
above applies to it.
-/

/-- `mul` on two positive magnitude codes is one `encode`, of the product of the significands at
the sum of the exponents. -/
theorem mul_eq_encode {p es a b : ℕ} (ha0 : 0 < a) (ha : a < 2 ^ p) (hb0 : 0 < b)
    (hb : b < 2 ^ p) :
    mul p es a b =
      encode p es (2 * regimeBias p)
        (significand es a (tailLength p a) * significand es b (tailLength p b))
        (exponent p es a (tailLength p a) + exponent p es b (tailLength p b)) := by
  unfold mul magnitude withSign nar
  kernel_notation
  rw [ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; omega),
    ite_eq_right (by rw [Bool.or_eq_true, Nat.beq_eq, Nat.beq_eq]; omega),
    ite_eq_left (by rw [Nat.div_eq_of_lt ha, Nat.div_eq_of_lt hb]; rfl),
    ite_eq_right (Nat.not_le.mpr ha), ite_eq_right (Nat.not_le.mpr hb)]

/-- The dyadic number that `mul` rounds is the exact product of the values of the two codes. -/
theorem mul_dyadic {p es a b : ℕ} (hp : 0 < p) (ha0 : 0 < a) (ha : a < 2 ^ p) (hb0 : 0 < b)
    (hb : b < 2 ^ p) :
    ((significand es a (tailLength p a) * significand es b (tailLength p b) : ℕ) : ℚ) *
        2 ^ (((exponent p es a (tailLength p a) + exponent p es b (tailLength p b) : ℕ) : ℤ) -
          ((2 * regimeBias p : ℕ) : ℤ) * 2 ^ es) =
      value p es a * value p es b := by
  have hbias : ((bias p es : ℕ) : ℤ) = ((regimeBias p : ℕ) : ℤ) * 2 ^ es := by
    have h : regimeBias p = 8 * (p + 1) := rfl
    rw [bias_eq_mul, h]
    push_cast
    ring
  rw [value_eq_fields hp ha0 ha, value_eq_fields hp hb0 hb, hbias, mul_mul_mul_comm,
    ← zpow_add₀ two_ne_zero]
  push_cast
  congr 2
  ring

/--
Posit Standard (2022), §5.4 with rule 1 of §4.1, for every number of exponent bits and positive
operands: when the exact product of the values of two positive magnitude codes is the value of
the code `m`, `mul` returns `m`.
-/
theorem mul_of_eq_value {p es a b m : ℕ} (hp : 0 < p) (ha0 : 0 < a) (ha : a < 2 ^ p)
    (hb0 : 0 < b) (hb : b < 2 ^ p) (hm0 : 0 < m) (hm : m < 2 ^ p)
    (h : value p es a * value p es b = value p es m) : mul p es a b = m := by
  rw [mul_eq_encode ha0 ha hb0 hb]
  exact encode_value hp
    (Nat.mul_ne_zero (significand_ne_zero es a _) (significand_ne_zero es b _)) hm0 hm
    (by rw [mul_dyadic hp ha0 ha hb0 hb, h])

end FloatLib.Floats.Formats.Posit.General
