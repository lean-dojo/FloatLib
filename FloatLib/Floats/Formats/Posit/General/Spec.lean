/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Rule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Posits with any number of exponent bits: the specification of an operation

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. This module states,
on values alone, what the result of an operation is in a format with `p` payload bits and `es`
exponent bits. It has no reference to how the operations of `Posit.KernelPath.Core` compute.

* `toRat? p es a` is the value of the encoding `a`: none for NaR (`2 ^ p`), zero for zero, the
  value of the magnitude code below the sign bit, and minus the value of the two's complement
  from the sign bit on (Posit Standard (2022), §3.2.2 with `2 ^ es` in place of `4`).
* `IsRounded p es x c`: `c` is the magnitude code that the rounding rule of the Posit Standard
  (2022), §4.1, assigns to the positive rational `x`. A value at or below the least positive
  value gets the least code and one at or above the greatest value the greatest code (rule 2).
  Otherwise `x` lies between the values, in the format with one more payload bit, of the two
  codes next to `2 * c`, and `c` is even when `x` is one of these two midpoints (rules 3 to 6).
  A value that a code represents gets that code (rule 1, `isRounded_value`).
* `IsRounded.unique`: at most one code satisfies the rule, so it is a specification.
* `IsRoundedTo p es q a`: the encoding `a` is the rounding of the rational `q` of any sign: zero
  for zero, the rounded code for a positive number, and the two's complement of the rounded
  code of `-q` for a negative one. `IsRoundedTo.unique`, `isRoundedTo_toRat?`.
* `encode_isRounded` and `withSign_encode_isRoundedTo`: the rounding `KernelPath.encode` of a
  positive dyadic number satisfies the rule, and so does its signed form.

`General.Arithmetic` proves that each kernel operation returns the encoding that this
specification names.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Floats.Formats.Posit.KernelPath

/-! ## Values of codes -/

/-- A code and its double, in the format with one more payload bit, have the same value. -/
theorem value_succ {p es m : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    value (p + 1) es (2 * m) = value p es m := by
  have h1 := pos_code (es := es) (Nat.succ_pos p) (show 0 < 2 * m by omega)
    (show 2 * m < 2 ^ (p + 1) by rw [pow_succ]; omega)
  have h2 := pos_code (es := es) hp hm0 hm
  have h3 := pos_succ p es (codeRegime p m) (fieldTail es m (tailLength p m))
  have h : pos (p + 1) es (codeRegime (p + 1) (2 * m))
        (fieldTail es (2 * m) (tailLength (p + 1) (2 * m))) =
      pos (p + 1) es (codeRegime p m) (fieldTail es m (tailLength p m)) := by
    rw [h1, h3, h2]
    push_cast
    ring
  exact (pos_eq_pos_iff (fieldTail_nonneg _ _ _) (fieldTail_lt _ _ _) (fieldTail_nonneg _ _ _)
    (fieldTail_lt _ _ _)).mp h

/-- Codes are ordered as their values. -/
theorem value_lt_value_iff {p es m m' : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p)
    (hm0' : 0 < m') (hm' : m' < 2 ^ p) : value p es m < value p es m' ↔ m < m' := by
  constructor
  · intro h
    by_contra hle
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hle) with heq | hlt
    · rw [heq] at h
      exact lt_irrefl _ h
    · exact lt_asymm h (value_strictMono hp hm0' hlt hm)
  · exact fun h => value_strictMono hp hm0 h hm'

/-- Codes are ordered as their values, weakly. -/
theorem value_le_value_iff {p es m m' : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p)
    (hm0' : 0 < m') (hm' : m' < 2 ^ p) : value p es m ≤ value p es m' ↔ m ≤ m' := by
  rw [← not_lt, ← Nat.not_lt, value_lt_value_iff hp hm0' hm' hm0 hm]

/-- Two codes with the same value are equal. -/
theorem value_injective {p es m m' : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p)
    (hm0' : 0 < m') (hm' : m' < 2 ^ p) (h : value p es m = value p es m') : m = m' :=
  Nat.le_antisymm ((value_le_value_iff hp hm0 hm hm0' hm').mp h.le)
    ((value_le_value_iff hp hm0' hm' hm0 hm).mp h.ge)

/-! ## The value of an encoding -/

/--
The value of the encoding `a` of a format with `p` payload bits and `es` exponent bits: none for
NaR, zero for zero, the value of the magnitude code below the sign bit, and minus the value of
the two's complement in `p + 1` bits from the sign bit on.
-/
def toRat? (p es a : ℕ) : Option ℚ :=
  if a = 2 ^ p then none
  else if a = 0 then some 0
  else if a < 2 ^ p then some (value p es a)
  else some (-value p es (2 ^ (p + 1) - a))

/-- NaR has no value. -/
theorem toRat?_nar (p es : ℕ) : toRat? p es (2 ^ p) = none := by
  simp [toRat?]

/-- Zero has the value zero. -/
theorem toRat?_zero (p es : ℕ) : toRat? p es 0 = some 0 := by
  have : (0 : ℕ) ≠ 2 ^ p := (Nat.two_pow_pos p).ne
  simp [toRat?, this]

/-- An encoding other than NaR has a value. -/
theorem exists_toRat? {p a : ℕ} (es : ℕ) (ha : a ≠ 2 ^ p) : ∃ x, toRat? p es a = some x := by
  unfold toRat?
  rw [ite_eq_right ha]
  split_ifs <;> exact ⟨_, rfl⟩

/-- An encoding with a value is not NaR. -/
theorem ne_nar_of_toRat? {p es a : ℕ} {x : ℚ} (h : toRat? p es a = some x) : a ≠ 2 ^ p := by
  rintro rfl
  rw [toRat?_nar] at h
  exact absurd h (by simp)

/-- A positive encoding has the value of its code. -/
theorem toRat?_of_lt {p es a : ℕ} (ha0 : a ≠ 0) (ha : a < 2 ^ p) :
    toRat? p es a = some (value p es a) := by
  unfold toRat?
  rw [ite_eq_right (Nat.ne_of_lt ha), ite_eq_right ha0, ite_eq_left ha]

/-- A negative encoding has minus the value of its two's complement. -/
theorem toRat?_of_gt {p es a : ℕ} (ha : 2 ^ p < a) :
    toRat? p es a = some (-value p es (2 ^ (p + 1) - a)) := by
  have := Nat.two_pow_pos p
  unfold toRat?
  rw [ite_eq_right (Nat.ne_of_gt ha), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- The value of an encoding is zero exactly for the zero encoding. -/
theorem toRat?_eq_zero_iff {p es a : ℕ} : toRat? p es a = some 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha0
    have hnar := ne_nar_of_toRat? h
    rcases Nat.lt_or_gt_of_ne hnar with hlt | hgt
    · rw [toRat?_of_lt ha0 hlt] at h
      have := value_pos p es a
      simp only [Option.some.injEq] at h
      linarith
    · rw [toRat?_of_gt hgt] at h
      have := value_pos p es (2 ^ (p + 1) - a)
      simp only [Option.some.injEq] at h
      linarith
  · rintro rfl
    exact toRat?_zero p es

/-! ## The rounding rule -/

/--
The rounding rule of the Posit Standard (2022), §4.1, with `es` exponent bits: `c` is the
magnitude code of the positive rational `x` in the format with `p` payload bits. `c` is a
positive magnitude code; a value at or below the least positive value has the least code and
one at or above the greatest value the greatest code; any other value lies between the values,
in the format with one more payload bit, of the codes `2 * c - 1` and `2 * c + 1`, and `c` is
even when `x` is one of these two.
-/
structure IsRounded (p es : ℕ) (x : ℚ) (c : ℕ) : Prop where
  /-- The code is not zero. -/
  pos : 0 < c
  /-- The code is below the sign bit. -/
  lt : c < 2 ^ p
  /-- A value at or below the least positive value has the least code. -/
  low : x ≤ value p es 1 → c = 1
  /-- A value at or above the greatest value has the greatest code. -/
  high : value p es (2 ^ p - 1) ≤ x → c = 2 ^ p - 1
  /-- Any other value lies between the two midpoints next to its code, with ties to the even
  code. -/
  between : value p es 1 < x → x < value p es (2 ^ p - 1) →
    value (p + 1) es (2 * c - 1) ≤ x ∧ x ≤ value (p + 1) es (2 * c + 1) ∧
      (x = value (p + 1) es (2 * c - 1) ∨ x = value (p + 1) es (2 * c + 1) → Even c)

/-- Two codes of one value under the rule cannot be in increasing order. -/
private theorem IsRounded.not_lt {p es : ℕ} {x : ℚ} {c c' : ℕ}
    (h : IsRounded p es x c) (h' : IsRounded p es x c') (hlo : value p es 1 < x)
    (hhi : x < value p es (2 ^ p - 1)) : ¬c < c' := by
  intro hlt
  obtain ⟨-, h2, h3⟩ := h.between hlo hhi
  obtain ⟨h1', -, h3'⟩ := h'.between hlo hhi
  have := h.pos
  have := h'.lt
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hle : value (p + 1) es (2 * c + 1) ≤ value (p + 1) es (2 * c' - 1) :=
    (value_le_value_iff (Nat.succ_pos p) (by omega) (by omega) (by omega) (by omega)).mpr
      (by omega)
  have hx1 : x = value (p + 1) es (2 * c + 1) := le_antisymm h2 (hle.trans h1')
  have hx2 : x = value (p + 1) es (2 * c' - 1) := le_antisymm (h2.trans hle) h1'
  have : 2 * c + 1 = 2 * c' - 1 :=
    value_injective (Nat.succ_pos p) (by omega) (by omega) (by omega) (by omega)
      (hx1.symm.trans hx2)
  have he : Even c := h3 (Or.inr hx1)
  have he' : Even c' := h3' (Or.inl hx2)
  have hcc : c' = c + 1 := by omega
  rw [hcc, Nat.even_add_one] at he'
  exact he' he

/-- The rounding rule assigns at most one code to a value. -/
theorem IsRounded.unique {p es : ℕ} {x : ℚ} {c c' : ℕ} (h : IsRounded p es x c)
    (h' : IsRounded p es x c') : c = c' := by
  by_cases hlo : x ≤ value p es 1
  · rw [h.low hlo, h'.low hlo]
  by_cases hhi : value p es (2 ^ p - 1) ≤ x
  · rw [h.high hhi, h'.high hhi]
  rcases Nat.lt_trichotomy c c' with hlt | heq | hgt
  · exact absurd hlt (h.not_lt h' (not_le.mp hlo) (not_le.mp hhi))
  · exact heq
  · exact absurd hgt (h'.not_lt h (not_le.mp hlo) (not_le.mp hhi))

/-- Posit Standard (2022), §4.1, rule 1, for every number of exponent bits: the value of a
magnitude code is rounded to that code. -/
theorem isRounded_value {p es m : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    IsRounded p es (value p es m) m := by
  have : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  refine ⟨hm0, hm, fun h => ?_, fun h => ?_, fun _ _ => ?_⟩
  · have := (value_le_value_iff hp hm0 hm Nat.one_pos (by omega)).mp h
    omega
  · have := (value_le_value_iff hp (by omega) (by omega) hm0 hm).mp h
    omega
  · rw [← value_succ hp hm0 hm]
    have h1 : value (p + 1) es (2 * m - 1) < value (p + 1) es (2 * m) :=
      value_strictMono (Nat.succ_pos p) (by omega) (by omega) (by omega)
    have h2 : value (p + 1) es (2 * m) < value (p + 1) es (2 * m + 1) :=
      value_strictMono (Nat.succ_pos p) (by omega) (by omega) (by omega)
    exact ⟨h1.le, h2.le, fun h => by rcases h with h | h <;> linarith⟩

/-- The rounding of a positive dyadic number by `encode` satisfies the rounding rule, for every
number of payload bits, every number of exponent bits and every input. -/
theorem encode_isRounded {p es bK M E : ℕ} (hp : 0 < p) (hM : M ≠ 0) :
    IsRounded p es ((M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)) (encode p es bK M E) := by
  have : 2 ≤ 2 ^ p := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hp
    simpa using this
  obtain ⟨hpos, hlt⟩ := encode_range (es := es) (bK := bK) (E := E) hp hM
  have ht0 := tail_nonneg es M E
  have ht := tail_lt hM es E
  have hval := val_dyadic hM es bK E
  refine ⟨hpos, hlt, encode_of_le_value_one hp hM, encode_of_value_max_le hp hM,
    fun hlo hhi => ?_⟩
  refine encode_between hp hM ?_ ?_
  · by_contra hk
    have h1 := pos_lt_one hp (not_lt.mp hk) ht
    have hcode := pos_code (es := es) hp Nat.one_pos (show 1 < 2 ^ p by omega)
    rw [Nat.cast_one] at hcode
    rw [← hcode] at h1
    have h2 := (pos_lt_pos_iff ht0 ht (fieldTail_nonneg _ _ _) (fieldTail_lt _ _ _)).mp h1
    rw [hval] at h2
    exact lt_asymm hlo h2
  · by_contra hk
    have h1 := le_pos (es := es) hp (not_lt.mp hk) ht0
    have h2 := pos_code (es := es) hp (show 0 < 2 ^ p - 1 by omega) (by omega)
    rw [Nat.cast_sub (by omega)] at h2
    push_cast at h2
    rw [← h2] at h1
    have h3 := (pos_lt_pos_iff ht0 ht (fieldTail_nonneg _ _ _) (fieldTail_lt _ _ _)).not.mp
      (not_lt.mpr h1)
    rw [hval] at h3
    exact h3 hhi

/-! ## Rounding with a sign -/

/--
The encoding `a` is the rounding of the rational `q`: the zero encoding for zero, the rounded
magnitude code for a positive number, and the two's complement in `p + 1` bits of the rounded
code of `-q` for a negative one.
-/
def IsRoundedTo (p es : ℕ) (q : ℚ) (a : ℕ) : Prop :=
  (q = 0 → a = 0) ∧ (0 < q → IsRounded p es q a) ∧
    (q < 0 → ∃ c, IsRounded p es (-q) c ∧ a = 2 ^ (p + 1) - c)

/-- A rational has at most one rounding. -/
theorem IsRoundedTo.unique {p es : ℕ} {q : ℚ} {a a' : ℕ}
    (h : IsRoundedTo p es q a) (h' : IsRoundedTo p es q a') : a = a' := by
  rcases lt_trichotomy q 0 with hq | hq | hq
  · obtain ⟨c, hc, rfl⟩ := h.2.2 hq
    obtain ⟨c', hc', rfl⟩ := h'.2.2 hq
    rw [hc.unique hc']
  · rw [h.1 hq, h'.1 hq]
  · exact (h.2.1 hq).unique (h'.2.1 hq)

/-- Zero is rounded to the zero encoding. -/
theorem isRoundedTo_zero (p es : ℕ) : IsRoundedTo p es 0 0 :=
  ⟨fun _ => rfl, fun h => absurd h (lt_irrefl _), fun h => absurd h (lt_irrefl _)⟩

/-- The rounding of a positive number is the rounding of its magnitude. -/
theorem isRoundedTo_of_pos {p es : ℕ} {q : ℚ} {c : ℕ} (hq : 0 < q) (h : IsRounded p es q c) :
    IsRoundedTo p es q c :=
  ⟨fun h0 => absurd h0 hq.ne', fun _ => h, fun hneg => absurd hq (not_lt.mpr hneg.le)⟩

/-- The rounding of a negative number is the two's complement of the rounding of its
magnitude. -/
theorem isRoundedTo_of_neg {p es : ℕ} {q : ℚ} {c : ℕ} (hq : q < 0) (h : IsRounded p es (-q) c) :
    IsRoundedTo p es q (2 ^ (p + 1) - c) :=
  ⟨fun h0 => absurd h0 hq.ne, fun hpos => absurd hq (not_lt.mpr hpos.le), fun _ => ⟨c, h, rfl⟩⟩

/-- A value that an encoding represents is rounded to that encoding: the rounding rule returns
every representable value unchanged, for every sign. -/
theorem isRoundedTo_toRat? {p es a : ℕ} {x : ℚ} (hp : 0 < p) (ha : a < 2 ^ (p + 1))
    (h : toRat? p es a = some x) : IsRoundedTo p es x a := by
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  have hnar := ne_nar_of_toRat? h
  by_cases ha0 : a = 0
  · subst ha0
    rw [toRat?_zero] at h
    simp only [Option.some.injEq] at h
    rw [← h]
    exact isRoundedTo_zero p es
  rcases Nat.lt_or_gt_of_ne hnar with hlt | hgt
  · rw [toRat?_of_lt ha0 hlt] at h
    simp only [Option.some.injEq] at h
    rw [← h]
    exact isRoundedTo_of_pos (value_pos p es a) (isRounded_value hp (Nat.pos_of_ne_zero ha0) hlt)
  · rw [toRat?_of_gt hgt] at h
    simp only [Option.some.injEq] at h
    rw [← h]
    have hc : IsRounded p es (-(-value p es (2 ^ (p + 1) - a))) (2 ^ (p + 1) - a) := by
      rw [neg_neg]
      exact isRounded_value hp (by omega) (by omega)
    have hres := isRoundedTo_of_neg (neg_lt_zero.mpr (value_pos p es (2 ^ (p + 1) - a))) hc
    rwa [show 2 ^ (p + 1) - (2 ^ (p + 1) - a) = a by omega] at hres

/-! ## The signed form of `encode` -/

/-- The sign factor of a sign bit: one for a clear bit and minus one for a set bit. -/
def signFactor (s : ℕ) : ℚ := if s = 0 then 1 else -1

/-- `withSign` on a sign bit and a magnitude code: the code itself, or its two's complement in
`p + 1` bits. -/
theorem withSign_eq_ite (p s c : ℕ) :
    withSign p s c = if s = 0 then c else 2 ^ (p + 1) - c := by
  unfold withSign
  kernel_notation

/-- A rounded magnitude code with a sign bit is the rounding of the signed number, for every
sign bit. -/
theorem withSign_isRoundedTo {p es : ℕ} {x : ℚ} {c : ℕ} (s : ℕ) (hx : 0 < x)
    (h : IsRounded p es x c) : IsRoundedTo p es (signFactor s * x) (withSign p s c) := by
  rw [withSign_eq_ite]
  unfold signFactor
  by_cases hs : s = 0
  · rw [ite_eq_left hs, ite_eq_left hs, one_mul]
    exact isRoundedTo_of_pos hx h
  · rw [ite_eq_right hs, ite_eq_right hs]
    refine isRoundedTo_of_neg (by linarith) ?_
    rwa [neg_mul, neg_neg, one_mul]

/-- The signed rounding of a nonzero dyadic number by `encode` and `withSign` is its rounding,
for every sign bit, every number of payload bits and every number of exponent bits. -/
theorem withSign_encode_isRoundedTo {p es bK M E : ℕ} (s : ℕ) (hp : 0 < p) (hM : M ≠ 0) :
    IsRoundedTo p es (signFactor s * ((M : ℚ) * 2 ^ ((E : ℤ) - (bK : ℤ) * 2 ^ es)))
      (withSign p s (encode p es bK M E)) :=
  withSign_isRoundedTo s (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hM) (zpow_pos two_pos _))
    (encode_isRounded hp hM)

/-- A rounding is an encoding below the modulus. -/
theorem IsRoundedTo.lt {p es : ℕ} {q : ℚ} {a : ℕ} (h : IsRoundedTo p es q a) :
    a < 2 ^ (p + 1) := by
  have := Nat.two_pow_pos p
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  rcases lt_trichotomy q 0 with hq | hq | hq
  · obtain ⟨c, hc, rfl⟩ := h.2.2 hq
    have := hc.pos
    omega
  · rw [h.1 hq]
    omega
  · have := (h.2.1 hq).lt
    omega

/-- A rounding is never NaR. -/
theorem IsRoundedTo.ne_nar {p es : ℕ} {q : ℚ} {a : ℕ} (h : IsRoundedTo p es q a) :
    a ≠ 2 ^ p := by
  have := Nat.two_pow_pos p
  have : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ, Nat.mul_comm]
  rcases lt_trichotomy q 0 with hq | hq | hq
  · obtain ⟨c, hc, rfl⟩ := h.2.2 hq
    have := hc.pos
    have := hc.lt
    omega
  · rw [h.1 hq]
    omega
  · have := (h.2.1 hq).lt
    omega

end FloatLib.Floats.Formats.Posit.General
