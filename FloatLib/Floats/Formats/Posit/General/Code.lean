/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.General.Rounding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Posits with any number of exponent bits: the codes

A FloatLib extension beyond the Posit Standard (2022), which fixes `es = 2`. A positive magnitude
code `m` (`0 < m < 2 ^ p`) of a format with `p` payload bits and `es` exponent bits is read by
`KernelPath.tailLength`, `KernelPath.significand` and `KernelPath.exponent`. This module proves
what those fields denote, for every `p` and every `es`.

* `codeRegime p m` and `fieldTail es m z` are the regime and the tail of the code: the run of
  identical bits, and the exponent field (with its missing low bits read as zeros) plus the
  fraction. `value p es m` is `General.val` of that pair: the value of the code (Posit Standard
  (2022), §3.2.2, with `2 ^ es` in place of `4`).
* `value_eq_fields`: the value is `significand * 2 ^ (exponent - bias)`, the number that the
  kernel operations compute with.
* `pos_code`: the position of the value of a code is the code. So the codes are the integer
  positions, and by `General.pos_lt_pos_iff` they are ordered as their values:
  `value_strictMono`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Numerics.Kernel

/-- `complement p m` is `m` below `2 ^ (p - 1)` and the complement in `p` bits otherwise. -/
theorem complement_eq (p m : Nat) :
    complement p m = if 2 ^ (p - 1) ≤ m then 2 ^ p - 1 - m else m := by
  unfold complement
  kernel_notation

/-- The complement of a `p`-bit magnitude has at most `p` bits. -/
theorem complement_lt {p m : Nat} (hm : m < 2 ^ p) : complement p m < 2 ^ p := by
  rw [complement_eq]
  split_ifs <;> omega

/-- `tailLength p m` is the bit length of `complement p m`. -/
theorem tailLength_eq {p m : Nat} (hm : m < 2 ^ p) :
    tailLength p m = if complement p m = 0 then 0 else (complement p m).log2 + 1 :=
  bitLength_eq (complement_lt hm)

/-- The regime complement of a `p`-bit magnitude has at most `p` bits. -/
theorem tailLength_le {p m : Nat} (hm : m < 2 ^ p) : tailLength p m ≤ p := by
  rw [tailLength_eq hm]
  split_ifs with h
  · omega
  · exact (Nat.log2_lt h).2 (complement_lt hm)

/-- `tailLength p m` is the number of binary digits of `complement p m`. -/
theorem tailLength_eq_size {p m : Nat} (hm : m < 2 ^ p) :
    tailLength p m = Nat.size (complement p m) := by
  rw [tailLength_eq hm, ← size_eq_log2, size_eq]

/-- The significand of a magnitude: the leading one and the `z - 1 - es` fraction bits. -/
theorem significand_eq (es m z : Nat) :
    significand es m z = 2 ^ (z - 1 - es) + m % 2 ^ (z - 1 - es) := by
  unfold significand fractionBits
  kernel_notation

/-- A decoded significand has its leading one, so it is not zero. -/
theorem significand_ne_zero (es m z : Nat) : significand es m z ≠ 0 := by
  unfold significand
  kernel_notation
  have := Nat.two_pow_pos (fractionBits es z)
  omega

/-- The biased exponent of a magnitude: the biased regime times `2 ^ es`, plus the exponent
field with its missing low bits as zeros, minus the number of fraction bits. -/
theorem exponent_eq (p es m z : Nat) :
    exponent p es m z =
      (if 2 ^ (p - 1) ≤ m then regimeBias p + p - z - 1 else regimeBias p + z - p) * 2 ^ es +
          m / 2 ^ (z - 1 - es) % 2 ^ min es (z - 1) * 2 ^ (es - min es (z - 1)) -
        (z - 1 - es) := by
  unfold exponent
  kernel_notation

/-- The exponent bias is `8 * (p + 1) * 2 ^ es`. -/
theorem bias_eq_mul (p es : Nat) : bias p es = 8 * (p + 1) * 2 ^ es := by
  unfold bias regimeBias
  kernel_notation

/-- The comparison key of an encoding below the modulus: the encoding plus the sign bit below
the sign bit, and minus it from the sign bit on. -/
theorem signedKey_eq {p a : Nat} (ha : a < 2 ^ (p + 1)) :
    signedKey p a = if a < 2 ^ p then a + 2 ^ p else a - 2 ^ p := by
  have hpos := Nat.two_pow_pos p
  unfold signedKey nar
  kernel_notation
  rw [Nat.pow_succ] at ha ⊢
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

end FloatLib.Floats.Formats.Posit.KernelPath

namespace FloatLib.Floats.Formats.Posit.General

open FloatLib.Floats.Formats.Posit.KernelPath

/-- The regime of a positive magnitude code: `p - z - 1` for a run of ones and `z - p` for a run
of zeros, with `z = tailLength p m` the number of bits from the regime terminator on. -/
def codeRegime (p m : ℕ) : ℤ :=
  if 2 ^ (p - 1) ≤ m then (p : ℤ) - (tailLength p m : ℤ) - 1 else (tailLength p m : ℤ) - (p : ℤ)

/-- The tail of a magnitude code whose regime terminator is followed by `z - 1` bits: the
exponent field, with its missing low bits read as zeros, plus the fraction. -/
def fieldTail (es m z : ℕ) : ℚ :=
  ((m / 2 ^ (z - 1 - es) % 2 ^ min es (z - 1) * 2 ^ (es - min es (z - 1)) : ℕ) : ℚ) +
    ((m % 2 ^ (z - 1 - es) : ℕ) : ℚ) / 2 ^ (z - 1 - es)

/-- The value of the positive magnitude code `m` in a format with `p` payload bits and `es`
exponent bits. -/
def value (p es m : ℕ) : ℚ := val es (codeRegime p m) (fieldTail es m (tailLength p m))

/-- Every code has a positive value. -/
theorem value_pos (p es m : ℕ) : 0 < value p es m := val_pos _ _ _

/-- The tail of a code is not negative. -/
theorem fieldTail_nonneg (es m z : ℕ) : 0 ≤ fieldTail es m z := by
  unfold fieldTail
  positivity

/-- The bits after the regime terminator are the tail: `2 ^ (z - 1) * tail` is those `z - 1` bits
times `2 ^ es`. -/
theorem two_pow_mul_fieldTail (es m z : ℕ) :
    (2 : ℚ) ^ (z - 1) * fieldTail es m z = ((m % 2 ^ (z - 1) : ℕ) : ℚ) * 2 ^ es := by
  unfold fieldTail
  by_cases h : es ≤ z - 1
  · obtain ⟨fb, hfb⟩ : ∃ fb, z - 1 = fb + es := ⟨z - 1 - es, by omega⟩
    have hmin : min es (z - 1) = es := by omega
    have hsub : z - 1 - es = fb := by omega
    have hmod : m % 2 ^ (fb + es) = m % 2 ^ fb + 2 ^ fb * (m / 2 ^ fb % 2 ^ es) := by
      rw [pow_add, Nat.mod_mul]
    have hmodq : ((m % 2 ^ (fb + es) : ℕ) : ℚ) =
        ((m % 2 ^ fb : ℕ) : ℚ) + 2 ^ fb * ((m / 2 ^ fb % 2 ^ es : ℕ) : ℚ) := by
      exact_mod_cast hmod
    rw [hmin, hsub, hfb, hmodq, Nat.sub_self, pow_zero, Nat.mul_one, pow_add]
    field_simp
    ring
  · obtain ⟨d, hd⟩ : ∃ d, es = (z - 1) + d := ⟨es - (z - 1), by omega⟩
    have hmin : min es (z - 1) = z - 1 := by omega
    have hsub : z - 1 - es = 0 := by omega
    have hsub' : es - (z - 1) = d := by omega
    rw [hmin, hsub, hsub', pow_zero, Nat.div_one, Nat.mod_one]
    conv_rhs => rw [hd, pow_add]
    push_cast
    ring

/-- The tail of a code is below `2 ^ es`. -/
theorem fieldTail_lt (es m z : ℕ) : fieldTail es m z < 2 ^ es := by
  have h := two_pow_mul_fieldTail es m z
  have hpos : (0 : ℚ) < 2 ^ (z - 1) := by positivity
  have hmod : ((m % 2 ^ (z - 1) : ℕ) : ℚ) < 2 ^ (z - 1) := by
    exact_mod_cast Nat.mod_lt m (Nat.two_pow_pos (z - 1))
  have hes : (0 : ℚ) < 2 ^ es := by positivity
  by_contra hge
  rw [not_lt] at hge
  nlinarith

/--
The shape of a positive magnitude code with `z = tailLength p m`. Below `2 ^ (p - 1)` the code is
`2 ^ (z - 1)` plus its low `z - 1` bits, with `1 ≤ z ≤ p - 1`. From `2 ^ (p - 1)` on, `z ≤ p - 1`,
the code with `z = 0` is `2 ^ p - 1`, and otherwise the code is `2 ^ p - 2 ^ z` plus its low
`z - 1` bits.
-/
theorem code_cases {p m : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    (m < 2 ^ (p - 1) ∧ 1 ≤ tailLength p m ∧ tailLength p m ≤ p - 1 ∧
        m = 2 ^ (tailLength p m - 1) + m % 2 ^ (tailLength p m - 1)) ∨
      (2 ^ (p - 1) ≤ m ∧ tailLength p m ≤ p - 1 ∧ (tailLength p m = 0 → m = 2 ^ p - 1) ∧
        (1 ≤ tailLength p m → 2 ^ tailLength p m ≤ 2 ^ p ∧
          m = 2 ^ p - 2 ^ tailLength p m + m % 2 ^ (tailLength p m - 1))) := by
  have hpp : 2 ^ p = 2 * 2 ^ (p - 1) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_comm]
  rw [tailLength_eq_size hm, complement_eq]
  by_cases htop : 2 ^ (p - 1) ≤ m
  · right
    rw [ite_eq_left htop]
    have hclt : 2 ^ p - 1 - m < 2 ^ (p - 1) := by omega
    generalize hc : 2 ^ p - 1 - m = c at hclt ⊢
    have hz : Nat.size c ≤ p - 1 := Nat.size_le.mpr hclt
    refine ⟨htop, hz, fun h0 => ?_, fun h1 => ?_⟩
    · have : c = 0 := Nat.size_eq_zero.mp h0
      omega
    · have hc0 : c ≠ 0 := by
        intro h
        rw [h] at h1
        simp at h1
      obtain ⟨hb1, hb2⟩ := size_bounds hc0
      obtain ⟨w, hw⟩ : ∃ w, Nat.size c = w + 1 := ⟨Nat.size c - 1, by omega⟩
      rw [hw] at hb1 hb2 hz ⊢
      simp only [Nat.add_sub_cancel] at hb1 hb2 ⊢
      obtain ⟨d, hd⟩ : ∃ d, p = w + 1 + (d + 1) := ⟨p - (w + 1) - 1, by omega⟩
      have hpw : 2 ^ p = 2 ^ w * (2 * 2 ^ (d + 1)) := by
        rw [hd]
        ring
      have hzw : 2 ^ (w + 1) = 2 ^ w * 2 := pow_succ 2 w
      have hA : 0 < 2 ^ w := Nat.two_pow_pos w
      have hD : 2 ≤ 2 ^ (d + 1) := by
        have := Nat.two_pow_pos d
        rw [pow_succ]
        omega
      refine ⟨Nat.pow_le_pow_right (by decide) (by omega), ?_⟩
      rw [hzw] at hb2 ⊢
      rw [hpw] at hc ⊢
      generalize 2 ^ w = A at hA hb1 hb2 hc ⊢
      generalize 2 ^ (d + 1) = D at hD hc ⊢
      have hmul : A * (2 * D - 2) = A * (2 * D) - A * 2 := Nat.mul_sub A (2 * D) 2
      have hle : A * 2 ≤ A * (2 * D) := Nat.mul_le_mul_left A (by omega)
      have hmc : m = A * (2 * D - 2) + (A * 2 - 1 - c) := by omega
      have hmod : m % A = A * 2 - 1 - c := by
        rw [hmc, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      omega
  · left
    rw [ite_eq_right htop]
    have hm0' : m ≠ 0 := by omega
    obtain ⟨hb1, hb2⟩ := size_bounds hm0'
    have hz : Nat.size m ≤ p - 1 := Nat.size_le.mpr (by omega)
    have hz1 : 1 ≤ Nat.size m := Nat.size_pos.mpr hm0
    refine ⟨by omega, hz1, hz, ?_⟩
    rw [pow_succ] at hb2
    have hmod : m % 2 ^ (Nat.size m - 1) = m - 2 ^ (Nat.size m - 1) := by
      rw [Nat.mod_eq_sub_mod hb1, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The position of the value of a positive magnitude code is the code, for every number of
exponent bits. -/
theorem pos_code {p es m : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    pos p es (codeRegime p m) (fieldTail es m (tailLength p m)) = (m : ℚ) := by
  have hstar := two_pow_mul_fieldTail es m (tailLength p m)
  have hes : (0 : ℚ) < 2 ^ es := by positivity
  rcases code_cases hp hm0 hm with ⟨hlt, hz1, hzp, hmeq⟩ | ⟨hge, hzp, hz0, hz1⟩
  · have hk : codeRegime p m = (tailLength p m : ℤ) - (p : ℤ) := by
      unfold codeRegime
      rw [ite_eq_right (Nat.not_le.mpr hlt)]
    rw [hk]
    generalize tailLength p m = z at hz1 hzp hmeq hstar ⊢
    unfold pos
    rw [ite_eq_left (by omega)]
    have e1 : (p : ℤ) + ((z : ℤ) - (p : ℤ)) - 1 = ((z - 1 : ℕ) : ℤ) := by omega
    have hmq : (m : ℚ) = 2 ^ (z - 1) + ((m % 2 ^ (z - 1) : ℕ) : ℚ) := by exact_mod_cast hmeq
    rw [e1, zpow_natCast, mul_add, mul_one, ← mul_div_assoc, hstar, mul_div_assoc,
      div_self hes.ne', mul_one]
    exact hmq.symm
  · have hk : codeRegime p m = (p : ℤ) - (tailLength p m : ℤ) - 1 := by
      unfold codeRegime
      rw [ite_eq_left hge]
    rw [hk]
    generalize tailLength p m = z at hzp hz0 hz1 hstar ⊢
    unfold pos
    rw [ite_eq_right (by omega)]
    have e1 : (p : ℤ) - 1 - ((p : ℤ) - (z : ℤ) - 1) = (z : ℤ) := by omega
    rw [e1, zpow_natCast, zpow_natCast]
    rcases Nat.eq_zero_or_pos z with h0 | hpos
    · subst h0
      have ha : fieldTail es m 0 = 0 := by simpa [Nat.mod_one] using hstar
      have hm1 : m = 2 ^ p - 1 := hz0 rfl
      have hone : 1 ≤ 2 ^ p := Nat.one_le_two_pow
      rw [ha, hm1, Nat.cast_sub hone]
      push_cast
      ring
    · obtain ⟨hle, hmeq⟩ := hz1 hpos
      obtain ⟨w, rfl⟩ : ∃ w, z = w + 1 := ⟨z - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hstar hmeq
      have hmq : (m : ℚ) = 2 ^ p - 2 ^ (w + 1) + ((m % 2 ^ w : ℕ) : ℚ) := by
        calc (m : ℚ) = ((2 ^ p - 2 ^ (w + 1) + m % 2 ^ w : ℕ) : ℚ) := by rw [← hmeq]
          _ = 2 ^ p - 2 ^ (w + 1) + ((m % 2 ^ w : ℕ) : ℚ) := by
            rw [Nat.cast_add, Nat.cast_sub hle]
            push_cast
            rfl
      have hfield : fieldTail es m (w + 1) = ((m % 2 ^ w : ℕ) : ℚ) * 2 ^ es / 2 ^ w := by
        rw [← hstar]
        field_simp
      rw [hmq, hfield, pow_succ, pow_succ]
      field_simp
      ring

/-- The value of a positive magnitude code is strictly increasing in the code, for every number
of exponent bits: codes are ordered as their values (Posit Standard (2022), §3.2.2, for
`es = 2`). -/
theorem value_strictMono {p es m m' : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hmm : m < m')
    (hm' : m' < 2 ^ p) : value p es m < value p es m' := by
  refine (pos_lt_pos_iff (p := p) (fieldTail_nonneg _ _ _) (fieldTail_lt _ _ _)
    (fieldTail_nonneg _ _ _) (fieldTail_lt _ _ _)).mp ?_
  rw [pos_code hp hm0 (by omega), pos_code hp (by omega) hm']
  exact_mod_cast hmm

/-- The exponent field of a code is the integer part of its tail. -/
theorem floor_fieldTail (es m z : ℕ) :
    ⌊fieldTail es m z⌋ =
      ((m / 2 ^ (z - 1 - es) % 2 ^ min es (z - 1) * 2 ^ (es - min es (z - 1)) : ℕ) : ℤ) := by
  have hfrac : ((m % 2 ^ (z - 1 - es) : ℕ) : ℚ) / 2 ^ (z - 1 - es) < 1 := by
    rw [div_lt_one (by positivity)]
    exact_mod_cast Nat.mod_lt m (Nat.two_pow_pos _)
  have hfrac0 : (0 : ℚ) ≤ ((m % 2 ^ (z - 1 - es) : ℕ) : ℚ) / 2 ^ (z - 1 - es) := by positivity
  rw [Int.floor_eq_iff, Int.cast_natCast]
  unfold fieldTail
  constructor <;> linarith

/-- The regime of a magnitude code of `p` payload bits is between `-p - 1` and `p`. -/
theorem codeRegime_bounds {p m : ℕ} (hm : m < 2 ^ p) :
    -(p : ℤ) - 1 ≤ codeRegime p m ∧ codeRegime p m ≤ (p : ℤ) := by
  have h := tailLength_le hm
  unfold codeRegime
  split_ifs <;> omega

/--
The value of a positive magnitude code is the number that the kernel fields denote:
`significand * 2 ^ (exponent - bias)`, for every number of exponent bits.
-/
theorem value_eq_fields {p es m : ℕ} (hp : 0 < p) (hm0 : 0 < m) (hm : m < 2 ^ p) :
    value p es m = (significand es m (tailLength p m) : ℚ) *
      2 ^ ((exponent p es m (tailLength p m) : ℤ) - (bias p es : ℤ)) := by
  have hz : tailLength p m ≤ p - 1 := by
    rcases code_cases hp hm0 hm with h | h
    · exact h.2.2.1
    · exact h.2.1
  have hkb := codeRegime_bounds hm
  have hk : ((if 2 ^ (p - 1) ≤ m then regimeBias p + p - tailLength p m - 1
      else regimeBias p + tailLength p m - p : ℕ) : ℤ) = 8 * ((p : ℤ) + 1) + codeRegime p m := by
    have hb : regimeBias p = 8 * (p + 1) := rfl
    unfold codeRegime
    rw [hb]
    split_ifs <;> omega
  unfold value
  rw [significand_eq, exponent_eq, bias_eq_mul]
  have hfloor := floor_fieldTail es m (tailLength p m)
  have hfract : Int.fract (fieldTail es m (tailLength p m)) =
      ((m % 2 ^ (tailLength p m - 1 - es) : ℕ) : ℚ) / 2 ^ (tailLength p m - 1 - es) := by
    rw [← Int.self_sub_floor, hfloor, Int.cast_natCast]
    unfold fieldTail
    ring
  unfold val taper
  rw [hfloor, hfract]
  generalize codeRegime p m = k at hkb hk ⊢
  generalize tailLength p m = z at hz hk ⊢
  generalize hfb : z - 1 - es = fb
  generalize m / 2 ^ fb % 2 ^ min es (z - 1) * 2 ^ (es - min es (z - 1)) = e
  generalize (if 2 ^ (p - 1) ≤ m then regimeBias p + p - z - 1 else regimeBias p + z - p) = Kb
    at hk ⊢
  have hle : fb ≤ Kb * 2 ^ es + e := by
    have h1 : Kb ≤ Kb * 2 ^ es := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos es)
    omega
  have hexp : k * 2 ^ es + (e : ℤ) =
      ((Kb * 2 ^ es + e : ℕ) : ℤ) - (fb : ℤ) - ((8 * (p + 1) * 2 ^ es : ℕ) : ℤ) + (fb : ℤ) := by
    push_cast
    rw [hk]
    ring
  rw [Nat.cast_sub hle, ← mul_assoc, ← zpow_add₀ two_ne_zero, hexp, zpow_add₀ two_ne_zero,
    zpow_natCast]
  push_cast
  field_simp

end FloatLib.Floats.Formats.Posit.General
