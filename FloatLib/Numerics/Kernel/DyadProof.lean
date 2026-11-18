/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Dyad
public import FloatLib.Numerics.Kernel.FracProof

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# `Dyad` computes in the rationals

Every operation of `FloatLib.Numerics.Kernel.Dyad` is the rational operation on the values
`toRat`, for all dyadic numbers, and each rounding is on the stated side with a stated error.

* `toRat_eq`: `x.toRat = (x.plus - x.minus) / 2 ^ x.scale`; `toRat_ofNat`, `toRat_ofInt`,
  `toRat_ofSigned`, `toRat_ofScaled` (`z * 2 ^ e` with an integer exponent).
* `toRat_add`, `toRat_sub`, `toRat_neg`, `toRat_mul`, `toRat_mulPow2`, `toRat_divPow2`,
  `toRat_norm`.
* `le_iff`, `lt_iff`, `beq_iff`, `isNeg_iff`, and `le_cast`, `lt_cast` in any ordered field.
* `dropDown_le`, `sub_dropDown_le`: removing `k` bits downward gives a number that is at most
  `x` and at least `x - (2 ^ k - 1) / 2 ^ scale`; `le_dropUp`, `dropUp_sub_le` upward.
* `roundDown_le`, `lt_roundDown_add`, `le_roundUp`, `roundUp_lt_add`: rounding to multiples of
  `2 ^ (-p)` moves a number by less than `2 ^ (-p)`, in the stated direction.
* `trimDown_le`, `le_trimUp`: cutting the numerator to a number of bits rounds in the stated
  direction. No error bound is stated for them.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Dyad

/-- The rational of a dyadic number is its numerator over `2 ^ scale`. -/
theorem toRat_eq (x : Dyad) : x.toRat = ((x.plus : ℚ) - x.minus) / 2 ^ x.scale := by
  unfold toRat
  rw [Frac.toRat_eq]
  change ((x.plus : ℚ) - x.minus) / ((1 <<< x.scale : Nat) : ℚ) = _
  rw [Nat.one_shiftLeft, Nat.cast_pow, Nat.cast_ofNat]

/-- The rational of a dyadic number is the integer of its numerator over `2 ^ scale`. -/
theorem toRat_eq_num (x : Dyad) : x.toRat = (x.num.toInt : ℚ) / 2 ^ x.scale := by
  rw [toRat_eq, Signed.toInt_eq]
  simp [num]

/-- The rational of the record with the given fields. -/
@[simp] theorem toRat_mk (plus minus scale : Nat) :
    (Dyad.mk plus minus scale).toRat = ((plus : ℚ) - minus) / 2 ^ scale :=
  toRat_eq _

/-- `ofNat` is the cast of a natural number. -/
@[simp] theorem toRat_ofNat (n : Nat) : (ofNat n).toRat = n := by
  simp [ofNat]

/-- `ofSigned` is the cast of the integer of a pair. -/
@[simp] theorem toRat_ofSigned (z : Signed) : (ofSigned z).toRat = z.toInt := by
  simp [ofSigned, Signed.toInt_eq]

/-- `ofInt` is the cast of an integer. -/
@[simp] theorem toRat_ofInt (z : Int) : (ofInt z).toRat = z := by
  cases z with
  | ofNat n => simp [ofInt]
  | negSucc n =>
    simp only [ofInt, toRat_mk, Int.negSucc_eq]
    push_cast
    simp

/-- `ofScaled z e` is `z * 2 ^ e`, for a positive, zero or negative exponent. -/
@[simp] theorem toRat_ofScaled (z e : Int) : (ofScaled z e).toRat = z * 2 ^ e := by
  cases e with
  | ofNat k =>
    cases z with
    | ofNat n =>
      change (Dyad.mk (n <<< k) 0 0).toRat = _
      rw [toRat_mk, Nat.shiftLeft_eq]
      simp
    | negSucc n =>
      change (Dyad.mk 0 ((n + 1) <<< k) 0).toRat = _
      rw [toRat_mk, Nat.shiftLeft_eq, Int.negSucc_eq]
      simp only [Nat.cast_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
        Nat.cast_ofNat, zero_sub, pow_zero, div_one, neg_add_rev, Int.reduceNeg, Int.cast_add,
        Int.cast_neg, Int.cast_one, Int.cast_natCast, Int.ofNat_eq_natCast, zpow_natCast]
      ring
  | negSucc k =>
    have hpow : (2 : ℚ) ^ (Int.negSucc k) = 1 / 2 ^ (k + 1) := by
      rw [zpow_negSucc, one_div]
    cases z with
    | ofNat n =>
      change (Dyad.mk n 0 (k + 1)).toRat = _
      rw [toRat_mk, hpow]
      simp [div_eq_mul_inv]
    | negSucc n =>
      change (Dyad.mk 0 (n + 1) (k + 1)).toRat = _
      rw [toRat_mk, hpow, Int.negSucc_eq]
      push_cast
      ring

/-- `norm` keeps the number. -/
@[simp] theorem toRat_norm (x : Dyad) : x.norm.toRat = x.toRat := by
  simp only [norm, toRat_eq, Nat.sub_eq]
  rw [Frac.cast_sub_sub]

/-- Two aligned numerators over the common power of two are the sum of the two numbers. -/
private theorem align (p q : ℚ) {a b s t : Nat} (h : a + s = b + t) :
    (p * 2 ^ s + q * 2 ^ t) / 2 ^ (a + s) = p / 2 ^ a + q / 2 ^ b := by
  have hb : (2 : ℚ) ^ (a + s) = 2 ^ b * 2 ^ t := by rw [h, pow_add]
  rw [add_div]
  congr 1
  · rw [pow_add]
    field_simp
  · rw [hb]
    field_simp

/-- The exponents after alignment agree: both are the larger of the two scales. -/
theorem scale_align (a b : Nat) : a + (b - a) = b + (a - b) := by omega

/-- `add` is the sum of the rationals. -/
@[simp] theorem toRat_add (x y : Dyad) : (x.add y).toRat = x.toRat + y.toRat := by
  rw [toRat_eq x, toRat_eq y, ← align _ _ (scale_align x.scale y.scale), toRat_eq]
  change (((x.plus <<< (y.scale - x.scale) + y.plus <<< (x.scale - y.scale) -
      (x.minus <<< (y.scale - x.scale) + y.minus <<< (x.scale - y.scale)) : Nat) : ℚ) -
      ((x.minus <<< (y.scale - x.scale) + y.minus <<< (x.scale - y.scale) -
        (x.plus <<< (y.scale - x.scale) + y.plus <<< (x.scale - y.scale)) : Nat) : ℚ)) /
      2 ^ (x.scale + (y.scale - x.scale)) = _
  rw [Frac.cast_sub_sub]
  simp only [Nat.shiftLeft_eq]
  push_cast
  ring

/-- `neg` is the negation of the rational. -/
@[simp] theorem toRat_neg (x : Dyad) : x.neg.toRat = -x.toRat := by
  simp only [neg, toRat_eq]
  ring

/-- `sub` is the sum with the negation. -/
theorem sub_eq (x y : Dyad) : x.sub y = x.add y.neg := rfl

/-- `sub` is the difference of the rationals. -/
@[simp] theorem toRat_sub (x y : Dyad) : (x.sub y).toRat = x.toRat - y.toRat := by
  rw [sub_eq, toRat_add, toRat_neg, sub_eq_add_neg]

/-- `mul` is the product of the rationals. -/
@[simp] theorem toRat_mul (x y : Dyad) : (x.mul y).toRat = x.toRat * y.toRat := by
  simp only [mul, toRat_eq, Nat.add_eq, Nat.mul_eq]
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- `mulPow2` multiplies by `2 ^ k`. -/
@[simp] theorem toRat_mulPow2 (x : Dyad) (k : Nat) : (x.mulPow2 k).toRat = x.toRat * 2 ^ k := by
  have hscale : x.scale - k + k = x.scale + (k - x.scale) := by omega
  have hpow : (2 : ℚ) ^ (x.scale - k) * 2 ^ k = 2 ^ x.scale * 2 ^ (k - x.scale) := by
    rw [← pow_add, ← pow_add, hscale]
  simp only [toRat_eq]
  change (((x.plus <<< (k - x.scale) : Nat) : ℚ) - ((x.minus <<< (k - x.scale) : Nat) : ℚ)) /
    2 ^ (x.scale - k) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, div_eq_iff (NeZero.ne _)]
  push_cast
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, eq_div_iff (NeZero.ne _)]
  linear_combination (-((x.plus : ℚ) - x.minus)) * hpow

/-- `divPow2` divides by `2 ^ k`. -/
@[simp] theorem toRat_divPow2 (x : Dyad) (k : Nat) : (x.divPow2 k).toRat = x.toRat / 2 ^ k := by
  simp only [divPow2, toRat_eq, Nat.add_eq]
  rw [pow_add, div_div]

/-- A number over its own power of two, written over a larger one. -/
theorem toRat_lift (x : Dyad) (s : Nat) :
    x.toRat = ((x.plus : ℚ) - x.minus) * 2 ^ s / 2 ^ (x.scale + s) := by
  rw [toRat_eq, pow_add]
  field_simp

/-- `le` decides `≤` on the rationals. -/
theorem le_iff (x y : Dyad) : x.le y = true ↔ x.toRat ≤ y.toRat := by
  rw [toRat_lift x (y.scale - x.scale), toRat_lift y (x.scale - y.scale),
    ← scale_align x.scale y.scale, div_le_div_iff_of_pos_right (Rat.pow_pos rfl)]
  change Nat.ble (x.plus <<< (y.scale - x.scale) + y.minus <<< (x.scale - y.scale))
    (y.plus <<< (x.scale - y.scale) + x.minus <<< (y.scale - x.scale)) = true ↔ _
  rw [Nat.ble_eq, ← Nat.cast_le (α := ℚ)]
  simp only [Nat.shiftLeft_eq]
  push_cast
  constructor <;> intro h <;> linarith

/-- `lt` decides `<` on the rationals. -/
theorem lt_iff (x y : Dyad) : x.lt y = true ↔ x.toRat < y.toRat := by
  rw [toRat_lift x (y.scale - x.scale), toRat_lift y (x.scale - y.scale),
    ← scale_align x.scale y.scale, div_lt_div_iff_of_pos_right (Rat.pow_pos rfl)]
  change Nat.ble (x.plus <<< (y.scale - x.scale) + y.minus <<< (x.scale - y.scale) + 1)
    (y.plus <<< (x.scale - y.scale) + x.minus <<< (y.scale - x.scale)) = true ↔ _
  rw [Nat.ble_eq, Nat.succ_le_iff, ← Nat.cast_lt (α := ℚ)]
  simp only [Nat.shiftLeft_eq]
  push_cast
  constructor <;> intro h <;> linarith

/-- `beq` decides equality of the rationals. -/
theorem beq_iff (x y : Dyad) : x.beq y = true ↔ x.toRat = y.toRat := by
  rw [toRat_lift x (y.scale - x.scale), toRat_lift y (x.scale - y.scale),
    ← scale_align x.scale y.scale, div_left_inj₀ (NeZero.ne _)]
  change Nat.beq (x.plus <<< (y.scale - x.scale) + y.minus <<< (x.scale - y.scale))
    (y.plus <<< (x.scale - y.scale) + x.minus <<< (y.scale - x.scale)) = true ↔ _
  rw [Nat.beq_eq, ← Nat.cast_inj (R := ℚ)]
  simp only [Nat.shiftLeft_eq]
  push_cast
  constructor <;> intro h <;> linarith

/-- `isNeg` decides `x < 0`. -/
theorem isNeg_iff (x : Dyad) : x.isNeg = true ↔ x.toRat < 0 := by
  rw [toRat_eq, div_lt_iff₀ (by positivity), zero_mul]
  change Nat.ble (x.plus + 1) x.minus = true ↔ _
  rw [Nat.ble_eq, Nat.succ_le_iff, ← Nat.cast_lt (α := ℚ), sub_neg]

/-! ## Rounding -/

/-- The numerator of `dropDown`: the numerator divided by `2 ^ k` rounded down, shifted back. -/
theorem num_dropDown (x : Dyad) (k : Nat) :
    (x.dropDown k).num = (x.num.floorShift k).shiftLeft (k - x.scale) := rfl

/--
`dropDown k` is the numerator divided by `2 ^ k` rounded down, times `2 ^ k`, over the same
power of two.
-/
theorem toRat_dropDown (x : Dyad) (k : Nat) :
    (x.dropDown k).toRat =
      ((x.num.toInt / ((2 ^ k : Nat) : Int) : Int) : ℚ) * 2 ^ k / 2 ^ x.scale := by
  have hscale : k - x.scale + x.scale = k + (x.scale - k) := by omega
  have hpow : (2 : ℚ) ^ (k - x.scale) * 2 ^ x.scale = 2 ^ k * 2 ^ (x.scale - k) := by
    rw [← pow_add, ← pow_add, hscale]
  rw [toRat_eq_num, num_dropDown, Signed.toInt_shiftLeft, Signed.toInt_floorShift,
    Int.shiftRight_eq_div_pow]
  change _ / 2 ^ (x.scale - k) = _
  rw [div_eq_div_iff (NeZero.ne _) (NeZero.ne _)]
  push_cast
  linear_combination ((x.num.toInt / 2 ^ k : Int) : ℚ) * hpow

/-- Removing bits downward does not increase the number. -/
theorem dropDown_le (x : Dyad) (k : Nat) : (x.dropDown k).toRat ≤ x.toRat := by
  rw [toRat_dropDown, toRat_eq_num, div_le_div_iff_of_pos_right (Rat.pow_pos rfl)]
  have h := Int.ediv_mul_le x.num.toInt (b := ((2 ^ k : Nat) : Int)) (by positivity)
  have hcast := Int.cast_le (R := ℚ) |>.2 h
  push_cast at hcast ⊢
  exact hcast

/-- Removing `k` bits downward lowers the number by at most `(2 ^ k - 1) / 2 ^ scale`. -/
theorem sub_dropDown_le (x : Dyad) (k : Nat) :
    x.toRat - (x.dropDown k).toRat ≤ (2 ^ k - 1) / 2 ^ x.scale := by
  rw [toRat_dropDown, toRat_eq_num, ← sub_div, div_le_div_iff_of_pos_right (Rat.pow_pos rfl)]
  have hpos : (0 : Int) < ((2 ^ k : Nat) : Int) := by positivity
  have h := Int.lt_ediv_add_one_mul_self x.num.toInt hpos
  have hint : x.num.toInt - x.num.toInt / ((2 ^ k : Nat) : Int) * ((2 ^ k : Nat) : Int) ≤
      ((2 ^ k : Nat) : Int) - 1 := by
    rw [add_mul, one_mul] at h
    omega
  have hcast := Int.cast_le (R := ℚ) |>.2 hint
  push_cast at hcast ⊢
  exact hcast

/-- `dropUp` is `dropDown` of the negation, negated. -/
theorem dropUp_eq (x : Dyad) (k : Nat) : x.dropUp k = (x.neg.dropDown k).neg := rfl

/-- Removing bits upward does not decrease the number. -/
theorem le_dropUp (x : Dyad) (k : Nat) : x.toRat ≤ (x.dropUp k).toRat := by
  have h := dropDown_le x.neg k
  rw [toRat_neg] at h
  rw [dropUp_eq, toRat_neg]
  linarith

/-- Removing `k` bits upward raises the number by at most `(2 ^ k - 1) / 2 ^ scale`. -/
theorem dropUp_sub_le (x : Dyad) (k : Nat) :
    (x.dropUp k).toRat - x.toRat ≤ (2 ^ k - 1) / 2 ^ x.scale := by
  have h := sub_dropDown_le x.neg k
  rw [toRat_neg] at h
  rw [dropUp_eq, toRat_neg]
  exact le_trans (le_of_eq (by ring)) h

/-- What `roundDown p` and `roundUp p` move a number by is less than `2 ^ (-p)`. -/
private theorem drop_error_lt (s p : Nat) : ((2 : ℚ) ^ (s - p) - 1) / 2 ^ s < 1 / 2 ^ p := by
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  rcases Nat.le_total p s with h | h
  · have hs : (2 : ℚ) ^ s = 2 ^ (s - p) * 2 ^ p := by rw [← pow_add, Nat.sub_add_cancel h]
    have hp : (0 : ℚ) < 2 ^ p := Rat.pow_pos rfl
    rw [hs]
    exact mul_lt_mul_of_pos_right (sub_one_lt _) hp
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, sub_self, zero_mul]
    exact Rat.pow_pos rfl

/-- `roundDown p` does not increase the number. -/
theorem roundDown_le (x : Dyad) (p : Nat) : (x.roundDown p).toRat ≤ x.toRat :=
  dropDown_le x _

/-- `roundDown p` lowers the number by less than `2 ^ (-p)`. -/
theorem lt_roundDown_add (x : Dyad) (p : Nat) : x.toRat < (x.roundDown p).toRat + 1 / 2 ^ p := by
  have h := sub_dropDown_le x (x.scale - p)
  have herror := drop_error_lt x.scale p
  unfold roundDown
  change x.toRat < (x.dropDown (x.scale - p)).toRat + 1 / 2 ^ p
  linarith

/-- `roundUp p` does not decrease the number. -/
theorem le_roundUp (x : Dyad) (p : Nat) : x.toRat ≤ (x.roundUp p).toRat :=
  le_dropUp x _

/-- `roundUp p` raises the number by less than `2 ^ (-p)`. -/
theorem roundUp_lt_add (x : Dyad) (p : Nat) : (x.roundUp p).toRat < x.toRat + 1 / 2 ^ p := by
  have h := dropUp_sub_le x (x.scale - p)
  have herror := drop_error_lt x.scale p
  unfold roundUp
  change (x.dropUp (x.scale - p)).toRat < x.toRat + 1 / 2 ^ p
  linarith

/-- Cutting the numerator to a number of bits downward does not increase the number. -/
theorem trimDown_le (x : Dyad) (count : Nat) : (x.trimDown count).toRat ≤ x.toRat :=
  dropDown_le x _

/-- Cutting the numerator to a number of bits upward does not decrease the number. -/
theorem le_trimUp (x : Dyad) (count : Nat) : x.toRat ≤ (x.trimUp count).toRat :=
  le_dropUp x _

section Cast

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A passed `le` gives the inequality in any ordered field, the reals included. -/
theorem le_cast {x y : Dyad} (h : x.le y = true) : (x.toRat : K) ≤ (y.toRat : K) :=
  Rat.cast_le.2 ((le_iff x y).1 h)

/-- A passed `lt` gives the strict inequality in any ordered field. -/
theorem lt_cast {x y : Dyad} (h : x.lt y = true) : (x.toRat : K) < (y.toRat : K) :=
  Rat.cast_lt.2 ((lt_iff x y).1 h)

end Cast

end FloatLib.Numerics.Kernel.Dyad
