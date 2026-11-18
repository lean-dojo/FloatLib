/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Frac
public import FloatLib.Numerics.Kernel.SignedProof
public import Mathlib.Data.Rat.Floor

import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.Positivity

/-!
# `Frac` computes in the rationals

Every operation of `FloatLib.Numerics.Kernel.Frac` is the rational operation on the values
`toRat`, for all fractions: the positive denominator is part of the type, so no theorem has a side
condition.

* `toRat_eq`: `x.toRat = (x.plus - x.minus) / x.den`; `toRat_ofRat`, `toRat_ofInt`,
  `toRat_ofNat`, `toRat_ofSigned`, `toRat_ofScientific`.
* `toRat_add`, `toRat_sub`, `toRat_neg`, `toRat_mul`, `toRat_inv`, `toRat_div`, `toRat_pow`,
  `toRat_mulPow2`, `toRat_divPow2`, `toRat_normalize`.
* `le_iff`, `lt_iff`, `beq_iff`, `isNeg_iff`: the Boolean comparisons decide the order of the
  rationals, and `le_cast`, `lt_cast` state them in any ordered field, the reals included.
* `toInt_floor`, `toInt_ceil`: `floor` and `ceil` are `⌊x.toRat⌋` and `⌈x.toRat⌉`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Frac

/-- The two truncated differences of a pair of naturals differ by their difference. -/
theorem cast_sub_sub (a b : Nat) :
    ((a - b : Nat) : ℚ) - ((b - a : Nat) : ℚ) = (a : ℚ) - b := by
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]
    simp
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_sub h]
    simp

/-- The denominator is not zero as a rational. -/
theorem den_ne_zero (x : Frac) : (x.den : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.2 x.den_pos.ne'

/-- The denominator is positive as a rational. -/
theorem den_cast_pos (x : Frac) : (0 : ℚ) < x.den :=
  Nat.cast_pos.2 x.den_pos

/-- The rational of a fraction is its numerator over its denominator. -/
theorem toRat_eq (x : Frac) : x.toRat = ((x.plus : ℚ) - x.minus) / x.den := by
  unfold toRat
  rw [Rat.mkRat_eq_div, Signed.toInt_eq]
  simp [num]

/-- The rational of a fraction given by its three parts. -/
@[simp] theorem toRat_mk (plus minus den : Nat) (h : 0 < den) :
    (Frac.mk plus minus den h).toRat = ((plus : ℚ) - minus) / den :=
  toRat_eq _

/-- `ofNat n` stands for `n`. -/
@[simp] theorem toRat_ofNat (n : Nat) : (ofNat n).toRat = n := by
  simp [toRat_eq, ofNat]

/-- `ofSigned z` stands for the integer of `z`. -/
@[simp] theorem toRat_ofSigned (z : Signed) : (ofSigned z).toRat = z.toInt := by
  simp [toRat_eq, ofSigned, Signed.toInt_eq]

/-- The numerator of `ofInt z` is the pair of `z`. -/
theorem num_ofInt (z : Int) : (ofInt z).num = Signed.ofInt z := by
  cases z <;> rfl

/-- The denominator of `ofInt z` is one. -/
theorem den_ofInt (z : Int) : (ofInt z).den = 1 := by
  cases z <;> rfl

/-- `ofInt z` stands for `z`. -/
@[simp] theorem toRat_ofInt (z : Int) : (ofInt z).toRat = z := by
  unfold toRat
  rw [num_ofInt, den_ofInt, Signed.toInt_ofInt, Rat.mkRat_eq_div]
  simp

/-- The numerator of `ofRat q` is the pair of the numerator of `q`. -/
theorem num_ofRat (q : ℚ) : (ofRat q).num = Signed.ofInt q.num := by
  unfold ofRat
  cases q.num <;> rfl

/-- The denominator of `ofRat q` is the denominator of `q`. -/
theorem den_ofRat (q : ℚ) : (ofRat q).den = q.den := by
  unfold ofRat
  cases q.num <;> rfl

/-- `ofRat q` stands for `q`. -/
@[simp] theorem toRat_ofRat (q : ℚ) : (ofRat q).toRat = q := by
  unfold toRat
  rw [num_ofRat, den_ofRat, Signed.toInt_ofInt, Rat.mkRat_eq_div, Rat.num_div_den]

/-- `ofScientific` stands for the decimal literal with the same three parts. -/
@[simp] theorem toRat_ofScientific (mantissa : Nat) (exponentSign : Bool) (exponent : Nat) :
    (ofScientific mantissa exponentSign exponent).toRat =
      (OfScientific.ofScientific mantissa exponentSign exponent : ℚ) := by
  rw [toRat_eq]
  cases exponentSign
  · change (((mantissa * 10 ^ exponent : Nat) : ℚ) - ((0 : Nat) : ℚ)) / ((1 : Nat) : ℚ) =
      Rat.ofScientific mantissa false exponent
    rw [Rat.ofScientific_false_def]
    simp
  · change ((mantissa : ℚ) - ((0 : Nat) : ℚ)) / ((10 ^ exponent : Nat) : ℚ) =
      Rat.ofScientific mantissa true exponent
    rw [Rat.ofScientific_true_def, Rat.mkRat_eq_div]
    simp

/-- `add` is addition of rationals. -/
@[simp] theorem toRat_add (x y : Frac) : (x.add y).toRat = x.toRat + y.toRat := by
  simp only [toRat_eq, add, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  rw [cast_sub_sub]
  push_cast
  rw [div_add_div _ _ x.den_ne_zero y.den_ne_zero]
  congr 1
  simp only [sub_mul, mul_comm (x.den : ℚ)]
  abel

/-- `sub` is subtraction of rationals. -/
@[simp] theorem toRat_sub (x y : Frac) : (x.sub y).toRat = x.toRat - y.toRat := by
  simp only [toRat_eq, sub, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  rw [cast_sub_sub]
  push_cast
  rw [div_sub_div _ _ x.den_ne_zero y.den_ne_zero]
  congr 1
  simp only [sub_mul, mul_comm (x.den : ℚ)]
  abel

/-- `neg` is negation of rationals. -/
@[simp] theorem toRat_neg (x : Frac) : x.neg.toRat = -x.toRat := by
  simp only [toRat_eq, neg]
  rw [← neg_div, neg_sub]

/-- `mul` is multiplication of rationals. -/
@[simp] theorem toRat_mul (x y : Frac) : (x.mul y).toRat = x.toRat * y.toRat := by
  simp only [toRat_eq, mul, Nat.add_eq, Nat.mul_eq]
  push_cast
  rw [div_mul_div_comm]
  congr 1
  rw [sub_mul, mul_sub, mul_sub]
  abel

/-- `inv` is the inverse of rationals, with the inverse of zero equal to zero. -/
@[simp] theorem toRat_inv (x : Frac) : x.inv.toRat = x.toRat⁻¹ := by
  obtain ⟨p, q, d, hd⟩ := x
  simp only [toRat_eq, inv, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]
  rcases lt_trichotomy p q with h | h | h
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h1 : p - (p + e + 1) = 0 := by omega
    have h2 : p + e + 1 - p = e + 1 := by omega
    rw [h1, h2]
    have h3 : 1 - (1 - (e + 1)) = 1 := by omega
    have h4 : 0 + (e + 1) + (1 - (0 + (e + 1))) = e + 1 := by omega
    rw [h3, h4]
    have hpe : ((p : ℚ) - ((p + e + 1 : ℕ) : ℚ)) = -((e : ℚ) + 1) := by
      push_cast
      ring
    rw [hpe]
    push_cast
    rw [neg_div, inv_neg, inv_div]
    ring
  · subst h
    simp
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h1 : q - (q + e + 1) = 0 := by omega
    have h2 : q + e + 1 - q = e + 1 := by omega
    rw [h1, h2]
    have h3 : 1 - (1 - (e + 1)) = 1 := by omega
    have h4 : e + 1 + 0 + (1 - (e + 1 + 0)) = e + 1 := by omega
    rw [h3, h4]
    have hpe : (((q + e + 1 : ℕ) : ℚ) - (q : ℚ)) = (e : ℚ) + 1 := by
      push_cast
      ring
    rw [hpe]
    push_cast
    rw [inv_div]
    ring

/-- `div` is division of rationals, with division by zero equal to zero. -/
@[simp] theorem toRat_div (x y : Frac) : (x.div y).toRat = x.toRat / y.toRat := by
  rw [div, toRat_mul, toRat_inv, div_eq_mul_inv]

/-- `pow` is the power of rationals. -/
@[simp] theorem toRat_pow (x : Frac) (n : Nat) : (x.pow n).toRat = x.toRat ^ n := by
  have h := Signed.toInt_pow x.num n
  rw [Signed.toInt_eq, Signed.toInt_eq] at h
  rw [toRat_eq, toRat_eq, div_pow]
  change (((x.num.pow n).plus : ℚ) - ((x.num.pow n).minus : ℚ)) / ((x.den ^ n : Nat) : ℚ) = _
  have h' : (((x.num.pow n).plus : ℚ) - ((x.num.pow n).minus : ℚ)) =
      ((x.plus : ℚ) - (x.minus : ℚ)) ^ n := by
    exact_mod_cast congrArg (fun z : Int => (z : ℚ)) h
  rw [h']
  push_cast
  rfl

/-- `mulPow2` multiplies by `2 ^ k`. -/
@[simp] theorem toRat_mulPow2 (x : Frac) (k : Nat) : (x.mulPow2 k).toRat = x.toRat * 2 ^ k := by
  simp only [toRat_eq, mulPow2, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  push_cast
  rw [← sub_mul, mul_div_right_comm]

/-- `divPow2` divides by `2 ^ k`. -/
@[simp] theorem toRat_divPow2 (x : Frac) (k : Nat) : (x.divPow2 k).toRat = x.toRat / 2 ^ k := by
  simp only [toRat_eq, divPow2, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  push_cast
  rw [div_mul_eq_div_div]

/-- `normalize` keeps the rational. -/
@[simp] theorem toRat_normalize (x : Frac) : x.normalize.toRat = x.toRat := by
  obtain ⟨p, q, d, hd⟩ := x
  simp only [toRat_eq, normalize, Nat.add_eq, Nat.sub_eq]
  set g := Nat.gcd (p - q + (q - p)) d
  change ((↑((p - q) / g) : ℚ) - ↑((q - p) / g)) / ↑(d / g) = _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hd
  have hgd : g ∣ d := Nat.gcd_dvd_right _ _
  have hgm : g ∣ p - q + (q - p) := Nat.gcd_dvd_left _ _
  have hgp : g ∣ p - q := by
    rcases Nat.le_total p q with h | h
    · rw [Nat.sub_eq_zero_of_le h]; exact dvd_zero g
    · rwa [Nat.sub_eq_zero_of_le h, Nat.add_zero] at hgm
  have hgq : g ∣ q - p := by
    rcases Nat.le_total p q with h | h
    · rwa [Nat.sub_eq_zero_of_le h, Nat.zero_add] at hgm
    · rw [Nat.sub_eq_zero_of_le h]; exact dvd_zero g
  have hg0 : (g : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hgpos.ne'
  rw [Nat.cast_div hgp hg0, Nat.cast_div hgq hg0, Nat.cast_div hgd hg0, ← cast_sub_sub p q]
  rw [← sub_div, div_div_div_cancel_right₀ hg0]

/-- `le` decides `≤` on the rationals. -/
theorem le_iff (x y : Frac) : x.le y = true ↔ x.toRat ≤ y.toRat := by
  rw [toRat_eq, toRat_eq, div_le_div_iff₀ x.den_cast_pos y.den_cast_pos]
  simp only [le, Nat.add_eq, Nat.mul_eq, Nat.ble_eq]
  rw [← Nat.cast_le (α := ℚ)]
  push_cast
  rw [sub_mul, sub_mul, sub_le_sub_iff]

/-- `lt` decides `<` on the rationals. -/
theorem lt_iff (x y : Frac) : x.lt y = true ↔ x.toRat < y.toRat := by
  rw [toRat_eq, toRat_eq, div_lt_div_iff₀ x.den_cast_pos y.den_cast_pos]
  simp only [lt, Nat.add_eq, Nat.mul_eq, Nat.ble_eq, Nat.succ_eq_add_one]
  rw [Nat.add_one_le_iff, ← Nat.cast_lt (α := ℚ)]
  push_cast
  rw [sub_mul, sub_mul, sub_lt_sub_iff]

/-- `beq` decides equality of the rationals. -/
theorem beq_iff (x y : Frac) : x.beq y = true ↔ x.toRat = y.toRat := by
  rw [toRat_eq, toRat_eq, div_eq_div_iff x.den_ne_zero y.den_ne_zero]
  simp only [beq, Nat.add_eq, Nat.mul_eq, Nat.beq_eq]
  rw [← Nat.cast_inj (R := ℚ)]
  push_cast
  rw [sub_mul, sub_mul, sub_eq_sub_iff_add_eq_add]

/-- `isNeg` decides whether the rational is negative. -/
theorem isNeg_iff (x : Frac) : x.isNeg = true ↔ x.toRat < 0 := by
  rw [toRat_eq, div_lt_iff₀ x.den_cast_pos, zero_mul]
  simp only [isNeg, Nat.ble_eq, Nat.succ_eq_add_one]
  rw [Nat.add_one_le_iff, ← Nat.cast_lt (α := ℚ), sub_lt_zero]

/-- `floor` is the largest integer at most the rational. -/
theorem toInt_floor (x : Frac) : x.floor.toInt = ⌊x.toRat⌋ := by
  rw [floor, Signed.toInt_floorDiv, ← Rat.floor_intCast_div_natCast, toRat, Rat.mkRat_eq_div]

/-- `ceil` is the smallest integer at least the rational. -/
theorem toInt_ceil (x : Frac) : x.ceil.toInt = ⌈x.toRat⌉ := by
  rw [ceil, Signed.toInt_ceilDiv, ← Rat.floor_intCast_div_natCast, toRat, Rat.mkRat_eq_div,
    Int.cast_neg, neg_div, Int.floor_neg, neg_neg]

section Cast

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A passing `le` is an inequality in every ordered field, the real numbers included. -/
theorem le_cast {x y : Frac} (h : x.le y = true) : (x.toRat : K) ≤ (y.toRat : K) :=
  Rat.cast_le.2 ((le_iff x y).1 h)

/-- A passing `lt` is a strict inequality in every ordered field, the real numbers included. -/
theorem lt_cast {x y : Frac} (h : x.lt y = true) : (x.toRat : K) < (y.toRat : K) :=
  Rat.cast_lt.2 ((lt_iff x y).1 h)

end Cast

end FloatLib.Numerics.Kernel.Frac
