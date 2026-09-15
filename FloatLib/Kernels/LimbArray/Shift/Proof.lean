/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.LimbArray.Shift.Runtime
public import FloatLib.Kernels.LimbArray.Arithmetic.Proof
public import FloatLib.Numerics.ShiftRightJam.Proof
import Mathlib.Tactic.Ring

/-!
# Limb arrays: value semantics of the shifts

The shifts of `Shift.Runtime` build each result limb from two source limbs, so their `toNat`
statements are proved bit by bit: `shiftLeftLimb_testBit` and `shiftRightLimb_testBit` read one
bit of a result limb as one bit of the source value, and `Nat.eq_of_testBit_eq` turns those
readings into `toNat_shiftLeft` and `toNat_shiftRight`.

`toNat_roundShiftRightEven` then combines the shift with the guard-and-sticky form of nearest-even
rounding from `FloatLib.Numerics.ShiftRightJam.Proof`. The guard bit, sticky test, and quotient
parity determine whether to increment the truncated quotient.
-/

@[expose] public section

namespace FloatLib.Numerics.LimbArray

/-! ## Machine-word shift bits -/

/-- A bit of a right-shifted limb, for shift counts below 32. -/
theorem uint32_shiftRight_testBit (x : UInt32) (r n : Nat) (hr : r < 32) :
    (x >>> UInt32.ofNat r).toNat.testBit n = x.toNat.testBit (r + n) := by
  rw [UInt32.toNat_shiftRight, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : r < 2 ^ 32),
    Nat.mod_eq_of_lt hr, Nat.testBit_shiftRight]

/-- A bit of a left-shifted limb, for shift counts below 32. -/
theorem uint32_shiftLeft_testBit (x : UInt32) (r n : Nat) (hr : r < 32) :
    (x <<< UInt32.ofNat r).toNat.testBit n =
      (decide (n < 32) && (decide (r ≤ n) && x.toNat.testBit (n - r))) := by
  rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (by omega : r < 2 ^ 32),
    Nat.mod_eq_of_lt hr, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]

/-! ## Left shift -/

/-- One bit of a result limb of the left shift is the corresponding bit of the source value. -/
theorem shiftLeftLimb_testBit (v : LimbArray) (q r i m : Nat) (hr : r < 32) (hm : m < 32) :
    (shiftLeftLimb v q r i).toNat.testBit m =
      (decide (32 * q + r ≤ 32 * i + m) && (toNat v).testBit (32 * i + m - (32 * q + r))) := by
  unfold shiftLeftLimb
  by_cases hi : i < q
  · rw [if_pos hi]
    have : ¬ (32 * q + r ≤ 32 * i + m) := by omega
    simp [this]
  · rw [if_neg hi]
    dsimp only
    obtain ⟨j, rfl⟩ : ∃ j, i = q + j := ⟨i - q, by omega⟩
    rw [Nat.add_sub_cancel_left]
    have hhigh : (v.limb j <<< UInt32.ofNat r).toNat.testBit m =
        (decide (r ≤ m) && (toNat v).testBit (32 * j + (m - r))) := by
      rw [uint32_shiftLeft_testBit _ _ _ hr]
      by_cases hrm : r ≤ m
      · rw [limb_testBit v j (m - r) (by omega)]
        simp [hm, hrm]
      · simp [hrm]
    by_cases hcase : r == 0 || j == 0
    · rw [if_pos hcase, hhigh]
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hcase
      rcases hcase with hr0 | hj0
      · subst hr0
        have hle : 32 * q + 0 ≤ 32 * (q + j) + m := by omega
        simp only [Nat.zero_le, decide_true, Bool.true_and, hle]
        congr 1
        omega
      · subst hj0
        by_cases hrm : r ≤ m
        · have hle : 32 * q + r ≤ 32 * (q + 0) + m := by omega
          simp only [hrm, decide_true, Bool.true_and, hle]
          congr 1
          omega
        · have hle : ¬ (32 * q + r ≤ 32 * (q + 0) + m) := by omega
          simp [hrm]
    · rw [if_neg hcase]
      rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq, not_or] at hcase
      obtain ⟨hr0, hj0⟩ := hcase
      rw [UInt32.toNat_or, Nat.testBit_or, hhigh, uint32_shiftRight_testBit _ _ _ (by omega)]
      have hle : 32 * q + r ≤ 32 * (q + j) + m := by omega
      simp only [hle, decide_true, Bool.true_and]
      by_cases hrm : r ≤ m
      · rw [limb_testBit_eq_false v (j - 1) _ (by omega)]
        simp only [hrm, decide_true, Bool.true_and, Bool.or_false]
        congr 1
        omega
      · rw [limb_testBit v (j - 1) _ (by omega)]
        simp only [hrm, decide_false, Bool.false_and, Bool.false_or]
        congr 1
        omega

/-- A left shift by `k` bits adds `k / 32 + 1` limbs. -/
@[simp] theorem size_shiftLeft (v : LimbArray) (k : Nat) :
    (shiftLeft v k).size = v.size + k / 32 + 1 := by
  simp [shiftLeft, size]

/-- Each limb of a left shift is the corresponding `shiftLeftLimb` value inside the new size and
zero above it. -/
theorem limb_shiftLeft (v : LimbArray) (k i : Nat) :
    (shiftLeft v k).limb i =
      if i < v.size + k / 32 + 1 then shiftLeftLimb v (k / 32) (k % 32) i else 0 := by
  by_cases hi : i < v.size + k / 32 + 1
  · have hi' : i < (shiftLeft v k).limbs.size := by
      change i < (shiftLeft v k).size
      rw [size_shiftLeft]
      exact hi
    rw [limb_eq_getElem _ hi', if_pos hi]
    simp [shiftLeft]
  · rw [limb_eq_zero_of_size_le _ (by simpa using hi), if_neg hi]

/-- The left shift multiplies the value by `2^k`. -/
@[simp, grind =] theorem toNat_shiftLeft (v : LimbArray) (k : Nat) : toNat (shiftLeft v k) = toNat v * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_mul_two_pow]
  have hn : n % 32 < 32 := Nat.mod_lt _ (by decide)
  have hdecomp : 32 * (n / 32) + n % 32 = n := Nat.div_add_mod n 32
  have hk : 32 * (k / 32) + k % 32 = k := Nat.div_add_mod k 32
  rw [← hdecomp, ← limb_testBit _ _ _ hn, limb_shiftLeft]
  by_cases hi : n / 32 < v.size + k / 32 + 1
  · rw [if_pos hi, shiftLeftLimb_testBit v _ _ _ _ (Nat.mod_lt _ (by decide)) hn, hk]
  · rw [if_neg hi]
    have hbig : 32 * v.size ≤ 32 * (n / 32) + n % 32 - k := by omega
    have hfalse : (toNat v).testBit (32 * (n / 32) + n % 32 - k) = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le (toNat_lt_two_pow_of_size_le (Nat.le_refl _))
        (Nat.pow_le_pow_right (by decide) hbig)
    rw [hfalse]
    simp

/-! ## Right shift -/

/-- One bit of a result limb of the right shift is the corresponding bit of the source value. -/
theorem shiftRightLimb_testBit (v : LimbArray) (q r i m : Nat) (hr : r < 32) (hm : m < 32) :
    (shiftRightLimb v q r i).toNat.testBit m = (toNat v).testBit (32 * i + m + (32 * q + r)) := by
  unfold shiftRightLimb
  dsimp only
  have hlow : (v.limb (i + q) >>> UInt32.ofNat r).toNat.testBit m =
      (decide (r + m < 32) && (toNat v).testBit (32 * i + m + (32 * q + r))) := by
    rw [uint32_shiftRight_testBit _ _ _ hr]
    by_cases hsum : r + m < 32
    · rw [limb_testBit v (i + q) (r + m) hsum]
      simp only [hsum, decide_true, Bool.true_and]
      congr 1
      omega
    · rw [limb_testBit_eq_false v (i + q) (r + m) (by omega)]
      simp [hsum]
  by_cases hr0 : r == 0
  · rw [if_pos hr0, hlow]
    rw [beq_iff_eq] at hr0
    subst hr0
    simp [hm]
  · rw [beq_iff_eq] at hr0
    rw [if_neg (by simpa using hr0), UInt32.toNat_or, Nat.testBit_or, hlow,
      uint32_shiftLeft_testBit (v.limb (i + q + 1)) (32 - r) m (by omega)]
    by_cases hsum : r + m < 32
    · have hhigh : ¬ (32 - r ≤ m) := by omega
      simp [hsum, hhigh]
    · have hhigh : 32 - r ≤ m := by omega
      rw [limb_testBit v (i + q + 1) (m - (32 - r)) (by omega)]
      simp only [hsum, decide_false, Bool.false_and, Bool.false_or, hm, decide_true, hhigh,
        Bool.true_and]
      congr 1
      omega

/-- A right shift keeps the limb count. -/
@[simp] theorem size_shiftRight (v : LimbArray) (k : Nat) : (shiftRight v k).size = v.size := by
  simp [shiftRight, size]

/-- Each limb of a right shift is the corresponding `shiftRightLimb` value inside the size and
zero above it. -/
theorem limb_shiftRight (v : LimbArray) (k i : Nat) :
    (shiftRight v k).limb i =
      if i < v.size then shiftRightLimb v (k / 32) (k % 32) i else 0 := by
  by_cases hi : i < v.size
  · have hi' : i < (shiftRight v k).limbs.size := by
      change i < (shiftRight v k).size
      rw [size_shiftRight]
      exact hi
    rw [limb_eq_getElem _ hi', if_pos hi]
    simp [shiftRight]
  · rw [limb_eq_zero_of_size_le _ (by simpa using hi), if_neg hi]

/-- The right shift divides the value by `2^k`. -/
@[simp, grind =] theorem toNat_shiftRight (v : LimbArray) (k : Nat) : toNat (shiftRight v k) = toNat v / 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_div_two_pow]
  have hn : n % 32 < 32 := Nat.mod_lt _ (by decide)
  have hdecomp : 32 * (n / 32) + n % 32 = n := Nat.div_add_mod n 32
  have hk : 32 * (k / 32) + k % 32 = k := Nat.div_add_mod k 32
  rw [← hdecomp, ← limb_testBit _ _ _ hn, limb_shiftRight]
  by_cases hi : n / 32 < v.size
  · rw [if_pos hi, shiftRightLimb_testBit v _ _ _ _ (Nat.mod_lt _ (by decide)) hn, hk]
  · rw [if_neg hi]
    have hbig : 32 * v.size ≤ 32 * (n / 32) + n % 32 + k := by omega
    have hfalse : (toNat v).testBit (32 * (n / 32) + n % 32 + k) = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le (toNat_lt_two_pow_of_size_le (Nat.le_refl _))
        (Nat.pow_le_pow_right (by decide) hbig)
    rw [hfalse]
    simp

/-! ## Nearest-even rounding -/

/-- Rounding a right shift keeps the limb count of the shifted array. -/
@[simp] theorem size_roundShiftRightEven (v : LimbArray) (shift : Nat) :
    (roundShiftRightEven v shift).size = v.size := by
  unfold roundShiftRightEven
  split
  · rfl
  · split
    · rw [size_addAt, size_shiftRight]
    · rw [size_shiftRight]

/-- The limb rounder agrees with the width-generic nearest-even shift. -/
@[simp, grind =] theorem toNat_roundShiftRightEven (v : LimbArray) (shift : Nat) :
    toNat (roundShiftRightEven v shift) = Numerics.roundShiftRightEven (toNat v) shift := by
  unfold roundShiftRightEven
  by_cases hshift : shift == 0
  · rw [if_pos hshift]
    rw [beq_iff_eq] at hshift
    subst hshift
    simp
  · rw [if_neg hshift]
    rw [beq_iff_eq] at hshift
    have hpos : 0 < shift := Nat.pos_of_ne_zero hshift
    rw [Numerics.roundShiftRightEven_eq_guard_sticky _ _ hpos, testBit_eq, testBit_eq,
      anyBelow_eq]
    by_cases hcond : (toNat v).testBit (shift - 1) &&
        (decide (toNat v % 2 ^ (shift - 1) ≠ 0) || (toNat v).testBit shift)
    · rw [if_pos hcond, if_pos hcond]
      have hne : toNat v ≠ 0 := by
        intro hzero
        rw [hzero] at hcond
        simp at hcond
      have hsize : 1 ≤ v.size := by
        by_contra hcontra
        have hzero : v.size = 0 := by omega
        apply hne
        rw [toNat_eq_segment_of_size_le (n := 0) (by omega)]
        rfl
      have hbound := toNat_lt v
      have hradix : 2 ≤ radix ^ v.size := by
        calc
          2 ≤ radix := by decide
          _ = radix ^ 1 := (pow_one radix).symm
          _ ≤ radix ^ v.size := Nat.pow_le_pow_right (by decide) hsize
      have hhalf : toNat v / 2 ^ shift ≤ toNat v / 2 :=
        Nat.div_le_div_left (by
          calc
            2 = 2 ^ 1 := (pow_one 2).symm
            _ ≤ 2 ^ shift := Nat.pow_le_pow_right (by decide) hpos) (by decide)
      rw [toNat_addAt _ _ _ (by rw [size_shiftRight]; omega)]
      · rw [toNat_shiftRight]
        simp
      · rw [size_shiftRight, toNat_shiftRight]
        simp only [pow_zero, Nat.mul_one, UInt32.toNat_one]
        omega
    · rw [if_neg hcond, if_neg hcond, toNat_shiftRight, Nat.add_zero]

end FloatLib.Numerics.LimbArray
