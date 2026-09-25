/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import Mathlib.Tactic.NormNum
public import FloatLib.Numerics.Quantization.Deterministic.Quotient
public import Mathlib.Data.Nat.Log

/-!
# Deterministic nearest-even shift rounding

Power-of-two nearest-even rounding shared by binary floating-point, fixed-point, and other
quantized representations. Guard, parity, and sticky bits decide rounding without constructing
a halfway marker.
-/

@[expose] public section

namespace FloatLib.Numerics

/--
Remainder discarded by shifting a natural number right.

Writing the operation this way avoids constructing `2^shift`. When `shift` exceeds the input's
bit length, the quotient is zero and the remainder is the original value.
-/
@[inline] def shiftRightRemainder (value shift : Nat) : Nat :=
  value - Nat.shiftLeft (Nat.shiftRight value shift) shift

/-- The bits discarded by a right shift are exactly the remainder modulo `2^shift`. -/
theorem shiftRightRemainder_eq_mod (value shift : Nat) :
    shiftRightRemainder value shift = value % 2 ^ shift := by
  simp only [shiftRightRemainder, Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq', Nat.shiftLeft_eq, Nat.mod_eq_sub_div_mul]

/--
Round `value / 2^shift` to the nearest natural number, breaking exact halfway cases toward even.

This is the power-of-two specialization of `roundQuotientEven`. It belongs in the common
quantization layer because binary floats, P3109 formats, and fixed-point kernels all discard low
binary digits in the same way. The guard bit decides whether rounding can increase the quotient.
The first shift retains the guard bit alongside the quotient. Only a set guard bit with an even
quotient requires checking whether shifting those retained bits back recovers the original value.
One low-byte extraction supplies both the guard bit and the quotient's parity.
-/
@[inline] def roundShiftRightEven (value shift : Nat) : Nat :=
  if shift == 0 then
    value
  else
    let amount := shift - 1
    let retained := Nat.shiftRight value amount
    let quotient := Nat.shiftRight retained 1
    let lowByte := UInt8.ofNat retained
    if (lowByte &&& 1) != 0 then
      if ((lowByte >>> 1) &&& 1) != 0 || Nat.shiftLeft retained amount != value then
        quotient + 1
      else
        quotient
    else
      quotient

/-- Shifting by no bits leaves the value unchanged. -/
@[simp, grind =] theorem roundShiftRightEven_zero (value : Nat) :
    roundShiftRightEven value 0 = value := by
  simp [roundShiftRightEven]

/-- The remainder of a shift splits into the sticky bits and the guard bit. -/
theorem mod_two_pow_succ_eq (x t : Nat) :
    x % 2 ^ (t + 1) = x % 2 ^ t + 2 ^ t * (if x.testBit t then 1 else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hmod : x / 2 ^ t % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : x / 2 ^ t % 2 = 1
  · simp [h]
  · have hzero : x / 2 ^ t % 2 = 0 := by omega
    simp [hzero]

private theorem shiftLeft_shiftRight_ne (value amount : Nat) :
    (Nat.shiftLeft (Nat.shiftRight value amount) amount != value) =
      decide (value % 2 ^ amount ≠ 0) := by
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq', Nat.shiftLeft_eq]
  have hsplit := Nat.div_add_mod' value (2 ^ amount)
  by_cases hzero : value % 2 ^ amount = 0
  · have heq : value / 2 ^ amount * 2 ^ amount = value := by omega
    simp [hzero, heq]
  · have hne : value / 2 ^ amount * 2 ^ amount ≠ value := by omega
    simp [hzero, hne]

private theorem uint8_shiftRight_and_one_ne_zero (value bit : Nat) (hbit : bit < 8) :
    (((UInt8.ofNat value >>> UInt8.ofNat bit) &&& 1) != 0) = value.testBit bit := by
  have hbyte : (UInt8.ofNat bit).toNat = bit :=
    UInt8.toNat_ofNat_of_lt' (hbit.trans_le (by decide))
  have hbitmod : bit % 8 = bit := Nat.mod_eq_of_lt hbit
  have htest : (value % 2 ^ 8).testBit bit = value.testBit bit := by
    simp only [Nat.testBit_mod_two_pow, hbit, decide_true, Bool.true_and]
  rw [← htest]
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, Nat.testBit]
  apply not_congr
  rw [← UInt8.toNat_inj]
  simp only [UInt8.toNat_and, UInt8.toNat_shiftRight, hbyte, hbitmod,
    UInt8.toNat_ofNat', UInt8.toNat_ofNat]
  norm_num only
  rw [Nat.and_comm]

/--
Nearest-even rounding in guard-and-sticky form.

The quotient is incremented exactly when the guard bit is set and either a sticky bit is set or
the quotient is odd.
-/
theorem roundShiftRightEven_eq_guard_sticky (x s : Nat) (hs : 0 < s) :
    roundShiftRightEven x s =
      x / 2 ^ s +
        if x.testBit (s - 1) && (decide (x % 2 ^ (s - 1) ≠ 0) || x.testBit s) then 1 else 0 := by
  have hquotient :
      Nat.shiftRight (Nat.shiftRight x (s - 1)) 1 = Nat.shiftRight x s := by
    change x >>> (s - 1) >>> 1 = x >>> s
    rw [← Nat.shiftRight_add]
    congr 1
    omega
  have hguard :
      ((UInt8.ofNat (Nat.shiftRight x (s - 1)) &&& 1) != 0) =
        x.testBit (s - 1) := by
    simpa only [show UInt8.ofNat 0 = (0 : UInt8) from rfl, UInt8.shiftRight_zero,
      Nat.shiftRight_eq', Nat.testBit_shiftRight, Nat.add_zero] using
      uint8_shiftRight_and_one_ne_zero (Nat.shiftRight x (s - 1)) 0 (by decide)
  have hparity :
      (((UInt8.ofNat (Nat.shiftRight x (s - 1)) >>> 1) &&& 1) != 0) =
        x.testBit s := by
    have hshift : s - 1 + 1 = s := by omega
    simpa only [show UInt8.ofNat 1 = (1 : UInt8) from rfl, Nat.shiftRight_eq',
      Nat.testBit_shiftRight, hshift] using
      uint8_shiftRight_and_one_ne_zero (Nat.shiftRight x (s - 1)) 1 (by decide)
  simp only [roundShiftRightEven, beq_iff_eq, Nat.ne_of_gt hs, ite_false]
  simp only [hquotient, hguard, hparity, shiftLeft_shiftRight_ne]
  simp only [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow]
  cases x.testBit (s - 1) <;> cases x.testBit s <;>
    by_cases hsticky : x % 2 ^ (s - 1) = 0 <;> simp [hsticky]

/-- Nearest-even shift rounding in quotient/remainder form. -/
theorem roundShiftRightEven_def (value shift : Nat) :
    roundShiftRightEven value shift =
      if shift == 0 then
        value
      else
        let quotient := Nat.shiftRight value shift
        let remainder := value - Nat.shiftLeft quotient shift
        let half := 2 ^ (shift - 1)
        if remainder < half then
          quotient
        else if half < remainder then
          quotient + 1
        else if quotient % 2 == 0 then
          quotient
        else
          quotient + 1 := by
  by_cases hshift : shift = 0
  · simp [hshift]
  obtain ⟨t, rfl⟩ : ∃ t, shift = t + 1 := ⟨shift - 1, by omega⟩
  rw [roundShiftRightEven_eq_guard_sticky value (t + 1) (by omega)]
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false, Nat.shiftRight_eq',
    Nat.shiftLeft_eq', Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_sub_cancel]
  symm
  have hremainder : value - value / 2 ^ (t + 1) * 2 ^ (t + 1) =
      value % 2 ^ (t + 1) := by
    have := Nat.div_add_mod' value (2 ^ (t + 1))
    omega
  rw [hremainder, mod_two_pow_succ_eq]
  have hlow : value % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
  have hbitParity : value.testBit (t + 1) =
      decide (value / 2 ^ (t + 1) % 2 = 1) := Nat.testBit_eq_decide_div_mod_eq
  cases hguard : value.testBit t
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Bool.false_and]
    rw [ite_eq_left hlow]
  · simp only [↓reduceIte, Nat.mul_one, Bool.true_and]
    rw [ite_eq_right (by omega)]
    by_cases hsticky : value % 2 ^ t = 0
    · rw [ite_eq_right (by omega)]
      simp only [hsticky, ne_eq, not_true_eq_false, decide_false, Bool.false_or, hbitParity]
      by_cases hodd : value / 2 ^ (t + 1) % 2 = 1
      · rw [ite_eq_right (by omega)]
        simp [hodd]
      · rw [ite_eq_left (by omega)]
        simp [hodd]
    · rw [ite_eq_left (by omega)]
      simp [hsticky]

/-- Nearest-even shifting is nearest-even division by the corresponding power of two. -/
theorem roundShiftRightEven_eq_roundQuotientEven (value shift : Nat) :
    roundShiftRightEven value shift = roundQuotientEven value (2 ^ shift) := by
  by_cases hs : shift = 0
  · simp [hs, roundQuotientEven, Nat.mod_one]
  have hp : 2 ^ shift = 2 * 2 ^ (shift - 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, shift = n + 1 := ⟨shift - 1, by omega⟩
    simp [pow_succ, Nat.mul_comm]
  rw [roundShiftRightEven_def]
  change (if shift == 0 then value else
    if shiftRightRemainder value shift < 2 ^ (shift - 1) then value.shiftRight shift
    else if 2 ^ (shift - 1) < shiftRightRemainder value shift then value.shiftRight shift + 1
    else if value.shiftRight shift % 2 == 0 then value.shiftRight shift
    else value.shiftRight shift + 1) = _
  simp only [beq_iff_eq, hs, ite_false, shiftRightRemainder_eq_mod, Nat.shiftRight_eq',
    Nat.shiftRight_eq_div_pow, roundQuotientEven]
  rw [hp]
  simp only [Nat.mul_lt_mul_left (by decide : 0 < (2 : Nat))]

private theorem roundShiftRightEven_eq_shiftRight_or_add_one
    (value shift : Nat) :
    roundShiftRightEven value shift = Nat.shiftRight value shift ∨
      roundShiftRightEven value shift = Nat.shiftRight value shift + 1 := by
  classical
  by_cases hshift : shift = 0
  · subst shift
    simp [roundShiftRightEven_def]
  · have hshiftBool : (shift == 0) = false := by
      simp [hshift]
    let quotient := Nat.shiftRight value shift
    let remainder := value - Nat.shiftLeft quotient shift
    let half := 2 ^ (shift - 1)
    have hround :
        roundShiftRightEven value shift =
          if remainder < half then quotient
          else if remainder > half then quotient + 1
          else if quotient % 2 = 0 then quotient else quotient + 1 := by
      simp (config := { zeta := true })
        [roundShiftRightEven_def, hshiftBool, quotient, remainder, half]
    by_cases hlt : remainder < half
    · left
      simp [hround, hlt, quotient]
    · by_cases hgt : remainder > half
      · right
        simp [hround, hlt, hgt, quotient]
      · by_cases heven : quotient % 2 = 0
        · left
          rw [hround]
          simp only [hlt, hgt, heven, ite_false, ite_true]
          rfl
        · right
          rw [hround]
          simp only [hlt, hgt, heven, ite_false]
          rfl

/-- Nearest-even shift rounding is never below the floor quotient. -/
theorem shiftRight_le_roundShiftRightEven (value shift : Nat) :
    Nat.shiftRight value shift ≤ roundShiftRightEven value shift := by
  rcases roundShiftRightEven_eq_shiftRight_or_add_one value shift with h | h
  · simp [h]
  · simp [h]

/-- Nearest-even shift rounding is at most one above the floor quotient. -/
theorem roundShiftRightEven_le_shiftRight_add1 (value shift : Nat) :
    roundShiftRightEven value shift ≤ Nat.shiftRight value shift + 1 := by
  rcases roundShiftRightEven_eq_shiftRight_or_add_one value shift with h | h
  · simp [h]
  · simp [h]

/-- A one-bit nearest-even shift increments the floor quotient exactly when `value % 4 = 3`. -/
theorem roundShiftRightEven_one (value : Nat) :
    roundShiftRightEven value 1 =
      if value % 4 = 3 then value / 2 + 1 else value / 2 := by
  have hmod4 : value % 4 < 4 :=
    Nat.mod_lt value (by decide)
  have hquotientParity :
      (value / 2) % 2 = (value % 4) / 2 := by
    simpa using (Nat.mod_mul_right_div_self value 2 2).symm
  have hremainderParity :
      value % 2 = (value % 4) % 2 := by
    exact (Nat.mod_mul_right_mod value 2 2).symm
  have hquotient :
      value.shiftRight 1 = value / 2 := by
    simpa using Nat.shiftRight_eq_div_pow value 1
  have hshiftBack :
      (value.shiftRight 1).shiftLeft 1 =
        (value / 2) * 2 := by
    simpa [Nat.shiftLeft_eq, hquotient]
  have hremainder :
      value - (value.shiftRight 1).shiftLeft 1 =
        value % 2 := by
    rw [hshiftBack]
    exact Nat.mod_eq_sub_div_mul.symm
  rw [roundShiftRightEven_def]
  simp only [beq_iff_eq, one_ne_zero, ite_false]
  norm_num only [Nat.reducePow, Nat.reduceSub]
  rw [hremainder, hquotient]
  have hcases :
      value % 4 = 0 ∨ value % 4 = 1 ∨
        value % 4 = 2 ∨ value % 4 = 3 := by
    omega
  rcases hcases with hmod4 | hmod4 | hmod4 | hmod4
  all_goals
    have hmod2 := hremainderParity
    have hquotientMod2 := hquotientParity
    rw [hmod4] at hmod2 hquotientMod2
    norm_num at hmod2 hquotientMod2
    simp [hmod4, hmod2, hquotientMod2]

/-- Rounding an exact multiple of two by one bit is exact. -/
theorem roundShiftRightEven_two_mul (value : Nat) :
    roundShiftRightEven (2 * value) 1 = value := by
  simp [roundShiftRightEven_def, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, Nat.mul_comm]

end FloatLib.Numerics
