/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic
public import FloatLib.Numerics.ShiftRightJam
import Mathlib.Tactic.Ring

/-!
# Nearest-even rounding through guard and sticky bits

The width-generic rounder `Numerics.roundShiftRightEven` compares the discarded remainder with the
halfway value `2^(shift - 1)`. Limb kernels can avoid constructing that value by using three
Boolean tests: the guard bit just below the kept quotient, whether
any lower bit is set, and the parity of the quotient. This module proves that restatement and its
consequences for the sticky-bit normalisation used by addition and fused multiply-add.

* `roundShiftRightEven_eq_guard_sticky` is the three-bit form of nearest-even rounding.
* `roundShiftRightEven_shiftRightJam` shows that jamming every bit below position `j` into one
  sticky bit does not change a later rounding by at least `j + 2` bits. Applying this to an
  addition result requires a separate argument relating that result to its jammed value.
* `roundShiftRightEven_mul_two_pow` and `roundShiftRightEven_mul_two_pow_of_le` relate rounding
  of a scaled value to rounding of the original.
* `shiftRightJam_add_mul_two_pow` and `shiftRightJam_mul_two_pow_sub` describe the jammed
  quotient of an aligned sum or difference in terms of the two operands, and `log2_shiftRightJam`
  locates its leading bit.

These statements apply to natural numbers independently of their storage. The fixed-word and
limb-array kernels use them to justify their rounding steps.
-/

@[expose] public section

namespace FloatLib.Numerics

/-! ## The guard-and-sticky form -/

/-- The number one has no bits above position zero. -/
theorem testBit_one_succ (i : Nat) : (1 : Nat).testBit (i + 1) = false :=
  Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (Nat.succ_ne_zero i))

/-- The remainder of a shift splits into the sticky bits and the guard bit. -/
theorem mod_two_pow_succ_eq (x t : Nat) :
    x % 2 ^ (t + 1) = x % 2 ^ t + 2 ^ t * (if x.testBit t then 1 else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  have hmod : x / 2 ^ t % 2 < 2 := Nat.mod_lt _ (by decide)
  by_cases h : x / 2 ^ t % 2 = 1
  · simp [h]
  · have hzero : x / 2 ^ t % 2 = 0 := by omega
    simp [hzero]

/--
Nearest-even rounding in guard-and-sticky form.

The quotient is incremented exactly when the guard bit is set and either a sticky bit is set or
the quotient is odd.
-/
theorem roundShiftRightEven_eq_guard_sticky (x s : Nat) (hs : 0 < s) :
    roundShiftRightEven x s =
      x / 2 ^ s +
        if x.testBit (s - 1) && (decide (x % 2 ^ (s - 1) ≠ 0) || x.testBit s) then 1 else 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [roundShiftRightEven_def]
  simp only [Nat.add_one_ne_zero, beq_iff_eq, ite_false, Nat.shiftRight_eq', Nat.shiftLeft_eq',
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.add_sub_cancel]
  have hremainder : x - x / 2 ^ (t + 1) * 2 ^ (t + 1) = x % 2 ^ (t + 1) := by
    have := Nat.div_add_mod' x (2 ^ (t + 1))
    omega
  rw [hremainder, mod_two_pow_succ_eq]
  have hlow : x % 2 ^ t < 2 ^ t := Nat.mod_lt _ (Nat.two_pow_pos t)
  have hbitParity : x.testBit (t + 1) = decide (x / 2 ^ (t + 1) % 2 = 1) :=
    Nat.testBit_eq_decide_div_mod_eq
  cases hguard : x.testBit t
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.add_zero, Bool.false_and]
    rw [ite_eq_left hlow]
  · simp only [↓reduceIte, Nat.mul_one, Bool.true_and]
    rw [ite_eq_right (by omega)]
    by_cases hsticky : x % 2 ^ t = 0
    · rw [ite_eq_right (by omega)]
      simp only [hsticky, ne_eq, not_true_eq_false, decide_false, Bool.false_or, hbitParity]
      by_cases hodd : x / 2 ^ (t + 1) % 2 = 1
      · rw [ite_eq_right (by omega)]
        simp [hodd]
      · rw [ite_eq_left (by omega)]
        simp [hodd]
    · rw [ite_eq_left (by omega)]
      simp [hsticky]

/-- The nearest-even quotient is at most the successor of the truncated quotient. -/
theorem roundShiftRightEven_le_succ (x s : Nat) :
    roundShiftRightEven x s ≤ x / 2 ^ s + 1 := by
  have := roundShiftRightEven_le_shiftRight_add1 x s
  rwa [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] at this

/-- The nearest-even quotient is at least the truncated quotient. -/
theorem div_two_pow_le_roundShiftRightEven (x s : Nat) :
    x / 2 ^ s ≤ roundShiftRightEven x s := by
  have := shiftRight_le_roundShiftRightEven x s
  rwa [Nat.shiftRight_eq', Nat.shiftRight_eq_div_pow] at this

/-! ## Jamming -/

/-- Setting the low bit of a natural number. -/
theorem or_one_eq (q : Nat) : q ||| 1 = if q % 2 = 0 then q + 1 else q := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
      by_cases heven : q % 2 = 0
      · simp [heven, Nat.testBit_zero, Nat.succ_mod_two_eq_one_iff]
      · have hodd : q % 2 = 1 := by omega
        simp [Nat.testBit_zero, hodd]
  | succ i =>
      rw [testBit_one_succ, Bool.or_false]
      by_cases heven : q % 2 = 0
      · rw [ite_eq_left heven, Nat.testBit_add_one, Nat.testBit_add_one]
        congr 1
        omega
      · rw [ite_eq_right heven]

/-- Jamming never decreases the truncated quotient. -/
theorem div_two_pow_le_shiftRightJam (x j : Nat) : x / 2 ^ j ≤ shiftRightJam x j := by
  unfold shiftRightJam
  dsimp only
  split
  · exact Nat.le_refl _
  · rw [or_one_eq]
    split <;> omega

/-- Jamming a value with a set bit at or above the jam position gives a nonzero result. -/
theorem shiftRightJam_ne_zero (x j : Nat) (hx : 2 ^ j ≤ x) : shiftRightJam x j ≠ 0 := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hquotient : 1 ≤ x / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le hpos]
    omega
  have := div_two_pow_le_shiftRightJam x j
  omega

/--
Rounding after a sticky-bit jam agrees with rounding the original value, provided the rounding
keeps at least the guard bit above the jammed position.
-/
theorem roundShiftRightEven_shiftRightJam (x j s : Nat) (hj : j + 2 ≤ s) :
    roundShiftRightEven (shiftRightJam x j) (s - j) = roundShiftRightEven x s := by
  obtain ⟨u, rfl⟩ : ∃ u, s = j + (u + 2) := ⟨s - j - 2, by omega⟩
  rw [show j + (u + 2) - j = u + 2 by omega]
  rw [roundShiftRightEven_eq_guard_sticky _ _ (by omega),
    roundShiftRightEven_eq_guard_sticky _ _ (by omega)]
  rw [shiftRightJam_div_pow x j (u + 2) (by omega), show u + 2 - 1 = u + 1 by omega,
    show j + (u + 2) - 1 = j + (u + 1) by omega, shiftRightJam_testBit x j (u + 1) (by omega),
    shiftRightJam_testBit x j (u + 2) (by omega)]
  have hsticky : decide (shiftRightJam x j % 2 ^ (u + 1) ≠ 0) =
      decide (x % 2 ^ (j + (u + 1)) ≠ 0) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_iff, decide_eq_true_iff]
    exact shiftRightJam_mod_pow_ne_zero_iff x j (u + 1) (by omega)
  rw [hsticky]

/-- The jammed quotient of an aligned sum. -/
theorem shiftRightJam_add_mul_two_pow (A B j : Nat) :
    shiftRightJam (A * 2 ^ j + B) j =
      if B % 2 ^ j = 0 then A + B / 2 ^ j else (A + B / 2 ^ j) ||| 1 := by
  unfold shiftRightJam
  dsimp only
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv : (A * 2 ^ j + B) / 2 ^ j = A + B / 2 ^ j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.add_comm]
  have hmod : (A * 2 ^ j + B) % 2 ^ j = B % 2 ^ j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [hdiv, hmod]
  simp only [beq_iff_eq]

/-- The jammed quotient of an aligned difference. -/
theorem shiftRightJam_mul_two_pow_sub (A B j : Nat) (hB : B ≤ A * 2 ^ j) :
    shiftRightJam (A * 2 ^ j - B) j =
      if B % 2 ^ j = 0 then A - B / 2 ^ j else (A - B / 2 ^ j - 1) ||| 1 := by
  unfold shiftRightJam
  dsimp only
  simp only [beq_iff_eq]
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hBdecomp := Nat.div_add_mod' B (2 ^ j)
  have hBmod : B % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
  by_cases hexact : B % 2 ^ j = 0
  · have hB' : B = B / 2 ^ j * 2 ^ j := by omega
    have hle : B / 2 ^ j ≤ A := by
      have hmul : B / 2 ^ j * 2 ^ j ≤ A * 2 ^ j := by
        rw [← hB']
        exact hB
      exact Nat.le_of_mul_le_mul_right hmul hpos
    have hdiff : A * 2 ^ j - B = (A - B / 2 ^ j) * 2 ^ j := by
      rw [Nat.sub_mul, ← hB']
    rw [hdiff, Nat.mul_div_cancel _ hpos, Nat.mul_mod_left]
    simp [hexact]
  · have hlt : B / 2 ^ j < A := by
      by_contra hcontra
      have hge : A ≤ B / 2 ^ j := Nat.le_of_not_lt hcontra
      have hmul : A * 2 ^ j ≤ B / 2 ^ j * 2 ^ j := Nat.mul_le_mul_right _ hge
      have hzero : B % 2 ^ j = 0 := by omega
      exact hexact hzero
    have hsucc : (B / 2 ^ j + 1) * 2 ^ j ≤ A * 2 ^ j := Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at hsucc
    have hdiff : A * 2 ^ j - B = (A - B / 2 ^ j - 1) * 2 ^ j + (2 ^ j - B % 2 ^ j) := by
      have h1 : (A - B / 2 ^ j - 1) * 2 ^ j = A * 2 ^ j - B / 2 ^ j * 2 ^ j - 2 ^ j := by
        rw [Nat.sub_mul, Nat.sub_mul, Nat.one_mul]
      omega
    have hremainderLt : 2 ^ j - B % 2 ^ j < 2 ^ j := by omega
    rw [hdiff, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hremainderLt,
      Nat.zero_add, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hremainderLt]
    have hne : 2 ^ j - B % 2 ^ j ≠ 0 := by omega
    simp [hexact, hne]

/-- Jamming preserves the shifted leading-bit position when the truncated quotient is at least two. -/
theorem log2_shiftRightJam (x j : Nat) (hx : 2 ^ (j + 1) ≤ x) :
    (shiftRightJam x j).log2 = x.log2 - j := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hquotient : 2 ≤ x / 2 ^ j := by
    rw [Nat.le_div_iff_mul_le hpos]
    rw [pow_succ] at hx
    omega
  have hxne : x ≠ 0 := by
    intro h
    rw [h] at hx
    have := Nat.two_pow_pos (j + 1)
    omega
  have hlog : (x / 2 ^ j).log2 = x.log2 - j := by
    have hj : j ≤ x.log2 := by
      rw [Nat.le_log2 hxne]
      exact le_trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ j)) hx
    have hqne : x / 2 ^ j ≠ 0 := by omega
    rw [Nat.log2_eq_iff hqne]
    constructor
    · rw [Nat.le_div_iff_mul_le hpos, ← pow_add, Nat.sub_add_cancel hj]
      exact Nat.log2_self_le hxne
    · rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add, show x.log2 - j + 1 + j = x.log2 + 1 by omega]
      exact Nat.lt_log2_self
  rw [← hlog]
  unfold shiftRightJam
  dsimp only
  by_cases hexact : x % 2 ^ j = 0
  · rw [ite_eq_left (by rw [beq_iff_eq]; exact hexact)]
  · rw [ite_eq_right (by rw [beq_iff_eq]; exact hexact)]
    have hqne : x / 2 ^ j ≠ 0 := by omega
    have hor : (x / 2 ^ j ||| 1) = x / 2 ^ j ∨ (x / 2 ^ j ||| 1) = x / 2 ^ j + 1 := by
      by_cases hodd : x / 2 ^ j % 2 = 1
      · left
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_or]
        cases i with
        | zero =>
            simp [Nat.testBit_zero, hodd]
        | succ i =>
            simp [testBit_one_succ]
      · right
        have heven : x / 2 ^ j % 2 = 0 := by omega
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_or]
        cases i with
        | zero =>
            simp [Nat.testBit_zero, heven, Nat.succ_mod_two_eq_one_iff]
        | succ i =>
            rw [testBit_one_succ, Bool.or_false, Nat.testBit_add_one, Nat.testBit_add_one]
            congr 1
            omega
    rcases hor with hor | hor
    · rw [hor]
    · rw [hor]
      symm
      rw [Nat.log2_eq_iff hqne]
      have hlog2 := Nat.log2_self_le (n := x / 2 ^ j + 1) (by omega)
      have hlog2' := Nat.lt_log2_self (n := x / 2 ^ j + 1)
      have heven : x / 2 ^ j % 2 = 0 := by
        by_contra hodd
        have : x / 2 ^ j % 2 = 1 := by omega
        have hor' : (x / 2 ^ j ||| 1) = x / 2 ^ j := by
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_or]
          cases i with
          | zero => simp [Nat.testBit_zero, this]
          | succ i => simp [testBit_one_succ]
        omega
      have hpowEven : ∀ m, 1 ≤ m → 2 ^ m % 2 = 0 := by
        intro m hm
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [pow_succ]
        simp
      have hne : x / 2 ^ j + 1 ≠ 2 ^ (x / 2 ^ j + 1).log2 := by
        intro heq
        have hm : 1 ≤ (x / 2 ^ j + 1).log2 := by
          rw [Nat.le_log2 (by omega)]
          omega
        have := hpowEven _ hm
        omega
      constructor
      · rcases Nat.lt_or_ge (x / 2 ^ j) (2 ^ (x / 2 ^ j + 1).log2) with hlt | hge
        · exfalso
          apply hne
          omega
        · exact hge
      · omega

/-! ## Scaling -/

/-- Rounding a value scaled by `2^k` by `k` more bits is rounding the value. -/
theorem roundShiftRightEven_mul_two_pow (x k s : Nat) :
    roundShiftRightEven (x * 2 ^ k) (s + k) = roundShiftRightEven x s := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  cases s with
  | zero =>
      rw [roundShiftRightEven_zero, Nat.zero_add]
      cases k with
      | zero => simp
      | succ k =>
          rw [roundShiftRightEven_eq_guard_sticky _ _ (by omega)]
          have hbit : (x * 2 ^ (k + 1)).testBit k = false := by
            rw [Nat.testBit_mul_two_pow]
            simp
          rw [Nat.add_sub_cancel, hbit]
          simp [Nat.mul_div_cancel _ (Nat.two_pow_pos (k + 1))]
  | succ t =>
      rw [roundShiftRightEven_eq_guard_sticky _ _ (by omega),
        roundShiftRightEven_eq_guard_sticky _ _ (by omega)]
      rw [show t + 1 + k - 1 = t + k by omega, Nat.add_sub_cancel]
      have hdiv : x * 2 ^ k / 2 ^ (t + 1 + k) = x / 2 ^ (t + 1) := by
        rw [pow_add, Nat.mul_comm (2 ^ (t + 1)), ← Nat.div_div_eq_div_mul,
          Nat.mul_div_cancel _ hpos]
      have hguard : (x * 2 ^ k).testBit (t + k) = x.testBit t := by
        rw [Nat.testBit_mul_two_pow]
        simp
      have hround : (x * 2 ^ k).testBit (t + 1 + k) = x.testBit (t + 1) := by
        rw [Nat.testBit_mul_two_pow]
        simp
      have hsticky : x * 2 ^ k % 2 ^ (t + k) = x % 2 ^ t * 2 ^ k := by
        rw [pow_add, Nat.mul_mod_mul_right]
      have hstickyIff : x * 2 ^ k % 2 ^ (t + k) ≠ 0 ↔ x % 2 ^ t ≠ 0 := by
        rw [hsticky]
        constructor
        · intro h hzero
          apply h
          rw [hzero, Nat.zero_mul]
        · intro h hzero
          apply h
          have := Nat.mul_eq_zero.mp hzero
          omega
      have hstickyDecide : decide (x * 2 ^ k % 2 ^ (t + k) ≠ 0) = decide (x % 2 ^ t ≠ 0) := by
        apply Bool.eq_iff_iff.mpr
        rw [decide_eq_true_iff, decide_eq_true_iff]
        exact hstickyIff
      rw [hdiv, hguard, hround, hstickyDecide]

/-- Rounding a value scaled by `2^k` by at most `k` bits is exact. -/
theorem roundShiftRightEven_mul_two_pow_of_le (x k s : Nat) (hs : s ≤ k) :
    roundShiftRightEven (x * 2 ^ k) s = x * 2 ^ (k - s) := by
  obtain ⟨d, rfl⟩ : ∃ d, k = s + d := ⟨k - s, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add, ← Nat.mul_assoc, Nat.mul_comm x, Nat.mul_assoc,
    Nat.mul_comm (2 ^ s)]
  have := roundShiftRightEven_mul_two_pow (x * 2 ^ d) s 0
  rw [Nat.zero_add, roundShiftRightEven_zero] at this
  exact this

end FloatLib.Numerics
