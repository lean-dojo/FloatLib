/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits
public import FloatLib.Tactic.CompiledAs
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic.Ring

/-!
# Specifications of elementary kernel arithmetic

Bit extraction and low-bit masking have their usual meanings. Ceiling division, ceiling shifts,
extrema and factorial agree with their mathematical specifications.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- The fast operations of Lean's kernel, in the notation of the library. -/
theorem fast_eq (a b : Nat) :
    Nat.add a b = a + b ∧ Nat.sub a b = a - b ∧ Nat.mul a b = a * b ∧ Nat.div a b = a / b ∧
    Nat.mod a b = a % b ∧ Nat.shiftLeft a b = a * 2 ^ b ∧ Nat.shiftRight a b = a / 2 ^ b ∧
    Nat.succ a = a + 1 ∧ Nat.land a b = a &&& b ∧ Nat.lor a b = a ||| b ∧
    Nat.xor a b = a ^^^ b ∧ (Nat.ble a b = true) = (a ≤ b) ∧ (Nat.beq a b = true) = (a = b) :=
  ⟨rfl, rfl, rfl, rfl, rfl, Nat.shiftLeft_eq a b, Nat.shiftRight_eq_div_pow a b, rfl, rfl, rfl,
    rfl, Nat.ble_eq, Nat.beq_eq⟩


/-- `bit n i` is bit `i` of `n`, as zero or one. -/
theorem bit_eq (n i : Nat) : bit n i = (n.testBit i).toNat := by
  change (n >>> i) &&& 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;> simp [h]

/-- `testBit n i` is `Nat.testBit n i`. -/
theorem testBit_eq (n i : Nat) : testBit n i = n.testBit i := by
  change Nat.beq ((n >>> i) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.testBit, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (n >>> i) with h | h <;> rw [h] <;> rfl

/-- `lowBits n k` is the remainder of `n` modulo `2 ^ k`. -/
theorem lowBits_eq (n k : Nat) : lowBits n k = n % 2 ^ k := by
  change n &&& (1 <<< k - 1) = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]

/-- `ceilDiv a b` is `(a + (b - 1)) / b`. -/
theorem ceilDiv_eq (a b : Nat) : ceilDiv a b = (a + (b - 1)) / b := rfl

/-- The ceiling of a quotient is its floor, plus one unless the division is exact. -/
theorem ceilDiv_eq_ite {a b : Nat} (hb : 0 < b) :
    ceilDiv a b = if a / b * b = a then a / b else a / b + 1 := by
  rw [ceilDiv_eq]
  have hd := Nat.div_add_mod a b
  have hr := Nat.mod_lt a hb
  split_ifs with h
  · apply Nat.div_eq_of_lt_le
    · rw [Nat.mul_comm] at h ⊢
      omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega
  · apply Nat.div_eq_of_lt_le
    · have : a % b ≠ 0 := fun h0 => h (by rw [Nat.mul_comm]; omega)
      rw [Nat.add_mul, Nat.one_mul]
      rw [Nat.mul_comm] at hd
      omega
    · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
      rw [Nat.mul_comm] at hd
      omega

/-- `ceilDiv a b` is Mathlib's ceiling division `a ⌈/⌉ b`, for every `b`. -/
theorem ceilDiv_eq_nat (a b : Nat) : ceilDiv a b = a ⌈/⌉ b := by
  rw [ceilDiv_eq, Nat.ceilDiv_eq_add_pred_div]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  · rw [Nat.add_sub_assoc hb]

/-- `b` times the ceiling of `a / b` is at least `a`. -/
theorem le_mul_ceilDiv {a b : Nat} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  rw [ceilDiv_eq_nat]
  simpa [smul_eq_mul] using le_smul_ceilDiv (b := a) hb

/-- `b` times the ceiling of `a / b` is less than `a + b`. -/
theorem mul_ceilDiv_lt {a b : Nat} (hb : 0 < b) : b * ceilDiv a b < a + b := by
  rw [ceilDiv_eq]
  have := Nat.div_mul_le_self (a + (b - 1)) b
  rw [Nat.mul_comm]
  omega

/-- `ceilShift n k` is the ceiling of `n / 2 ^ k`. -/
theorem ceilShift_eq (n k : Nat) : ceilShift n k = ceilDiv n (2 ^ k) := by
  change (n + (1 <<< k - 1)) >>> k = _
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow, ceilDiv_eq]

/--
The floor of a negated quotient is the negated ceiling: `(-a) / b = -⌈a / b⌉` for naturals `a`
and `b > 0`, with the integer division that rounds down.
-/
theorem neg_ediv_natCast {a b : Nat} (hb : 0 < b) :
    (-(a : Int)) / (b : Int) = -((ceilDiv a b : Nat) : Int) := by
  have h1 := le_mul_ceilDiv (a := a) hb
  have h2 := mul_ceilDiv_lt (a := a) hb
  refine ((Int.ediv_emod_unique (r := (b : Int) * ceilDiv a b - a) (by exact_mod_cast hb)).mpr
    ⟨by ring, ?_, ?_⟩).1
  · have : ((a : Nat) : Int) ≤ ((b * ceilDiv a b : Nat) : Int) := by exact_mod_cast h1
    push_cast at this
    omega
  · have : ((b * ceilDiv a b : Nat) : Int) < ((a + b : Nat) : Int) := by exact_mod_cast h2
    push_cast at this
    omega

/-- `maxNat a b` is the larger of `a` and `b`. -/
theorem maxNat_eq (a b : Nat) : maxNat a b = max a b := by
  change a + (b - a) = _
  omega

/-- `minNat a b` is the smaller of `a` and `b`. -/
theorem minNat_eq (a b : Nat) : minNat a b = min a b := by
  change a - (a - b) = _
  omega

/-- `factorial` is the factorial. -/
theorem factorial_eq (n : Nat) : factorial n = n.factorial := by
  induction n with
  | zero => rfl
  | succ k ih =>
    change (k + 1) * factorial k = _
    rw [ih, Nat.factorial_succ]

/-- Compiled code runs Mathlib's `Nat.factorial`. -/
compiled_as factorial := Nat.factorial by factorial_eq
end FloatLib.Numerics.Kernel
