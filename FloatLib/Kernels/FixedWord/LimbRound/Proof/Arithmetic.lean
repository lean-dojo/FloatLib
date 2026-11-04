/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.LimbRound.Runtime
public import FloatLib.Kernels.FixedWord.Product.Proof
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Data.Rat.Cast.Order

/-!
# Four-word subtraction, comparison, and widening

Here are the natural-number meanings of the four-word complement, subtraction, comparison, low-bit
and doubling helpers, and of the widening shift from two words to four. It's plain word arithmetic,
independent of the rounding kernels in `LimbRound.Proof.UInt256`.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

namespace UInt256

/-- The four-word complement is `2^256 - 1 - value`. -/
theorem complement_toNat (value : UInt256) :
    value.complement.toNat = 2 ^ 256 - 1 - value.toNat := by
  have h0 := value.limb0.toNat_lt
  have h1 := value.limb1.toNat_lt
  have h2 := value.limb2.toNat_lt
  have h3 := value.limb3.toNat_lt
  unfold complement UInt256.toNat
  simp only [UInt64.toNat_not, UInt64.size]
  omega

/-- Four-word subtraction agrees with `Nat` subtraction when the subtrahend is at most the
minuend. -/
theorem sub_toNat (x y : UInt256) (hordered : y.toNat ≤ x.toNat) :
    (sub x y).toNat = x.toNat - y.toNat := by
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  have hone : (⟨0, 0, 0, 1⟩ : UInt256).toNat = 1 := by simp [UInt256.toNat]
  unfold sub
  rw [add256_value_toNat, add256_value_toNat, complement_toNat, hone]
  omega

/-- Native four-word comparison agrees with comparison of mathematical values. -/
@[simp, grind =] theorem less_eq_true_iff (x y : UInt256) :
    less x y = true ↔ x.toNat < y.toNat := by
  have := x.limb0.toNat_lt
  have := x.limb1.toNat_lt
  have := x.limb2.toNat_lt
  have := y.limb0.toNat_lt
  have := y.limb1.toNat_lt
  have := y.limb2.toNat_lt
  unfold less UInt256.toNat
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj]
  omega

/-- Setting the low bit of a four-limb value agrees with natural-number bitwise OR. -/
theorem setLowBit_toNat (value : UInt256) : value.setLowBit.toNat = value.toNat ||| 1 := by
  have hlow := value.limb0.toNat_lt
  have hone : (1 : Nat) < 2 ^ 64 := by norm_num
  have hlowSet : value.limb0.toNat ||| 1 < 2 ^ 64 := Nat.or_lt_two_pow hlow hone
  have hsplit (low : Nat) :
      low + value.limb1.toNat * 2 ^ 64 + value.limb2.toNat * 2 ^ 128 +
          value.limb3.toNat * 2 ^ 192 =
        2 ^ 64 * (value.limb1.toNat + value.limb2.toNat * 2 ^ 64 +
          value.limb3.toNat * 2 ^ 128) + low := by
    ring
  unfold setLowBit UInt256.toNat
  dsimp only
  rw [UInt64.toNat_or, UInt64.toNat_one, hsplit, hsplit,
    Nat.two_pow_add_eq_or_of_lt hlowSet, Nat.two_pow_add_eq_or_of_lt hlow, Nat.or_assoc]

/-- Doubling a four-limb value below `2^255` agrees with `Nat` doubling. -/
theorem double_toNat (value : UInt256) (hvalue : value.toNat < 2 ^ 255) :
    value.double.toNat = value.toNat * 2 := by
  unfold double
  rw [add256_value_toNat, Nat.mod_eq_of_lt (by omega)]
  omega

end UInt256

/-- The widening shuffle agrees with `<<<` for every shift below 128. -/
theorem UInt128.shiftLeft256_toNat (value : UInt128) (shift : Nat) (hshift : shift < 128) :
    (value.shiftLeft256 shift).toNat = value.toNat <<< shift := by
  unfold UInt128.shiftLeft256
  by_cases hzero : shift = 0
  · subst hzero
    simp
  rw [ite_eq_right (by simpa using hzero)]
  by_cases hsmall : shift < 64
  · rw [ite_eq_left hsmall]
    have hcomplementPos : 0 < 64 - shift := by omega
    have hcomplementLt : 64 - shift < 64 := by omega
    have hcomplement : 64 - (64 - shift) = shift := by omega
    have hlow := shiftLeftLowBits_toNat value.lo (64 - shift) hcomplementPos
    have hmiddle := shiftedPair_toNat value.lo value.hi (64 - shift) hcomplementPos hcomplementLt
    have hhigh := FixedWord.shiftRight_toNat value.hi (64 - shift) hcomplementLt
    rw [hcomplement] at hlow hmiddle
    rw [Nat.shiftRight_eq_div_pow] at hhigh
    unfold UInt256.toNat
    dsimp only
    rw [hlow, hmiddle, hhigh]
    unfold UInt128.toNat
    have hlo := (Nat.mod_add_div value.lo.toNat (2 ^ (64 - shift))).symm
    have hhi := (Nat.mod_add_div value.hi.toNat (2 ^ (64 - shift))).symm
    have hpow : 2 ^ (64 - shift) * 2 ^ shift = 2 ^ 64 := by
      rw [← pow_add]
      congr 1
      omega
    rw [Nat.shiftLeft_eq]
    set complementPow := 2 ^ (64 - shift) with hcomplementDef
    set rlo := value.lo.toNat % complementPow
    set qlo := value.lo.toNat / complementPow
    set rhi := value.hi.toNat % complementPow
    set qhi := value.hi.toNat / complementPow
    rw [hlo, hhi]
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num,
      show (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 64 * 2 ^ 64 by norm_num, ← hpow]
    simp only [UInt64.toNat_zero, zero_mul, add_zero]
    ring
  rw [ite_eq_right hsmall]
  by_cases h64 : shift = 64
  · subst h64
    simp only [beq_self_eq_true, ite_true]
    simp [UInt256.toNat, UInt128.toNat, Nat.shiftLeft_eq]
    ring
  rw [ite_eq_right (by simpa using h64)]
  exact UInt256.toNat_ofUInt128ShiftedLeft value shift (by omega) hshift

end FloatLib.Numerics.FixedWord
