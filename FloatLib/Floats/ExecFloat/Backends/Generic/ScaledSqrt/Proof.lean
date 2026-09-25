/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Generic.ScaledSqrt.Runtime
public import FloatLib.Kernels.FixedWord.IntegerSquareRoot.Proof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-!
# Exact square roots at the rounding scale

Integer division by a square commutes with the floor square root. Applying this at a power of two
retains the guard bit, while comparison with the reconstructed square recovers the sticky bit.
These identities preserve the entire extended mantissa and the unpacked rounding result.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.ScaledSqrt

open Float.Model.UnpackedFloat

/-- Dividing a radicand by an integer square commutes with its floor square root. -/
theorem sqrt_div_square (n d : Nat) : Nat.sqrt (n / (d * d)) = Nat.sqrt n / d := by
  by_cases hd : d = 0
  · simp [hd]
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hdd : 0 < d * d := Nat.mul_pos hdpos hdpos
  symm
  apply Nat.eq_sqrt.mpr
  constructor
  · apply (Nat.le_div_iff_mul_le hdd).mpr
    have h := Nat.mul_self_le_mul_self (Nat.div_mul_le_self (Nat.sqrt n) d)
    calc
      (Nat.sqrt n / d) * (Nat.sqrt n / d) * (d * d) =
          ((Nat.sqrt n / d) * d) * ((Nat.sqrt n / d) * d) := by ring
      _ ≤ Nat.sqrt n * Nat.sqrt n := h
      _ ≤ n := Nat.sqrt_le n
  · apply (Nat.div_lt_iff_lt_mul hdd).mpr
    have h : Nat.sqrt n < (Nat.sqrt n / d + 1) * d :=
      by simpa [Nat.mul_comm] using Nat.lt_mul_div_succ (Nat.sqrt n) hdpos
    have hn := Nat.sqrt_lt.mp h
    nlinarith only [hn]

/-- Discarding twice as many radicand bits gives exactly the shifted floor square root. -/
theorem sqrt_shift (n k : Nat) : Nat.sqrt (n >>> (2 * k)) = Nat.sqrt n >>> k := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
    rw [show 2 * k = k + k by omega, pow_add]
  rw [hp, sqrt_div_square]

/-- A positive extended-mantissa shift has one guard bit and the exact discarded-bit sticky flag. -/
theorem shift_extended_succ (em : ExtendedMantissa) (k : Nat) :
    (em >>> (k + 1)) =
      ⟨em.mantissa / 2 ^ (k + 1), em.mantissa / 2 ^ k % 2 != 0,
        em.mantissa % 2 ^ k != 0 || em.roundBit || em.stickyBit⟩ := by
  induction k with
  | zero =>
    cases em
    simp [HShiftRight.hShiftRight, Nat.repeat, ExtendedMantissa.shiftRightOne, Nat.mod_one]
  | succ k ih =>
    change (k + 1 + 1).repeat ExtendedMantissa.shiftRightOne em = _
    simp only [Nat.repeat]
    change ExtendedMantissa.shiftRightOne (em >>> (k + 1)) = _
    rw [ih]
    simp only [ExtendedMantissa.shiftRightOne, Nat.pow_succ, Nat.div_div_eq_div_mul]
    congr 1
    have hmod : em.mantissa % (2 ^ k * 2) =
        em.mantissa % 2 ^ k + 2 ^ k * (em.mantissa / 2 ^ k % 2) := by
      rw [Nat.mod_mul]
    have hz : em.mantissa % (2 ^ k * 2) = 0 ↔
        em.mantissa % 2 ^ k = 0 ∧ em.mantissa / 2 ^ k % 2 = 0 := by
      rw [hmod, Nat.add_eq_zero_iff]
      simp
    apply Bool.eq_iff_iff.mpr
    simp [hz]
    tauto

private theorem sqrt_grid_eq_iff (n d : Nat) :
    n = (Nat.sqrt n / d * (Nat.sqrt n / d)) * (d * d) ↔
      n = Nat.sqrt n * Nat.sqrt n ∧ Nat.sqrt n % d = 0 := by
  have hmul : (Nat.sqrt n / d * (Nat.sqrt n / d)) * (d * d) =
      (Nat.sqrt n / d * d) * (Nat.sqrt n / d * d) := by ring
  constructor
  · intro h
    have hr : Nat.sqrt n = Nat.sqrt n / d * d := by
      conv_lhs => rw [h, hmul, Nat.sqrt_eq]
    constructor
    · rw [hr]
      exact h.trans hmul
    · have hdiv := Nat.mod_add_div (Nat.sqrt n) d
      rw [Nat.mul_comm d] at hdiv
      omega
  · rintro ⟨hn, hm⟩
    have hr : Nat.sqrt n = Nat.sqrt n / d * d := by
      have hdiv := Nat.mod_add_div (Nat.sqrt n) d
      rw [Nat.mul_comm d] at hdiv
      omega
    calc
      n = Nat.sqrt n * Nat.sqrt n := hn
      _ = (Nat.sqrt n / d * d) * (Nat.sqrt n / d * d) := by rw [← hr]
      _ = _ := hmul.symm

/-- The reduced radicand preserves every field of the original shifted extended mantissa. -/
theorem shifted_eq (n k : Nat) :
    shifted n k =
      (ExtendedMantissa.ofMantissaAndAccuracy (Nat.sqrt n)
        (accuracy n (Nat.sqrt n)) >>> k) := by
  let r := Nat.sqrt n
  have hz : n - r * r = 0 ↔ n = r * r := by
    have := Nat.sqrt_le n
    dsimp [r]
    omega
  cases k with
  | zero =>
    simp [shifted,
      FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt,
      HShiftRight.hShiftRight, Nat.repeat]
  | succ k =>
    rw [shift_extended_succ]
    simp only [shifted,
      FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat_eq_sqrt]
    rw [sqrt_shift]
    simp only [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
      Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hp : 2 ^ (2 * k) = 2 ^ k * 2 ^ k := by
      rw [show 2 * k = k + k by omega, pow_add]
    rw [hp]
    have hg := sqrt_grid_eq_iff n (2 ^ k)
    by_cases hexact : n - r * r = 0
    · have hn : n = Nat.sqrt n * Nat.sqrt n := hz.mp hexact
      have hg' : n = Nat.sqrt n / 2 ^ k * (Nat.sqrt n / 2 ^ k) *
          (2 ^ k * 2 ^ k) ↔ Nat.sqrt n % 2 ^ k = 0 := by
        exact ⟨fun h => (hg.mp h).2, fun h => hg.mpr ⟨hn, h⟩⟩
      simp only [accuracy,
        show n - Nat.sqrt n * Nat.sqrt n = 0 from hexact, ite_true,
        ExtendedMantissa.ofMantissaAndAccuracy]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp [hg']
    · have hn : ¬ n = Nat.sqrt n * Nat.sqrt n := hz.not.mp hexact
      have hg' : ¬ n = Nat.sqrt n / 2 ^ k * (Nat.sqrt n / 2 ^ k) *
          (2 ^ k * 2 ^ k) := fun h => hn (hg.mp h).1
      simp only [accuracy,
        show ¬ n - Nat.sqrt n * Nat.sqrt n = 0 from hexact, ite_false]
      split <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, hg']

private theorem log2_sqrt (n : Nat) : (Nat.sqrt n).log2 = n.log2 / 2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hsqrtPos : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (Nat.pos_of_ne_zero hn)
  apply (Nat.log2_eq_iff (Nat.ne_of_gt hsqrtPos)).mpr
  constructor
  · rw [Nat.le_sqrt, ← Nat.pow_add]
    calc
      2 ^ (n.log2 / 2 + n.log2 / 2) ≤ 2 ^ n.log2 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n := Nat.log2_self_le hn
  · rw [Nat.sqrt_lt, ← Nat.pow_add]
    calc
      n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
      _ ≤ 2 ^ ((n.log2 / 2 + 1) + (n.log2 / 2 + 1)) :=
        Nat.pow_le_pow_right (by decide) (by omega)

/-- Scaling before the root preserves the complete unpacked result, including normalization. -/
theorem round_eq (spec : Float.Model.Format) (sign : Sign) (n : Nat) (e : Int) :
    round spec sign n e =
      roundWithAccuracy spec sign (Nat.sqrt n) e
        (accuracy n (Nat.sqrt n)) := by
  simp only [round, roundWithAccuracy, shiftToTargetExponent, shiftToExponent,
    Float.Model.totalExponent,
    log2_sqrt, shifted_eq]
  rfl

end FloatLib.Floats.Formats.BinaryInterchange.Model.ScaledSqrt
