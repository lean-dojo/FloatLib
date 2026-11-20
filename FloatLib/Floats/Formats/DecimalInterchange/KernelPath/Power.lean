/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Division
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Runtime
public import Mathlib.Algebra.Order.Field.Power

/-!
# Kernel path of the decimal integer power

`Arithmetic.pown` (IEEE 754-2019 §9.2) rounds the exact power of a finite datum once. With a
natural exponent the exact power is a coefficient at an exponent, which `KernelPath.project`
rounds; with a negative exponent it is the reciprocal of one, a ratio of natural numbers on the
scale of the least quantum, which `KernelPath.projectRatio` rounds.

`pown` is the kernel form: the power of the coefficient, the quantum exponent times the
exponent of the power as the preferred exponent, and the sign of an odd power of a negative
datum (`powerSign`). A zero to a negative power, an infinity and a NaN are left to the
specification. `pown_eq`, tagged `@[kernel_optimize]`, proves it equal to the specification for
every format, rounding direction, datum and integer exponent.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/--
Whether an integer power with the exponent `exponent` of a datum of sign `negative` is
negative, by the parity of the exponent read off its constructor (`powerSign_eq`).
-/
def powerSign (negative : Bool) (exponent : Int) : Bool :=
  Bool.and negative
    (Int.casesOn (motive := fun _ => Bool) exponent (fun k => Nat.beq (Nat.mod k 2) 1)
      (fun k => Nat.beq (Nat.mod k 2) 0))

/-- `powerSign` is the sign of a power in the specification. -/
theorem powerSign_eq (negative : Bool) (exponent : Int) :
    powerSign negative exponent = Arithmetic.powerSign negative exponent := by
  unfold powerSign Arithmetic.powerSign
  congr 1
  rcases exponent with k | k
  · change Nat.beq (k % 2) 1 = decide (((k : Nat) : Int) % 2 = 1)
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
    omega
  · change Nat.beq (k % 2) 0 = decide (Int.negSucc k % 2 = 1)
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, Int.negSucc_eq]
    omega

/--
The sign that the specification gives an integer power of a finite datum is `powerSign`, also
when the power is zero.
-/
theorem zpow_sign (s : Bool) (c : Nat) (q n : Int) :
    (if Datum.finiteValue s c q ^ n = 0 then Arithmetic.powerSign s n
      else decide (Datum.finiteValue s c q ^ n < 0)) = Arithmetic.powerSign s n := by
  by_cases hzero : Datum.finiteValue s c q ^ n = 0
  · rw [ite_eq_left hzero]
  · rw [ite_eq_right hzero]
    by_cases hc : c = 0
    · have hvalue : Datum.finiteValue s c q = 0 := (Datum.finiteValue_eq_zero_iff s c q).2 hc
      have hn : n = 0 := by
        by_contra hne
        exact hzero (by rw [hvalue, zero_zpow n hne])
      subst hn
      simp [Arithmetic.powerSign]
    · have hpos : (0 : ℚ) < (c : ℚ) * (10 : ℚ) ^ q :=
        mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hc)) (zpow_pos (by norm_num) _)
      cases s
      · have hvalue : (0 : ℚ) < Datum.finiteValue false c q := by
          simpa [Datum.finiteValue] using hpos
        have hpower := zpow_pos hvalue n
        simp [Arithmetic.powerSign, hpower.le]
      · have hvalue : Datum.finiteValue true c q < 0 := by
          simpa [Datum.finiteValue] using hpos
        rcases Int.even_or_odd n with heven | hodd
        · have hmod : n % 2 = 0 := Int.even_iff.1 heven
          have hpower := heven.zpow_nonneg (Datum.finiteValue true c q)
          simp [Arithmetic.powerSign, hmod, hpower]
        · have hmod : n % 2 = 1 := Int.odd_iff.1 hodd
          have hpower := hodd.zpow_neg_iff.2 hvalue
          simp [Arithmetic.powerSign, hmod, hpower]

/-- A power of ten as the ratio of two powers of ten on the scale of the least quantum. -/
theorem zpow_eq_scaled (f : Format) (e : Int) {a b : Nat}
    (hab : (a : Int) - (b : Int) = e + f.bias) :
    (10 : ℚ) ^ e = (10 : ℚ) ^ a / (10 : ℚ) ^ b * (10 : ℚ) ^ f.minQuantum := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  rw [← zpow_natCast (10 : ℚ) a, ← zpow_natCast (10 : ℚ) b, ← zpow_sub₀ hten, ← zpow_add₀ hten]
  congr 1
  unfold Format.minQuantum
  omega

/--
Kernel form of `Arithmetic.pown` (`pown_eq`): for a finite datum and a natural exponent the
power of the coefficient is projected at the quantum exponent times the exponent of the power;
for a nonzero finite datum and a negative exponent the reciprocal of that power is rounded as a
ratio. A zero to a negative power, an infinity and a NaN are left to the specification.
-/
def pown (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Int.casesOn (motive := fun _ => Outcome) n
        (fun k => project f mode (powerSign s n) (Nat.pow c k) (Int.mul q n))
        (fun k =>
          Bool.casesOn (motive := fun _ => Outcome) (Nat.beq c 0)
            ((fun preferred =>
              offsets preferred f.bias fun above below =>
                projectRatio f mode (powerSign s n) (Nat.pow 10 above)
                  (Nat.mul (Nat.pow c (Nat.succ k)) (Nat.pow 10 below)) preferred)
              (Int.mul q n))
            (Arithmetic.pown f mode x n)))
    (fun _ => Arithmetic.pown f mode x n) (fun _ _ _ => Arithmetic.pown f mode x n)

/--
IEEE 754-2019 §9.2 `pown` on decimal data is its kernel form, for every format, rounding
direction, datum and integer exponent: the same datum and the same flags.
-/
@[kernel_optimize] theorem pown_eq (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    Arithmetic.pown f mode x n = pown f mode x n := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  have hmul : ∀ m k : Int, Int.mul m k = m * k := fun _ _ => rfl
  rcases n with k | k
  · change _ = project f mode (powerSign s (Int.ofNat k)) (Nat.pow c k) (Int.mul q (Int.ofNat k))
    have hspec : Arithmetic.pown f mode (.finite s c q) (Int.ofNat k) =
        DecimalInterchange.project f mode (Datum.finiteValue s c q ^ (Int.ofNat k))
          (q * Int.ofNat k) (Arithmetic.powerSign s (Int.ofNat k)) := by
      simp [Arithmetic.pown]
    rw [hspec, project_eq, DecimalInterchange.project, powerSign_eq, zpow_sign, hmul]
    congr 1
    rw [abs_zpow, Datum.finiteValue_abs, Int.ofNat_eq_natCast, zpow_natCast, mul_pow,
      ← zpow_natCast ((10 : ℚ) ^ q) k, ← zpow_mul, show Nat.pow c k = c ^ k from rfl,
      Nat.cast_pow]
  · rcases c with _ | c
    · rfl
    · change _ = (fun preferred =>
          offsets preferred f.bias fun above below =>
            projectRatio f mode (powerSign s (Int.negSucc k)) (Nat.pow 10 above)
              (Nat.mul (Nat.pow (c + 1) (Nat.succ k)) (Nat.pow 10 below)) preferred)
        (Int.mul q (Int.negSucc k))
      have hspec : Arithmetic.pown f mode (.finite s (c + 1) q) (Int.negSucc k) =
          DecimalInterchange.project f mode (Datum.finiteValue s (c + 1) q ^ (Int.negSucc k))
            (q * Int.negSucc k) (Arithmetic.powerSign s (Int.negSucc k)) := by
        simp [Arithmetic.pown]
      dsimp only
      rw [offsets_eq]
      simp only [hmul, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one]
      generalize ha : (q * Int.negSucc k + f.bias).toNat = a
      generalize hb : (-(q * Int.negSucc k + f.bias)).toNat = b
      have hab : (a : Int) - (b : Int) = q * Int.negSucc k + f.bias := by omega
      rw [hspec, projectRatio_eq f mode _ _ (Nat.mul_ne_zero (by positivity) (by positivity)),
        DecimalInterchange.project, powerSign_eq, zpow_sign]
      congr 1
      rw [abs_zpow, Datum.finiteValue_abs, mul_zpow, ← zpow_mul,
        zpow_eq_scaled f (q * Int.negSucc k) hab, zpow_negSucc]
      push_cast
      field_simp

/-! ## Kernel shapes -/

kernel_shape powerSign
kernel_shape pown

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
