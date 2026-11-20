/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Power
public import FloatLib.Kernels.IntegerRoot.Proof

/-!
# Kernel path of the decimal root of integer degree

`Arithmetic.rootn` (IEEE 754-2019 §9.2) is specified on rational numbers: the radicand is put
on a grid by a rational quotient, an integer root brackets the root, and comparisons of
rational powers decide the rounding, the `inexact` flag and the tininess.

`rootRatio` computes the same outcome for a radicand `(num / den) × 10 ^ (degree × minQuantum)`,
a ratio of natural numbers on the power of the least quantum: the number of digits of the
integer part of the ratio gives the rounding quantum, `Numerics.IntegerRoot.newton` the integer
root of the ratio at the power of that quantum, and comparisons of natural numbers the increment
(`rootIncrement`), the `inexact` flag and the tininess. `rootRatio_eq` proves it equal to
`rootMagnitude` for every format, rounding direction, sign, nonzero degree, numerator, nonzero
denominator and preferred exponent.

`rootn` is the kernel form of `Arithmetic.rootn`, and `rootn_eq`, tagged `@[kernel_optimize]`,
proves the two equal for every format, rounding direction, datum and degree: a nonzero finite
datum at its exponent is such a ratio for a positive degree, and its reciprocal for a negative
degree. A zero, a negative datum with an even degree, the degree zero, an infinity and a NaN
are left to the specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/--
The amount, zero or one, by which the integer root `lower` of degree `degree` of `n / scale` is
incremented when the root of sign `negative` is rounded in `mode` (`rootIncrement_eq`): to
nearest by comparing the power of the midpoint with the radicand, with the parity of `lower`
at a tie, and away from zero in the direction of the sign when the root is not exact.
-/
def rootIncrement (mode : RoundingMode) (negative : Bool) (degree lower n scale : Nat) : Nat :=
  (fun midpoint twice =>
    RoundingMode.casesOn (motive := fun _ => Nat) mode
      (Bool.casesOn (motive := fun _ => Nat) (Nat.ble (Nat.succ midpoint) twice)
        (Bool.casesOn (motive := fun _ => Nat) (Nat.beq midpoint twice) 0 (Nat.mod lower 2))
        1)
      (flag (Nat.ble midpoint twice))
      0
      (flag (Bool.and (Bool.not negative)
        (Nat.ble (Nat.succ (Nat.mul (Nat.pow lower degree) scale)) n)))
      (flag (Bool.and negative (Nat.ble (Nat.succ (Nat.mul (Nat.pow lower degree) scale)) n))))
    (Nat.mul (Nat.pow (Nat.succ (Nat.mul 2 lower)) degree) scale) (Nat.mul (Nat.pow 2 degree) n)

/-- `rootIncrement` decides the increment of the specification on natural numbers. -/
theorem rootIncrement_eq (mode : RoundingMode) (negative : Bool) (degree lower n : Nat)
    {scale : Nat} (hscale : 0 < scale) :
    (if mode.rootIncrement negative degree lower ((n : ℚ) / (scale : ℚ)) then lower + 1
      else lower) = lower + rootIncrement mode negative degree lower n scale := by
  have hS : (0 : ℚ) < (scale : ℚ) := Nat.cast_pos.2 hscale
  have hlt : (2 * (lower : ℚ) + 1) ^ degree < 2 ^ degree * ((n : ℚ) / (scale : ℚ)) ↔
      (2 * lower + 1) ^ degree * scale < 2 ^ degree * n := by
    rw [← mul_div_assoc, lt_div_iff₀ hS]
    norm_cast
  have heq : (2 * (lower : ℚ) + 1) ^ degree = 2 ^ degree * ((n : ℚ) / (scale : ℚ)) ↔
      (2 * lower + 1) ^ degree * scale = 2 ^ degree * n := by
    rw [← mul_div_assoc, eq_div_iff hS.ne']
    norm_cast
  have hle : (2 * (lower : ℚ) + 1) ^ degree ≤ 2 ^ degree * ((n : ℚ) / (scale : ℚ)) ↔
      (2 * lower + 1) ^ degree * scale ≤ 2 ^ degree * n := by
    rw [← mul_div_assoc, le_div_iff₀ hS]
    norm_cast
  have hup : (lower : ℚ) ^ degree < (n : ℚ) / (scale : ℚ) ↔ lower ^ degree * scale < n := by
    rw [lt_div_iff₀ hS]
    norm_cast
  have hmodf : ∀ m k : Nat, Nat.mod m k = m % k := fun _ _ => rfl
  cases mode <;> cases negative <;>
    simp only [RoundingMode.rootIncrement, rootIncrement, flag_eq, hlt, heq, hle, hup, natBle_eq,
      natBeq_eq, hmodf, casesOn_decide, decide_eq_true_eq, Nat.mul_eq, Nat.pow_eq,
      Nat.succ_eq_add_one, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Bool.not_true,
      Bool.not_false, Bool.true_and, Bool.false_and] <;>
    split_ifs <;> omega

/--
The outcome of the root of degree `degree` of the radicand
`(num / den) × 10 ^ (degree × minQuantum)` rounded into `f` with the sign `negative`, with
`preferred` as the preferred exponent of an exact result (`rootRatio_eq`).
-/
def rootRatio (f : Format) (mode : RoundingMode) (negative : Bool) (degree num den : Nat)
    (preferred : Int) : Outcome :=
  (fun shift =>
    (fun scale =>
      (fun lower =>
        (fun rounded =>
          deliverRounded f mode negative rounded shift
            (Bool.not (Nat.beq (Nat.mul (Nat.pow rounded degree) scale) num))
            (Nat.ble (Nat.succ num)
              (Nat.mul den (Nat.pow (Nat.pow 10 degree) (Nat.mul 3 f.declets))))
            preferred)
          (Nat.add lower (rootIncrement mode negative degree lower num scale)))
        (IntegerRoot.newton degree (Nat.div num scale)))
      (Nat.mul den (Nat.pow (Nat.pow 10 degree) shift)))
    (Nat.sub (Nat.succ (Nat.div (Nat.pred (decimalLength (Nat.div num den))) degree))
      (Nat.succ (Nat.mul 3 f.declets)))

/--
`rootRatio` is the specified root of the radicand `(num / den) × 10 ^ (degree × minQuantum)`:
the same datum and the same flags, for every format, rounding direction, sign, nonzero degree,
numerator, nonzero denominator and preferred exponent.
-/
theorem rootRatio_eq (f : Format) (mode : RoundingMode) (negative : Bool) (degree num : Nat)
    {den : Nat} (hden : den ≠ 0) (preferred : Int) :
    rootRatio f mode negative degree num den preferred =
      rootMagnitude f mode negative degree
        ((num : ℚ) / (den : ℚ) * (10 : ℚ) ^ ((degree : Int) * f.minQuantum)) preferred := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  have hdenq : (0 : ℚ) < (den : ℚ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hden)
  have hmin : (0 : ℚ) < (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := zpow_pos (by norm_num) _
  have hdivf : ∀ m k : Nat, Nat.div m k = m / k := fun _ _ => rfl
  have hprecision : 3 * f.declets + 1 = f.precision := rfl
  unfold rootRatio
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one,
    Nat.pred_eq_sub_one, hdivf, decimalLength_eq_log, Nat.add_sub_cancel, hprecision,
    IntegerRoot.newton_eq_nthRoot]
  obtain ⟨r, hr⟩ : ∃ r : ℚ,
      r = (num : ℚ) / (den : ℚ) * (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := ⟨_, rfl⟩
  rw [← hr]
  have hscaled : r / (10 : ℚ) ^ ((degree : Int) * f.minQuantum) = (num : ℚ) / (den : ℚ) := by
    rw [hr, mul_div_assoc, div_self hmin.ne', mul_one]
  generalize hshift : Nat.log 10 (num / den) / degree + 1 - f.precision = shift
  have hquantum : rootQuantum f degree r = (shift : Int) - f.bias := by
    rw [rootQuantum, hscaled, rootScaleShift, Rat.natFloor_natCast_div_natCast, hshift,
      Format.minQuantum]
    ring
  have hscale : 0 < den * (10 ^ degree) ^ shift :=
    Nat.mul_pos (Nat.pos_of_ne_zero hden) (by positivity)
  have hpow : (10 : ℚ) ^ ((degree : Int) * ((shift : Int) - f.bias)) =
      (((10 ^ degree) ^ shift : Nat) : ℚ) * (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := by
    have hpower : (10 : ℚ) ^ ((degree : Int) * (shift : Int)) =
        (((10 ^ degree) ^ shift : Nat) : ℚ) := by
      rw [zpow_mul, zpow_natCast, zpow_natCast]
      norm_cast
    rw [Format.minQuantum, mul_sub, sub_eq_add_neg, zpow_add₀ hten, hpower, mul_neg]
  have hvalue : r / (10 : ℚ) ^ ((degree : Int) * ((shift : Int) - f.bias)) =
      (num : ℚ) / ((den * (10 ^ degree) ^ shift : Nat) : ℚ) := by
    rw [hpow, hr, mul_div_mul_right _ _ hmin.ne', div_div, Nat.cast_mul]
  have hround : mode.rootRound negative degree
        (r / (10 : ℚ) ^ ((degree : Int) * ((shift : Int) - f.bias))) =
      Nat.nthRoot degree (num / (den * (10 ^ degree) ^ shift)) +
        rootIncrement mode negative degree
          (Nat.nthRoot degree (num / (den * (10 ^ degree) ^ shift))) num
          (den * (10 ^ degree) ^ shift) := by
    rw [RoundingMode.rootRound, hvalue, rootFloor, Rat.natFloor_natCast_div_natCast,
      IntegerRoot.root_eq_nthRoot]
    exact rootIncrement_eq mode negative degree _ num hscale
  generalize (10 ^ degree) ^ shift = S at hscale hpow hvalue hround ⊢
  generalize hD : den * S = D at hscale hvalue hround ⊢
  generalize Nat.nthRoot degree (num / D) +
    rootIncrement mode negative degree (Nat.nthRoot degree (num / D)) num D = R at hround ⊢
  have hpower : ((10 : ℚ) ^ ((shift : Int) - f.bias)) ^ degree =
      (S : ℚ) * (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := by
    rw [← zpow_natCast ((10 : ℚ) ^ ((shift : Int) - f.bias)) degree, ← zpow_mul, mul_comm, hpow]
  have hval : ((rootPair f mode negative degree r).1 : ℚ) *
        (10 : ℚ) ^ (rootPair f mode negative degree r).2 =
      (R : ℚ) * (10 : ℚ) ^ ((shift : Int) - f.bias) := by
    rw [← hround, ← hquantum]
    exact Numerics.RadixText.carry_value 10 (by decide) _ _ _
  have hinexact : decide ((((rootPair f mode negative degree r).1 : ℚ) *
        (10 : ℚ) ^ (rootPair f mode negative degree r).2) ^ degree ≠ r) =
      !Nat.beq (R ^ degree * D) num := by
    have hcast : ((R : ℚ) ^ degree * (S : ℚ) * (den : ℚ) = (num : ℚ)) ↔
        R ^ degree * D = num := by
      rw [← hD, Nat.mul_comm den S, ← Nat.mul_assoc]
      norm_cast
    rw [hval, mul_pow, hpower, hr, ← mul_assoc, Bool.eq_iff_iff, decide_eq_true_eq, ne_eq,
      mul_left_inj' hmin.ne', eq_div_iff hdenq.ne', hcast, natBeq_eq]
    simp
  have htiny : decide (r < f.minNormal ^ degree) =
      Nat.ble (num + 1) (den * (10 ^ degree) ^ (3 * f.declets)) := by
    have hp : f.precision - 1 = 3 * f.declets := rfl
    have hnormal : f.minNormal ^ degree =
        (((10 ^ degree) ^ (3 * f.declets) : Nat) : ℚ) *
          (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := by
      rw [Format.minNormal, mul_pow, hp, ← zpow_natCast ((10 : ℚ) ^ f.minQuantum) degree,
        ← zpow_mul, mul_comm f.minQuantum, ← pow_mul, mul_comm (3 * f.declets) degree, pow_mul]
      norm_cast
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq, hnormal, ← div_lt_iff₀ hmin, hscaled,
      div_lt_iff₀ hdenq, Nat.add_one_le_iff, Nat.mul_comm den]
    norm_cast
  have hpair : rootPair f mode negative degree r =
      if R = f.coefficientBound then (f.payloadBound, (shift : Int) - f.bias + 1)
      else (R, (shift : Int) - f.bias) := by
    rw [rootPair, hquantum, hround, f.carry_eq]
  rw [rootMagnitude]
  dsimp only
  rw [hinexact, htiny]
  exact deliverRounded_eq f mode negative R shift _ _ preferred _ hpair

/--
A power of ten as the ratio of two powers of ten on the grid `10 ^ (degree × minQuantum)`.
-/
theorem zpow_eq_degree_ratio (f : Format) (degree : Nat) (e : Int) {a b : Nat}
    (hab : (a : Int) - (b : Int) = e + (degree : Int) * f.bias) :
    (10 : ℚ) ^ e =
      (10 : ℚ) ^ a / (10 : ℚ) ^ b * (10 : ℚ) ^ ((degree : Int) * f.minQuantum) := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  rw [← zpow_natCast (10 : ℚ) a, ← zpow_natCast (10 : ℚ) b, ← zpow_sub₀ hten, ← zpow_add₀ hten]
  congr 1
  rw [Format.minQuantum, mul_neg]
  linarith

/-- Whether an integer degree is even, by the parity read off its constructor. -/
def evenDegree (degree : Int) : Bool :=
  Int.casesOn (motive := fun _ => Bool) degree (fun k => Nat.beq (Nat.mod k 2) 0)
    (fun k => Nat.beq (Nat.mod k 2) 1)

/-- `evenDegree` decides whether an integer degree is even. -/
theorem evenDegree_eq (degree : Int) : evenDegree degree = decide (degree % 2 = 0) := by
  unfold evenDegree
  rcases degree with k | k
  · change Nat.beq (k % 2) 0 = decide (((k : Nat) : Int) % 2 = 0)
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff]
    omega
  · change Nat.beq (k % 2) 1 = decide (Int.negSucc k % 2 = 0)
    rw [Bool.eq_iff_iff, Nat.beq_eq, decide_eq_true_iff, Int.negSucc_eq]
    omega

/--
Kernel form of `Arithmetic.rootn` (`rootn_eq`): for a nonzero finite datum and a positive
degree the coefficient at its exponent is put on the grid `10 ^ (degree × minQuantum)` as a
ratio of natural numbers, for a negative degree its reciprocal, and `rootRatio` rounds the
root with the sign of an odd root of a negative datum. A zero, a negative datum with an even
degree, the degree zero, an infinity and a NaN are left to the specification.
-/
def rootn (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun s c q =>
      Bool.casesOn (motive := fun _ => Outcome)
        (Bool.or (Nat.beq c 0) (Bool.and s (evenDegree n)))
        (Int.casesOn (motive := fun _ => Outcome) n
          (fun k =>
            Bool.casesOn (motive := fun _ => Outcome) (Nat.beq k 0)
              (offsets q (Int.mul (Int.ofNat k) f.bias) fun above below =>
                rootRatio f mode (powerSign s n) k (Nat.mul c (Nat.pow 10 above))
                  (Nat.pow 10 below) (q / (Int.ofNat k)))
              (Arithmetic.rootn f mode x n))
          (fun k =>
            offsets (Int.neg q) (Int.mul (Int.ofNat (Nat.succ k)) f.bias) fun above below =>
              rootRatio f mode (powerSign s n) (Nat.succ k) (Nat.pow 10 above)
                (Nat.mul c (Nat.pow 10 below)) (Int.neg q / (Int.ofNat (Nat.succ k)))))
        (Arithmetic.rootn f mode x n))
    (fun _ => Arithmetic.rootn f mode x n) (fun _ _ _ => Arithmetic.rootn f mode x n)

/--
IEEE 754-2019 §9.2 `rootn` on decimal data is its kernel form, for every format, rounding
direction, datum and degree: the same datum and the same flags.
-/
@[kernel_optimize] theorem rootn_eq (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) :
    Arithmetic.rootn f mode x n = rootn f mode x n := by
  rcases x with ⟨s, c, q⟩ | s | ⟨s, t, p⟩ <;> try rfl
  have hmul : ∀ m k : Int, Int.mul m k = m * k := fun _ _ => rfl
  have hneg : ∀ m : Int, Int.neg m = -m := fun _ => rfl
  change _ = Bool.casesOn (motive := fun _ => Outcome)
    (Bool.or (Nat.beq c 0) (Bool.and s (evenDegree n))) _ _
  rw [evenDegree_eq, natBeq_eq]
  by_cases hc : c = 0
  · simp [hc]
  by_cases hinvalid : s = true ∧ n % 2 = 0
  · simp [hc, hinvalid.1, hinvalid.2]
  have hspecial : (s && decide (n % 2 = 0)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hinvalid
      ⟨(Bool.and_eq_true_iff.mp h).1, of_decide_eq_true (Bool.and_eq_true_iff.mp h).2⟩
  have hguard : (decide (c = 0) || s && decide (n % 2 = 0)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact hc (of_decide_eq_true h)
    · rw [hspecial] at h
      exact Bool.false_ne_true h
  rw [hguard]
  rcases n with k | k
  · rcases k with _ | k
    · rfl
    · change _ = offsets q (Int.mul (Int.ofNat (k + 1)) f.bias) fun above below =>
        rootRatio f mode (powerSign s (Int.ofNat (k + 1))) (k + 1) (Nat.mul c (Nat.pow 10 above))
          (Nat.pow 10 below) (q / (Int.ofNat (k + 1)))
      rw [offsets_eq]
      simp only [hmul, Nat.mul_eq, Nat.pow_eq]
      generalize ha : (q + Int.ofNat (k + 1) * f.bias).toNat = a
      generalize hb : (-(q + Int.ofNat (k + 1) * f.bias)).toNat = b
      have hab : (a : Int) - (b : Int) = q + ((k + 1 : Nat) : Int) * f.bias := by
        rw [← ha, ← hb]
        simp only [Int.ofNat_eq_natCast]
        omega
      have hspec : Arithmetic.rootn f mode (.finite s c q) (Int.ofNat (k + 1)) =
          rootMagnitude f mode (Arithmetic.powerSign s (Int.ofNat (k + 1))) (k + 1)
            ((c : ℚ) * (10 : ℚ) ^ q) (q / (Int.ofNat (k + 1))) := by
        have hn : (Int.ofNat (k + 1) : Int) ≠ 0 := by
          simp only [Int.ofNat_eq_natCast]
          omega
        have hpos : ¬ (Int.ofNat (k + 1) : Int) < 0 := by
          simp only [Int.ofNat_eq_natCast]
          omega
        simp only [Arithmetic.rootn, ite_eq_right hn, ite_eq_right hc, ite_eq_right hpos, hspecial,
          Bool.false_eq_true, ↓reduceIte, Arithmetic.powerSign]
        rfl
      rw [hspec, rootRatio_eq f mode _ _ _ (by positivity), powerSign_eq,
        zpow_eq_degree_ratio f (k + 1) q hab]
      congr 1
      push_cast
      ring
  · change _ = offsets (Int.neg q) (Int.mul (Int.ofNat (k + 1)) f.bias) fun above below =>
      rootRatio f mode (powerSign s (Int.negSucc k)) (k + 1) (Nat.pow 10 above)
        (Nat.mul c (Nat.pow 10 below)) (Int.neg q / (Int.ofNat (k + 1)))
    rw [offsets_eq]
    simp only [hmul, hneg, Nat.mul_eq, Nat.pow_eq]
    generalize ha : (-q + Int.ofNat (k + 1) * f.bias).toNat = a
    generalize hb : (-(-q + Int.ofNat (k + 1) * f.bias)).toNat = b
    have hab : (a : Int) - (b : Int) = -q + ((k + 1 : Nat) : Int) * f.bias := by
      rw [← ha, ← hb]
      simp only [Int.ofNat_eq_natCast]
      omega
    have hspec : Arithmetic.rootn f mode (.finite s c q) (Int.negSucc k) =
        rootMagnitude f mode (Arithmetic.powerSign s (Int.negSucc k)) (k + 1)
          (((c : ℚ) * (10 : ℚ) ^ q)⁻¹) (-q / (Int.ofNat (k + 1))) := by
      have hn : (Int.negSucc k : Int) ≠ 0 := by
        simp only [Int.negSucc_eq]
        omega
      have hlt : (Int.negSucc k : Int) < 0 := Int.negSucc_lt_zero k
      simp only [Arithmetic.rootn, ite_eq_right hn, ite_eq_right hc, ite_eq_left hlt, hspecial,
        Bool.false_eq_true, ↓reduceIte, Arithmetic.powerSign]
      rfl
    rw [hspec, rootRatio_eq f mode _ _ _ (Nat.mul_ne_zero hc (by positivity)), powerSign_eq,
      mul_inv, ← zpow_neg, zpow_eq_degree_ratio f (k + 1) (-q) hab]
    congr 1
    push_cast
    field_simp

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
