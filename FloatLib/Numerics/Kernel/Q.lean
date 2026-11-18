/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Z

/-!
# `Rat` operations for Lean's kernel

Core's `Rat` keeps every value in lowest terms. Its `Rat.add` and `Rat.mul` reach the gcd and
division through instances, dependent `if`s and `Int.divExact`.

The functions here take and return `Rat` and compute the same values (`QProof`). They use the
`Int` functions of `Z` for the numerator and reduce the fraction with `Nat.gcd` and natural-number
division, which the kernel computes with GMP. The two proof fields establish that the
denominator is nonzero and the fraction is in lowest terms.

They are for definitions that must keep the type `Rat`, such as FloatLib's rational enclosures. A
checker that can defer reduction can use `Frac` and call `Frac.normalize` when needed.

## Main definitions

* `Q.normalize num den h`, `Q.mk num den`: the rational `num / den` in lowest terms.
* `Q.add`, `Q.sub`, `Q.mul`, `Q.neg`, `Q.inv`, `Q.div`, `Q.pow`, `Q.abs`.
* `Q.mulPow2`, `Q.divPow2`: multiplication and division by `2 ^ k`.
* `Q.le`, `Q.lt`, `Q.beq`: comparisons as Booleans; `Q.min`, `Q.max`.
* `Q.floor`, `Q.ceil`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel.Q

/-- The absolute value of `-n` is `n`. -/
theorem natAbs_negOfNat (n : Nat) : (Z.negOfNat n).natAbs = n := by
  cases n <;> rfl

/-- `Z.natAbs` is the absolute value. -/
theorem natAbs_natAbs (x : Int) : Z.natAbs x = x.natAbs := by
  cases x <;> rfl

/-- The absolute value of a quotient rounded toward zero is the quotient of the absolute value. -/
theorem natAbs_tdivNat (x : Int) (d : Nat) : (Z.tdivNat x d).natAbs = x.natAbs / d := by
  cases x with
  | ofNat m => rfl
  | negSucc m => exact natAbs_negOfNat _

/-- The absolute value of a negation is the absolute value. -/
theorem natAbs_neg (x : Int) : (Z.neg x).natAbs = x.natAbs := by
  cases x with
  | ofNat m => exact natAbs_negOfNat m
  | negSucc m => rfl

/-- The absolute value of a power is the power of the absolute value. -/
theorem natAbs_pow (x : Int) (n : Nat) : (Z.pow x n).natAbs = x.natAbs ^ n := by
  cases x with
  | ofNat m => rfl
  | negSucc m =>
    change (Nat.rec (motive := fun _ => Int) (Int.ofNat ((m + 1) ^ n))
      (fun _ _ => Z.negOfNat ((m + 1) ^ n)) (n % 2)).natAbs = _
    cases n % 2 with
    | zero => rfl
    | succ k => exact natAbs_negOfNat _

/-- A nonzero denominator divided by its gcd with the numerator is not zero. -/
theorem den_ne_zero (num : Int) {den : Nat} (h : den ≠ 0) :
    Nat.div den (Nat.gcd (Z.natAbs num) den) ≠ 0 :=
  Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h))

/-- Numerator and denominator divided by their gcd are coprime. -/
theorem reduced (num : Int) {den : Nat} (h : den ≠ 0) :
    (Z.tdivNat num (Nat.gcd (Z.natAbs num) den)).natAbs.Coprime
      (Nat.div den (Nat.gcd (Z.natAbs num) den)) := by
  rw [natAbs_tdivNat, natAbs_natAbs]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero h))

/--
The rational `num / den` in lowest terms, for `den ≠ 0`: one gcd and two divisions. It is
`Rat.normalize num den h`.
-/
noncomputable def normalize (num : Int) (den : Nat) (h : den ≠ 0) : Rat :=
  ⟨Z.tdivNat num (Nat.gcd (Z.natAbs num) den), Nat.div den (Nat.gcd (Z.natAbs num) den),
    den_ne_zero num h, reduced num h⟩

/-- The rational `num / den` in lowest terms, and zero for `den = 0`. It is `mkRat num den`. -/
noncomputable def mk (num : Int) (den : Nat) : Rat :=
  Nat.rec (motive := fun _ => Rat) ⟨Int.ofNat 0, 1, by decide, by decide⟩
    (fun k _ => normalize num (Nat.succ k) (Nat.succ_ne_zero k)) den

/-- `a + b`. -/
noncomputable def add (a b : Rat) : Rat :=
  normalize (Z.add (Z.mul a.num (Int.ofNat b.den)) (Z.mul b.num (Int.ofNat a.den)))
    (Nat.mul a.den b.den) (Nat.mul_ne_zero a.den_nz b.den_nz)

/-- `a - b`. -/
noncomputable def sub (a b : Rat) : Rat :=
  normalize (Z.sub (Z.mul a.num (Int.ofNat b.den)) (Z.mul b.num (Int.ofNat a.den)))
    (Nat.mul a.den b.den) (Nat.mul_ne_zero a.den_nz b.den_nz)

/-- `a * b`. -/
noncomputable def mul (a b : Rat) : Rat :=
  normalize (Z.mul a.num b.num) (Nat.mul a.den b.den) (Nat.mul_ne_zero a.den_nz b.den_nz)

/-- `-a`: the numerator changes sign and nothing needs reducing. -/
noncomputable def neg (a : Rat) : Rat :=
  ⟨Z.neg a.num, a.den, a.den_nz, (natAbs_neg a.num).symm ▸ a.reduced⟩

/-- `a⁻¹`, and zero for zero. -/
noncomputable def inv (a : Rat) : Rat :=
  Int.rec (motive := fun _ => Rat) (fun n => mk (Int.ofNat a.den) n)
    (fun n => mk (Z.negOfNat a.den) (Nat.succ n)) a.num

/-- `a / b`, and zero for `b = 0`. -/
noncomputable def div (a b : Rat) : Rat := mul a (inv b)

/-- `a ^ n`: one power of the numerator and one of the denominator, and nothing needs reducing. -/
noncomputable def pow (a : Rat) (n : Nat) : Rat :=
  ⟨Z.pow a.num n, Nat.pow a.den n, Nat.ne_of_gt (Nat.pow_pos a.den_pos),
    (natAbs_pow a.num n).symm ▸ a.reduced.pow n n⟩

/-- `|a|`. -/
noncomputable def abs (a : Rat) : Rat :=
  ⟨Int.ofNat (Z.natAbs a.num), a.den, a.den_nz, (natAbs_natAbs a.num).symm ▸ a.reduced⟩

/-- `a * 2 ^ k`. -/
noncomputable def mulPow2 (a : Rat) (k : Nat) : Rat :=
  normalize (Z.shiftLeft a.num k) a.den a.den_nz

/-- `a / 2 ^ k`. -/
noncomputable def divPow2 (a : Rat) (k : Nat) : Rat :=
  normalize a.num (Nat.shiftLeft a.den k)
    (Nat.ne_of_gt (Nat.lt_of_lt_of_le a.den_pos (Nat.le_shiftLeft)))

/-- Whether `a ≤ b`, by cross-multiplication. -/
noncomputable def le (a b : Rat) : Bool :=
  Int.ble' (Z.mul a.num (Int.ofNat b.den)) (Z.mul b.num (Int.ofNat a.den))

/-- Whether `a < b`, by cross-multiplication. -/
noncomputable def lt (a b : Rat) : Bool :=
  Int.blt' (Z.mul a.num (Int.ofNat b.den)) (Z.mul b.num (Int.ofNat a.den))

/-- Whether `a = b`: both fields agree, since both numbers are in lowest terms. -/
noncomputable def beq (a b : Rat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Nat.beq a.den b.den) (Int.beq' a.num b.num)

/-- The smaller of `a` and `b`. -/
noncomputable def min (a b : Rat) : Rat := Bool.rec (motive := fun _ => Rat) b a (le a b)

/-- The larger of `a` and `b`. -/
noncomputable def max (a b : Rat) : Rat := Bool.rec (motive := fun _ => Rat) a b (le a b)

/-- The largest integer at most `a`. -/
noncomputable def floor (a : Rat) : Int := Z.floorDiv a.num a.den

/-- The smallest integer at least `a`. -/
noncomputable def ceil (a : Rat) : Int := Z.ceilDiv a.num a.den

end FloatLib.Numerics.Kernel.Q
