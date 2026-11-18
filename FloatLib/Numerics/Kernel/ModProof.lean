/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Arithmetic
public import FloatLib.Numerics.Kernel.Bits.Proof.PopCount
public import FloatLib.Numerics.Kernel.Mod

import Mathlib.Algebra.Ring.Divisibility.Basic

/-!
# The kernel modular operations compute powers and inverses

* `powModWindow_eq` and `powMod_eq`: `powModWindow w a e n = a ^ e % n` and
  `powMod a e n = a ^ e % n`, for every window, base, exponent and modulus, zero included.
* `isInvMod_iff`: `isInvMod a x n = true ↔ a * x % n = 1 % n`.
* `invMod_spec`: for coprime `a` and `n`, `a * invMod a n % n = 1 % n`.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- The loop of `powModWindow`, named for the proof. -/
private noncomputable def powLoop (w n : Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ step base e acc =>
      Bool.rec (motive := fun _ => Nat)
        (step (Nat.mod (Nat.pow base (Nat.shiftLeft 1 (Nat.succ w))) n)
          (Nat.shiftRight e (Nat.succ w))
          (Nat.mod
            (Nat.mul acc (Nat.pow base (Nat.land e (Nat.sub (Nat.shiftLeft 1 (Nat.succ w)) 1))))
            n))
        acc
        (Nat.beq e 0))

private theorem powLoop_succ (w n count base e acc : Nat) :
    powLoop w n (count + 1) base e acc =
      Bool.rec (motive := fun _ => Nat)
        (powLoop w n count (base ^ (1 <<< (w + 1)) % n) (e >>> (w + 1))
          (acc * base ^ (e &&& (1 <<< (w + 1) - 1)) % n))
        acc (Nat.beq e 0) := rfl

/-- With a count above the exponent and a reduced product, the loop returns
`acc * base ^ e % n`. -/
private theorem powLoop_eq (w n : Nat) :
    ∀ count base e acc : Nat, e < count → acc % n = acc →
      powLoop w n count base e acc = acc * base ^ e % n := by
  intro count
  induction count with
  | zero => intro base e acc he; omega
  | succ count ih =>
    intro base e acc he hacc
    rw [powLoop_succ]
    by_cases h0 : e = 0
    · subst h0
      change acc = _
      rw [Nat.pow_zero, Nat.mul_one, hacc]
    · have hbeq : Nat.beq e 0 = false := by
        cases h : Nat.beq e 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) h0
      have hone : 1 < 2 ^ (w + 1) := Nat.one_lt_two_pow (by omega)
      have hdiv : e / 2 ^ (w + 1) < count :=
        lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero h0) hone) (by omega)
      rw [hbeq]
      change powLoop w n count _ _ _ = _
      rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow,
        Nat.and_two_pow_sub_one_eq_mod, ih _ _ _ hdiv (Nat.mod_mod _ _)]
      conv_rhs => rw [← Nat.mod_add_div e (2 ^ (w + 1)), Nat.pow_add, Nat.pow_mul, ← Nat.mul_assoc]
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod]

/-- `powModWindow w a e n` is `a ^ e % n`, for every window and every modulus. -/
theorem powModWindow_eq (w a e n : Nat) : powModWindow w a e n = a ^ e % n := by
  change powLoop w n (Nat.succ e) (a % n) e (1 % n) = _
  rw [powLoop_eq w n (Nat.succ e) _ e _ (Nat.lt_succ_self e) (Nat.mod_mod 1 n)]
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod, ← Nat.mul_mod, Nat.one_mul]

/-- `powMod a e n` is `a ^ e % n`, for every modulus. -/
theorem powMod_eq (a e n : Nat) : powMod a e n = a ^ e % n := by
  unfold powMod
  cases Nat.beq (Nat.shiftRight n 1280) 0 <;> exact powModWindow_eq _ a e n

/-- `isInvMod` checks `a * x % n = 1 % n`. -/
theorem isInvMod_iff (a x n : Nat) : isInvMod a x n = true ↔ a * x % n = 1 % n := by
  change Nat.beq (a * x % n) (1 % n) = true ↔ _
  rw [Nat.beq_eq]

/-- The loop of `invMod`, named for the proof. -/
private noncomputable def invLoop (n : Nat) : Nat → Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat) (fun _ _ s₀ _ => s₀)
    (fun _ step r₀ r₁ s₀ s₁ =>
      Bool.rec (motive := fun _ => Nat)
        (step r₁ (Nat.mod r₀ r₁) s₁
          (Nat.mod (Nat.add s₀ (Nat.sub n (Nat.mod (Nat.mul (Nat.div r₀ r₁) s₁) n))) n))
        s₀
        (Nat.beq r₁ 0))

private theorem invLoop_succ (n count r₀ r₁ s₀ s₁ : Nat) :
    invLoop n (count + 1) r₀ r₁ s₀ s₁ =
      Bool.rec (motive := fun _ => Nat)
        (invLoop n count r₁ (r₀ % r₁) s₁ ((s₀ + (n - r₀ / r₁ * s₁ % n)) % n)) s₀
        (Nat.beq r₁ 0) := rfl

/-- The loop of `invMod` keeps `rᵢ ≡ sᵢ * a` modulo `n` and the gcd of the two remainders, so
with coprime remainders it ends on a residue `s` with `s * a ≡ 1`. -/
private theorem invMod_loop (a n : Nat) (hn : 0 < n) :
    ∀ count r₀ r₁ s₀ s₁ : Nat, r₁ < count → Nat.gcd r₀ r₁ = 1 →
      ((s₀ : Int) * a) % n = (r₀ : Int) % n → ((s₁ : Int) * a) % n = (r₁ : Int) % n →
      ((invLoop n count r₀ r₁ s₀ s₁ : Nat) : Int) * a % n = 1 % n := by
  intro count
  induction count with
  | zero => intro r₀ r₁ s₀ s₁ h; omega
  | succ count ih =>
    intro r₀ r₁ s₀ s₁ hcount hgcd h₀ h₁
    rw [invLoop_succ]
    by_cases hzero : r₁ = 0
    · subst hzero
      rw [Nat.gcd_zero_right] at hgcd
      subst hgcd
      change (s₀ : Int) * a % n = 1 % n
      rw [h₀]
      rfl
    · have hbeq : Nat.beq r₁ 0 = false := by
        cases h : Nat.beq r₁ 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hzero
      have hpos : 0 < r₁ := Nat.pos_of_ne_zero hzero
      rw [hbeq]
      refine ih r₁ (r₀ % r₁) s₁ _ (by have := Nat.mod_lt r₀ hpos; omega) ?_ h₁ ?_
      · rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
        exact hgcd
      · have hlt : r₀ / r₁ * s₁ % n < n := Nat.mod_lt _ hn
        have hcast : (((s₀ + (n - r₀ / r₁ * s₁ % n)) % n : Nat) : Int) =
            ((s₀ : Int) + (n - ((r₀ / r₁ : Nat) : Int) * s₁ % n)) % n := by
          rw [Int.natCast_mod, Nat.cast_add, Nat.cast_sub hlt.le, Int.natCast_mod, Nat.cast_mul]
        have hr : ((r₀ % r₁ : Nat) : Int) = (r₀ : Int) - ((r₀ / r₁ : Nat) : Int) * r₁ := by
          have := Nat.div_add_mod r₀ r₁
          have hc : ((r₁ * (r₀ / r₁) + r₀ % r₁ : Nat) : Int) = (r₀ : Int) := by rw [this]
          rw [Nat.cast_add, Nat.cast_mul] at hc
          linarith
        rw [hcast, hr, Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.mul_emod]
        have key : ((s₀ : Int) + (n - ((r₀ / r₁ : Nat) : Int) * s₁ % n)) * a -
            ((r₀ : Int) - ((r₀ / r₁ : Nat) : Int) * r₁) =
            ((s₀ : Int) * a - r₀) - ((r₀ / r₁ : Nat) : Int) * ((s₁ : Int) * a - r₁) +
              n * (a + ((r₀ / r₁ : Nat) : Int) * s₁ / n * a) := by
          have := Int.mul_ediv_add_emod (((r₀ / r₁ : Nat) : Int) * s₁) n
          have e : ((r₀ / r₁ : Nat) : Int) * s₁ % n =
              ((r₀ / r₁ : Nat) : Int) * s₁ - n * (((r₀ / r₁ : Nat) : Int) * s₁ / n) := by linarith
          rw [e]
          ring
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, key]
        have d₀ : (n : Int) ∣ (s₀ : Int) * a - r₀ :=
          Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h₀)
        have d₁ : (n : Int) ∣ (s₁ : Int) * a - r₁ :=
          Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.1 h₁)
        exact Int.emod_eq_zero_of_dvd
          (dvd_add (dvd_sub d₀ (Dvd.dvd.mul_left d₁ _)) (dvd_mul_right _ _))

/-- For coprime `a` and `n`, `invMod a n` is an inverse of `a` modulo `n`. -/
theorem invMod_spec {a n : Nat} (h : Nat.Coprime a n) : a * invMod a n % n = 1 % n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have ha : a = 1 := by simpa using h
    subst ha
    rfl
  · have hloop := invMod_loop a n hn (Nat.succ (a % n)) n (a % n) 0 (1 % n) (Nat.lt_succ_self _)
      (by
        rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]
        exact h)
      (by simp)
      (by
        rw [Int.natCast_mod, Int.natCast_mod, Nat.cast_one, Int.emod_emod_of_dvd _ (dvd_refl _),
          Int.mul_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.mul_emod, one_mul])
    have hcast : ((a * invMod a n % n : Nat) : Int) = ((1 % n : Nat) : Int) := by
      rw [Int.natCast_mod, Nat.cast_mul, Int.natCast_mod, Nat.cast_one, mul_comm]
      exact hloop
    exact_mod_cast hcast

/-! ### Compiled code

The kernel loops count down a literal with `Nat.rec`, which compiled code would unfold in full
before the first step. Compiled code runs the loops below, by pattern matching.
-/

namespace Compiled

/-- Square and multiply, one bit of the exponent per step: `acc * base ^ e % n` for a reduced
`acc`. -/
def powLoop (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | e + 1, base, acc =>
    powLoop n ((e + 1) / 2) (base * base % n) (if (e + 1) % 2 = 1 then acc * base % n else acc)
decreasing_by omega

/-- Compiled form of `powMod`. -/
def powMod (a e n : Nat) : Nat := powLoop n e (a % n) (1 % n)

/-- Compiled form of `powModWindow`: the window does not change the value. -/
def powModWindow (_w a e n : Nat) : Nat := powMod a e n

/-- The loop of `invMod` by pattern matching. -/
def invLoop (n : Nat) : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, s₀, _ => s₀
  | count + 1, r₀, r₁, s₀, s₁ =>
    if r₁ = 0 then s₀
    else invLoop n count r₁ (r₀ % r₁) s₁ ((s₀ + (n - r₀ / r₁ * s₁ % n)) % n)

/-- Compiled form of `invMod`. -/
def invMod (a n : Nat) : Nat := invLoop n (a % n + 1) n (a % n) 0 (1 % n)

/-- The compiled loop returns `acc * base ^ e % n` for a reduced product. -/
theorem powLoop_eq (n : Nat) : ∀ e base acc : Nat, acc % n = acc →
    powLoop n e base acc = acc * base ^ e % n := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro base acc hacc
    match e with
    | 0 => rw [powLoop, Nat.pow_zero, Nat.mul_one, hacc]
    | e + 1 =>
      rw [powLoop]
      have hhalf : (e + 1) / 2 < e + 1 := by omega
      split
      · rename_i hodd
        have hpow : acc * base ^ (e + 1) = acc * base * (base * base) ^ ((e + 1) / 2) := by
          conv_lhs => rw [show e + 1 = 2 * ((e + 1) / 2) + 1 by omega]
          ring
        rw [ih _ hhalf _ _ (Nat.mod_mod _ _), Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod,
          ← Nat.mul_mod, hpow]
      · rename_i heven
        have hpow : acc * base ^ (e + 1) = acc * (base * base) ^ ((e + 1) / 2) := by
          conv_lhs => rw [show e + 1 = 2 * ((e + 1) / 2) by omega]
          ring
        rw [ih _ hhalf _ _ hacc, Nat.mul_mod, ← Nat.pow_mod, ← Nat.mul_mod, hpow]

/-- The compiled power is `a ^ e % n`. -/
theorem powMod_eq (a e n : Nat) : powMod a e n = a ^ e % n := by
  rw [powMod, powLoop_eq n e _ _ (Nat.mod_mod 1 n), Nat.mul_mod, Nat.mod_mod, ← Nat.pow_mod,
    ← Nat.mul_mod, Nat.one_mul]

end Compiled

/-- Compiled code runs `Compiled.powMod` in place of `powMod`. -/
@[csimp] theorem powMod_eq_compiled : @powMod = @Compiled.powMod := by
  funext a e n
  rw [powMod_eq, Compiled.powMod_eq]

/-- Compiled code runs `Compiled.powModWindow` in place of `powModWindow`. -/
@[csimp] theorem powModWindow_eq_compiled : @powModWindow = @Compiled.powModWindow := by
  funext w a e n
  rw [powModWindow_eq, Compiled.powModWindow, Compiled.powMod_eq]

/-- The kernel loop of `invMod` and the compiled loop agree step by step. -/
private theorem invLoop_eq_compiled (n : Nat) : ∀ count r₀ r₁ s₀ s₁ : Nat,
    invLoop n count r₀ r₁ s₀ s₁ = Compiled.invLoop n count r₀ r₁ s₀ s₁ := by
  intro count
  induction count with
  | zero => intro r₀ r₁ s₀ s₁; rfl
  | succ count ih =>
    intro r₀ r₁ s₀ s₁
    rw [invLoop_succ, Compiled.invLoop]
    by_cases hzero : r₁ = 0
    · subst hzero
      rfl
    · have hbeq : Nat.beq r₁ 0 = false := by
        cases h : Nat.beq r₁ 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hzero
      rw [hbeq, ite_eq_right hzero]
      exact ih _ _ _ _

/-- Compiled code runs `Compiled.invMod` in place of `invMod`. -/
@[csimp] theorem invMod_eq_compiled : @invMod = @Compiled.invMod := by
  funext a n
  exact invLoop_eq_compiled n (a % n + 1) n (a % n) 0 (1 % n)

end FloatLib.Numerics.Kernel
