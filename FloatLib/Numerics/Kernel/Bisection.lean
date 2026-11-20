/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Order.Bisection.Proof

/-!
# Bisection on power-of-two intervals

This kernel implementation agrees with the shared bounded reference search for every predicate.
Its maximum theorem is a corollary of the generic bracket theorem. `guarded` takes a guess of
the number that the bisection finds and confirms it with two tests (`guarded_eq`).
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/--
The largest number from `lo` to `lo + 2 ^ bits - 1` at which `below` holds, for a `below` that
holds at `lo` and at every number under one at which it holds (`bisect_spec`): `bits` steps, each
of which adds a power of two to `lo` when `below` holds there.
-/
def bisect (below : Nat → Bool) (bits lo : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun lo => lo)
    (fun k next lo =>
      (fun mid => Bool.casesOn (motive := fun _ => Nat) (below mid) (next lo) (next mid))
        (Nat.add lo (Nat.pow 2 k)))
    bits lo

/-- One step of the bisection. -/
theorem bisect_succ (below : Nat → Bool) (k lo : Nat) :
    bisect below (k + 1) lo =
      Bool.casesOn (motive := fun _ => Nat) (below (lo + 2 ^ k)) (bisect below k lo)
        (bisect below k (lo + 2 ^ k)) :=
  rfl


/-- The kernel search is the reference bisection on an interval of length `2 ^ bits`. -/
theorem bisect_eq (below : Nat → Bool) (bits lo : Nat) :
    bisect below bits lo = Numerics.bisect below bits lo (lo + 2 ^ bits) := by
  induction bits generalizing lo with
  | zero => rfl
  | succ bits ih =>
      have hpos : 0 < 2 ^ bits := Nat.two_pow_pos bits
      have hnontrivial : lo + 1 < lo + 2 ^ (bits + 1) := by
        rw [Nat.pow_succ]
        omega
      have hmid : (lo + (lo + 2 ^ (bits + 1))) / 2 = lo + 2 ^ bits := by
        rw [Nat.pow_succ]
        omega
      have hupper : lo + 2 ^ (bits + 1) = (lo + 2 ^ bits) + 2 ^ bits := by
        rw [Nat.pow_succ]
        omega
      rw [bisect_succ, Numerics.bisect, ite_eq_left hnontrivial, hmid]
      cases h : below (lo + 2 ^ bits)
      · simpa only [h, Bool.false_eq_true, ite_false] using ih lo
      · simpa only [h, ite_true, hupper] using ih (lo + 2 ^ bits)

/-- A downward-closed predicate's largest accepted index in the searched interval. -/
theorem bisect_spec (below : Nat → Bool)
    (hdown : ∀ i j, i ≤ j → below j = true → below i = true)
    (bits lo : Nat) (hlo : below lo = true)
    (hup : ∀ j, lo + 2 ^ bits ≤ j → below j = false) :
    below (bisect below bits lo) = true ∧
      ∀ j, bisect below bits lo < j → below j = false := by
  rw [bisect_eq]
  exact Numerics.bisect_spec below hdown bits lo (lo + 2 ^ bits)
    (by have := Nat.two_pow_pos bits; omega) (by simp) hlo hup

/--
A number at which a downward-closed test holds, and at whose successor it fails, is the number
that the bisection finds. A caller with a guess of that number checks it with two tests and
does not run the bisection.
-/
theorem bisect_eq_of_bracket (below : Nat → Bool)
    (hdown : ∀ i j, i ≤ j → below j = true → below i = true)
    (bits lo : Nat) (hlo : below lo = true)
    (hup : ∀ j, lo + 2 ^ bits ≤ j → below j = false)
    {guess : Nat} (hguess : below guess = true) (hnext : below (guess + 1) = false) :
    bisect below bits lo = guess := by
  obtain ⟨hstar, hmax⟩ := bisect_spec below hdown bits lo hlo hup
  rcases Nat.lt_trichotomy (bisect below bits lo) guess with hlt | heq | hgt
  · rw [hmax guess hlt] at hguess
    cases hguess
  · exact heq
  · have hbelow := hdown (guess + 1) _ hgt hstar
    rw [hnext] at hbelow
    cases hbelow

/--
`hit guess` when `below` holds at `guess` and fails at its successor, and `other` otherwise: a
guess of the number that a bisection finds, with the two tests that confirm it.
-/
def guarded (below : Nat → Bool) (guess : Nat) (hit : Nat → Nat) (other : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (below guess) other
    (Bool.casesOn (motive := fun _ => Nat) (below (Nat.succ guess)) (hit guess) other)

/-- With the result at the bisection as the alternative, a guarded guess is that result,
whatever the guess. -/
theorem guarded_eq (below : Nat → Bool)
    (hdown : ∀ i j, i ≤ j → below j = true → below i = true)
    (bits : Nat) (hzero : below 0 = true) (hup : ∀ j, 0 + 2 ^ bits ≤ j → below j = false)
    (guess : Nat) (hit : Nat → Nat) :
    guarded below guess hit (hit (bisect below bits 0)) = hit (bisect below bits 0) := by
  unfold guarded
  cases hguess : below guess
  · rfl
  · cases hnext : below (Nat.succ guess)
    · change hit guess = hit (bisect below bits 0)
      rw [bisect_eq_of_bracket below hdown bits 0 hzero hup hguess hnext]
    · rfl

end FloatLib.Numerics.Kernel
