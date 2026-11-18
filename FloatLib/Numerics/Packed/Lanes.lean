/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Proof.Products
public import FloatLib.Numerics.Packed.Proof.Sums
public import FloatLib.Numerics.Packed.Proof.Unsigned

import Mathlib.Tactic.Ring

/-!
# Arithmetic on all lanes of a row at once

A row holds `n` natural numbers in one natural number, lane `k` in bits `[w * k, w * (k + 1))`.
One operation of Lean's kernel on two rows then acts on all `n` lanes, as long as no lane
overflows into its neighbour. This module states, for each kernel operation, the condition under
which it acts lane by lane, for every lane width and every pair of naturals:

* `lane_add`, `lane_sub`, `lane_mul`: addition, subtraction and multiplication by one number act
  lane by lane when no lane carries, borrows or overflows;
* `lane_land` (in `Packed.Proof`), `lane_lor`, `lane_xor`: the bitwise operations always do;
* `lane_shiftRight_mod`: a right shift by `s ≤ w` followed by a mask of the low `w - s` bits of each
  lane shifts each lane;
* `lane_ones`, `lane_const`: the lanes of `ones w n` and of a number repeated in every lane;
* `le_of_lane_le`: a row whose lanes are all at most those of another is at most the other.

`Packed.Machine` builds an evaluator of whole programs on these.
-/

@[expose] public section

namespace FloatLib.Numerics.Packed

/-- The lanes of zero are zero. -/
@[simp] theorem lane_zero_row (w k : Nat) : lane w k 0 = 0 := by
  simp [lane_eq]

/-- A row whose lanes are all at most those of another row is at most that row. -/
theorem le_of_lane_le {w : Nat} (hw : 1 ≤ w) :
    ∀ {u v : Nat}, (∀ j, lane w j v ≤ lane w j u) → v ≤ u := by
  intro u v
  induction v using Nat.strong_induction_on generalizing u with
  | _ v ih =>
      intro h
      rcases Nat.eq_zero_or_pos v with rfl | hpos
      · exact Nat.zero_le _
      · have hbase : 2 ≤ 2 ^ w := by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
        have hlt : v / 2 ^ w < v := Nat.div_lt_self hpos hbase
        have hhigh : v / 2 ^ w ≤ u / 2 ^ w :=
          ih _ hlt fun j => by
            have := h (j + 1)
            rwa [lane_succ, lane_succ] at this
        have hlow := h 0
        rw [lane_zero, lane_zero] at hlow
        calc v = v % 2 ^ w + 2 ^ w * (v / 2 ^ w) := (Nat.mod_add_div v _).symm
          _ ≤ u % 2 ^ w + 2 ^ w * (u / 2 ^ w) :=
            Nat.add_le_add hlow (Nat.mul_le_mul_left _ hhigh)
          _ = u := Nat.mod_add_div u _

/-- Addition acts lane by lane when no lane carries. -/
theorem lane_add {w : Nat} :
    ∀ {u v : Nat}, (∀ j, lane w j u + lane w j v < 2 ^ w) →
      ∀ k, lane w k (u + v) = lane w k u + lane w k v := by
  intro u v h k
  induction k generalizing u v with
  | zero =>
      have h0 := h 0
      rw [lane_zero, lane_zero] at h0
      rw [lane_zero, lane_zero, lane_zero, Nat.add_mod, Nat.mod_eq_of_lt h0]
  | succ k ih =>
      have h0 := h 0
      rw [lane_zero, lane_zero] at h0
      have hdiv : (u + v) / 2 ^ w = u / 2 ^ w + v / 2 ^ w := by
        rw [Nat.add_div (Nat.two_pow_pos w), ite_eq_right (Nat.not_le.mpr h0), Nat.add_zero]
      rw [lane_succ, lane_succ, lane_succ, hdiv]
      exact ih fun j => by
        have := h (j + 1)
        rwa [lane_succ, lane_succ] at this

/-- Subtraction acts lane by lane when no lane borrows. -/
theorem lane_sub {w : Nat} (hw : 1 ≤ w) :
    ∀ {u v : Nat}, (∀ j, lane w j v ≤ lane w j u) →
      ∀ k, lane w k (u - v) = lane w k u - lane w k v := by
  intro u v h k
  induction k generalizing u v with
  | zero =>
      have h0 := h 0
      rw [lane_zero, lane_zero] at h0
      have hle := le_of_lane_le hw h
      rw [lane_zero, lane_zero, lane_zero]
      have hu := Nat.mod_add_div u (2 ^ w)
      have hv := Nat.mod_add_div v (2 ^ w)
      have hhigh : v / 2 ^ w ≤ u / 2 ^ w := Nat.div_le_div_right hle
      have hsplit : u - v = (u % 2 ^ w - v % 2 ^ w) + 2 ^ w * (u / 2 ^ w - v / 2 ^ w) := by
        rw [Nat.mul_sub]
        have := Nat.mul_le_mul_left (2 ^ w) hhigh
        omega
      rw [hsplit, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos w)))
  | succ k ih =>
      have h0 := h 0
      rw [lane_zero, lane_zero] at h0
      have hle := le_of_lane_le hw h
      have hhigh : v / 2 ^ w ≤ u / 2 ^ w := Nat.div_le_div_right hle
      have hdiv : (u - v) / 2 ^ w = u / 2 ^ w - v / 2 ^ w := by
        have hu := Nat.mod_add_div u (2 ^ w)
        have hv := Nat.mod_add_div v (2 ^ w)
        have hsplit : u - v = (u % 2 ^ w - v % 2 ^ w) + 2 ^ w * (u / 2 ^ w - v / 2 ^ w) := by
          rw [Nat.mul_sub]
          have := Nat.mul_le_mul_left (2 ^ w) hhigh
          omega
        rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w),
          Nat.div_eq_of_lt
            (lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt _ (Nat.two_pow_pos w))),
          Nat.zero_add]
      rw [lane_succ, lane_succ, lane_succ, hdiv]
      exact ih fun j => by
        have := h (j + 1)
        rwa [lane_succ, lane_succ] at this

/-- Multiplication by one number acts lane by lane when no lane overflows. -/
theorem lane_mul {w : Nat} (c : Nat) :
    ∀ {u : Nat}, (∀ j, lane w j u * c < 2 ^ w) → ∀ k, lane w k (u * c) = lane w k u * c := by
  intro u h k
  induction k generalizing u with
  | zero =>
      have h0 := h 0
      rw [lane_zero] at h0
      rw [lane_zero, lane_zero]
      have hsplit : u * c = u % 2 ^ w * c + 2 ^ w * (u / 2 ^ w * c) := by
        conv_lhs => rw [← Nat.mod_add_div u (2 ^ w)]
        rw [add_mul]; ac_rfl
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  | succ k ih =>
      have h0 := h 0
      rw [lane_zero] at h0
      have hdiv : u * c / 2 ^ w = u / 2 ^ w * c := by
        have hsplit : u * c = u % 2 ^ w * c + 2 ^ w * (u / 2 ^ w * c) := by
          conv_lhs => rw [← Nat.mod_add_div u (2 ^ w)]
          rw [add_mul]; ac_rfl
        rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos w), Nat.div_eq_of_lt h0,
          Nat.zero_add]
      rw [lane_succ, lane_succ, hdiv]
      exact ih fun j => by
        have := h (j + 1)
        rwa [lane_succ] at this

/-- A disjunction acts lane by lane. -/
theorem lane_lor (w k u v : Nat) : lane w k (u ||| v) = lane w k u ||| lane w k v := by
  simp only [lane, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  change ((u ||| v) >>> (w * k)) &&& (2 ^ w - 1) =
    ((u >>> (w * k)) &&& (2 ^ w - 1)) ||| ((v >>> (w * k)) &&& (2 ^ w - 1))
  rw [Nat.shiftRight_or_distrib, Nat.and_or_distrib_right]

/-- An exclusive disjunction acts lane by lane. -/
theorem lane_xor (w k u v : Nat) : lane w k (u ^^^ v) = lane w k u ^^^ lane w k v := by
  simp only [lane, pow2_eq, Nat.sub_eq, Nat.mul_eq]
  change ((u ^^^ v) >>> (w * k)) &&& (2 ^ w - 1) =
    ((u >>> (w * k)) &&& (2 ^ w - 1)) ^^^ ((v >>> (w * k)) &&& (2 ^ w - 1))
  rw [Nat.shiftRight_xor_distrib, Nat.and_xor_distrib_right]

/--
A right shift by `s ≤ w` moves the low bits of the next lane into the top of each lane. The low
`w - s` bits of each lane are the lane shifted right.
-/
theorem lane_shiftRight_mod {w s : Nat} (hs : s ≤ w) (k u : Nat) :
    lane w k (u >>> s) % 2 ^ (w - s) = lane w k u >>> s := by
  simp only [lane_eq, Nat.shiftRight_eq_div_pow]
  have hsplit : 2 ^ w = 2 ^ s * 2 ^ (w - s) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [Nat.mod_mod_of_dvd _ ⟨2 ^ s, by rw [hsplit, Nat.mul_comm]⟩, Nat.div_div_eq_div_mul,
    Nat.mul_comm (2 ^ s), ← Nat.div_div_eq_div_mul, hsplit, Nat.mod_mul_right_div_self]

/-- The lanes of `ones w n` are one below `n` and zero from `n` on. -/
theorem lane_ones {w : Nat} (hw : 1 ≤ w) (n k : Nat) :
    lane w k (ones w n) = if k < n then 1 else 0 := by
  have hone : (1 : Nat) < 2 ^ w := Nat.one_lt_two_pow (by omega)
  obtain ⟨hlanes, hlt⟩ := lanes_mul_ones (n := n) hw hone
  rw [Nat.one_mul] at hlanes hlt
  by_cases hk : k < n
  · rw [ite_eq_left hk]
    have hget : (lanes w n (ones w n))[k]'(by rw [length_lanes]; exact hk) = lane w k (ones w
      n) := by
      simp [lanes]
    rw [← hget]
    simp [hlanes]
  · rw [ite_eq_right hk, lane_eq]
    have hbig : ones w n < 2 ^ (w * k) :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega)))
    rw [Nat.div_eq_of_lt hbig, Nat.zero_mod]

/-- The row with `c` in each of its `n` lanes, for `c < 2 ^ w`. -/
theorem lane_const {w : Nat} (hw : 1 ≤ w) {c : Nat} (hc : c < 2 ^ w) (n k : Nat) :
    lane w k (ones w n * c) = if k < n then c else 0 := by
  rw [lane_mul c (fun j => by rw [lane_ones hw]; split <;> simp [hc]), lane_ones hw]
  split <;> simp

end FloatLib.Numerics.Packed
