/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits
public import FloatLib.Numerics.Packed.Proof.Digits
public import Mathlib.Data.Nat.Bitwise

/-!
# Natural numbers with fixed-width digits

The encoded lane sum agrees with Mathlib's digit representation. Bounds, bit and digit extraction,
addition, constant digits and modular digit sums are shared by bit-length search and population
count.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- A quotient read off from `a * (b - 1) + 1 = c`. -/
theorem sub_one_div_sub_one {a b c : Nat} (h : a * (b - 1) + 1 = c) (hb : 1 < b) :
    (c - 1) / (b - 1) = a := by
  have hc : c - 1 = a * (b - 1) := by omega
  rw [hc, Nat.mul_div_cancel _ (by omega)]

/-- `∑ j < k, digit j * 2 ^ (width * j)`, the number whose lanes of `width` bits are `digit`. -/
def lanes (width : Nat) (digit : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => lanes width digit k + digit k * 2 ^ (width * k)

/-- The lane sum is the value of its digits in base `2 ^ width`. -/
private theorem lanes_eq_ofDigits (width : Nat) (digit : Nat → Nat) (k : Nat) :
    lanes width digit k = Nat.ofDigits (2 ^ width : Nat) ((List.range k).map digit) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [lanes, ih, List.range_succ, List.map_append, List.map_cons, List.map_nil,
        Nat.ofDigits_append, List.length_map, List.length_range, Nat.ofDigits_singleton,
        ← Nat.pow_mul, Nat.mul_comm]

/-- Digits below the lane base give a word below the total bit bound. -/
theorem lanes_lt {width : Nat} {digit : Nat → Nat}
    (hdigit : ∀ j, digit j < 2 ^ width) (k : Nat) :
    lanes width digit k < 2 ^ (width * k) := by
  rw [lanes_eq_ofDigits]
  simpa only [List.length_map, List.length_range] using
    Packed.ofDigits_lt width ((List.range k).map digit)
      (fun d hd => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hd; exact hdigit j)

/-- Bit `r` of lane `j` is bit `r` of the digit of that lane. -/
theorem testBit_lanes {width : Nat} {digit : Nat → Nat}
    (hdigit : ∀ j, digit j < 2 ^ width) (k j r : Nat) (hr : r < width) :
    (lanes width digit k).testBit (width * j + r) = (decide (j < k) && (digit j).testBit r) := by
  induction k with
  | zero => simp [lanes]
  | succ k ih =>
      have hsum : lanes width digit (k + 1) = 2 ^ (width * k) * digit k + lanes width digit k := by
        simp only [lanes]; ring
      rw [hsum, Nat.testBit_two_pow_mul_add _ (lanes_lt hdigit k)]
      by_cases hjk : j < k
      · have hlt : width * j + r < width * k := by
          calc width * j + r < width * j + width := by omega
            _ = width * (j + 1) := by ring
            _ ≤ width * k := Nat.mul_le_mul_left _ hjk
        simp [hlt, ih, hjk, Nat.lt_succ_of_lt hjk]
      · have hge : ¬ width * j + r < width * k := by
          have : width * k ≤ width * j := Nat.mul_le_mul_left _ (Nat.le_of_not_lt hjk)
          omega
        rw [ite_eq_right hge]
        by_cases hjeq : j = k
        · subst hjeq
          simp
        · have hgt : k < j := by omega
          have hindex : width ≤ width * j + r - width * k := by
            have : width * (k + 1) ≤ width * j := Nat.mul_le_mul_left _ hgt
            have hexpand : width * (k + 1) = width * k + width := by ring
            omega
          have hfalse : (digit k).testBit (width * j + r - width * k) = false :=
            Nat.testBit_lt_two_pow
              (Nat.lt_of_lt_of_le (hdigit k) (Nat.pow_le_pow_right (by decide) hindex))
          have hnot : ¬ j < k + 1 := by omega
          simp [hfalse, hnot]

/-- The lane sum of constant ones in closed form. -/
theorem lanes_one_mul (width k : Nat) :
    lanes width (fun _ => 1) k * (2 ^ width - 1) + 1 = 2 ^ (width * k) := by
  induction k with
  | zero => simp [lanes]
  | succ k ih =>
      have hpos : 0 < 2 ^ width := Nat.two_pow_pos _
      have hsplit : 2 ^ (width * (k + 1)) = 2 ^ (width * k) * 2 ^ width := by
        rw [← Nat.pow_add]; congr 1
      simp only [lanes, one_mul]
      rw [hsplit, ← ih]
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ width = m + 1 := ⟨2 ^ width - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring

/-- The all-ones lane mask has one in every lane of width `B + 1`. -/
theorem laneOnes_eq (B : Nat) : laneOnes B = lanes (B + 1) (fun _ => 1) B := by
  have h := lanes_one_mul (B + 1) B
  rw [Nat.mul_comm (B + 1) B] at h
  change (1 <<< (B * (B + 1)) - 1) / (1 <<< (B + 1) - 1) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
  exact sub_one_div_sub_one h (Nat.one_lt_two_pow (by omega))

/-- The lane sum of the powers of two in closed form. -/
theorem lanes_pow_mul (width k : Nat) :
    lanes (width + 1) (fun j => 2 ^ j) k * (2 ^ (width + 2) - 1) + 1 = 2 ^ (k * (width + 2)) := by
  induction k with
  | zero => simp [lanes]
  | succ k ih =>
      have hsplit : 2 ^ ((k + 1) * (width + 2)) = 2 ^ (k * (width + 2)) * 2 ^ (width + 2) := by
        rw [← Nat.pow_add]; congr 1; ring
      have hterm : 2 ^ k * 2 ^ ((width + 1) * k) = 2 ^ (k * (width + 2)) := by
        rw [← Nat.pow_add]; congr 1; ring
      simp only [lanes]
      rw [hsplit, hterm, ← ih]
      obtain ⟨m, hm⟩ : ∃ m, 2 ^ (width + 2) = m + 1 :=
        ⟨2 ^ (width + 2) - 1, by have := Nat.two_pow_pos (width + 2); omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring

/-- Lane `j` of `n * laneOnes + laneOffsets` holds `n + 2 ^ B - 2 ^ j`. -/
theorem lanes_compare (B n k : Nat) (hk : k ≤ B) :
    lanes (B + 1) (fun j => n + 2 ^ B - 2 ^ j) k + lanes (B + 1) (fun j => 2 ^ j) k =
      n * lanes (B + 1) (fun _ => 1) k + 2 ^ B * lanes (B + 1) (fun _ => 1) k := by
  induction k with
  | zero => simp [lanes]
  | succ k ih =>
      have hle : 2 ^ k ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) (by omega)
      have hdigit : n + 2 ^ B - 2 ^ k + 2 ^ k = n + 2 ^ B := by omega
      simp only [lanes, one_mul]
      have ih' := ih (by omega)
      calc lanes (B + 1) (fun j => n + 2 ^ B - 2 ^ j) k +
              (n + 2 ^ B - 2 ^ k) * 2 ^ ((B + 1) * k) +
            (lanes (B + 1) (fun j => 2 ^ j) k + 2 ^ k * 2 ^ ((B + 1) * k))
          = (lanes (B + 1) (fun j => n + 2 ^ B - 2 ^ j) k + lanes (B + 1) (fun j => 2 ^ j) k) +
              (n + 2 ^ B - 2 ^ k + 2 ^ k) * 2 ^ ((B + 1) * k) := by ring
        _ = _ := by rw [ih', hdigit]; ring

/-- A lane sum of digits is congruent to the sum of its digits modulo `2 ^ width - 1`. -/
theorem lanes_mod (width : Nat) (digit : Nat → Nat) (total : Nat → Nat)
    (htotal : ∀ k, total (k + 1) = total k + digit k) (hzero : total 0 = 0) (k : Nat) :
    lanes width digit k % (2 ^ width - 1) = total k % (2 ^ width - 1) := by
  induction k with
  | zero => simp [lanes, hzero]
  | succ k ih =>
      have hpow : 2 ^ (width * k) % (2 ^ width - 1) = 1 % (2 ^ width - 1) := by
        have hone : 2 ^ width % (2 ^ width - 1) = 1 % (2 ^ width - 1) := by
          obtain ⟨m, hm⟩ : ∃ m, 2 ^ width = m + 1 :=
            ⟨2 ^ width - 1, by have := Nat.two_pow_pos width; omega⟩
          rw [hm, Nat.add_sub_cancel, Nat.add_mod_left]
        rw [Nat.pow_mul, Nat.pow_mod, hone, ← Nat.pow_mod, Nat.one_pow]
      simp only [lanes, htotal]
      rw [Nat.add_mod, Nat.mul_mod, hpow, ih, ← Nat.mul_mod, Nat.mul_one, ← Nat.add_mod]

/-- Lane sums add lane by lane. -/
theorem lanes_add (w : Nat) (d e : Nat → Nat) (k : Nat) :
    lanes w d k + lanes w e k = lanes w (fun j => d j + e j) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lanes]
    rw [← ih]
    ring

/-- Lane sums of digits that agree below `k` are equal. -/
theorem lanes_congr {w : Nat} {d e : Nat → Nat} (k : Nat) (h : ∀ j, j < k → d j = e j) :
    lanes w d k = lanes w e k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lanes]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

/-- The lane sum of a constant digit. -/
theorem lanes_const (w c k : Nat) :
    lanes w (fun _ => c) k = c * lanes w (fun _ => 1) k := by
  simp only [lanes_eq_ofDigits, List.map_const', List.length_range]
  exact Packed.ofDigits_replicate (2 ^ w) c k

/-- The lanes of the digits of `x` are `x` below `2 ^ (w * k)`. -/
theorem lanes_digits (w x k : Nat) :
    lanes w (fun j => x / 2 ^ (w * j) % 2 ^ w) k = x % 2 ^ (w * k) := by
  induction k with
  | zero => simp [lanes, Nat.mod_one]
  | succ k ih =>
    simp only [lanes]
    rw [ih, show w * (k + 1) = w * k + w by ring, Nat.pow_add, Nat.mod_mul]
    ring

/-- Digit `i` of a lane sum is its lane `i`. -/
theorem digit_lanes {w : Nat} {d : Nat → Nat} (hd : ∀ j, d j < 2 ^ w) {i : Nat} :
    ∀ {k : Nat}, i < k → lanes w d k / 2 ^ (w * i) % 2 ^ w = d i := by
  intro k hi
  rw [lanes_eq_ofDigits]
  have h := Packed.lanes_ofDigits w ((List.range k).map d)
    (fun x hx => by obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx; exact hd j)
  have := congrArg (fun xs => xs[i]?) h
  simpa [Packed.lanes, Packed.lane_eq, hi] using this

end FloatLib.Numerics.Kernel
