/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Length

/-!
# Correctness of population count

Pairwise lane addition preserves the sum of the digits. The final remainder therefore computes the
sum of the binary digits for every natural number.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- The sum of the binary digits of `n` is its lowest bit plus the sum for `n / 2`. -/
theorem digits_two_sum (n : Nat) : (Nat.digits 2 n).sum = n % 2 + (Nat.digits 2 (n / 2)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' (by decide) hn, List.sum_cons]

/-- `∑ j < k, d j`. -/
private def lsum (d : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => lsum d k + d k

/-- Sums of values that agree below `k` are equal. -/
private theorem lsum_congr {d e : Nat → Nat} (k : Nat) (h : ∀ j, j < k → d j = e j) :
    lsum d k = lsum e k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change lsum d k + d k = lsum e k + e k
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

/-- Adding neighbouring pairs first gives the same sum. -/
private theorem lsum_pairs (d : Nat → Nat) (k : Nat) :
    lsum (fun j => d (2 * j) + d (2 * j + 1)) k = lsum d (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change lsum (fun j => d (2 * j) + d (2 * j + 1)) k + (d (2 * k) + d (2 * k + 1)) =
      lsum d (2 * k) + d (2 * k) + d (2 * k + 1)
    rw [ih, Nat.add_assoc]

/-- A sum of `k` values that are at most one is at most `k`. -/
private theorem lsum_le {d : Nat → Nat} (h : ∀ j, d j ≤ 1) (k : Nat) : lsum d k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    change lsum d k + d k ≤ k + 1
    have := h k
    omega

/-- The sum with its first value taken out. -/
private theorem lsum_succ (d : Nat → Nat) (k : Nat) :
    lsum d (k + 1) = d 0 + lsum (fun j => d (j + 1)) k := by
  induction k with
  | zero => change 0 + d 0 = d 0 + 0; omega
  | succ k ih =>
    change lsum d (k + 1) + d (k + 1) = d 0 + (lsum (fun j => d (j + 1)) k + d (k + 1))
    rw [ih, Nat.add_assoc]

/-- `pairMask` has the digit `2 ^ w - 1` in every lane of `2 * w` bits. -/
private theorem pairMask_eq (w K : Nat) :
    pairMask w (2 * w * K) = lanes (2 * w) (fun _ => 2 ^ w - 1) K := by
  have h := lanes_one_mul (2 * w) K
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
  have hsq : 2 ^ (2 * w) - 1 = (2 ^ w - 1) * (2 ^ w + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ w = m + 1 := ⟨2 ^ w - 1, by omega⟩
    rw [show 2 * w = w + w by omega, Nat.pow_add, hm]
    simp only [Nat.add_sub_cancel]
    have : (m + 1) * (m + 1) = m * (m + 1 + 1) + 1 := by ring
    omega
  change (1 <<< (2 * w * K) - 1) / (1 <<< w + 1) = _
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft, lanes_const]
  apply Nat.div_eq_of_eq_mul_left (Nat.succ_pos _)
  rw [Nat.succ_eq_add_one, ← h, Nat.add_sub_cancel, hsq]
  ring

/-- Masking with `pairMask` keeps the lowest `w` bits of every lane of `2 * w` bits. -/
private theorem land_pairMask (w x K : Nat) :
    x &&& lanes (2 * w) (fun _ => 2 ^ w - 1) K =
      lanes (2 * w) (fun j => x / 2 ^ (2 * w * j) % 2 ^ w) K := by
  induction K with
  | zero => exact Nat.and_zero x
  | succ K ih =>
    have hdigit : ∀ j : Nat, (fun _ : Nat => 2 ^ w - 1) j < 2 ^ (2 * w) := by
      intro _
      have h1 : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 := Nat.two_pow_pos w
      change 2 ^ w - 1 < 2 ^ (2 * w)
      omega
    have hM := lanes_lt hdigit K
    have hlow : x % 2 ^ (2 * w * K) &&& lanes (2 * w) (fun _ => 2 ^ w - 1) K =
        x &&& lanes (2 * w) (fun _ => 2 ^ w - 1) K := by
      have h := Nat.and_mod_two_pow (a := x) (b := lanes (2 * w) (fun _ => 2 ^ w - 1) K)
        (n := 2 * w * K)
      rw [Nat.mod_eq_of_lt hM, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hM)] at h
      exact h.symm
    change x &&& (lanes (2 * w) (fun _ => 2 ^ w - 1) K + (2 ^ w - 1) * 2 ^ (2 * w * K)) =
      lanes (2 * w) (fun j => x / 2 ^ (2 * w * j) % 2 ^ w) K +
        x / 2 ^ (2 * w * K) % 2 ^ w * 2 ^ (2 * w * K)
    have hx : x &&& (lanes (2 * w) (fun _ => 2 ^ w - 1) K + (2 ^ w - 1) * 2 ^ (2 * w * K)) =
        (2 ^ (2 * w * K) * (x / 2 ^ (2 * w * K)) + x % 2 ^ (2 * w * K)) &&&
          (2 ^ (2 * w * K) * (2 ^ w - 1) + lanes (2 * w) (fun _ => 2 ^ w - 1) K) := by
      rw [Nat.div_add_mod, Nat.add_comm, Nat.mul_comm]
    rw [hx, Nat.add_comm (2 ^ (2 * w * K) * (x / 2 ^ (2 * w * K))),
      Nat.add_comm (2 ^ (2 * w * K) * (2 ^ w - 1)),
      Packed.land_split (Nat.mod_lt _ (Nat.two_pow_pos _)) hM, hlow, ih,
      Nat.and_two_pow_sub_one_eq_mod]
    ring

/-- `pairSum` puts the sum of two neighbouring lanes of `w` bits into each lane of `2 * w` bits. -/
private theorem pairSum_eq (w x K : Nat) :
    pairSum (pairMask w (2 * w * K)) w x =
      lanes (2 * w)
        (fun j => x / 2 ^ (w * (2 * j)) % 2 ^ w + x / 2 ^ (w * (2 * j + 1)) % 2 ^ w) K := by
  change (x &&& pairMask w (2 * w * K)) + ((x >>> w) &&& pairMask w (2 * w * K)) = _
  rw [pairMask_eq, land_pairMask, land_pairMask, lanes_add]
  refine lanes_congr K (fun j _ => ?_)
  show x / 2 ^ (2 * w * j) % 2 ^ w + x >>> w / 2 ^ (2 * w * j) % 2 ^ w = _
  rw [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 2 * w * j = w * (2 * j) by ring, show w + w * (2 * j) = w * (2 * j + 1) by ring]

/--
One level keeps the sum of the lanes: the lanes of `2 * w` bits of the result add up to what the
lanes of `w` bits of `x` add up to, and the result stays below `2 ^ (2 * w * K)`.
-/
private theorem pairSum_level {w : Nat} (hw : 0 < w) (x K : Nat) :
    pairSum (pairMask w (2 * w * K)) w x < 2 ^ (2 * w * K) ∧
      lsum (fun j => pairSum (pairMask w (2 * w * K)) w x / 2 ^ (2 * w * j) % 2 ^ (2 * w)) K =
        lsum (fun j => x / 2 ^ (w * j) % 2 ^ w) (2 * K) := by
  have hdigit : ∀ j, (fun j => x / 2 ^ (w * (2 * j)) % 2 ^ w +
      x / 2 ^ (w * (2 * j + 1)) % 2 ^ w) j < 2 ^ (2 * w) := by
    intro j
    have h1 : x / 2 ^ (w * (2 * j)) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have h2 : x / 2 ^ (w * (2 * j + 1)) % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
    have h3 : 2 ^ w + 2 ^ w ≤ 2 ^ (2 * w) := by
      rw [← Nat.two_mul, ← Nat.pow_succ']
      exact Nat.pow_le_pow_right (by decide) (by omega)
    change _ + _ < _
    omega
  rw [pairSum_eq]
  refine ⟨lanes_lt hdigit K, ?_⟩
  rw [lsum_congr K (fun j hj => digit_lanes hdigit hj)]
  exact lsum_pairs (fun j => x / 2 ^ (w * j) % 2 ^ w) K

/-- `k` levels keep the sum of the lanes, for a number below `2 ^ total`. -/
private theorem pairLevels_eq (K : Nat) : ∀ (k w x total : Nat), 0 < w → total = w * 2 ^ k * K →
    x < 2 ^ total →
    pairLevels total k w x < 2 ^ total ∧
      lsum (fun j => pairLevels total k w x / 2 ^ (w * 2 ^ k * j) % 2 ^ (w * 2 ^ k)) K =
        lsum (fun j => x / 2 ^ (w * j) % 2 ^ w) (2 ^ k * K) := by
  intro k
  induction k with
  | zero =>
    intro w x total _ _ hx
    refine ⟨hx, ?_⟩
    change lsum (fun j => x / 2 ^ (w * 2 ^ 0 * j) % 2 ^ (w * 2 ^ 0)) K = _
    rw [Nat.pow_zero, Nat.mul_one, Nat.one_mul]
  | succ k ih =>
    intro w x total hw htotal _
    have htotal' : total = 2 * w * (2 ^ k * K) := by rw [htotal, Nat.pow_succ]; ring
    have hlevel := pairSum_level hw x (2 ^ k * K)
    rw [← htotal'] at hlevel
    have hstep := ih (w + w) (pairSum (pairMask w total) w x) total (by omega)
      (by rw [htotal, Nat.pow_succ]; ring) hlevel.1
    change pairLevels total k (w + w) (pairSum (pairMask w total) w x) < 2 ^ total ∧
      lsum (fun j => pairLevels total k (w + w) (pairSum (pairMask w total) w x) /
        2 ^ (w * 2 ^ (k + 1) * j) % 2 ^ (w * 2 ^ (k + 1))) K = _
    refine ⟨hstep.1, ?_⟩
    have hw2 : w * 2 ^ (k + 1) = (w + w) * 2 ^ k := by rw [Nat.pow_succ]; ring
    rw [hw2, hstep.2, show w + w = 2 * w by omega, hlevel.2]
    congr 1
    rw [Nat.pow_succ]; ring

/-- The bits of `n < 2 ^ t` add up to the sum of its binary digits. -/
private theorem lsum_bits : ∀ (t n : Nat), n < 2 ^ t →
    lsum (fun j => n / 2 ^ (1 * j) % 2 ^ 1) t = (Nat.digits 2 n).sum := by
  intro t
  induction t with
  | zero =>
    intro n hn
    have : n = 0 := by simpa using hn
    subst this
    simp [lsum]
  | succ t ih =>
    intro n hn
    rw [lsum_succ, digits_two_sum n]
    have hhalf : n / 2 < 2 ^ t := by rw [Nat.pow_succ] at hn; omega
    rw [← ih (n / 2) hhalf]
    congr 1
    · simp
    · refine lsum_congr t (fun j _ => ?_)
      show n / 2 ^ (1 * (j + 1)) % 2 ^ 1 = n / 2 / 2 ^ (1 * j) % 2 ^ 1
      rw [Nat.div_div_eq_div_mul, Nat.one_mul, Nat.one_mul, Nat.pow_succ']

/--
The lane count. For `n < 2 ^ (2 ^ k * K)` whose binary digits add up to less than
`2 ^ 2 ^ k - 1`, `k` levels of `pairSum` followed by the remainder modulo `2 ^ 2 ^ k - 1` give
the sum of the binary digits of `n`.
-/
theorem pairLevels_mod {k K n : Nat} (hn : n < 2 ^ (2 ^ k * K))
    (hsum : (Nat.digits 2 n).sum < 2 ^ 2 ^ k - 1) :
    pairLevels (2 ^ k * K) k 1 n % (2 ^ 2 ^ k - 1) = (Nat.digits 2 n).sum := by
  have h := pairLevels_eq K k 1 n (2 ^ k * K) Nat.one_pos (by rw [Nat.one_mul]) hn
  rw [Nat.one_mul] at h
  obtain ⟨hlt, hs⟩ := h
  rw [lsum_bits _ n hn] at hs
  have hr := lanes_digits (2 ^ k) (pairLevels (2 ^ k * K) k 1 n) K
  rw [Nat.mod_eq_of_lt hlt] at hr
  have hm := lanes_mod (2 ^ k)
    (fun j => pairLevels (2 ^ k * K) k 1 n / 2 ^ (2 ^ k * j) % 2 ^ 2 ^ k)
    (lsum (fun j => pairLevels (2 ^ k * K) k 1 n / 2 ^ (2 ^ k * j) % 2 ^ 2 ^ k))
    (fun _ => rfl) rfl K
  rw [hr, hs, Nat.mod_eq_of_lt hsum] at hm
  exact hm

/-- The sum of the binary digits of `n` is at most its bit length. -/
theorem digits_two_sum_le_size (n : Nat) : (Nat.digits 2 n).sum ≤ size n := by
  have hn : n < 2 ^ size n := by rw [size_eq]; exact Nat.lt_size_self n
  rw [← lsum_bits _ n hn]
  refine lsum_le (fun j => ?_) _
  have := Nat.mod_lt (n / 2 ^ (1 * j)) (Nat.two_pow_pos 1)
  change n / 2 ^ (1 * j) % 2 ^ 1 ≤ 1
  omega

/-- `popCount n` is the sum of the binary digits of `n`, for every `n`. -/
theorem popCount_eq (n : Nat) : popCount n = (Nat.digits 2 n).sum := by
  unfold popCount
  rw [beq_shiftRight_zero n 64]
  have hsize : n < 2 ^ size n := by rw [size_eq]; exact Nat.lt_size_self n
  by_cases h64 : n < 2 ^ 64
  · rw [decide_eq_true h64]
    have hsum : (Nat.digits 2 n).sum < 2 ^ 2 ^ 3 - 1 := by
      have h1 := digits_two_sum_le_size n
      have h2 : size n ≤ 64 := by rw [size_eq]; exact Nat.size_le.2 h64
      exact Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (by decide)
    exact pairLevels_mod (k := 3) (K := 8) h64 hsum
  · rw [decide_eq_false h64]
    have hL : size n < 2 ^ size (size n) := by
      rw [size_eq (size n)]; exact Nat.lt_size_self _
    have hk : size (size n) < 2 ^ size (size (size n)) := by
      rw [size_eq (size (size n))]; exact Nat.lt_size_self _
    have hW : 2 * 2 ^ size (size n) ≤ 2 ^ 2 ^ size (size (size n)) := by
      rw [← Nat.pow_succ']
      exact Nat.pow_le_pow_right (by decide) hk
    have hsum : (Nat.digits 2 n).sum < 2 ^ 2 ^ size (size (size n)) - 1 := by
      have h1 := digits_two_sum_le_size n
      omega
    have hcover : n < 2 ^ (2 ^ size (size (size n)) * (size n / 2 ^ size (size (size n)) + 1)) :=
      Nat.lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by decide)
        (Nat.le_of_lt (Nat.lt_mul_div_succ _ (Nat.two_pow_pos _))))
    have h := pairLevels_mod hcover hsum
    change pairLevels (1 <<< size (size (size n)) * (size n / 1 <<< size (size (size n)) + 1))
      (size (size (size n))) 1 n % (1 <<< (1 <<< size (size (size n))) - 1) = _
    rw [Nat.one_shiftLeft, Nat.one_shiftLeft]
    exact h

/-- Compiled form of `popCount`: the sum of the binary digits. -/
def Compiled.popCount (n : Nat) : Nat := (Nat.digits 2 n).sum

/-- Compiled code sums the binary digits. -/
compiled_as popCount := Compiled.popCount by popCount_eq

end FloatLib.Numerics.Kernel
