/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.Bits.Proof.Lanes
public import FloatLib.Tactic.CompiledAs
public import Mathlib.Data.Nat.Size

/-!
# Correctness of bit-length searches

The lane, binary and window searches compute the binary logarithm plus one under their stated
bounds, and zero at zero. The combined size function agrees with Mathlib's Nat.size for every
natural number.
-/

@[expose] public section

namespace FloatLib.Numerics.Kernel

/-- Bit `B` of a lane: `(n + x - y) / x` is one exactly when `y ≤ n`, for `y ≤ x` and `n < x`. -/
private theorem add_sub_div_eq_flag {x y n : Nat} (hy : y ≤ x) (hn : n < x) :
    (n + x - y) / x = if y ≤ n then 1 else 0 := by
  split
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- The number of `j < k` with `2 ^ j ≤ n`. -/
private def countPowersLE (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => countPowersLE n k + if 2 ^ k ≤ n then 1 else 0

private theorem countPowersLE_le (n k : Nat) : countPowersLE n k ≤ k := by
  induction k with
  | zero => simp [countPowersLE]
  | succ k ih => simp only [countPowersLE]; split <;> omega

private theorem countPowersLE_eq (n k : Nat) :
    countPowersLE n k = if n = 0 then 0 else min k (n.log2 + 1) := by
  induction k with
  | zero => simp [countPowersLE]
  | succ k ih =>
      by_cases hn : n = 0
      · subst n
        simp [countPowersLE, ih]
      simp only [countPowersLE, ih, hn, ite_false]
      by_cases hle : 2 ^ k ≤ n
      · have := (Nat.le_log2 hn).2 hle
        simp only [hle, ite_true]
        omega
      · have : ¬ k ≤ n.log2 := fun h => hle ((Nat.le_log2 hn).1 h)
        simp only [hle, ite_false]
        omega

/--
`bitLength B n` is the bit length of `n` when `n < 2 ^ B`: zero for `n = 0`, and otherwise one more
than the position `n.log2` of the leading bit.
-/
theorem laneLength_eq {B n : Nat} (hn : n < 2 ^ B) :
    laneLength B n = if n = 0 then 0 else n.log2 + 1 := by
  have hwidth : B < B + 1 := Nat.lt_succ_self B
  have hdigitOne : ∀ j : Nat, (fun _ : Nat => 1) j < 2 ^ (B + 1) := fun _ =>
    Nat.one_lt_two_pow (by omega)
  have hdigit : ∀ j, (fun j => n + 2 ^ B - 2 ^ j) j < 2 ^ (B + 1) := fun j => by
    have : 2 ^ (B + 1) = 2 ^ B + 2 ^ B := by rw [Nat.pow_succ]; omega
    have hpos := Nat.two_pow_pos j
    change n + 2 ^ B - 2 ^ j < 2 ^ (B + 1)
    omega
  have hflag : ∀ j, (fun j => if 2 ^ j ≤ n then 1 else 0) j < 2 ^ (B + 1) := fun j => by
    have : 1 < 2 ^ (B + 1) := Nat.one_lt_two_pow (by omega)
    change (if 2 ^ j ≤ n then 1 else 0) < 2 ^ (B + 1)
    split <;> omega
  -- The offsets are the constant `2 ^ B` in each lane minus the powers of two.
  have hpowLanes :
      (2 ^ (B * (B + 2)) - 1) / (2 ^ (B + 2) - 1) = lanes (B + 1) (fun j => 2 ^ j) B :=
    sub_one_div_sub_one (lanes_pow_mul B B) (Nat.one_lt_two_pow (by omega))
  have hsum :
      n * laneOnes B + laneOffsets B = lanes (B + 1) (fun j => n + 2 ^ B - 2 ^ j) B := by
    have hcompare := lanes_compare B n B le_rfl
    have hzero := lanes_compare B 0 B le_rfl
    have hoffsets : laneOffsets B =
        2 ^ B * lanes (B + 1) (fun _ => 1) B - lanes (B + 1) (fun j => 2 ^ j) B := by
      change laneOnes B <<< B - (1 <<< (B * (B + 2)) - 1) / (1 <<< (B + 2) - 1) = _
      rw [Nat.one_shiftLeft, Nat.one_shiftLeft, hpowLanes, laneOnes_eq, Nat.shiftLeft_eq,
        Nat.mul_comm]
    rw [hoffsets, laneOnes_eq]
    omega
  -- Shifting right by `B` and masking leaves bit `B` of each lane in its bit zero.
  have hmask :
      (n * laneOnes B + laneOffsets B) >>> B &&& laneOnes B =
        lanes (B + 1) (fun j => if 2 ^ j ≤ n then 1 else 0) B := by
    rw [hsum, laneOnes_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < B + 1 ∧ i = (B + 1) * j + r :=
      ⟨i / (B + 1), i % (B + 1), Nat.mod_lt _ (by omega), (Nat.div_add_mod i (B + 1)).symm⟩
    rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_lanes hdigitOne _ _ _ hr,
      testBit_lanes hflag _ _ _ hr]
    by_cases hjB : j < B
    · by_cases hr0 : r = 0
      · subst hr0
        have hindex : B + ((B + 1) * j + 0) = (B + 1) * j + B := by omega
        rw [hindex, testBit_lanes hdigit _ _ _ hwidth]
        have hpowj : 2 ^ j ≤ 2 ^ B := Nat.pow_le_pow_right (by decide) (by omega)
        have hbit : (n + 2 ^ B - 2 ^ j).testBit B = decide (2 ^ j ≤ n) := by
          rw [Nat.testBit_eq_decide_div_mod_eq, add_sub_div_eq_flag hpowj hn]
          by_cases hle : 2 ^ j ≤ n <;> simp [hle]
        by_cases hle : 2 ^ j ≤ n <;> simp [hjB, hbit, hle]
      · have hone : (1 : Nat).testBit r = false :=
          Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hr0)
        have hflagBit : (if 2 ^ j ≤ n then 1 else 0 : Nat).testBit r = false := by
          split
          · exact hone
          · simp
        simp [hone, hflagBit]
    · simp [hjB]
  have hcount := lanes_mod (B + 1) (fun j => if 2 ^ j ≤ n then 1 else 0) (countPowersLE n)
    (fun _ => rfl) rfl B
  have hbound : countPowersLE n B < 2 ^ (B + 1) - 1 := by
    have h1 := countPowersLE_le n B
    have h2 : B + 1 < 2 ^ (B + 1) := Nat.lt_two_pow_self
    omega
  change ((n * laneOnes B + laneOffsets B) >>> B &&& laneOnes B) % (1 <<< (B + 1) - 1) = _
  rw [Nat.one_shiftLeft, hmask, hcount, Nat.mod_eq_of_lt hbound]
  rw [countPowersLE_eq]
  by_cases hzero : n = 0
  · simp [hzero]
  · rw [ite_eq_right hzero, ite_eq_right hzero]
    have := (Nat.log2_lt hzero).2 hn
    omega

/-- The logarithm of a number splits at a shift that leaves a nonzero upper part. -/
theorem log2_of_shiftRight {n s : Nat} (hupper : n >>> s ≠ 0) :
    n.log2 = s + (n >>> s).log2 := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hupper (Nat.zero_shiftRight s)
  have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
  have hlow : 2 ^ (n >>> s).log2 ≤ n >>> s := Nat.log2_self_le hupper
  have hhigh : n >>> s < 2 ^ ((n >>> s).log2 + 1) := Nat.lt_log2_self
  rw [Nat.shiftRight_eq_div_pow] at hlow hhigh hupper ⊢
  rw [Nat.log2_eq_iff hn]
  constructor
  · rw [Nat.pow_add, Nat.mul_comm]
    exact (Nat.le_div_iff_mul_le hpos).1 hlow
  · rw [show s + (n / 2 ^ s).log2 + 1 = (n / 2 ^ s).log2 + 1 + s by omega, Nat.pow_add]
    exact (Nat.div_lt_iff_lt_mul hpos).1 hhigh

/--
`searchLength k n acc` is `acc` plus the bit length of `n`, for every `n < 2 ^ 2 ^ k`.
-/
theorem searchLength_eq (k : Nat) : ∀ n acc : Nat, n < 2 ^ 2 ^ k →
    searchLength k n acc = acc + if n = 0 then 0 else n.log2 + 1 := by
  induction k with
  | zero =>
    intro n acc hn
    have hcases : n = 0 ∨ n = 1 := by
      have : n < 2 := hn
      omega
    rcases hcases with rfl | rfl
    · rfl
    · change acc + 1 = acc + if (1 : Nat) = 0 then 0 else Nat.log2 1 + 1
      rw [show Nat.log2 1 = 0 from (Nat.log2_eq_iff (by decide)).2 (by decide)]
      rfl
  | succ k ih =>
    intro n acc hn
    have hsplit : 2 ^ 2 ^ (k + 1) = 2 ^ 2 ^ k * 2 ^ 2 ^ k := by
      rw [← Nat.pow_add, Nat.pow_succ]
      congr 1
      omega
    have hpos : 0 < 2 ^ 2 ^ k := Nat.two_pow_pos _
    change Bool.casesOn (motive := fun _ => Nat) (Nat.beq (n >>> 2 ^ k) 0)
      (searchLength k (n >>> 2 ^ k) (acc + 2 ^ k)) (searchLength k n acc) = _
    by_cases hupper : n >>> 2 ^ k = 0
    · rw [hupper, show Nat.beq 0 0 = true from rfl]
      refine ih n acc ?_
      rw [Nat.shiftRight_eq_div_pow] at hupper
      exact (Nat.div_eq_zero_iff_lt hpos).1 hupper
    · have hbeq : Nat.beq (n >>> 2 ^ k) 0 = false := by
        cases h : Nat.beq (n >>> 2 ^ k) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hupper
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hupper (Nat.zero_shiftRight _)
      have hbound : n >>> 2 ^ k < 2 ^ 2 ^ k := by
        rw [Nat.shiftRight_eq_div_pow]
        exact (Nat.div_lt_iff_lt_mul hpos).2 (by rw [← hsplit]; exact hn)
      rw [hbeq]
      change searchLength k (n >>> 2 ^ k) (acc + 2 ^ k) = _
      rw [ih _ _ hbound, ite_eq_right hupper, ite_eq_right hn0, log2_of_shiftRight hupper]
      omega

/--
`windowLength W k n acc` is `acc` plus the bit length of `n`, for every `n < 2 ^ (W * 2 ^ k)`.
-/
theorem windowLength_eq (W k : Nat) : ∀ n acc : Nat, n < 2 ^ (W * 2 ^ k) →
    windowLength W k n acc = acc + if n = 0 then 0 else n.log2 + 1 := by
  induction k with
  | zero =>
    intro n acc hn
    rw [Nat.pow_zero, Nat.mul_one] at hn
    change acc + laneLength W n = _
    rw [laneLength_eq hn]
  | succ k ih =>
    intro n acc hn
    have hsplit : 2 ^ (W * 2 ^ (k + 1)) = 2 ^ (W * 2 ^ k) * 2 ^ (W * 2 ^ k) := by
      rw [← Nat.pow_add, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
    have hpos : 0 < 2 ^ (W * 2 ^ k) := Nat.two_pow_pos _
    change Bool.casesOn (motive := fun _ => Nat) (Nat.beq (n >>> (W * 2 ^ k)) 0)
      (windowLength W k (n >>> (W * 2 ^ k)) (acc + W * 2 ^ k)) (windowLength W k n acc) = _
    by_cases hupper : n >>> (W * 2 ^ k) = 0
    · rw [hupper, show Nat.beq 0 0 = true from rfl]
      refine ih n acc ?_
      rw [Nat.shiftRight_eq_div_pow] at hupper
      exact (Nat.div_eq_zero_iff_lt hpos).1 hupper
    · have hbeq : Nat.beq (n >>> (W * 2 ^ k)) 0 = false := by
        cases h : Nat.beq (n >>> (W * 2 ^ k)) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hupper
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hupper (Nat.zero_shiftRight _)
      have hbound : n >>> (W * 2 ^ k) < 2 ^ (W * 2 ^ k) := by
        rw [Nat.shiftRight_eq_div_pow]
        exact (Nat.div_lt_iff_lt_mul hpos).2 (by rw [← hsplit]; exact hn)
      rw [hbeq]
      change windowLength W k (n >>> (W * 2 ^ k)) (acc + W * 2 ^ k) = _
      rw [ih _ _ hbound, ite_eq_right hupper, ite_eq_right hn0, log2_of_shiftRight hupper]
      omega

/--
`bitLength B n` is the bit length of `n`: zero for zero and `n.log2 + 1` otherwise, for every
`B` and every `n < 2 ^ B`.
-/
theorem bitLength_eq {B n : Nat} (hn : n < 2 ^ B) :
    bitLength B n = if n = 0 then 0 else n.log2 + 1 := by
  unfold bitLength
  cases hsmall : Nat.ble B 384
  · cases hwide : Nat.ble B 16777216
    · exact laneLength_eq hn
    · have hB : B ≤ 16777216 := Nat.le_of_ble_eq_true hwide
      have hquot : (B - 1) / 128 < 2 ^ 17 :=
        Nat.lt_of_lt_of_le (by omega : (B - 1) / 128 < 131072) (by decide)
      have hcover : (B - 1) / 128 < 2 ^ laneLength 17 ((B - 1) / 128) := by
        rw [laneLength_eq hquot]
        split
        · next h => rw [h]; decide
        · exact Nat.lt_log2_self
      have hbound : n < 2 ^ (128 * 2 ^ laneLength 17 ((B - 1) / 128)) := by
        refine lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) ?_)
        generalize 2 ^ laneLength 17 ((B - 1) / 128) = steps at hcover
        omega
      change windowLength 128 (laneLength 17 ((B - 1) / 128)) n 0 = _
      rw [windowLength_eq _ _ n 0 hbound, Nat.zero_add]
  · exact laneLength_eq hn

/-- A number whose bits from position `B` on are all zero is below `2 ^ B`. -/
theorem lt_two_pow_of_shiftRight_eq_zero {n B : Nat} (h : n >>> B = 0) : n < 2 ^ B := by
  rw [Nat.shiftRight_eq_div_pow] at h
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos B)).1 h

/-- The test `Nat.beq (n >>> B) 0` decides `n < 2 ^ B`. -/
theorem beq_shiftRight_zero (n B : Nat) :
    Nat.beq (Nat.shiftRight n B) 0 = decide (n < 2 ^ B) := by
  change Nat.beq (n >>> B) 0 = _
  by_cases h : n < 2 ^ B
  · rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h, decide_eq_true h]
    rfl
  · rw [decide_eq_false h]
    cases hb : Nat.beq (n >>> B) 0
    · rfl
    · exact absurd (lt_two_pow_of_shiftRight_eq_zero (Nat.eq_of_beq_eq_true hb)) h

/--
`windowBelow k n other` is the bit length of `n` whenever `other` is: the search answers when
`n < 2 ^ (128 * 2 ^ k)`, and `other` is returned as it is otherwise.
-/
theorem windowBelow_eq (k n : Nat) {other : Nat}
    (hother : other = if n = 0 then 0 else n.log2 + 1) :
    windowBelow k n other = if n = 0 then 0 else n.log2 + 1 := by
  have hk : Nat.shiftLeft 128 k = 128 * 2 ^ k := by
    change 128 <<< k = _
    rw [Nat.shiftLeft_eq]
  unfold windowBelow
  rw [beq_shiftRight_zero, hk]
  by_cases h : n < 2 ^ (128 * 2 ^ k)
  · rw [decide_eq_true h]
    change windowLength 128 k n 0 = _
    rw [windowLength_eq 128 k n 0 h, Nat.zero_add]
  · rw [decide_eq_false h]
    exact hother

/-- The bits of a number below `2 ^ (s + t)` from position `s` on are a number below `2 ^ t`. -/
theorem shiftRight_lt_two_pow {n B : Nat} (s t : Nat) (hn : n < 2 ^ B) (hB : s + t = B) :
    n >>> s < 2 ^ t := by
  subst hB
  rw [Nat.shiftRight_eq_div_pow]
  refine (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s)).2 ?_
  rw [← Nat.pow_add, Nat.add_comm]
  exact hn

/--
A bit length split at bit `s`: when `low` is the bit length of `n` for `n < 2 ^ s` and `high` the
bit length of the upper part `n >>> s` when it is not zero, the test on the upper part selects
the bit length of `n`.
-/
theorem lengthSplit_eq (n s : Nat) {low high : Nat}
    (hlow : n < 2 ^ s → low = if n = 0 then 0 else n.log2 + 1)
    (hhigh : n >>> s ≠ 0 → high = (n >>> s).log2 + 1) :
    Bool.casesOn (motive := fun _ => Nat) (Nat.beq (Nat.shiftRight n s) 0) (Nat.add s high) low =
      if n = 0 then 0 else n.log2 + 1 := by
  rw [beq_shiftRight_zero n s]
  by_cases h : n < 2 ^ s
  · rw [decide_eq_true h]
    exact hlow h
  · rw [decide_eq_false h]
    have hn : n ≠ 0 := by
      rintro rfl
      exact h (Nat.two_pow_pos s)
    have hupper : n >>> s ≠ 0 := fun h0 => h (lt_two_pow_of_shiftRight_eq_zero h0)
    change s + high = _
    rw [hhigh hupper, ite_eq_right hn, log2_of_shiftRight hupper]
    omega

/-- `size128 n` is the bit length of every `n < 2 ^ 128`: zero for zero and `n.log2 + 1`
otherwise. -/
theorem size128_eq {n : Nat} (hn : n < 2 ^ 128) :
    size128 n = if n = 0 then 0 else n.log2 + 1 :=
  lengthSplit_eq n 64 (fun h => laneLength_eq h)
    (fun h => (laneLength_eq (shiftRight_lt_two_pow 64 64 hn rfl)).trans (ite_eq_right h))

/-- `size256 n` is the bit length of every `n < 2 ^ 256`: zero for zero and `n.log2 + 1`
otherwise. -/
theorem size256_eq {n : Nat} (hn : n < 2 ^ 256) :
    size256 n = if n = 0 then 0 else n.log2 + 1 :=
  lengthSplit_eq n 128 (fun h => size128_eq h)
    (fun h => (size128_eq (shiftRight_lt_two_pow 128 128 hn rfl)).trans (ite_eq_right h))

/-- `size512 n` is the bit length of every `n < 2 ^ 512`: zero for zero and `n.log2 + 1`
otherwise. -/
theorem size512_eq {n : Nat} (hn : n < 2 ^ 512) :
    size512 n = if n = 0 then 0 else n.log2 + 1 :=
  lengthSplit_eq n 256 (fun h => size256_eq h)
    (fun h => (size256_eq (shiftRight_lt_two_pow 256 256 hn rfl)).trans (ite_eq_right h))

/-- `sizeAbove n` is the bit length `n.log2 + 1` of every `n` with `2 ^ 256 ≤ n`. -/
theorem sizeAbove_eq {n : Nat} (hn : 2 ^ 256 ≤ n) : sizeAbove n = n.log2 + 1 := by
  have hn0 : n ≠ 0 := by
    have := Nat.two_pow_pos 256
    omega
  have h256 : n >>> 256 ≠ 0 := fun h =>
    absurd (lt_two_pow_of_shiftRight_eq_zero h) (Nat.not_lt.2 hn)
  unfold sizeAbove
  rw [beq_shiftRight_zero n 512, beq_shiftRight_zero n 1024, beq_shiftRight_zero n 4096]
  by_cases h512 : n < 2 ^ 512
  · rw [decide_eq_true h512]
    change 256 + size256 (n >>> 256) = _
    rw [size256_eq (shiftRight_lt_two_pow 256 256 h512 rfl), ite_eq_right h256,
      log2_of_shiftRight h256]
    omega
  · rw [decide_eq_false h512]
    have hupper : n >>> 512 ≠ 0 := fun h => h512 (lt_two_pow_of_shiftRight_eq_zero h)
    by_cases h1024 : n < 2 ^ 1024
    · rw [decide_eq_true h1024]
      change 512 + size512 (n >>> 512) = _
      rw [size512_eq (shiftRight_lt_two_pow 512 512 h1024 rfl), ite_eq_right hupper,
        log2_of_shiftRight hupper]
      omega
    · rw [decide_eq_false h1024]
      by_cases h4096 : n < 2 ^ 4096
      · rw [decide_eq_true h4096]
        have hwindow : n < 2 ^ (128 * 2 ^ 5) := by
          rw [show 128 * 2 ^ 5 = 4096 from rfl]
          exact h4096
        change windowLength 128 5 n 0 = _
        rw [windowLength_eq 128 5 n 0 hwindow, Nat.zero_add, ite_eq_right hn0]
      · rw [decide_eq_false h4096]
        exact (windowBelow_eq 7 n (windowBelow_eq 10 n (windowBelow_eq 17 n
          (windowBelow_eq 25 n (by rw [ite_eq_right hn0]))))).trans (ite_eq_right hn0)

/--
`size n` is the bit length of `n`: zero for zero, and one more than the position `n.log2` of the
leading bit otherwise. There is no bound on `n`.
-/
theorem size_eq_log2 (n : Nat) : size n = if n = 0 then 0 else n.log2 + 1 := by
  unfold size
  rw [beq_shiftRight_zero n 64, beq_shiftRight_zero n 128, beq_shiftRight_zero n 256]
  by_cases h64 : n < 2 ^ 64
  · rw [decide_eq_true h64]
    exact laneLength_eq h64
  · rw [decide_eq_false h64]
    have hn : n ≠ 0 := by
      rintro rfl
      exact h64 (Nat.two_pow_pos 64)
    have hupper : n >>> 64 ≠ 0 := fun h => h64 (lt_two_pow_of_shiftRight_eq_zero h)
    by_cases h128 : n < 2 ^ 128
    · rw [decide_eq_true h128]
      change 64 + laneLength 64 (n >>> 64) = _
      rw [laneLength_eq (shiftRight_lt_two_pow 64 64 h128 rfl), ite_eq_right hupper,
        ite_eq_right hn, log2_of_shiftRight hupper]
      omega
    · rw [decide_eq_false h128, ite_eq_right hn]
      have htop : n >>> 128 ≠ 0 := fun h => h128 (lt_two_pow_of_shiftRight_eq_zero h)
      by_cases h256 : n < 2 ^ 256
      · rw [decide_eq_true h256]
        change 128 + size128 (n >>> 128) = _
        rw [size128_eq (shiftRight_lt_two_pow 128 128 h256 rfl), ite_eq_right htop,
          log2_of_shiftRight htop]
        omega
      · rw [decide_eq_false h256]
        exact sizeAbove_eq (Nat.not_lt.1 h256)

/-- `size n` is Mathlib's `Nat.size n`, the number of bits of `n`. -/
theorem size_eq (n : Nat) : size n = Nat.size n := by
  rw [size_eq_log2]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [ite_eq_right hn]
    apply le_antisymm
    · exact Nat.lt_size.2 (Nat.log2_self_le hn)
    · exact Nat.size_le.2 Nat.lt_log2_self

/-- Compiled form of `size`: the binary logarithm plus one, and zero for zero. -/
def Compiled.size (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- Compiled code computes the bit length with `Nat.log2`. -/
compiled_as size := Compiled.size by size_eq_log2

/-- `Nat.log2` is the kernel bit length minus one, for every natural number. -/
theorem log2_eq_size_sub_one (n : Nat) : n.log2 = size n - 1 := by
  rw [size_eq_log2]
  by_cases hn : n = 0
  · subst hn
    rfl
  · rw [ite_eq_right hn]
    rfl

end FloatLib.Numerics.Kernel
