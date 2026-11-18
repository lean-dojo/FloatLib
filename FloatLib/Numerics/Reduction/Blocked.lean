/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Div

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A dot product with a fixed order of operations

A dot product adds `a k * b k` over `k < K`, and floating point needs an order for that sum. Here
`K` is cut into blocks of width `w`. Each block's partial sum is a chain of fused multiply-adds
starting from zero (`blockDot`), and the block partials are added from left to right
(`kernelEntry`). The operations are parameters, so the same schedule describes an exact sum, a
rounded format, or a generated kernel, and a kernel proved equal to `kernelEntry` gives every entry
as a function of its two vectors alone, such as the row and column of a matrix product, whatever
the shape of the call. With IEEE 754 fused multiply-add and addition that fixes the bits of every
finite or infinite result.

* With an exact commutative addition and `fma a b c = a * b + c`, every block width gives the
  ordinary sum, added to the start value when there is one (`kernelEntry_eq_sum`). The product
  is any operation: only the addition is used.
* An entry reads only the first `K` terms of its vectors (`kernelEntry_congr`).
* A dot product may be computed in pieces along `K`: a call on a range of `K` that starts on a
  block boundary, continuing from the result of the call on the terms before it, extends the
  running sum by its blocks (`kernelEntry_first`, `kernelEntry_continue`), so the last call ends
  with the whole sum. This is the meaning of the start value.

With no terms `kernelEntry` is `zero`, or the start value when there is one.
-/

@[expose] public section

namespace FloatLib.Numerics.BlockedDot

open scoped BigOperators

variable {β : Type*}

/-- The partial sum of `a k * b k` over `[lo, hi)`: a chain of fused multiply-adds from `zero`. -/
def blockDot (fma : β → β → β → β) (zero : β) (a b : ℕ → β) (lo hi : ℕ) : β :=
  (List.range' lo (hi - lo)).foldl (fun acc k => fma (a k) (b k) acc) zero

/-- Number of blocks of width `w` that cover `K` terms: the ceiling of `K / w`. -/
def blockCount (w K : ℕ) : ℕ := K ⌈/⌉ w

/-- Block `u` of width `w` covers the terms `[u w, min ((u + 1) w, K))`. -/
def blockPartial (fma : β → β → β → β) (zero : β) (a b : ℕ → β) (w K u : ℕ) : β :=
  blockDot fma zero a b (u * w) (min ((u + 1) * w) K)

/-- Folding the next `m'` units onto the fold of the first `m` gives the fold of all `m + m'`. -/
theorem foldl_continue (add : β → β → β) (v : ℕ → β) (s m m' : ℕ) (init : β) :
    (List.range' (s + m) m').foldl (fun acc u => add acc (v u))
        ((List.range' s m).foldl (fun acc u => add acc (v u)) init) =
      (List.range' s (m + m')).foldl (fun acc u => add acc (v u)) init := by
  rw [← List.range'_append, List.foldl_append, Nat.one_mul]

/-- The blocked dot product over `K` terms in blocks of `w`: the block partials added from left to
right, from the first block's partial, or from `start` when the call continues an earlier one. With
no terms and no `start` it is `zero`. -/
def kernelEntry (fma : β → β → β → β) (add : β → β → β) (zero : β) (a b : ℕ → β) (w K : ℕ) :
    Option β → β
  | none => (List.range' 1 (blockCount w K - 1)).foldl
      (fun acc u => add acc (blockPartial fma zero a b w K u)) (blockPartial fma zero a b w K 0)
  | some start => (List.range' 0 (blockCount w K)).foldl
      (fun acc u => add acc (blockPartial fma zero a b w K u)) start

/-- An entry reads only the first `K` terms of each operand. -/
theorem kernelEntry_congr (fma : β → β → β → β) (add : β → β → β) (zero : β) {a a' b b' : ℕ → β}
    {w K : ℕ} (h : ∀ c < K, a c = a' c ∧ b c = b' c) (start : Option β) :
    kernelEntry fma add zero a b w K start = kernelEntry fma add zero a' b' w K start := by
  have hp : ∀ u, blockPartial fma zero a b w K u = blockPartial fma zero a' b' w K u := by
    intro u
    unfold blockPartial blockDot
    refine List.foldl_ext _ _ _ fun acc c hc => ?_
    obtain ⟨h₁, h₂⟩ := List.mem_range'_1.mp hc
    have hlt : c < min ((u + 1) * w) K := by
      by_cases hle : u * w ≤ min ((u + 1) * w) K
      · rw [Nat.add_sub_cancel' hle] at h₂
        exact h₂
      · omega
    have hK : c < K := Nat.lt_of_lt_of_le hlt (Nat.min_le_right _ _)
    rw [(h c hK).1, (h c hK).2]
  cases start <;> simp only [kernelEntry, hp]

/-- The terms from `lo` on. -/
def shift (a : ℕ → β) (lo : ℕ) : ℕ → β := fun c => a (lo + c)

/-- The fold of the first `t` blocks of the whole product. -/
def prefixFold (fma : β → β → β → β) (add : β → β → β) (zero : β) (a b : ℕ → β) (w K t : ℕ) : β :=
  (List.range' 1 (t - 1)).foldl (fun acc u => add acc (blockPartial fma zero a b w K u))
    (blockPartial fma zero a b w K 0)

/-- The dot product of the operands shifted by `lo` over `[x, y)` is that of the operands over
`[lo + x, lo + y)`, in the same order. -/
theorem blockDot_shift (fma : β → β → β → β) (zero : β) (a b : ℕ → β) (lo x y : ℕ) :
    blockDot fma zero (shift a lo) (shift b lo) x y = blockDot fma zero a b (lo + x) (lo + y) := by
  unfold blockDot shift
  rw [Nat.add_sub_add_left, ← List.map_add_range', List.foldl_map]

/-- When the width `w` is positive and divides `l`, `l` terms make exactly `l / w` blocks. -/
theorem blockCount_of_dvd {w l : ℕ} (hw : 0 < w) (h : w ∣ l) : blockCount w l = l / w := by
  obtain ⟨q, rfl⟩ := h
  rw [blockCount, Nat.mul_div_cancel_left q hw]
  exact smul_ceilDiv hw q

/-- When the width `w` is positive and divides `lo`, the `lo / w` blocks before `lo` and the
blocks of the next `l` terms add up to the number of blocks of the first `lo + l` terms. -/
theorem blockCount_add {w lo l : ℕ} (hw : 0 < w) (h : w ∣ lo) :
    lo / w + blockCount w l = blockCount w (lo + l) := by
  obtain ⟨q, rfl⟩ := h
  unfold blockCount
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.ceilDiv_eq_add_pred_div,
    show w * q + l + w - 1 = w * q + (l + w - 1) by omega, Nat.mul_add_div hw,
    Nat.mul_div_cancel_left q hw]

/-- The blocks of a range of `K` are blocks of the whole product, when the range starts on a block
boundary and ends on one or at the end. -/
theorem blockPartial_shift (fma : β → β → β → β) (zero : β) (a b : ℕ → β) {w K lo l u : ℕ}
    (hw : 0 < w) (hlo : w ∣ lo) (hu : u < blockCount w l)
    (hfit : (w ∣ l ∧ lo + l ≤ K) ∨ lo + l = K) :
    blockPartial fma zero (shift a lo) (shift b lo) w l u =
      blockPartial fma zero a b w K (lo / w + u) := by
  unfold blockPartial
  rw [blockDot_shift]
  have hlo' : lo / w * w = lo := Nat.div_mul_cancel hlo
  have hstart : lo + u * w = (lo / w + u) * w := by rw [Nat.add_mul, hlo']
  have hend : lo + min ((u + 1) * w) l = min ((lo / w + u + 1) * w) K := by
    have he : (lo / w + u + 1) * w = lo + (u + 1) * w := by
      rw [Nat.add_assoc, Nat.add_mul, hlo']
    rw [he]
    rcases hfit with ⟨hdvd, hle⟩ | hK
    · rw [blockCount_of_dvd hw hdvd] at hu
      have h₁ : (u + 1) * w ≤ l := (Nat.le_div_iff_mul_le hw).mp (Nat.succ_le_of_lt hu)
      rw [Nat.min_eq_left h₁, Nat.min_eq_left (by omega)]
    · subst hK
      rw [Nat.add_min_add_left]
  rw [hstart, hend]

/-- The call on the first range, from no start, is the fold of its blocks of the whole product. -/
theorem kernelEntry_first (fma : β → β → β → β) (add : β → β → β) (zero : β) (a b : ℕ → β)
    {w K l : ℕ} (hw : 0 < w) (hl : 0 < l) (hfit : (w ∣ l ∧ l ≤ K) ∨ l = K) :
    kernelEntry fma add zero (shift a 0) (shift b 0) w l none =
      prefixFold fma add zero a b w K (blockCount w l) := by
  have hfit' : (w ∣ l ∧ 0 + l ≤ K) ∨ 0 + l = K := by rw [Nat.zero_add]; exact hfit
  have hc : 0 < blockCount w l := by
    unfold blockCount
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_pos (by omega) hw
  simp only [kernelEntry, prefixFold]
  rw [blockPartial_shift fma zero a b hw (dvd_zero w) hc hfit', Nat.zero_div, Nat.zero_add]
  refine List.foldl_ext _ _ _ fun acc u hu => ?_
  rw [blockPartial_shift fma zero a b hw (dvd_zero w) (by
    have := List.mem_range'_1.mp hu; omega) hfit', Nat.zero_div, Nat.zero_add]

/-- The call on a later range, from the result of the terms before it, extends the fold by its
blocks. -/
theorem kernelEntry_continue (fma : β → β → β → β) (add : β → β → β) (zero : β) (a b : ℕ → β)
    {w K lo l : ℕ} (hw : 0 < w) (hlo : w ∣ lo) (hpos : 0 < lo)
    (hfit : (w ∣ l ∧ lo + l ≤ K) ∨ lo + l = K) :
    kernelEntry fma add zero (shift a lo) (shift b lo) w l
        (some (prefixFold fma add zero a b w K (lo / w))) =
      prefixFold fma add zero a b w K (lo / w + blockCount w l) := by
  have ht : 0 < lo / w := Nat.div_pos (Nat.le_of_dvd hpos hlo) hw
  have hstep : kernelEntry fma add zero (shift a lo) (shift b lo) w l
      (some (prefixFold fma add zero a b w K (lo / w))) =
      (List.range' (1 + (lo / w - 1)) (blockCount w l)).foldl
        (fun acc u => add acc (blockPartial fma zero a b w K u))
        ((List.range' 1 (lo / w - 1)).foldl
          (fun acc u => add acc (blockPartial fma zero a b w K u))
          (blockPartial fma zero a b w K 0)) := by
    simp only [kernelEntry, prefixFold]
    rw [show 1 + (lo / w - 1) = lo / w + 0 by omega, ← List.map_add_range', List.foldl_map]
    refine List.foldl_ext _ _ _ fun acc u hu => ?_
    rw [blockPartial_shift fma zero a b hw hlo (by have := List.mem_range'_1.mp hu; omega) hfit]
  rw [hstep, foldl_continue add (fun u => blockPartial fma zero a b w K u) 1 (lo / w - 1)
    (blockCount w l) (blockPartial fma zero a b w K 0)]
  unfold prefixFold
  rw [show lo / w - 1 + blockCount w l = lo / w + blockCount w l - 1 by omega]

/-! ## Full blocks and a short last block

A generated kernel runs a loop with a constant trip count over the full blocks and handles the
remainder once. `kernelEntry_eq_blocks` gives `kernelEntry` that shape for every positive width:
`K / w` blocks of exactly `w` terms, then one block of `K % w` terms when that is not zero. -/

/-- A block below the block count starts below `K`. -/
theorem mul_lt_of_lt_blockCount {w K u : ℕ} (hw : 0 < w) (h : u < blockCount w K) :
    u * w < K := by
  by_contra hc
  have hle : K ≤ w * u := by rw [Nat.mul_comm]; exact Nat.le_of_not_lt hc
  exact absurd ((ceilDiv_le_iff_le_mul hw).mpr hle) (Nat.not_le_of_lt h)

/-- The number of blocks is the number of full blocks, plus one when terms remain. -/
theorem blockCount_eq_div_add {w : ℕ} (hw : 0 < w) (K : ℕ) :
    blockCount w K = K / w + if 0 < K % w then 1 else 0 := by
  have hpred : w - 1 < w := Nat.sub_lt hw Nat.one_pos
  have := Nat.mod_lt K hw
  unfold blockCount
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.add_sub_assoc hw, Nat.add_div hw, Nat.div_eq_of_lt hpred,
    Nat.mod_eq_of_lt hpred, Nat.add_zero]
  split <;> split <;> omega

/-- Where block `u` ends, for `u ≤ K / w`: `w` terms after its start when it is a full block,
`K % w` terms after its start when it is the block after the full ones. -/
theorem min_succ_mul_eq {w K u : ℕ} (hw : 0 < w) (h : u ≤ K / w) :
    min ((u + 1) * w) K = u * w + if u < K / w then w else K % w := by
  split
  · rename_i hlt
    rw [Nat.min_eq_left ((Nat.le_div_iff_mul_le hw).mp hlt), Nat.succ_mul]
  · rename_i hge
    have hu : u = K / w := Nat.le_antisymm h (Nat.le_of_not_lt hge)
    subst hu
    rw [Nat.min_eq_right (by rw [Nat.succ_mul]; exact (Nat.lt_div_mul_add hw).le),
      Nat.div_add_mod']

/-- A full block: for `u < K / w`, block `u` is the `w` terms from `u * w`. -/
theorem blockPartial_of_lt_div (fma : β → β → β → β) (zero : β) (a b : ℕ → β) {w K u : ℕ}
    (h : u < K / w) :
    blockPartial fma zero a b w K u = blockDot fma zero a b (u * w) (u * w + w) := by
  have hw : 0 < w := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
  unfold blockPartial
  rw [min_succ_mul_eq hw (Nat.le_of_lt h), ite_eq_left h]

/-- The short last block: block `K / w` is the `K % w` terms after the full blocks. -/
theorem blockPartial_div (fma : β → β → β → β) (zero : β) (a b : ℕ → β) {w : ℕ} (hw : 0 < w)
    (K : ℕ) :
    blockPartial fma zero a b w K (K / w) =
      blockDot fma zero a b (K / w * w) (K / w * w + K % w) := by
  unfold blockPartial
  rw [min_succ_mul_eq (K := K) hw (Nat.le_refl _), ite_eq_right (Nat.lt_irrefl _)]

/-- **`kernelEntry` as a generated kernel computes it.** From the start value, or from the first
block's partial when there is none, add the full blocks of `w` terms from `first` on, then the
short last block when `K % w` terms remain. Every block in the loop has the constant length `w`. -/
theorem kernelEntry_eq_blocks (fma : β → β → β → β) (add : β → β → β) (zero : β) (a b : ℕ → β)
    {w : ℕ} (hw : 0 < w) (K : ℕ) (start : Option β) :
    kernelEntry fma add zero a b w K start =
      let first := if start.isSome then 0 else 1
      let run := (List.range' first (K / w - first)).foldl
        (fun acc u => add acc (blockDot fma zero a b (u * w) (u * w + w)))
        (start.getD (blockDot fma zero a b 0 (min w K)))
      if 0 < K % w ∧ first ≤ K / w then
        add run (blockDot fma zero a b (K / w * w) (K / w * w + K % w))
      else run := by
  have hcount := blockCount_eq_div_add hw K
  have hfull : ∀ (l : List ℕ), (∀ u ∈ l, u < K / w) → ∀ init,
      l.foldl (fun acc u => add acc (blockPartial fma zero a b w K u)) init =
        l.foldl (fun acc u => add acc (blockDot fma zero a b (u * w) (u * w + w))) init := by
    intro l hl init
    refine List.foldl_ext _ _ _ fun acc u hu => ?_
    rw [blockPartial_of_lt_div fma zero a b (hl u hu)]
  have hmem : ∀ first u, u ∈ List.range' first (K / w - first) → u < K / w := by
    intro first u hu
    have := List.mem_range'_1.mp hu
    omega
  have htail := blockPartial_div fma zero a b hw K
  cases start with
  | some x =>
    unfold kernelEntry
    rw [hcount]
    simp only [Option.isSome_some, ↓reduceIte, Nat.sub_zero, Nat.zero_le, and_true,
      Option.getD_some]
    by_cases ht : 0 < K % w
    · simp only [ht, ↓reduceIte]
      rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.zero_add, Nat.one_mul, htail, hfull _ (fun u hu => hmem 0 u (by simpa using hu))]
    · simp only [ht, ↓reduceIte, Nat.add_zero]
      exact hfull _ (fun u hu => hmem 0 u (by simpa using hu)) x
  | none =>
    have h0 : blockPartial fma zero a b w K 0 = blockDot fma zero a b 0 (min w K) := by
      simp [blockPartial]
    unfold kernelEntry
    rw [hcount, h0]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.getD_none]
    by_cases ht : 0 < K % w ∧ 1 ≤ K / w
    · simp only [ht, and_self, ↓reduceIte]
      rw [show K / w + 1 - 1 = K / w - 1 + 1 by omega, List.range'_concat]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show 1 + 1 * (K / w - 1) = K / w by omega, htail, hfull _ (hmem 1)]
    · simp only [ht, ↓reduceIte]
      rw [show K / w + (if 0 < K % w then 1 else 0) - 1 = K / w - 1 by split <;> omega]
      exact hfull _ (hmem 1) _

/-! ## With an exact commutative addition the reproducible product is the product -/

section Exact

variable {R : Type*} [AddCommMonoid R]

/-- With a commutative addition, folding `acc + v u` over the `n` indices from `s` adds
`∑ u ∈ Finset.Ico s (s + n), v u` to the start `z`. -/
theorem foldl_add_eq (v : ℕ → R) : ∀ (n s : ℕ) (z : R),
    (List.range' s n).foldl (fun acc u => acc + v u) z = z + ∑ u ∈ Finset.Ico s (s + n), v u
  | 0, s, z => by simp
  | n + 1, s, z => by
    rw [List.range'_succ, List.foldl_cons, foldl_add_eq v n (s + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : s < s + (n + 1)),
      show s + 1 + n = s + (n + 1) by omega, add_assoc]

variable [Mul R]

/-- Folding `a k * b k + acc` over the `n` indices from `lo` adds
`∑ k ∈ Finset.Ico lo (lo + n), a k * b k` to the start `z`: `foldl_add_eq` with the two
summands exchanged. -/
theorem foldl_fma_eq (a b : ℕ → R) : ∀ (n lo : ℕ) (z : R),
    (List.range' lo n).foldl (fun acc k => a k * b k + acc) z =
      z + ∑ k ∈ Finset.Ico lo (lo + n), a k * b k := by
  intro n lo z
  have hstep : (fun (acc : R) (k : ℕ) => a k * b k + acc) = fun acc k => acc + a k * b k :=
    funext fun acc => funext fun k => add_comm _ _
  rw [hstep]
  exact foldl_add_eq (fun k => a k * b k) n lo z

/-- A block partial is the sum over its terms. -/
theorem blockDot_eq_sum (a b : ℕ → R) (lo hi : ℕ) :
    blockDot (fun x y z => x * y + z) 0 a b lo hi = ∑ k ∈ Finset.Ico lo hi, a k * b k := by
  unfold blockDot
  rw [foldl_fma_eq, zero_add]
  rcases Nat.le_total lo hi with h | h
  · rw [Nat.add_sub_cancel' h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero, Finset.Ico_self, Finset.Ico_eq_empty_of_le h]

/-- The first `n` blocks cover the terms below `min (n w) K`. -/
theorem sum_blockPartial (a b : ℕ → R) (w K : ℕ) : ∀ n : ℕ,
    ∑ u ∈ Finset.range n, blockPartial (fun x y z => x * y + z) 0 a b w K u =
      ∑ k ∈ Finset.Ico 0 (min (n * w) K), a k * b k
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_blockPartial a b w K n, blockPartial, blockDot_eq_sum]
    by_cases h : n * w ≤ K
    · rw [min_eq_left h, Finset.sum_Ico_consecutive _ (Nat.zero_le _) (le_min (by
        rw [Nat.succ_mul]; exact Nat.le_add_right _ _) h)]
    · have hK : K < n * w := Nat.lt_of_not_le h
      have hK' : K ≤ (n + 1) * w := Nat.le_trans (Nat.le_of_lt hK)
        (by rw [Nat.succ_mul]; exact Nat.le_add_right _ _)
      rw [min_eq_right (Nat.le_of_lt hK), min_eq_right hK',
        Finset.Ico_eq_empty_of_le (Nat.le_of_lt hK), Finset.sum_empty, add_zero]

/-- Blocks of width `w` cover all `K` terms. -/
theorem le_blockCount_mul (w K : ℕ) (hw : 0 < w) : K ≤ blockCount w K * w := by
  rw [blockCount, Nat.mul_comm]
  exact (ceilDiv_le_iff_le_mul hw).mp le_rfl

/-- **The reproducible product is the product.** With an exact commutative addition, for every
positive block width, an entry is `∑ k < K, a k * b k`, added to the start value when there is
one. -/
theorem kernelEntry_eq_sum (a b : ℕ → R) (w K : ℕ) (hw : 0 < w) (start : Option R) :
    kernelEntry (fun x y z => x * y + z) (· + ·) 0 a b w K start =
      start.getD 0 + ∑ k ∈ Finset.range K, a k * b k := by
  have hall : ∑ u ∈ Finset.range (blockCount w K),
      blockPartial (fun x y z => x * y + z) 0 a b w K u = ∑ k ∈ Finset.range K, a k * b k := by
    rw [sum_blockPartial, min_eq_right (le_blockCount_mul w K hw), Finset.range_eq_Ico]
  cases start with
  | some z =>
    simp only [kernelEntry, Option.getD_some]
    rw [foldl_add_eq, Nat.zero_add, ← Finset.range_eq_Ico, hall]
  | none =>
    simp only [kernelEntry, Option.getD_none, zero_add]
    rw [foldl_add_eq, ← hall]
    rcases Nat.eq_zero_or_pos (blockCount w K) with h0 | hpos
    · have hK : K = 0 := Nat.le_zero.mp (by simpa [h0] using le_blockCount_mul w K hw)
      subst hK
      simp [h0, blockPartial, blockDot]
    · rw [show 1 + (blockCount w K - 1) = blockCount w K by omega, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot hpos]

end Exact

end FloatLib.Numerics.BlockedDot
