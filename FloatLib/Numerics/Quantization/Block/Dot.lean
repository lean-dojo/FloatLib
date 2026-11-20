/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Block.Policy
public import FloatLib.Numerics.ErrorBound.Algebra
public import FloatLib.Numerics.Reduction.Blocked
public import FloatLib.Numerics.Reduction.Tree

/-!
# Block dot products and ordered accumulation

A dot product of two block-scaled operands has an exact form and an accumulated form.

Exactly, the sum of the decoded products is, block by block, the product of the two block scales
times the dot product of the stored elements (`sum_decode_mul_decode`). This is the factored form
of OCP MX 1.0, section 6.1, and of NVFP4 (NVIDIA, arXiv:2509.25149, equation 5), for every element
format, scale format and block shape whose scales are constant on the blocks.

Hardware accumulates. `accumulate A terms` stores every partial sum in an accumulator format `A`,
in list order, and `accumulateChunked N W chunks` accumulates each chunk in a narrow format `N`
and adds the chunk results in a wider format `W`: the promotion DeepSeek-V3 reports for Hopper FP8
matrix products, with a narrow accumulator promoted every 128 elements. The bounds need only the
error budget of the accumulator, `|A.round z - z| ≤ u * |z| + η`, so they hold for every format
with such a budget.

Two other descriptions of an ordered sum in the library are stated through these. The blocked
dot product `BlockedDot.kernelEntry`, with its fused multiply-add rounded in `N` and its addition
in `W`, is `accumulateChunked N W` on the products of its blocks, and has that bound. And
`accumulate` is one schedule of `ReductionTree`, the left chain from zero, so a theorem about
every schedule holds for it.

## Main results

* `sum_decode_mul_decode`: exact block factorization of a dot product.
* `abs_foldl_round_sub_le`: accumulation of computed terms `f c` against exact terms `g c` with
  `|f c - g c| ≤ e c`. Over `n` terms the error is at most
  `((1 + u) ^ n - 1) * ∑ |g c| + (1 + u) ^ n * ∑ e c + n * (1 + u) ^ n * η`. Rounded products,
  rounded block-scale multiplications and promoted partial sums are all terms of this form.
* `abs_accumulate_sub_le`: accumulation of exact terms.
* `accumulate_eq_sum`: accumulation is exact when the accumulator stores every partial sum.
* `abs_accumulateChunked_sub_le`: with at most `k` terms in each of `m` chunks, promotion has error
  at most `((1 + u_W) ^ m * (1 + u_N) ^ k - 1) * ∑ |t|` plus
  `m * (1 + u_W) ^ m * (k * (1 + u_N) ^ k * η_N + η_W)`.
* `kernelEntry_eq_accumulateChunked`, `abs_kernelEntry_sub_le`: the blocked dot product over `n`
  terms in blocks of width `w` is accumulation with promotion, with that bound for
  `m = blockCount w n` and `k = w`, against the exact dot product.
* `accumulate_eq_eval`, `accumulate_scaled`: accumulation is the left chain of `ReductionTree`,
  so it commutes with scaling the format, by the theorem of reduction schedules.
* `abs_accumulate_sub_accumulate_le_of_perm`: two orders of the same `n` terms differ by at most
  twice the accumulation bound.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Block

variable {ι γ K : Type*}

section Exact

variable [Field K] [Fintype ι] [DecidableEq γ]

/--
Exact block dot product. If each operand's total scale is constant on the blocks of `group`, the
sum of the decoded products is the sum over the blocks of the product of the two block scales and
the dot product of the block's stored elements.
-/
theorem sum_decode_mul_decode (group : ι → γ) (s t : γ → K) (e f : ι → K) :
    ∑ i, Format.decode (fun i => s (group i)) e i * Format.decode (fun i => t (group i)) f i =
      ∑ g ∈ Finset.univ.image group, s g * t g * ∑ i ∈ members group g, e i * f i := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := group) (t := Finset.univ.image group)
    (fun i _ => Finset.mem_image_of_mem group (Finset.mem_univ i))]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hg : group i = g := (Finset.mem_filter.mp hi).2
  simp only [Format.decode, hg]
  ac_rfl

end Exact

section Accumulate

variable [Field K]

/-- Ordered accumulation: every partial sum, in list order, is stored in the accumulator format.
The accumulator starts at zero. -/
def accumulate (A : Rounding K) (terms : List K) : K :=
  terms.foldl (fun acc t => A.round (acc + t)) 0

/-- Accumulation with promotion: each chunk is accumulated in the narrow format `N`, and the chunk
results are accumulated in the wide format `W`. -/
def accumulateChunked (N W : Rounding K) (chunks : List (List K)) : K :=
  accumulate W (chunks.map (accumulate N))

/-- Accumulation is exact when the accumulator stores every partial sum without error. -/
theorem accumulate_eq_sum {A : Rounding K} (terms : List K)
    (h : ∀ l, l <+: terms → A.Fixes l.sum) : accumulate A terms = terms.sum := by
  induction terms using List.reverseRecOn with
  | nil => rfl
  | append_singleton init t ih =>
    have hinit : accumulate A init = init.sum :=
      ih fun l hl => h l (hl.trans (List.prefix_append init [t]))
    have hfull := h (init ++ [t]) List.prefix_rfl
    simp only [accumulate, List.foldl_append, List.foldl_cons, List.foldl_nil] at hinit ⊢
    rw [hinit]
    simpa [Rounding.Fixes] using hfull

/-- Sum of an affine function of the entries of a list. -/
private theorem sum_map_mul_add {α : Type*} (l : List α) (f : α → K) (a b : K) :
    (l.map fun c => a * f c + b).sum = a * (l.map f).sum + l.length * b := by
  induction l with
  | nil => simp
  | cons c rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [ih]
    rw [mul_add, add_mul]; ac_rfl

/-! ## The blocked dot product is accumulation with promotion -/

/-- Accumulation in the identity format is the sum. -/
theorem accumulate_exact (terms : List K) : accumulate Rounding.exact terms = terms.sum :=
  accumulate_eq_sum terms fun _ _ => rfl

/-- The products of chunk `u` of a dot product over `n` terms in chunks of width `w`: the terms
`a k * b k` for `k` in `[u w, min ((u + 1) w, n))`. -/
def dotChunk (a b : ℕ → K) (w n u : ℕ) : List K :=
  (List.range' (u * w) (min ((u + 1) * w) n - u * w)).map fun k => a k * b k

/-- The chunks of a dot product over `n` terms in chunks of width `w`. -/
def dotChunks (a b : ℕ → K) (w n : ℕ) : List (List K) :=
  (List.range' 0 (Numerics.BlockedDot.blockCount w n)).map (dotChunk a b w n)

/--
The blocked dot product is accumulation with promotion. With the fused multiply-add rounded in
the format `N`, the addition of block partials rounded in the format `W`, and the start zero,
`BlockedDot.kernelEntry` accumulates each block in `N` and the block results in `W`.
-/
theorem kernelEntry_eq_accumulateChunked (N W : Rounding K) (a b : ℕ → K) (w n : ℕ) :
    Numerics.BlockedDot.kernelEntry (fun x y z => N.round (x * y + z))
        (fun x y => W.round (x + y)) 0 a b w n (some 0) =
      accumulateChunked N W (dotChunks a b w n) := by
  have hstep : (fun (acc : K) (k : ℕ) => N.round (a k * b k + acc)) =
      fun acc k => N.round (acc + a k * b k) :=
    funext fun acc => funext fun k => by rw [add_comm]
  simp only [Numerics.BlockedDot.kernelEntry, Numerics.BlockedDot.blockPartial,
    Numerics.BlockedDot.blockDot, hstep, accumulateChunked, accumulate, dotChunks, dotChunk,
    List.map_map, List.foldl_map, Function.comp_def]

/-- The chunks hold every term once: their sums add up to the dot product. -/
theorem sum_dotChunks (a b : ℕ → K) {w : ℕ} (hw : 0 < w) (n : ℕ) :
    ((dotChunks a b w n).map List.sum).sum = ∑ k ∈ Finset.range n, a k * b k := by
  have h := kernelEntry_eq_accumulateChunked Rounding.exact Rounding.exact a b w n
  have hexact : accumulateChunked Rounding.exact Rounding.exact (dotChunks a b w n) =
      ((dotChunks a b w n).map List.sum).sum := by
    rw [accumulateChunked, accumulate_exact]
    congr 1
    exact List.map_congr_left fun c _ => accumulate_exact c
  rw [← hexact, ← h]
  have := Numerics.BlockedDot.kernelEntry_eq_sum a b w n hw (some 0)
  simpa [Rounding.exact] using this

/-! ## Accumulation is the left chain of reduction schedules -/

/-- Ordered accumulation is one reduction schedule, the left chain from zero. -/
theorem accumulate_eq_eval (A : Rounding K) (terms : List K) :
    accumulate A terms =
      (Numerics.ReductionTree.leftChain 0 terms).eval (fun x y => A.round (x + y)) id := by
  rw [Numerics.ReductionTree.eval_leftChain]
  rfl

/--
Accumulation commutes with scaling the format. Accumulating the terms scaled by `σ` in the format
`A.scaled σ` gives the accumulation in `A`, scaled by `σ`: `ReductionTree.map_eval` on the left
chain.
-/
theorem accumulate_scaled (A : Rounding K) {σ : K} (hσ : σ ≠ 0) (terms : List K) :
    accumulate (A.scaled σ) (terms.map (· * σ)) = accumulate A terms * σ := by
  have h := Numerics.ReductionTree.map_eval (Numerics.ReductionTree.leftChain 0 terms)
    (fun x y => A.round (x + y)) id (· * σ) (fun x y => (A.scaled σ).round (x + y))
    (Numerics.ReductionTree.AllNodes.of_forall _ _ _ fun x y => by
      simp only [Rounding.scaled_round, ← add_mul, mul_div_assoc, div_self hσ, mul_one])
  rw [← accumulate_eq_eval A terms, Numerics.ReductionTree.eval_leftChain] at h
  simpa [accumulate, List.foldl_map, Function.comp_def] using h.symm

/-! ## Error bounds of accumulation -/

variable [LinearOrder K] [IsStrictOrderedRing K]

/--
Accumulation of computed terms. Starting from `a`, which approximates the exact partial sum `a'`
of magnitude at most `B`, the accumulator adds computed terms `f c` whose exact values are `g c`
with `|f c - g c| ≤ e c`. The result differs from the exact sum by at most the propagated start
error, the accumulated rounding of the exact terms, the propagated term errors and the absolute
budget of each addition.
-/
theorem abs_foldl_round_sub_le {α : Type*} {A : Rounding K} {u η : K} (hu : 0 ≤ u)
    (hη : 0 ≤ η) (hA : ∀ z, |A.round z - z| ≤ u * |z| + η) (f g e : α → K) (l : List α)
    (he : ∀ c ∈ l, |f c - g c| ≤ e c) (a a' B : K) (hB : |a'| ≤ B) :
    |l.foldl (fun acc c => A.round (acc + f c)) a - (a' + (l.map g).sum)| ≤
      (1 + u) ^ l.length * |a - a'| +
        ((1 + u) ^ l.length - 1) * (B + (l.map fun c => |g c|).sum) +
        (1 + u) ^ l.length * (l.map e).sum + l.length * (1 + u) ^ l.length * η := by
  induction l generalizing a a' B with
  | nil => simp
  | cons c rest ih =>
    have hc : |f c - g c| ≤ e c := he c List.mem_cons_self
    have hrest : ∀ c ∈ rest, |f c - g c| ≤ e c := fun c hc => he c (List.mem_cons_of_mem _ hc)
    have hB' : |a' + g c| ≤ B + |g c| :=
      Numerics.Backward.abs_add_le_add hB le_rfl
    have h := ih hrest (A.round (a + f c)) (a' + g c) (B + |g c|) hB'
    set p := (1 + u) ^ rest.length with hp
    have hp1 : 1 ≤ p := one_le_pow₀ (by exact le_add_of_nonneg_right hu)
    have hG : 0 ≤ (rest.map fun c => |g c|).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
        exact abs_nonneg _
    have hδ : |A.round (a + f c) - (a' + g c)| ≤
        (1 + u) * |a - a'| + u * (B + |g c|) + (1 + u) * e c + η := by
      have h1 := hA (a + f c)
      have h2 : |a + f c| ≤ B + |a - a'| + |g c| + e c := by
        have ha : |a| ≤ B + |a - a'| := by
          simpa only [sub_zero] using Numerics.compose_error
            (le_refl |a - a'|) (show |a' - 0| ≤ B by simpa using hB)
        have hf : |f c| ≤ |g c| + e c := by
          simpa only [sub_zero] using Numerics.compose_error hc
            (show |g c - 0| ≤ |g c| by simp)
        simpa only [add_assoc] using Numerics.Backward.abs_add_le_add ha hf
      have h3 : |A.round (a + f c) - (a' + g c)| ≤
          |A.round (a + f c) - (a + f c)| + |a - a'| + |f c - g c| := by
        simpa only [add_assoc, add_left_comm, add_comm] using
          Numerics.add_error (le_refl |a - a'|) (le_refl |f c - g c|)
            (le_refl |A.round (a + f c) - (a + f c)|)
      have h4 : u * |a + f c| ≤ u * (B + |a - a'| + |g c| + e c) :=
        mul_le_mul_of_nonneg_left h2 hu
      linarith
    have hpδ := mul_le_mul_of_nonneg_left hδ (by linarith : (0 : K) ≤ p)
    have hE : 0 ≤ (rest.map e).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact (abs_nonneg _).trans (hrest c hc)
    have hn : (0 : K) ≤ rest.length := Nat.cast_nonneg _
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, List.length_cons, pow_succ,
      Nat.cast_add, Nat.cast_one]
    rw [← hp]
    have e1 : a' + (g c + (rest.map g).sum) = a' + g c + (rest.map g).sum := by ac_rfl
    rw [e1]
    refine h.trans ?_
    linarith [mul_nonneg (mul_nonneg (by linarith : (0 : K) ≤ p) hu) hG,
      mul_nonneg (mul_nonneg (by linarith : (0 : K) ≤ p) hu) hE,
      mul_nonneg (mul_nonneg (mul_nonneg hn (by linarith : (0 : K) ≤ p)) hu) hη,
      mul_nonneg (mul_nonneg (by linarith : (0 : K) ≤ p) hu) hη,
      mul_nonneg (by linarith : (0 : K) ≤ p) hη, abs_nonneg (g c), abs_nonneg (a - a')]

/--
Ordered accumulation of `n` exact terms in a format with budget `u * |z| + η` has error at most
`((1 + u) ^ n - 1) * ∑ |t| + n * (1 + u) ^ n * η`.
-/
theorem abs_accumulate_sub_le {A : Rounding K} {u η : K} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hA : ∀ z, |A.round z - z| ≤ u * |z| + η) (terms : List K) :
    |accumulate A terms - terms.sum| ≤
      ((1 + u) ^ terms.length - 1) * (terms.map abs).sum +
        terms.length * (1 + u) ^ terms.length * η := by
  have h := abs_foldl_round_sub_le hu hη hA (fun t => t) (fun t => t) (fun _ => 0) terms
    (fun c _ => by simp) 0 0 0 (by simp)
  simpa [accumulate] using h

/--
Accumulation with promotion. With at most `k` terms in each of the `m` chunks, a narrow
accumulator with budget `u_N * |z| + η_N` and a wide accumulator with budget `u_W * |z| + η_W`,
the result differs from the exact sum of all terms by at most
`((1 + u_W) ^ m * (1 + u_N) ^ k - 1)` times the sum of the magnitudes, plus
`m * (1 + u_W) ^ m * (k * (1 + u_N) ^ k * η_N + η_W)`.
-/
theorem abs_accumulateChunked_sub_le {N W : Rounding K} {uN ηN uW ηW : K}
    (huN : 0 ≤ uN) (hηN : 0 ≤ ηN) (huW : 0 ≤ uW) (hηW : 0 ≤ ηW)
    (hN : ∀ z, |N.round z - z| ≤ uN * |z| + ηN) (hW : ∀ z, |W.round z - z| ≤ uW * |z| + ηW)
    (chunks : List (List K)) (k : ℕ) (hk : ∀ c ∈ chunks, c.length ≤ k) :
    |accumulateChunked N W chunks - (chunks.map List.sum).sum| ≤
      ((1 + uW) ^ chunks.length * (1 + uN) ^ k - 1) *
          (chunks.map fun c => (c.map abs).sum).sum +
        chunks.length * (1 + uW) ^ chunks.length * (k * (1 + uN) ^ k * ηN + ηW) := by
  set T := (chunks.map fun c => (c.map abs).sum).sum with hT
  set pW := (1 + uW) ^ chunks.length
  set pN := (1 + uN) ^ k
  have hpW1 : 1 ≤ pW := one_le_pow₀ (by exact le_add_of_nonneg_right huW)
  -- Error of one chunk in the narrow accumulator.
  have hchunk : ∀ c ∈ chunks, |accumulate N c - c.sum| ≤
      (pN - 1) * (c.map abs).sum + k * pN * ηN := by
    intro c hc
    have h := abs_accumulate_sub_le huN hηN hN c
    have hlen : (c.length : K) ≤ k := by exact_mod_cast hk c hc
    have hpow : (1 + uN) ^ c.length ≤ pN := pow_le_pow_right₀ (by linarith) (hk c hc)
    have hpow1 : 1 ≤ (1 + uN) ^ c.length := one_le_pow₀ (by exact le_add_of_nonneg_right huN)
    have habs : 0 ≤ (c.map abs).sum :=
      List.sum_nonneg fun x hx => by
        obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
        exact abs_nonneg _
    have h1 : ((1 + uN) ^ c.length - 1) * (c.map abs).sum ≤ (pN - 1) * (c.map abs).sum :=
      mul_le_mul_of_nonneg_right (by linarith) habs
    have h2 : (c.length : K) * (1 + uN) ^ c.length * ηN ≤ k * pN * ηN := by
      have : (c.length : K) * (1 + uN) ^ c.length ≤ k * pN :=
        mul_le_mul hlen hpow (by linarith) (by exact_mod_cast Nat.zero_le k)
      exact mul_le_mul_of_nonneg_right this hηN
    linarith
  have h := abs_foldl_round_sub_le huW hηW hW (accumulate N) List.sum
    (fun c => (pN - 1) * (c.map abs).sum + k * pN * ηN) chunks hchunk 0 0 0 (by simp)
  have hsumAbs : (chunks.map fun c => |c.sum|).sum ≤ T := by
    rw [hT]
    refine List.sum_le_sum fun c _ => ?_
    exact List.le_sum_of_subadditive abs abs_zero.le abs_add_le c
  have hsumE : (chunks.map fun c => (pN - 1) * (c.map abs).sum + k * pN * ηN).sum =
      (pN - 1) * T + chunks.length * (k * pN * ηN) :=
    sum_map_mul_add chunks (fun c => (c.map abs).sum) (pN - 1) (k * pN * ηN)
  have hfold : accumulateChunked N W chunks =
      chunks.foldl (fun acc c => W.round (acc + accumulate N c)) 0 := by
    simp [accumulateChunked, accumulate, List.foldl_map]
  rw [hfold]
  simp only [sub_zero, abs_zero, mul_zero, zero_add] at h
  rw [hsumE] at h
  refine h.trans ?_
  have hm : (0 : K) ≤ chunks.length := Nat.cast_nonneg _
  linarith [mul_le_mul_of_nonneg_left hsumAbs (by linarith : (0 : K) ≤ pW - 1),
    mul_nonneg (mul_nonneg hm (by linarith : (0 : K) ≤ pW)) hηW]

/--
**Error of the blocked dot product.** With fused multiply-adds rounded in a format of budget
`uN * |z| + ηN` and block partials added in a format of budget `uW * |z| + ηW`, the blocked dot
product over `n` terms in `m = blockCount w n` blocks of width `w` differs from the exact dot
product by at most `((1 + uW) ^ m * (1 + uN) ^ w - 1) * ∑ |a k * b k|` plus
`m * (1 + uW) ^ m * (w * (1 + uN) ^ w * ηN + ηW)`.
-/
theorem abs_kernelEntry_sub_le {N W : Rounding K} {uN ηN uW ηW : K}
    (huN : 0 ≤ uN) (hηN : 0 ≤ ηN) (huW : 0 ≤ uW) (hηW : 0 ≤ ηW)
    (hN : ∀ z, |N.round z - z| ≤ uN * |z| + ηN) (hW : ∀ z, |W.round z - z| ≤ uW * |z| + ηW)
    (a b : ℕ → K) {w : ℕ} (hw : 0 < w) (n : ℕ) :
    |Numerics.BlockedDot.kernelEntry (fun x y z => N.round (x * y + z))
        (fun x y => W.round (x + y)) 0 a b w n (some 0) - ∑ k ∈ Finset.range n, a k * b k| ≤
      ((1 + uW) ^ Numerics.BlockedDot.blockCount w n * (1 + uN) ^ w - 1) *
          ∑ k ∈ Finset.range n, |a k * b k| +
        Numerics.BlockedDot.blockCount w n * (1 + uW) ^ Numerics.BlockedDot.blockCount w n *
          (w * (1 + uN) ^ w * ηN + ηW) := by
  have hlength : (dotChunks a b w n).length = Numerics.BlockedDot.blockCount w n := by
    simp [dotChunks]
  have hk : ∀ c ∈ dotChunks a b w n, c.length ≤ w := by
    intro c hc
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hc
    simp only [dotChunk, List.length_map, List.length_range']
    have hmin : min ((u + 1) * w) n ≤ (u + 1) * w := Nat.min_le_left _ _
    have hsucc : (u + 1) * w = u * w + w := Nat.succ_mul u w
    omega
  have habs : ((dotChunks a b w n).map fun c => (c.map abs).sum).sum =
      ∑ k ∈ Finset.range n, |a k * b k| := by
    have h := sum_dotChunks (fun k => |a k * b k|) (fun _ => 1) hw n
    simp only [mul_one] at h
    rw [← h]
    simp [dotChunks, dotChunk, List.map_map, Function.comp_def]
  have h := abs_accumulateChunked_sub_le huN hηN huW hηW hN hW (dotChunks a b w n) w hk
  rw [← kernelEntry_eq_accumulateChunked, sum_dotChunks a b hw n, habs, hlength] at h
  exact h

/--
Two orders of one accumulation. In a format with budget `u * |z| + η`, accumulating `n` terms in
two orders gives results at most `2 * (((1 + u) ^ n - 1) * ∑ |t| + n * (1 + u) ^ n * η)` apart.
-/
theorem abs_accumulate_sub_accumulate_le_of_perm {A : Rounding K} {u η : K} (hu : 0 ≤ u)
    (hη : 0 ≤ η) (hA : ∀ z, |A.round z - z| ≤ u * |z| + η) {terms terms' : List K}
    (h : terms.Perm terms') :
    |accumulate A terms - accumulate A terms'| ≤
      2 * (((1 + u) ^ terms.length - 1) * (terms.map abs).sum +
        terms.length * (1 + u) ^ terms.length * η) := by
  have h₁ := abs_accumulate_sub_le hu hη hA terms
  have h₂ := abs_accumulate_sub_le hu hη hA terms'
  rw [← h.length_eq, ← (h.map abs).sum_eq, ← h.sum_eq, abs_sub_comm] at h₂
  have bound := Numerics.compose_error h₁ h₂
  linarith

end Accumulate

end FloatLib.Floats.Formats.Block
