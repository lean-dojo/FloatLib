/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.ErrorBound
public import FloatLib.Numerics.ErrorBound.Loop

/-!
# Backward error

A backward-error statement says that a computed value is the exact result for perturbed inputs:
`computed = f (x₁ * (1 + δ₁), …, xₙ * (1 + δₙ))` with a bound on each `|δᵢ|`. When underflow adds
an absolute error that no relative perturbation of the inputs accounts for, the statement becomes
`|computed - f (x₁ * (1 + δ₁), …)| ≤ a`, which Higham calls mixed forward-backward stability.

The lemmas do not depend on a number format. Most concern real numbers; addition, subtraction
and product perturbation bounds hold over any linearly ordered commutative ring.

* A mixed error `MixedError x x₀ r a` of one operation is the standard model
  `x = x₀ * c + η` with `|c - 1| ≤ r` and `|η| ≤ a` for the explicit factor `MixedError.factor`
  and offset `MixedError.offset`.
* `Backward.round` moves that factor onto a reference `R` once `R * c = R'` is known, and the
  `Backward.scale_*` lemmas prove such an equation for a leaf, a sum, the absorbing factor of a
  product and a numerator. A perturbation that already took factors `g` takes a further one by
  `Backward.abs_delta_scale`: bounds multiply, so `k` roundings give `(1 + u) ^ k - 1`.
* `List.fold_backward` is the loop rule. One step computes `G (observe s * ρ) v p` up to `a s v`,
  where `G` is the exact step on an entry perturbed by `p`, and scaling the accumulator by `c` is
  the same as scaling the perturbation (`G (s * c) v (scale c p) = G s v p * c`). Then the loop
  equals the exact loop of `G` on perturbed entries, up to `List.foldBackwardAbsolute`. The entry at
  position `k` of `n` takes the factors of the `n - 1 - k` later steps.
  `List.fold_backward_exact` states the equality when no step has an absolute error, the `fixed`
  forms cover an accumulator that takes no factor, and the `finRange` forms index the
  perturbations by `Fin n`. The slope of `G` in its accumulator is required at the perturbations
  a step may take, so the entries that multiply the accumulator may be perturbed, as in a
  product of entries.
* `List.foldBackwardAbsolute_le_geom` is the absolute term in closed form.
* A square takes a factor as its square root in both factors (`Backward.scale_sq`), which is as
  close to one (`Backward.abs_sqrt_sub_one_le`).
* A backward statement gives a forward bound. The `Backward.deviation_*` lemmas bound what a
  perturbation changes in a read, a product, a quotient, an exponential, a logarithm and a
  computation perturbed as a whole, and `List.abs_foldl_sub_foldl_le` accumulates the changes
  `D v` of the steps of a loop through the exact loop, as `∑ j, D j` when the step adds to its
  accumulator (`List.foldl_finRange_add_eq_sum`). `List.abs_foldl_affine_sub_le` is the case
  of a sum or of Horner's rule, and `List.abs_foldl_add_sub_le_mul` the relative bound of a sum
  whose terms have one sign.

## References

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM, 2002,
  Sections 1.5, 3.1 and 5.1.
-/

@[expose] public section

namespace FloatLib.Numerics

noncomputable section

/-! ### The standard model of a mixed error -/

namespace MixedError

variable {x x₀ r a : ℝ}

/-- The factor `c` of the standard model `x = x₀ * c + η` of `MixedError x x₀ r a`: the error
`x - x₀` is split between the relative and the absolute part in the proportion `r * |x₀| : a`. -/
def factor (x x₀ r a : ℝ) : ℝ :=
  1 + r * (if 0 ≤ x₀ then 1 else -1) * ((x - x₀) / (r * |x₀| + a))

/-- The offset `η` of the standard model `x = x₀ * c + η` of `MixedError x x₀ r a`. -/
def offset (x x₀ r a : ℝ) : ℝ :=
  a * ((x - x₀) / (r * |x₀| + a))

/-- The error of a mixed bound is at most its budget, so their ratio is at most one in
magnitude. -/
private theorem abs_ratio_le_one (h : MixedError x x₀ r a) :
    |(x - x₀) / (r * |x₀| + a)| ≤ 1 := by
  rcases (add_nonneg (mul_nonneg h.r_nonneg (abs_nonneg x₀)) h.a_nonneg).eq_or_lt with hW | hW
  · rw [← hW]; simp
  · rw [abs_div, abs_of_pos hW]
    exact (div_le_one hW).mpr h.bound

/-- A mixed error is the standard model with the factor `factor` and the offset `offset`. -/
theorem eq_mul_factor_add_offset (h : MixedError x x₀ r a) :
    x = x₀ * factor x x₀ r a + offset x x₀ r a := by
  unfold factor offset
  have hs : x₀ * (if 0 ≤ x₀ then (1 : ℝ) else -1) = |x₀| := by
    split_ifs with hx
    · rw [mul_one, abs_of_nonneg hx]
    · rw [mul_neg_one, abs_of_neg (not_le.mp hx)]
  rcases (add_nonneg (mul_nonneg h.r_nonneg (abs_nonneg x₀)) h.a_nonneg).eq_or_lt with hW | hW
  · have hx : x = x₀ := by
      have hb := h.bound
      rw [← hW] at hb
      exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)
    rw [← hW]
    simp [hx]
  · have hsplit : x₀ * (1 + r * (if 0 ≤ x₀ then 1 else -1) * ((x - x₀) / (r * |x₀| + a))) +
        a * ((x - x₀) / (r * |x₀| + a)) =
          x₀ + (r * (x₀ * (if 0 ≤ x₀ then 1 else -1)) + a) * ((x - x₀) / (r * |x₀| + a)) := by
      ring
    rw [hsplit, hs]
    field_simp
    ring

/-- The factor of the standard model is within `r` of one. -/
theorem abs_factor_sub_one_le (h : MixedError x x₀ r a) : |factor x x₀ r a - 1| ≤ r := by
  have hsign : |(if 0 ≤ x₀ then (1 : ℝ) else -1)| = 1 := by split_ifs <;> simp
  have hratio := abs_ratio_le_one h
  have hr := h.r_nonneg
  unfold factor
  rw [add_sub_cancel_left, abs_mul, abs_mul, hsign, abs_of_nonneg hr, mul_one]
  exact mul_le_of_le_one_right hr hratio

/-- The offset of the standard model is at most `a` in magnitude. -/
theorem abs_offset_le (h : MixedError x x₀ r a) : |offset x x₀ r a| ≤ a := by
  have hratio := abs_ratio_le_one h
  have ha := h.a_nonneg
  unfold offset
  rw [abs_mul, abs_of_nonneg ha]
  exact mul_le_of_le_one_right ha hratio

end MixedError

/-! ### Moving factors onto a reference -/

namespace Backward

variable {x X R R' A B A' B' c d g h r a : ℝ}

/-- Two factors within `g - 1` and `h - 1` of one have a product within `g * h - 1` of one. -/
theorem abs_mul_sub_one_le (hc : |c - 1| ≤ g - 1) (hd : |d - 1| ≤ h - 1) :
    |c * d - 1| ≤ g * h - 1 := by
  have hg := (abs_nonneg _).trans hc
  have hsplit : c * d - 1 = (c - 1) * (d - 1) + (c - 1) + (d - 1) := by ring
  calc |c * d - 1| ≤ |(c - 1) * (d - 1)| + |c - 1| + |d - 1| := by
        rw [hsplit]; exact abs_add_three _ _ _
    _ = |c - 1| * |d - 1| + |c - 1| + |d - 1| := by rw [abs_mul]
    _ ≤ (g - 1) * (h - 1) + (g - 1) + (h - 1) := by gcongr
    _ = g * h - 1 := by ring

/-- A perturbation `d` that took factors `g` takes the factor `c`: the new perturbation
`(1 + d) * c - 1` took factors `g * h`. -/
theorem abs_delta_scale (hd : |d| ≤ g - 1) (hc : |c - 1| ≤ h - 1) :
    |(1 + d) * c - 1| ≤ g * h - 1 :=
  abs_mul_sub_one_le (by simpa using hd) hc

/-- A factor within `r` of one took `1 + r`. -/
theorem abs_sub_one_le_growth (hc : |c - 1| ≤ r) : |c - 1| ≤ 1 + r - 1 := by
  simpa using hc

/-- The loop form of `abs_delta_scale`: a perturbation that took `g * q ^ m` takes one more
factor of a step and has then taken `g * q ^ (m + 1)`. -/
theorem slot_growth (β : Type*) (g q : ℝ) (m : ℕ) (_v : β) (p c : ℝ)
    (hp : |p| ≤ g * q ^ m - 1) (hc : |c - 1| ≤ q - 1) :
    |(1 + p) * c - 1| ≤ g * q ^ (m + 1) - 1 := by
  rw [pow_succ, ← mul_assoc]
  exact abs_delta_scale hp hc

/-- One rounding with a relative error of at most one has a growth of at most two. -/
theorem one_add_le_two (hr : r ≤ 1) : 1 + r ≤ 2 := by
  linarith

/-- A factor within `h - 1` of one is nonnegative when the growth `h` is at most two. -/
theorem nonneg_of_abs_sub_one_le (hc : |c - 1| ≤ h - 1) (hh : h ≤ 2) : 0 ≤ c := by
  have := neg_abs_le (c - 1)
  linarith

/-- The square root of a nonnegative factor within `h - 1` of one is within `h - 1` of one as
well. -/
theorem abs_sqrt_sub_one_le (h0 : 0 ≤ c) (hc : |c - 1| ≤ h - 1) : |√c - 1| ≤ h - 1 := by
  have hs := Real.sqrt_nonneg c
  have hmul : (√c - 1) * (√c + 1) = c - 1 := by
    calc (√c - 1) * (√c + 1) = √c * √c - 1 := by ring
      _ = c - 1 := by rw [Real.mul_self_sqrt h0]
  have hle : |√c - 1| ≤ |c - 1| := by
    rw [← hmul, abs_mul]
    exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_nonneg (by linarith)]; linarith)
  exact hle.trans hc

/-- A growth that bounds a factor's distance from one is nonnegative. -/
theorem growth_nonneg (hc : |c - 1| ≤ g - 1) : 0 ≤ g := by
  linarith [abs_nonneg (c - 1)]

/-- The perturbations of the entries of a list are mapped by `f`, as when each takes a factor:
a bound `B k` on the one at position `k` becomes `B' k` when `f` turns the one into the other. -/
theorem forall_getElem_map {P : Type*} (f : P → P) (n : ℕ) (B B' : (k : ℕ) → k < n → P → Prop)
    (ps : List P) (hf : ∀ k hk p, B k hk p → B' k hk (f p))
    (hb : ∀ (k : ℕ) (hk : k < n) (hp : k < ps.length), B k hk ps[k]) :
    ∀ (k : ℕ) (hk : k < n) (hp : k < (ps.map f).length), B' k hk (ps.map f)[k] := by
  intro k hk hp
  rw [List.getElem_map]
  exact hf k hk _ (hb k hk (by simpa using hp))

/-- Mapping the perturbations of a list keeps their number. -/
theorem length_map {P : Type*} {n : ℕ} (f : P → P) (ps : List P) (hn : ps.length = n) :
    (ps.map f).length = n := by
  simpa using hn

/-- A factor within `g - 1` of one has magnitude at most `g`. -/
theorem abs_le_of_abs_sub_one_le (hc : |c - 1| ≤ g - 1) : |c| ≤ g := by
  have := abs_sub_abs_le_abs_sub c 1
  rw [abs_one] at this
  linarith

/-- A perturbed leaf takes a factor. -/
theorem scale_leaf (v d c : ℝ) : v * (1 + d) * c = v * (1 + ((1 + d) * c - 1)) := by ring

/-- An unperturbed leaf takes its first factor. -/
theorem scale_fresh (v c : ℝ) : v * c = v * (1 + (c - 1)) := by ring

/-- Zero takes any factor. -/
theorem scale_zero (c : ℝ) : (0 : ℝ) * c = 0 := zero_mul c

/-- A sum takes a factor in both terms. -/
theorem scale_add (hA : A * c = A') (hB : B * c = B') : (A + B) * c = A' + B' := by
  rw [add_mul, hA, hB]

/-- A difference takes a factor in both terms. -/
theorem scale_sub (hA : A * c = A') (hB : B * c = B') : (A - B) * c = A' - B' := by
  rw [sub_mul, hA, hB]

/-- A negation takes a factor in its operand. -/
theorem scale_neg (hA : A * c = A') : -A * c = -A' := by
  rw [neg_mul, hA]

/-- A product takes a factor in its left factor. -/
theorem scale_mul_left (B : ℝ) (hA : A * c = A') : A * B * c = A' * B := by
  rw [mul_right_comm, hA]

/-- A product takes a factor in its right factor. -/
theorem scale_mul_right (A : ℝ) (hB : B * c = B') : A * B * c = A * B' := by
  rw [mul_assoc, hB]

/-- A square takes a nonnegative factor as its square root in both factors: `x * x * c` is the
square of `x * √c`. -/
theorem scale_sq (h0 : 0 ≤ c) (hA : A * √c = A') (hB : B * √c = B') : A * B * c = A' * B' := by
  rw [← hA, ← hB, mul_mul_mul_comm, Real.mul_self_sqrt h0]

/-- A factor on the left factor of a product moves onto the right factor. -/
theorem move_right (A : ℝ) (hB : B * c = B') : A * c * B = A * B' := by
  rw [← hB]
  ring

/-- A factor on the right factor of a product moves onto the left factor. -/
theorem move_left (B : ℝ) (hA : A * c = A') : A * (B * c) = A' * B := by
  rw [← hA]
  ring

/-- A perturbation `d` within `g - 1` is the factor `1 + d` within `g - 1` of one. -/
theorem abs_one_add_sub_one_le (hd : |d| ≤ g - 1) : |1 + d - 1| ≤ g - 1 := by
  simpa using hd

/-- The factor `1 + (c - 1)` of a first perturbation is nonnegative when `c` is. -/
theorem one_add_nonneg (hc : 0 ≤ c) : 0 ≤ 1 + (c - 1) := by
  linarith

/-- The factor `1 + d` of a perturbation stays nonnegative when it takes a nonnegative factor. -/
theorem one_add_scale_nonneg (hd : 0 ≤ 1 + d) (hc : 0 ≤ c) : 0 ≤ 1 + ((1 + d) * c - 1) := by
  have := mul_nonneg hd hc
  linarith

/-- A square root takes a nonnegative factor as its square in its argument. -/
theorem scale_sqrt (h0 : 0 ≤ c) (hA : A * (c * c) = A') : √A * c = √A' := by
  rw [← hA, Real.sqrt_mul' A (mul_self_nonneg c), Real.sqrt_mul_self h0]

/-- A maximum takes a nonnegative factor in both operands. -/
theorem scale_max (h0 : 0 ≤ c) (hA : A * c = A') (hB : B * c = B') :
    max A B * c = max A' B' := by
  rw [← hA, ← hB, max_mul_of_nonneg _ _ h0]

/-- A minimum takes a nonnegative factor in both operands. -/
theorem scale_min (h0 : 0 ≤ c) (hA : A * c = A') (hB : B * c = B') :
    min A B * c = min A' B' := by
  rw [← hA, ← hB, min_mul_of_nonneg _ _ h0]

/-- A branch takes a factor in both alternatives. -/
theorem scale_ite {p : Prop} [Decidable p] (hA : A * c = A') (hB : B * c = B') :
    (if p then A else B) * c = if p then A' else B' := by
  split_ifs <;> assumption

/-- A quotient takes a factor in its numerator. -/
theorem scale_div (B : ℝ) (hA : A * c = A') : A / B * c = A' / B := by
  rw [div_mul_eq_mul_div, hA]

/-- A negated value is as close to its negated reference. -/
theorem neg (hx : |x - R| ≤ A) : |-x - -R| ≤ A := by
  rwa [neg_sub_neg, abs_sub_comm]

/-- The square root of a value within `A` of its reference is within `√A` of the square root of
the reference. -/
theorem sqrt (hx : |x - R| ≤ A) : |√x - √R| ≤ √A := by
  have hd := abs_nonneg (√x - √R)
  have hsum : |√x - √R| ≤ √x + √R := by
    rw [abs_le]
    constructor <;> linarith [Real.sqrt_nonneg x, Real.sqrt_nonneg R]
  have hsq : |√x - √R| ^ 2 ≤ A :=
    calc |√x - √R| ^ 2 = |√x - √R| * |√x - √R| := sq _
      _ ≤ |√x - √R| * (√x + √R) := mul_le_mul_of_nonneg_left hsum hd
      _ ≤ |x - R| := abs_sqrt_sub_sqrt_mul_le x R
      _ ≤ A := hx
  calc |√x - √R| = √(|√x - √R| ^ 2) := (Real.sqrt_sq hd).symm
    _ ≤ √A := Real.sqrt_le_sqrt hsq

/-- A branch between two values, each within its bound of its reference, is within the bound of
the alternative taken of the same branch between the references. -/
theorem branch {p : Prop} [Decidable p] {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |(if p then x else y) - (if p then R else S)| ≤ if p then A else B := by
  split_ifs <;> assumption

/-- The maximum of two values within `A` and `B` of their references is within the larger of
`A` and `B` of the maximum of the references. -/
theorem maximum {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |max x y - max R S| ≤ max A B :=
  (abs_max_sub_max_le_max x y R S).trans (max_le_max hx hy)

/-- The minimum of two values within `A` and `B` of their references is within the larger of
`A` and `B` of the minimum of the references. -/
theorem minimum {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |min x y - min R S| ≤ max A B :=
  (abs_min_sub_min_le_max x y R S).trans (max_le_max hx hy)

/-- A perturbed read `v * (1 + d)` with `|d| ≤ b` is within `|v| * b` of the read `v`. -/
theorem deviation_leaf (v : ℝ) {b : ℝ} (hd : |d| ≤ b) : |v * (1 + d) - v| ≤ |v| * b := by
  rw [show v * (1 + d) - v = v * d by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left hd (abs_nonneg v)

/-- A product of two values within `A` and `B` of their references `R` and `S` is within
`A * |y| + (|x| + A) * B` of `R * S`. The bound reads the computed values, not the references. -/
theorem mul {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) :
    |x * y - R * S| ≤ A * |y| + (|x| + A) * B := by
  have hx' : |R - x| ≤ A := by rwa [abs_sub_comm]
  have hy' : |S - y| ≤ B := by rwa [abs_sub_comm]
  have h := deviation_mul hx' hy'
  rw [abs_sub_comm] at h
  exact h.trans_eq (by ring)

/-- A quotient of two values within `A` and `B` of their references `R` and `S`, where `B` is
below `|S|`, is within `(A * |S| + |R| * B) / (|S| * (|S| - B))` of `R / S`. -/
theorem deviation_div {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) (hS : B < |S|) :
    |x / y - R / S| ≤ (A * |S| + |R| * B) / (|S| * (|S| - B)) := by
  have hB := (abs_nonneg _).trans hy
  have hSpos : 0 < |S| := lt_of_le_of_lt hB hS
  have hgap : 0 < |S| - B := sub_pos.mpr hS
  have hylow : |S| - B ≤ |y| := by
    have := abs_sub_abs_le_abs_sub S y
    rw [abs_sub_comm] at this
    linarith
  have hypos : 0 < |y| := lt_of_lt_of_le hgap hylow
  have hy0 : y ≠ 0 := abs_pos.mp hypos
  have hS0 : S ≠ 0 := abs_pos.mp hSpos
  have hsplit : x / y - R / S = ((x - R) * S - R * (y - S)) / (y * S) := by
    field_simp
    ring
  have hnum : |(x - R) * S - R * (y - S)| ≤ A * |S| + |R| * B := by
    calc |(x - R) * S - R * (y - S)| ≤ |(x - R) * S| + |R * (y - S)| := abs_sub _ _
      _ = |x - R| * |S| + |R| * |y - S| := by rw [abs_mul, abs_mul]
      _ ≤ A * |S| + |R| * B := by gcongr
  rw [hsplit, abs_div, abs_mul]
  calc |(x - R) * S - R * (y - S)| / (|y| * |S|)
      ≤ (A * |S| + |R| * B) / (|y| * |S|) :=
        div_le_div_of_nonneg_right hnum (mul_pos hypos hSpos).le
    _ ≤ (A * |S| + |R| * B) / (|S| * (|S| - B)) := by
        have hnonneg : 0 ≤ A * |S| + |R| * B :=
          add_nonneg (mul_nonneg ((abs_nonneg _).trans hx) hSpos.le)
            (mul_nonneg (abs_nonneg R) hB)
        refine div_le_div_of_nonneg_left hnonneg (mul_pos hSpos hgap) ?_
        rw [mul_comm |y| |S|]
        exact mul_le_mul_of_nonneg_left hylow hSpos.le

/-- A value within `A` of its reference `R`, perturbed as a whole by `d` with `|d| ≤ b`, is
within `A + (|R| + A) * b` of `R`. -/
theorem deviation_node {b : ℝ} (hx : |x - R| ≤ A) (hd : |d| ≤ b) :
    |x * (1 + d) - R| ≤ A + (|R| + A) * b := by
  have hA := (abs_nonneg _).trans hx
  have hxabs : |x| ≤ |R| + A := by
    have := abs_sub_abs_le_abs_sub x R
    linarith
  have hsplit : x * (1 + d) - R = (x - R) + x * d := by ring
  calc |x * (1 + d) - R| ≤ |x - R| + |x * d| := by rw [hsplit]; exact abs_add_le _ _
    _ = |x - R| + |x| * |d| := by rw [abs_mul]
    _ ≤ A + (|R| + A) * b := by gcongr

/-- The exponential of a value within `A` of its reference `R` is within `exp R * (exp A - 1)`
of `exp R`. -/
theorem deviation_exp (hx : |x - R| ≤ A) :
    |Real.exp x - Real.exp R| ≤ Real.exp R * (Real.exp A - 1) := by
  have hstep : ∀ t : ℝ, |Real.exp t - 1| ≤ Real.exp |t| - 1 := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht, abs_of_nonneg (by linarith [Real.add_one_le_exp t])]
    · have hle : Real.exp t - 1 ≤ 0 := by linarith [Real.exp_le_one_iff.mpr ht]
      rw [abs_of_nonpos ht, abs_of_nonpos hle]
      linarith [Real.add_one_le_exp t, Real.add_one_le_exp (-t)]
  have hfactor : Real.exp x - Real.exp R = Real.exp R * (Real.exp (x - R) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add, add_sub_cancel]
  rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos R)]
  exact mul_le_mul_of_nonneg_left
    ((hstep _).trans (sub_le_sub_right (Real.exp_le_exp.mpr hx) 1)) (Real.exp_pos R).le

/-- The logarithm of a value within `A` of its reference `R`, where `A` is below `R`, is within
`A / (R - A)` of `log R`. -/
theorem deviation_log (hx : |x - R| ≤ A) (hR : A < R) :
    |Real.log x - Real.log R| ≤ A / (R - A) := by
  have hA := (abs_nonneg _).trans hx
  have hgap : 0 < R - A := sub_pos.mpr hR
  have hxlow : R - A ≤ x := by linarith [(abs_le.mp hx).1]
  have key := log_error (lt_of_lt_of_le hgap hxlow) (lt_of_le_of_lt hA hR) hx
    (show |Real.log x - Real.log x| ≤ 0 by simp)
  exact (key.trans_eq (add_zero _)).trans
    (div_le_div_of_nonneg_left hA hgap (le_min hxlow (by linarith)))

/-- A quotient of two values within `A` and `B` of their references, where `B` is below the
magnitude of the divisor `y`, in terms of the values. -/
theorem div_of_lt {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ B) (hpos : B < |y|) :
    |x / y - R / S| ≤ (A * |y| + |x| * B) / (|y| * (|y| - B)) := by
  rw [abs_sub_comm]
  exact deviation_div (by rwa [abs_sub_comm]) (by rwa [abs_sub_comm]) hpos

/-- The exponential of a value within `A` of its reference, in terms of the value. -/
theorem exp (hx : |x - R| ≤ A) :
    |Real.exp x - Real.exp R| ≤ Real.exp x * (Real.exp A - 1) := by
  rw [abs_sub_comm]
  exact deviation_exp (by rwa [abs_sub_comm])

/-- The logarithm of a value within `A` of its reference, where `A` is below the value. -/
theorem log (hx : |x - R| ≤ A) (hpos : A < x) : |Real.log x - Real.log R| ≤ A / (x - A) := by
  rw [abs_sub_comm]
  exact deviation_log (by rwa [abs_sub_comm]) hpos

/-- The logarithm of a value equal to its reference. -/
theorem log_exact (hx : |x - R| ≤ 0) : |Real.log x - Real.log R| ≤ 0 := by
  rw [eq_of_abs_sub_nonpos hx]
  simp

/-- A value within `A` of a reference that is within `B` of the exact value is within `B + A`
of the exact value: a backward statement and a bound on what its perturbations change give a
forward bound. -/
theorem forward {E : ℝ} (hx : |x - R| ≤ A) (hR : |R - E| ≤ B) : |x - E| ≤ B + A :=
  compose_error hx hR

/-- A quotient of a value within `A` of its reference by a value `y` equal to its reference is
within `A / |y|` of the quotient of the references. -/
theorem div {y S : ℝ} (hx : |x - R| ≤ A) (hy : |y - S| ≤ 0) : |x / y - R / S| ≤ A / |y| := by
  rw [← eq_of_abs_sub_nonpos hy, ← sub_div, abs_div]
  exact div_le_div_of_nonneg_right hx (abs_nonneg y)

/-- One rounded operation. The computed `x` has the mixed error `(r, a)` against the exact
operation `X` on the computed operands, `X` is within `A` of the reference `R`, and `R` takes
the factor of the rounding: then `x` is within `A * (1 + r) + a` of the scaled reference. -/
theorem round (hloc : MixedError x X r a) (hX : |X - R| ≤ A)
    (hscale : R * MixedError.factor x X r a = R') : |x - R'| ≤ A * (1 + r) + a := by
  have hA := (abs_nonneg _).trans hX
  have hc : |MixedError.factor x X r a| ≤ 1 + r :=
    abs_le_of_abs_sub_one_le (abs_sub_one_le_growth hloc.abs_factor_sub_one_le)
  have hsplit : x - R' = (X - R) * MixedError.factor x X r a + MixedError.offset x X r a := by
    rw [← hscale]
    nth_rewrite 1 [hloc.eq_mul_factor_add_offset]
    ring
  calc |x - R'| ≤ |(X - R) * MixedError.factor x X r a| + |MixedError.offset x X r a| := by
        rw [hsplit]; exact abs_add_le _ _
    _ = |X - R| * |MixedError.factor x X r a| + |MixedError.offset x X r a| := by rw [abs_mul]
    _ ≤ A * (1 + r) + a := by
        gcongr
        exact hloc.abs_offset_le

/-- One operation with an absolute error only, such as a rounding to an integer: no factor moves,
and the absolute error is added. -/
theorem offset (hloc : MixedError x X 0 a) (hX : |X - R| ≤ A) : |x - R| ≤ A + a := by
  have hb := hloc.bound
  rw [zero_mul, zero_add] at hb
  calc |x - R| ≤ |x - X| + |X - R| := abs_sub_le x X R
    _ ≤ A + a := by linarith

/-- An exact operation keeps the bound of its exact value. -/
theorem exact (hloc : MixedError x X 0 0) (hX : |X - R| ≤ A) : |x - R| ≤ A := by
  rwa [mixedError_zero_zero_iff.mp hloc]

/-- The zero perturbation is within the bound of a growth of one. A loop step that perturbs no
entry is given this perturbation, so that the loop rule applies to it. -/
theorem abs_zero_le : |(0 : ℝ)| ≤ 1 - 1 := by
  simp

/-- The budget of a bound is nonnegative. -/
theorem budget_nonneg (hx : |x - R| ≤ A) : 0 ≤ A :=
  (abs_nonneg _).trans hx

/-- A bound against a reference holds against an equal reference. -/
theorem restate (hx : |x - R| ≤ A) (hR : R = R') : |x - R'| ≤ A :=
  hR ▸ hx

/-- An equality is a bound by zero. -/
theorem of_eq (h : x = R) : |x - R| ≤ 0 := by simp [h]

/-- A difference of two values of a step that is affine in its accumulator, with slope `μ`. -/
theorem abs_sub_le_of_eq_mul {D μ s s' : ℝ} (h : D = μ * (s - s')) : |D| ≤ |μ| * |s - s'| := by
  rw [h, abs_mul]

/-- A difference of two values of a step that adds to its accumulator. -/
theorem abs_sub_le_of_eq {D s s' : ℝ} (h : D = s - s') : |D| ≤ 1 * |s - s'| := by
  rw [h, one_mul]

/-- A difference of two values of a step that is affine in its accumulator, with a slope `μ`
of magnitude at most `L`. -/
theorem abs_sub_le_of_eq_mul_le {D μ s s' L : ℝ} (h : D = μ * (s - s')) (hμ : |μ| ≤ L) :
    |D| ≤ L * |s - s'| := by
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_right hμ (abs_nonneg _)

/-- The perturbation of an entry before any later step: it took `g * q ^ 0`. -/
theorem slot_start (hd : |d| ≤ g - 1) (q : ℝ) : |d| ≤ g * q ^ 0 - 1 := by
  rwa [pow_zero, mul_one]

/-- The bound of a perturbation before any later step is its own bound. -/
theorem slot_stop {q : ℝ} (hd : |d| ≤ g * q ^ 0 - 1) : |d| ≤ g - 1 := by
  rwa [pow_zero, mul_one] at hd

/-- A perturbed read is at most the read times the growth of its perturbation. -/
theorem abs_perturbed_le (v : ℝ) (hd : |d| ≤ g - 1) : |v * (1 + d)| ≤ |v| * g := by
  rw [abs_mul]
  obtain ⟨hlow, hhigh⟩ := abs_le.mp hd
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_nonneg v)

/-- A negation has the bound of its operand. -/
theorem abs_neg_le {x A : ℝ} (hx : |x| ≤ A) : |-x| ≤ A := by
  rwa [abs_neg]

/-- A quotient is at most the bound of its numerator over the magnitude of its divisor. -/
theorem abs_div_le {x A : ℝ} (y : ℝ) (hx : |x| ≤ A) : |x / y| ≤ A / |y| := by
  rw [abs_div]
  gcongr

/-- A maximum is at most the larger bound of its operands. -/
theorem abs_max_le {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) : |max x y| ≤ max A B := by
  obtain ⟨hxlow, hxhigh⟩ := abs_le.mp hx
  obtain ⟨_, hyhigh⟩ := abs_le.mp hy
  exact abs_le.mpr ⟨((neg_le_neg (le_max_left A B)).trans hxlow).trans (le_max_left x y),
    max_le_max hxhigh hyhigh⟩

/-- A minimum is at most the larger bound of its operands. -/
theorem abs_min_le {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) : |min x y| ≤ max A B := by
  obtain ⟨hxlow, hxhigh⟩ := abs_le.mp hx
  obtain ⟨hylow, _⟩ := abs_le.mp hy
  exact abs_le.mpr ⟨le_min ((neg_le_neg (le_max_left A B)).trans hxlow)
    ((neg_le_neg (le_max_right A B)).trans hylow),
    (min_le_left x y).trans (hxhigh.trans (le_max_left A B))⟩

/-- A branch is at most the branch of the bounds of its alternatives. -/
theorem abs_ite_le {p : Prop} [Decidable p] {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |if p then x else y| ≤ if p then A else B := by
  split <;> assumption

/-- A square root is at most the square root of a bound of its argument. -/
theorem abs_sqrt_le {x A : ℝ} (hx : |x| ≤ A) : |√x| ≤ √A := by
  rw [abs_of_nonneg (Real.sqrt_nonneg x)]
  exact Real.sqrt_le_sqrt ((le_abs_self x).trans hx)

end Backward

end

end FloatLib.Numerics

namespace List

open FloatLib.Numerics

variable {α β P : Type*}

/-- One iteration of a loop beside the absolute error of its backward analysis: a step with
slope `L value` in its accumulator multiplies the incoming error by `L value * q`, where `q`
bounds the factor the accumulator takes, and adds its own `a state value`. -/
def backwardFoldStep (step : α → β → α) (L : β → ℝ) (q : ℝ) (a : α → β → ℝ) (state : α × ℝ)
    (value : β) : α × ℝ :=
  (step state.1 value, L value * (q * state.2) + a state.1 value)

/-- The absolute error that the backward analysis of a loop accumulates in the loop's own order:
zero before the first step, then `L v * (q * error) + a state v` at each step. -/
def foldBackwardAbsolute (step : α → β → α) (L : β → ℝ) (q : ℝ) (a : α → β → ℝ) (initial : α)
    (input : List β) : ℝ :=
  (input.foldl (backwardFoldStep step L q a) (initial, 0)).2

/-- The first component of the loop that `backwardFoldStep` runs is the loop itself. -/
theorem foldl_backwardFoldStep_fst (step : α → β → α) (L : β → ℝ) (q : ℝ) (a : α → β → ℝ)
    (initial : α) (budget : ℝ) (input : List β) :
    (input.foldl (backwardFoldStep step L q a) (initial, budget)).1 = input.foldl step initial := by
  induction input generalizing initial budget with
  | nil => rfl
  | cons value _ ih => exact ih _ _

/-- A loop without steps accumulates no absolute error. -/
@[simp]
theorem foldBackwardAbsolute_nil (step : α → β → α) (L : β → ℝ) (q : ℝ) (a : α → β → ℝ)
    (initial : α) : foldBackwardAbsolute step L q a initial [] = 0 :=
  rfl

/-- The accumulated absolute error after one more step. -/
theorem foldBackwardAbsolute_append_singleton (step : α → β → α) (L : β → ℝ) (q : ℝ)
    (a : α → β → ℝ) (initial : α) (input : List β) (value : β) :
    foldBackwardAbsolute step L q a initial (input ++ [value]) =
      L value * (q * foldBackwardAbsolute step L q a initial input) +
        a (input.foldl step initial) value := by
  unfold foldBackwardAbsolute
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [backwardFoldStep, foldl_backwardFoldStep_fst]

/-- **The accumulated absolute error in closed form.** When every slope is at most `ℓ` and every
step adds at most `c`, the error after `n` steps is at most `c * ∑ k < n, (ℓ * q) ^ k`. The
signs of `q`, the slopes and the step errors are needed at the visited states only (`hfacts`). -/
theorem foldBackwardAbsolute_le_geom (step : α → β → α) (L : β → ℝ) (q ℓ c : ℝ)
    (a : α → β → ℝ) (condition : α → β → Prop)
    (hfacts : ∀ s v, condition s v → 0 ≤ q ∧ 0 ≤ L v ∧ 0 ≤ a s v) (hℓ : ∀ v, L v ≤ ℓ)
    (hc : ∀ s v, a s v ≤ c) (initial : α) (input : List β)
    (hvalid : AllSteps step condition initial input) :
    foldBackwardAbsolute step L q a initial input ≤
      c * ∑ k ∈ Finset.range input.length, (ℓ * q) ^ k := by
  suffices h : 0 ≤ foldBackwardAbsolute step L q a initial input ∧
      foldBackwardAbsolute step L q a initial input ≤
        c * ∑ k ∈ Finset.range input.length, (ℓ * q) ^ k from h.2
  induction input using List.reverseRecOn with
  | nil => simp
  | append_singleton rest value ih =>
    rw [allSteps_append_singleton] at hvalid
    obtain ⟨hnonneg, hle⟩ := ih hvalid.1
    obtain ⟨hq, hLv, hav⟩ := hfacts _ _ hvalid.2
    rw [foldBackwardAbsolute_append_singleton, List.length_append, List.length_singleton,
      Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum]
    have hℓ0 : 0 ≤ ℓ := hLv.trans (hℓ value)
    refine ⟨add_nonneg (mul_nonneg hLv (mul_nonneg hq hnonneg)) hav, add_le_add ?_ (hc _ _)⟩
    calc L value * (q * foldBackwardAbsolute step L q a initial rest)
        ≤ ℓ * (q * (c * ∑ k ∈ Finset.range rest.length, (ℓ * q) ^ k)) :=
          mul_le_mul (hℓ value) (mul_le_mul_of_nonneg_left hle hq) (mul_nonneg hq hnonneg) hℓ0
      _ = ∑ k ∈ Finset.range rest.length, c * (ℓ * q) ^ (k + 1) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring

/-- **A backward statement gives a forward bound.** Two loops whose steps differ by at most
`D v` at one accumulator, the second with slope at most `L v` in its accumulator, differ by at
most the loop `e ↦ e * L v + D v` of accumulated differences, from a bound `e` on the distance
of their starts. With the exact step for the second loop and the step on perturbed entries for
the first, `D v` is what the perturbations of one step change. -/
theorem abs_foldl_sub_foldl_le (input : List β) (F F₀ : ℝ → β → ℝ) (L D : β → ℝ)
    (hL0 : ∀ v, 0 ≤ L v) (hL : ∀ s s' v, |F₀ s v - F₀ s' v| ≤ L v * |s - s'|)
    (hD : ∀ v ∈ input, ∀ s, |F s v - F₀ s v| ≤ D v) {a b e : ℝ} (he : |a - b| ≤ e) :
    |input.foldl F a - input.foldl F₀ b| ≤ input.foldl (fun e v => e * L v + D v) e := by
  induction input generalizing a b e with
  | nil => exact he
  | cons v rest ih =>
    have hstep : |F a v - F₀ b v| ≤ e * L v + D v := by
      have h1 := hD v (by simp) a
      have h2 : |F₀ a v - F₀ b v| ≤ |a - b| * L v := by
        rw [mul_comm]
        exact hL a b v
      have h3 := mul_le_mul_of_nonneg_right he (hL0 v)
      have := abs_sub_le (F a v) (F₀ a v) (F₀ b v)
      linarith
    simp only [List.foldl_cons]
    exact ih (fun w hw => hD w (by simp [hw])) hstep

/-- Two loops `s ↦ s * m v + t v` with the same multipliers, whose terms differ by at most
`c v`, differ by at most the loop `e ↦ e * |m v| + c v` from the distance of their starts. With
`t v = t₀ v * (1 + δ v)` and `|δ v| ≤ b v` the terms differ by at most `b v * |t₀ v|`: this is
the forward bound of a sum (`m v = 1`) or of Horner's rule (`m v = x`) from its backward
statement. -/
theorem abs_foldl_affine_sub_le (input : List β) (m t t₀ c : β → ℝ)
    (h : ∀ v ∈ input, |t v - t₀ v| ≤ c v) (a b : ℝ) :
    |input.foldl (fun s v => s * m v + t v) a - input.foldl (fun s v => s * m v + t₀ v) b| ≤
      input.foldl (fun e v => e * |m v| + c v) |a - b| :=
  abs_foldl_sub_foldl_le input (fun s v => s * m v + t v) (fun s v => s * m v + t₀ v)
    (fun v => |m v|) c (fun v => abs_nonneg _)
    (fun s s' v => by
      rw [show s * m v + t₀ v - (s' * m v + t₀ v) = m v * (s - s') by ring, abs_mul])
    (fun v hv s => by
      rw [show s * m v + t v - (s * m v + t₀ v) = t v - t₀ v by ring]
      exact h v hv) le_rfl

/-- `abs_foldl_sub_foldl_le` for a loop over the indices of `Fin n`. -/
theorem abs_foldl_finRange_sub_le {n : ℕ} (F F₀ : ℝ → Fin n → ℝ) (L D : Fin n → ℝ)
    (hL0 : ∀ j, 0 ≤ L j) (hL : ∀ s s' j, |F₀ s j - F₀ s' j| ≤ L j * |s - s'|)
    (hD : ∀ j s, |F s j - F₀ s j| ≤ D j) {a b e : ℝ} (he : |a - b| ≤ e) :
    |(List.finRange n).foldl F a - (List.finRange n).foldl F₀ b| ≤
      (List.finRange n).foldl (fun e j => e * L j + D j) e :=
  abs_foldl_sub_foldl_le (List.finRange n) F F₀ L D hL0 hL (fun j _ s => hD j s) he

/-- The loop of accumulated differences of a step with slope one over `Fin n` is a sum. -/
theorem foldl_finRange_add_eq_sum {n : ℕ} (D : Fin n → ℝ) (e : ℝ) :
    (List.finRange n).foldl (fun e j => e * 1 + D j) e = e + ∑ j, D j := by
  rw [Fin.sum_univ_def]
  generalize List.finRange n = l
  induction l generalizing e with
  | nil => simp
  | cons j rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    ring

/-- A loop over a list is the loop over its positions. -/
private theorem foldl_eq_foldl_finRange (input : List β) (F₀ : ℝ → β → ℝ) (b : ℝ) :
    input.foldl F₀ b = (List.finRange input.length).foldl (fun s k => F₀ s input[k.1]) b := by
  conv_lhs => rw [← List.map_getElem_finRange input, List.foldl_map]

/-- A loop over a list beside as many perturbations is the loop over the positions. -/
private theorem foldl_zip_eq_foldl_finRange (input : List β) (ps : List P)
    (hlen : ps.length = input.length) (F : ℝ → β × P → ℝ) (a : ℝ) :
    (input.zip ps).foldl F a = (List.finRange input.length).foldl
      (fun s k => F s (input[k.1], ps[k.1]'(by rw [hlen]; exact k.2))) a := by
  have hzip : input.zip ps = (List.finRange input.length).map
      fun k => (input[k.1], ps[k.1]'(by rw [hlen]; exact k.2)) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i h₁ h₂
      simp
  rw [hzip, List.foldl_map]

/-- `abs_foldl_sub_foldl_le` for a loop over a list beside its perturbations against the exact
loop over the list: the differences are accumulated over the positions. -/
theorem abs_foldl_zip_sub_foldl_le (input : List β) (ps : List P) (G : ℝ → β → P → ℝ)
    (F₀ : ℝ → β → ℝ) (L D : Fin input.length → ℝ) (hlen : ps.length = input.length)
    (hL0 : ∀ k, 0 ≤ L k)
    (hL : ∀ s s' (k : Fin input.length), |F₀ s input[k.1] - F₀ s' input[k.1]| ≤ L k * |s - s'|)
    (hD : ∀ (k : Fin input.length) s,
      |G s input[k.1] (ps[k.1]'(by rw [hlen]; exact k.2)) - F₀ s input[k.1]| ≤ D k)
    {a b e : ℝ} (he : |a - b| ≤ e) :
    |(input.zip ps).foldl (fun s vp => G s vp.1 vp.2) a - input.foldl F₀ b| ≤
      (List.finRange input.length).foldl (fun e k => e * L k + D k) e := by
  rw [foldl_zip_eq_foldl_finRange input ps hlen, foldl_eq_foldl_finRange input F₀ b]
  exact abs_foldl_sub_foldl_le (List.finRange input.length) _ _ L D hL0 hL (fun k _ s => hD k s) he

/-- Two sums whose terms differ by at most `c v` differ by at most the sum of the `c v`: the
forward bound `∑ b v * |t₀ v|` of a sum of terms `t₀ v * (1 + δ v)` with `|δ v| ≤ b v`. -/
theorem abs_foldl_add_sub_le (input : List β) (t t₀ c : β → ℝ)
    (h : ∀ v ∈ input, |t v - t₀ v| ≤ c v) :
    |input.foldl (fun s v => s + t v) 0 - input.foldl (fun s v => s + t₀ v) 0| ≤
      (input.map c).sum := by
  have key := abs_foldl_affine_sub_le input (fun _ => 1) t t₀ c h 0 0
  simp only [mul_one, abs_one, sub_self, abs_zero] at key
  rwa [List.sum_eq_foldl, List.foldl_map]

/-- The relative form: a sum of terms within `γ * t₀ v` of the terms `t₀ v`, which are then
nonnegative when `γ` is positive, is within `γ` times the exact sum. A sum without cancellation
whose backward perturbations are at most `γ` has the relative error `γ`. -/
theorem abs_foldl_add_sub_le_mul (input : List β) (t t₀ : β → ℝ) (γ : ℝ)
    (h : ∀ v ∈ input, |t v - t₀ v| ≤ γ * t₀ v) :
    |input.foldl (fun s v => s + t v) 0 - input.foldl (fun s v => s + t₀ v) 0| ≤
      γ * input.foldl (fun s v => s + t₀ v) 0 := by
  have key := abs_foldl_add_sub_le input t t₀ (fun v => γ * t₀ v) h
  rwa [List.sum_map_mul_left, List.sum_eq_foldl, List.foldl_map] at key

/-- Scaling the start of a perturbed loop is the same as scaling its perturbations, when one
step has this property for the factor `c`. -/
theorem foldl_zip_scale (G : ℝ → β → P → ℝ) (scale : ℝ → P → P) (c : ℝ)
    (hG : ∀ s v p, G (s * c) v (scale c p) = G s v p * c) (input : List β) (ps : List P)
    (s : ℝ) :
    (input.zip (ps.map (scale c))).foldl (fun s vp => G s vp.1 vp.2) (s * c) =
      (input.zip ps).foldl (fun s vp => G s vp.1 vp.2) s * c := by
  induction input generalizing ps s with
  | nil => simp
  | cons v rest ih =>
    cases ps with
    | nil => simp
    | cons p ps =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons]
      rw [hG]
      exact ih _ _

/-- The core of the loop rules, for a closeness relation `near budget computed reference` that
one step preserves (`hnear`): an absolute bound for `fold_backward`, equality for
`fold_backward_exact`. One step computes `G (observe s * ρ) v p` up to the step fact `S`, for a
factor `ρ` within `q - 1` of one and a perturbation `p` of the entry. Then the loop is near the
exact loop of `G` on perturbed entries, started at `observe initial * (1 + δ₀)`. The perturbation
at position `k` of `n` satisfies `B (n - 1 - k)`, after the scalings of the later steps. -/
theorem fold_backward_core (observe : α → ℝ) (step : α → β → α) (G : ℝ → β → P → ℝ)
    (scale : ℝ → P → P) (q : ℝ) (L : β → ℝ) (B : ℕ → β → P → Prop) (a : α → β → ℝ)
    (condition : α → β → Prop) (S : α → β → ℝ → P → Prop) (near : ℝ → ℝ → ℝ → Prop)
    (hG : ∀ c, |c - 1| ≤ q - 1 → ∀ s v p, G (s * c) v (scale c p) = G s v p * c)
    (hB : ∀ m v p c, B m v p → |c - 1| ≤ q - 1 → B (m + 1) v (scale c p))
    (hstep : ∀ s v, condition s v → ∃ ρ p, |ρ - 1| ≤ q - 1 ∧ B 0 v p ∧ S s v ρ p)
    (hnear₀ : ∀ x, near 0 x x)
    (hnear : ∀ s v ρ p y budget, |ρ - 1| ≤ q - 1 → S s v ρ p → near budget (observe s) y →
      near (L v * (q * budget) + a s v) (observe (step s v)) (G (y * ρ) v p))
    (initial : α) (input : List β) (hvalid : AllSteps step condition initial input) :
    ∃ δ₀ : ℝ, |δ₀| ≤ q ^ input.length - 1 ∧ ∃ ps : List P, ps.length = input.length ∧
      (∀ (k : ℕ) (hk : k < input.length) (hp : k < ps.length),
        B (input.length - 1 - k) input[k] ps[k]) ∧
      near (foldBackwardAbsolute step L q a initial input) (observe (input.foldl step initial))
        ((input.zip ps).foldl (fun s vp => G s vp.1 vp.2) (observe initial * (1 + δ₀))) := by
  induction input using List.reverseRecOn with
  | nil =>
    refine ⟨0, by simp, [], rfl, fun k hk => absurd hk (by simp), ?_⟩
    simpa using hnear₀ (observe initial)
  | append_singleton rest value ih =>
    rw [allSteps_append_singleton] at hvalid
    obtain ⟨δ₀, hδ₀, ps, hlength, hbounds, hmain⟩ := ih hvalid.1
    obtain ⟨ρ, p, hρ, hp, hS⟩ := hstep _ _ hvalid.2
    refine ⟨(1 + δ₀) * ρ - 1, ?_, ps.map (scale ρ) ++ [p], by simp [hlength], ?_, ?_⟩
    · rw [List.length_append, List.length_singleton, pow_succ]
      exact Backward.abs_delta_scale hδ₀ hρ
    · intro k hk hpk
      rw [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · have hpl : k < ps.length := hlength ▸ hlt
        rw [List.getElem_append_left hlt,
          List.getElem_append_left (by simpa using hpl), List.getElem_map,
          show (rest ++ [value]).length - 1 - k = rest.length - 1 - k + 1 by
            rw [List.length_append, List.length_singleton]; omega]
        exact hB _ _ _ _ (hbounds k hlt hpl) hρ
      · subst heq
        have hpl : (ps.map (scale ρ)).length = rest.length := by simp [hlength]
        rw [List.getElem_append_right (le_refl _),
          List.getElem_append_right (by rw [hpl]),
          show (rest ++ [value]).length - 1 - rest.length = 0 by
            rw [List.length_append, List.length_singleton]; omega]
        simpa [hpl] using hp
    · rw [foldBackwardAbsolute_append_singleton, List.foldl_append, List.foldl_cons,
        List.foldl_nil, List.zip_append (by simp [hlength]), List.foldl_append,
        List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil,
        show observe initial * (1 + ((1 + δ₀) * ρ - 1)) = observe initial * (1 + δ₀) * ρ by ring,
        foldl_zip_scale G scale ρ (hG ρ hρ)]
      exact hnear _ _ _ _ _ _ hρ hS hmain

/-- **The loop rule of backward error.** One step computes `G (observe s * ρ) v p` up to
`a s v`: the exact step `G` on the accumulator scaled by a factor `ρ` within `q - 1` of one and
on the entry perturbed by `p`. Scaling the accumulator by `c` is the same as scaling the
perturbation (`hG`), and `G` has slope at most `L v` in its accumulator at each perturbation that
a step may take (`hL`). Then the loop is within `foldBackwardAbsolute` of the exact loop of `G`
on perturbed entries, started at `observe initial * (1 + δ₀)` with `|δ₀| ≤ q ^ n - 1`. The
perturbation at position `k` of `n` satisfies `B (n - 1 - k)`. The condition is required at the
visited states only. -/
theorem fold_backward (observe : α → ℝ) (step : α → β → α) (G : ℝ → β → P → ℝ)
    (scale : ℝ → P → P) (q : ℝ) (L : β → ℝ) (B : ℕ → β → P → Prop) (a : α → β → ℝ)
    (condition : α → β → Prop)
    (hG : ∀ c, |c - 1| ≤ q - 1 → ∀ s v p, G (s * c) v (scale c p) = G s v p * c)
    (hL : ∀ s s' v p, B 0 v p → |G s v p - G s' v p| ≤ L v * |s - s'|)
    (hB : ∀ m v p c, B m v p → |c - 1| ≤ q - 1 → B (m + 1) v (scale c p))
    (hstep : ∀ s v, condition s v → ∃ ρ p, |ρ - 1| ≤ q - 1 ∧ B 0 v p ∧
      |observe (step s v) - G (observe s * ρ) v p| ≤ a s v)
    (initial : α) (input : List β) (hvalid : AllSteps step condition initial input) :
    ∃ δ₀ : ℝ, |δ₀| ≤ q ^ input.length - 1 ∧ ∃ ps : List P, ps.length = input.length ∧
      (∀ (k : ℕ) (hk : k < input.length) (hp : k < ps.length),
        B (input.length - 1 - k) input[k] ps[k]) ∧
      |observe (input.foldl step initial) -
          (input.zip ps).foldl (fun s vp => G s vp.1 vp.2) (observe initial * (1 + δ₀))| ≤
        foldBackwardAbsolute step L q a initial input := by
  refine fold_backward_core observe step G scale q L B a condition
    (fun s v ρ p => B 0 v p ∧ |observe (step s v) - G (observe s * ρ) v p| ≤ a s v)
    (fun budget x y => |x - y| ≤ budget) hG hB
    (fun s v hc => by
      obtain ⟨ρ, p, hρ, hp, hs⟩ := hstep s v hc
      exact ⟨ρ, p, hρ, hp, hp, hs⟩)
    (fun x => by simp) ?_ initial input hvalid
  intro s v ρ p y budget hρ hS hy
  obtain ⟨hp, hS⟩ := hS
  have hbudget := (abs_nonneg _).trans hy
  have hLv : 0 ≤ L v := by simpa using (abs_nonneg _).trans (hL 1 0 v p hp)
  have hρq : |ρ| ≤ q := Backward.abs_le_of_abs_sub_one_le hρ
  have hslope : |G (observe s * ρ) v p - G (y * ρ) v p| ≤ L v * (q * budget) := by
    refine (hL _ _ v p hp).trans (mul_le_mul_of_nonneg_left ?_ hLv)
    rw [← sub_mul, abs_mul, mul_comm q]
    gcongr
  calc |observe (step s v) - G (y * ρ) v p|
      ≤ |observe (step s v) - G (observe s * ρ) v p| +
          |G (observe s * ρ) v p - G (y * ρ) v p| := abs_sub_le _ _ _
    _ ≤ L v * (q * budget) + a s v := by linarith

/-- **The loop rule of backward error without absolute error.** When one step computes
`G (observe s * ρ) v p` exactly, the loop equals the exact loop of `G` on perturbed entries. -/
theorem fold_backward_exact (observe : α → ℝ) (step : α → β → α) (G : ℝ → β → P → ℝ)
    (scale : ℝ → P → P) (q : ℝ) (B : ℕ → β → P → Prop) (condition : α → β → Prop)
    (hG : ∀ c, |c - 1| ≤ q - 1 → ∀ s v p, G (s * c) v (scale c p) = G s v p * c)
    (hB : ∀ m v p c, B m v p → |c - 1| ≤ q - 1 → B (m + 1) v (scale c p))
    (hstep : ∀ s v, condition s v → ∃ ρ p, |ρ - 1| ≤ q - 1 ∧ B 0 v p ∧
      observe (step s v) = G (observe s * ρ) v p)
    (initial : α) (input : List β) (hvalid : AllSteps step condition initial input) :
    ∃ δ₀ : ℝ, |δ₀| ≤ q ^ input.length - 1 ∧ ∃ ps : List P, ps.length = input.length ∧
      (∀ (k : ℕ) (hk : k < input.length) (hp : k < ps.length),
        B (input.length - 1 - k) input[k] ps[k]) ∧
      observe (input.foldl step initial) =
        (input.zip ps).foldl (fun s vp => G s vp.1 vp.2) (observe initial * (1 + δ₀)) := by
  refine fold_backward_core observe step G scale q (fun _ => 0) B (fun _ _ => 0) condition
    (fun s v ρ p => observe (step s v) = G (observe s * ρ) v p) (fun _ x y => x = y) hG hB hstep
    (fun _ => rfl) ?_ initial input hvalid
  intro s v ρ p y _ _ hS hy
  rw [hS, hy]

/-- The loop rule for an accumulator that takes no factor: one step computes
`G (observe s) v p` up to `a s v`. The loop is within `foldBackwardAbsolute` of the exact loop of
`G` on perturbed entries from `observe initial`, and each perturbation satisfies `B`. -/
theorem fold_backward_fixed (observe : α → ℝ) (step : α → β → α) (G : ℝ → β → P → ℝ)
    (L : β → ℝ) (B : β → P → Prop) (a : α → β → ℝ) (condition : α → β → Prop)
    (hL : ∀ s s' v p, B v p → |G s v p - G s' v p| ≤ L v * |s - s'|)
    (hstep : ∀ s v, condition s v → ∃ p, B v p ∧ |observe (step s v) - G (observe s) v p| ≤ a s v)
    (initial : α) (input : List β) (hvalid : AllSteps step condition initial input) :
    ∃ ps : List P, ps.length = input.length ∧
      (∀ (k : ℕ) (hk : k < input.length) (hp : k < ps.length), B input[k] ps[k]) ∧
      |observe (input.foldl step initial) -
          (input.zip ps).foldl (fun s vp => G s vp.1 vp.2) (observe initial)| ≤
        foldBackwardAbsolute step L 1 a initial input := by
  have hone : ∀ c : ℝ, |c - 1| ≤ 1 - 1 → c = 1 := fun c hc =>
    sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using hc))
  obtain ⟨δ₀, hδ₀, ps, hlength, hbounds, hmain⟩ := fold_backward observe step G (fun _ p => p) 1 L
    (fun _ => B) a condition (fun c hc s v p => by rw [hone c hc, mul_one, mul_one]) hL
    (fun _ _ _ _ hp _ => hp)
    (fun s v hc => by
      obtain ⟨p, hp, hs⟩ := hstep s v hc
      exact ⟨1, p, by simp, hp, by simpa using hs⟩) initial input hvalid
  have hzero : δ₀ = 0 := abs_nonpos_iff.mp (by simpa using hδ₀)
  rw [hzero, add_zero, mul_one] at hmain
  exact ⟨ps, hlength, hbounds, hmain⟩

/-- The loop rule for an accumulator that takes no factor, without absolute error. -/
theorem fold_backward_fixed_exact (observe : α → ℝ) (step : α → β → α) (G : ℝ → β → P → ℝ)
    (B : β → P → Prop) (condition : α → β → Prop)
    (hstep : ∀ s v, condition s v → ∃ p, B v p ∧ observe (step s v) = G (observe s) v p)
    (initial : α) (input : List β) (hvalid : AllSteps step condition initial input) :
    ∃ ps : List P, ps.length = input.length ∧
      (∀ (k : ℕ) (hk : k < input.length) (hp : k < ps.length), B input[k] ps[k]) ∧
      observe (input.foldl step initial) =
        (input.zip ps).foldl (fun s vp => G s vp.1 vp.2) (observe initial) := by
  have hone : ∀ c : ℝ, |c - 1| ≤ 1 - 1 → c = 1 := fun c hc =>
    sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using hc))
  obtain ⟨δ₀, hδ₀, ps, hlength, hbounds, hmain⟩ := fold_backward_exact observe step G
    (fun _ p => p) 1 (fun _ => B) condition
    (fun c hc s v p => by rw [hone c hc, mul_one, mul_one]) (fun _ _ _ _ hp _ => hp)
    (fun s v hc => by
      obtain ⟨p, hp, hs⟩ := hstep s v hc
      exact ⟨1, p, by simp, hp, by simpa using hs⟩) initial input hvalid
  have hzero : δ₀ = 0 := abs_nonpos_iff.mp (by simpa using hδ₀)
  rw [hzero, add_zero, mul_one] at hmain
  exact ⟨ps, hlength, hbounds, hmain⟩

/-- A list of perturbations of the indices of `Fin n` is a function on `Fin n`: the perturbed
loop over `List.finRange n` reads the perturbation of each index, and a bound at each position is
a bound at each index. -/
theorem exists_fin_of_zip_finRange {n : ℕ} (Q : ℕ → Fin n → P → Prop)
    (T : (ℝ → Fin n × P → ℝ) → List (Fin n × P) → Prop)
    (G : ℝ → Fin n → P → ℝ)
    (h : ∃ ps : List P, ps.length = (List.finRange n).length ∧
      (∀ (k : ℕ) (hk : k < (List.finRange n).length) (hp : k < ps.length),
        Q k (List.finRange n)[k] ps[k]) ∧
      T (fun s vp => G s vp.1 vp.2) ((List.finRange n).zip ps)) :
    ∃ p : Fin n → P, (∀ j : Fin n, Q j j (p j)) ∧
      T (fun s vp => G s vp.1 vp.2) ((List.finRange n).map fun j => (j, p j)) := by
  obtain ⟨ps, hlength, hbounds, hmain⟩ := h
  rw [List.length_finRange] at hlength
  refine ⟨fun j => ps[j.1]'(hlength ▸ j.2), fun j => ?_, ?_⟩
  · have := hbounds j.1 (by simp) (hlength ▸ j.2)
    simpa using this
  · have hzip : (List.finRange n).zip ps =
        (List.finRange n).map fun j => (j, ps[j.1]'(hlength ▸ j.2)) := by
      apply List.ext_getElem
      · simp [hlength]
      · intro k hk₁ hk₂
        simp
    rwa [hzip] at hmain

/-- `exists_fin_of_zip_finRange` for an absolute bound against a perturbed loop. -/
theorem exists_fin_of_zip_finRange_abs {n : ℕ} (Q : ℕ → Fin n → P → Prop)
    (G : ℝ → Fin n → P → ℝ) (x init A : ℝ)
    (h : ∃ ps : List P, ps.length = (List.finRange n).length ∧
      (∀ (k : ℕ) (hk : k < (List.finRange n).length) (hp : k < ps.length),
        Q k (List.finRange n)[k] ps[k]) ∧
      |x - ((List.finRange n).zip ps).foldl (fun s vp => G s vp.1 vp.2) init| ≤ A) :
    ∃ p : Fin n → P, (∀ j : Fin n, Q j j (p j)) ∧
      |x - (List.finRange n).foldl (fun s j => G s j (p j)) init| ≤ A := by
  obtain ⟨p, hp, hmain⟩ := exists_fin_of_zip_finRange Q (fun f l => |x - l.foldl f init| ≤ A) G h
  exact ⟨p, hp, by simpa [List.foldl_map] using hmain⟩

/-- `exists_fin_of_zip_finRange` for an equality with a perturbed loop. -/
theorem exists_fin_of_zip_finRange_eq {n : ℕ} (Q : ℕ → Fin n → P → Prop)
    (G : ℝ → Fin n → P → ℝ) (x init : ℝ)
    (h : ∃ ps : List P, ps.length = (List.finRange n).length ∧
      (∀ (k : ℕ) (hk : k < (List.finRange n).length) (hp : k < ps.length),
        Q k (List.finRange n)[k] ps[k]) ∧
      x = ((List.finRange n).zip ps).foldl (fun s vp => G s vp.1 vp.2) init) :
    ∃ p : Fin n → P, (∀ j : Fin n, Q j j (p j)) ∧
      x = (List.finRange n).foldl (fun s j => G s j (p j)) init := by
  obtain ⟨p, hp, hmain⟩ := exists_fin_of_zip_finRange Q (fun f l => x = l.foldl f init) G h
  exact ⟨p, hp, by simpa [List.foldl_map] using hmain⟩

/-- Scaling the start of a loop on perturbed entries is the same as scaling the perturbation of
each entry, when one step has this property for the factor `c`. -/
theorem foldl_scale (G : ℝ → β → P → ℝ) (scale : ℝ → P → P) (c : ℝ)
    (hG : ∀ s v p, G (s * c) v (scale c p) = G s v p * c) (p : β → P) (input : List β) (s : ℝ) :
    input.foldl (fun s v => G s v (scale c (p v))) (s * c) =
      input.foldl (fun s v => G s v (p v)) s * c := by
  induction input generalizing s with
  | nil => rfl
  | cons v rest ih =>
    simp only [List.foldl_cons]
    rw [hG]
    exact ih _

/-- `fold_backward` for a loop over the indices of `Fin n`: the perturbations are a function on
`Fin n`, and the one at index `j` satisfies `B (n - 1 - j)`. -/
theorem fold_backward_finRange {n : ℕ} (observe : α → ℝ) (step : α → Fin n → α)
    (G : ℝ → Fin n → P → ℝ) (scale : ℝ → P → P) (q : ℝ) (L : Fin n → ℝ)
    (B : ℕ → Fin n → P → Prop) (a : α → Fin n → ℝ) (condition : α → Fin n → Prop)
    (hG : ∀ c, |c - 1| ≤ q - 1 → ∀ s v p, G (s * c) v (scale c p) = G s v p * c)
    (hL : ∀ s s' v p, B 0 v p → |G s v p - G s' v p| ≤ L v * |s - s'|)
    (hB : ∀ m v p c, B m v p → |c - 1| ≤ q - 1 → B (m + 1) v (scale c p))
    (hstep : ∀ s v, condition s v → ∃ ρ p, |ρ - 1| ≤ q - 1 ∧ B 0 v p ∧
      |observe (step s v) - G (observe s * ρ) v p| ≤ a s v)
    (initial : α) (hvalid : AllSteps step condition initial (List.finRange n)) :
    ∃ δ₀ : ℝ, |δ₀| ≤ q ^ n - 1 ∧ ∃ p : Fin n → P, (∀ j : Fin n, B (n - 1 - j) j (p j)) ∧
      |observe ((List.finRange n).foldl step initial) -
          (List.finRange n).foldl (fun s j => G s j (p j)) (observe initial * (1 + δ₀))| ≤
        foldBackwardAbsolute step L q a initial (List.finRange n) := by
  obtain ⟨δ₀, hδ₀, h⟩ := fold_backward observe step G scale q L B a condition hG hL hB hstep
    initial (List.finRange n) hvalid
  rw [List.length_finRange] at hδ₀
  obtain ⟨p, hp, hmain⟩ := exists_fin_of_zip_finRange_abs
    (fun k v p => B ((List.finRange n).length - 1 - k) v p) G _ _ _ h
  exact ⟨δ₀, hδ₀, p, fun j => by simpa using hp j, hmain⟩

/-- `fold_backward_exact` for a loop over the indices of `Fin n`. -/
theorem fold_backward_exact_finRange {n : ℕ} (observe : α → ℝ) (step : α → Fin n → α)
    (G : ℝ → Fin n → P → ℝ) (scale : ℝ → P → P) (q : ℝ) (B : ℕ → Fin n → P → Prop)
    (condition : α → Fin n → Prop)
    (hG : ∀ c, |c - 1| ≤ q - 1 → ∀ s v p, G (s * c) v (scale c p) = G s v p * c)
    (hB : ∀ m v p c, B m v p → |c - 1| ≤ q - 1 → B (m + 1) v (scale c p))
    (hstep : ∀ s v, condition s v → ∃ ρ p, |ρ - 1| ≤ q - 1 ∧ B 0 v p ∧
      observe (step s v) = G (observe s * ρ) v p)
    (initial : α) (hvalid : AllSteps step condition initial (List.finRange n)) :
    ∃ δ₀ : ℝ, |δ₀| ≤ q ^ n - 1 ∧ ∃ p : Fin n → P, (∀ j : Fin n, B (n - 1 - j) j (p j)) ∧
      observe ((List.finRange n).foldl step initial) =
        (List.finRange n).foldl (fun s j => G s j (p j)) (observe initial * (1 + δ₀)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := fold_backward_exact observe step G scale q B condition hG hB hstep
    initial (List.finRange n) hvalid
  rw [List.length_finRange] at hδ₀
  obtain ⟨p, hp, hmain⟩ := exists_fin_of_zip_finRange_eq
    (fun k v p => B ((List.finRange n).length - 1 - k) v p) G _ _ h
  exact ⟨δ₀, hδ₀, p, fun j => by simpa using hp j, hmain⟩

/-- `fold_backward_fixed` for a loop over the indices of `Fin n`. -/
theorem fold_backward_fixed_finRange {n : ℕ} (observe : α → ℝ) (step : α → Fin n → α)
    (G : ℝ → Fin n → P → ℝ) (L : Fin n → ℝ) (B : Fin n → P → Prop) (a : α → Fin n → ℝ)
    (condition : α → Fin n → Prop)
    (hL : ∀ s s' v p, B v p → |G s v p - G s' v p| ≤ L v * |s - s'|)
    (hstep : ∀ s v, condition s v → ∃ p, B v p ∧ |observe (step s v) - G (observe s) v p| ≤ a s v)
    (initial : α) (hvalid : AllSteps step condition initial (List.finRange n)) :
    ∃ p : Fin n → P, (∀ j : Fin n, B j (p j)) ∧
      |observe ((List.finRange n).foldl step initial) -
          (List.finRange n).foldl (fun s j => G s j (p j)) (observe initial)| ≤
        foldBackwardAbsolute step L 1 a initial (List.finRange n) :=
  exists_fin_of_zip_finRange_abs (fun _ v p => B v p) G _ _ _
    (fold_backward_fixed observe step G L B a condition hL hstep initial (List.finRange n) hvalid)

/-- `fold_backward_fixed_exact` for a loop over the indices of `Fin n`. -/
theorem fold_backward_fixed_exact_finRange {n : ℕ} (observe : α → ℝ) (step : α → Fin n → α)
    (G : ℝ → Fin n → P → ℝ) (B : Fin n → P → Prop) (condition : α → Fin n → Prop)
    (hstep : ∀ s v, condition s v → ∃ p, B v p ∧ observe (step s v) = G (observe s) v p)
    (initial : α) (hvalid : AllSteps step condition initial (List.finRange n)) :
    ∃ p : Fin n → P, (∀ j : Fin n, B j (p j)) ∧
      observe ((List.finRange n).foldl step initial) =
        (List.finRange n).foldl (fun s j => G s j (p j)) (observe initial) :=
  exists_fin_of_zip_finRange_eq (fun _ v p => B v p) G _ _
    (fold_backward_fixed_exact observe step G B condition hstep initial (List.finRange n) hvalid)

end List
