/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.HalfUlp
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError

/-!
# Recursive summation and inner products with the constants `(n - 1) u` and `n u`

The classical bound of recursive summation of `n` values is `((1 + u) ^ (n - 1) - 1) * ∑ |x i|`,
or `γ (n - 1) * ∑ |x i|` with `γ k = k u / (1 - k u)` under the restriction `k u < 1`. Rump showed
that the linear constant alone holds, with no restriction on `n` and no term of second order,
and Jeannerod and Rump showed the same for inner products:

  `|fl (∑ x i) - ∑ x i| ≤ (n - 1) * u * ∑ |x i|`,
  `|fl (∑ x i * y i) - ∑ x i * y i| ≤ n * u * ∑ |x i * y i|` when no product underflows

(S. M. Rump, *Error estimation of floating-point summation and dot product*, BIT Numerical
Mathematics 52 (2012), 201–220; C.-P. Jeannerod and S. M. Rump, *Improved error bounds for inner
products in floating-point arithmetic*, SIAM J. Matrix Anal. Appl. 34 (2013), 338–344, and *On
relative errors of floating-point operations: optimal bounds and applications*, Mathematics of
Computation 87 (2018), 803–819, for the relative error `u / (1 + u)` of one rounding). The proof
uses two facts about a sum of two values of the format rounded to nearest: it errs by at most
the smaller operand, because each operand is itself a value of the format
(`Model.abs_toReal_add_sub_le_abs_right`), and by at most `u / (1 + u)` of the exact sum
(`Model.one_add_mul_abs_toReal_add_sub_le`).

* `Model.one_add_mul_abs_toReal_foldl_add_sub_le`: adding the `n` terms of a list to a seed in
  order has error at most `n * u / (1 + u) * (|seed| + ∑ |term i|)`.
* `Model.abs_toReal_foldl_add_sub_le`: from a seed of real value zero, the first addition is
  exact, and the error is at most `(n - 1) * u * ∑ |term i|`.
* `Model.abs_toReal_foldl_add_mul_sub_le`: the inner product loop `acc := acc + left i * right i`
  from such a seed has error at most `n * u * ∑ |left i * right i|` when no exact product is in
  the subnormal range.

They hold for every IEEE descriptor and every length, under the premise that the result is
finite, which makes every partial sum finite. They are stated like the other left-to-right sums
of `Analysis.MixedError`, over a list of indices. Addition has no underflow error, so no
absolute term appears in the first two. In a format of low precision the difference from
`(1 + u) ^ (n - 1) - 1` is large: with eight bits of precision and `n = 1024` the linear constant
is about 4 and the power about 54.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

variable {fmt : FloatFormat}

/-- The rounding error of a finite sum is at most the magnitude of its right operand: the sum is
rounded to a nearest value of the format, and the left operand is a value of the format at that
distance from the exact sum. -/
theorem abs_toReal_add_sub_le_abs_right (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true) :
    |toReal (add x y) - (toReal x + toReal y)| ≤ |toReal y| := by
  obtain ⟨hx, -⟩ := isFinite_of_isFinite_add hfmt hout
  rw [toReal_add_eq_roundAt x y hfmt hout]
  have h := abs_roundAt_sub_le_abs_sub fmt (toReal_genericFormat_of_isFinite x hx)
    (toReal x + toReal y)
  rwa [sub_add_cancel_left, abs_neg] at h

/-- A finite sum has relative error at most `u / (1 + u)`, with no underflow term: below the
normal range the exact sum of two values of the format is a value of the format. -/
theorem one_add_mul_abs_toReal_add_sub_le (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hout : isFinite (add x y) = true) :
    (1 + unitRoundoffAt fmt) * |toReal (add x y) - (toReal x + toReal y)| ≤
      unitRoundoffAt fmt * |toReal x + toReal y| := by
  by_cases hnormal : minNormalAt fmt ≤ |toReal x + toReal y|
  · rw [toReal_add_eq_roundAt x y hfmt hout]
    exact one_add_mul_abs_roundAt_sub_le fmt hnormal
  · obtain ⟨hx, hy⟩ := isFinite_of_isFinite_add hfmt hout
    have hsum := genericFormat_add_of_abs_lt_minNormalAt fmt
      (toReal_genericFormat_of_isFinite x hx) (toReal_genericFormat_of_isFinite y hy)
      (not_le.mp hnormal)
    rw [toReal_add_eq_roundAt x y hfmt hout,
      show roundAt fmt (toReal x + toReal y) = toReal x + toReal y from
        Flocq.round_preserves_generic Flocq.nearestEven _ hsum, sub_self, abs_zero, mul_zero]
    exact mul_nonneg (unitRoundoffAt_pos fmt).le (abs_nonneg _)

variable {ι : Type*} {l : List ι} {term left right : ι → Model fmt} {seed : Model fmt}

/-- Every prefix of a finite left-to-right sum has a finite sum. -/
private theorem isFinite_foldl_add_take (hfmt : fmt.isIEEE = true)
    (hsum : isFinite (l.foldl (fun acc i => add acc (term i)) seed) = true) (k : ℕ) :
    isFinite ((l.take k).foldl (fun acc i => add acc (term i)) seed) = true := by
  induction l generalizing seed k with
  | nil => simpa using hsum
  | cons i l ih =>
    cases k with
    | zero => exact isFinite_of_mem_scanl_add hfmt hsum (by simp [List.scanl_cons])
    | succ k => exact ih (by simpa using hsum) k

/-- Every term of a finite left-to-right sum is finite. -/
private theorem isFinite_term_of_isFinite_foldl_add (hfmt : fmt.isIEEE = true)
    (hsum : isFinite (l.foldl (fun acc i => add acc (term i)) seed) = true) :
    ∀ i ∈ l, isFinite (term i) = true := by
  induction l generalizing seed with
  | nil => simp
  | cons i l ih =>
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · have h := isFinite_foldl_add_take hfmt hsum 1
      exact (isFinite_of_isFinite_add hfmt (by simpa using h)).2
    · exact ih (by simpa using hsum) j hj

/-- A left-to-right sum onto a seed: adding the `n` terms of a list to `seed` in order has error
at most `n * u / (1 + u) * (|seed| + ∑ |term i|)` against the exact sum, when the result is
finite. The constant is linear in `n`, with no restriction on `n` (Rump 2012; Jeannerod and Rump
2013, 2018). -/
theorem one_add_mul_abs_toReal_foldl_add_sub_le (hfmt : fmt.isIEEE = true)
    (hsum : isFinite (l.foldl (fun acc i => add acc (term i)) seed) = true) :
    (1 + unitRoundoffAt fmt) * |toReal (l.foldl (fun acc i => add acc (term i)) seed) -
        (toReal seed + (l.map fun i => toReal (term i)).sum)| ≤
      l.length * unitRoundoffAt fmt *
        (|toReal seed| + (l.map fun i => |toReal (term i)|).sum) := by
  have hfin := isFinite_foldl_add_take hfmt hsum
  clear hsum
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton init x ih =>
    have hinit : ∀ k,
        isFinite ((init.take k).foldl (fun acc i => add acc (term i)) seed) = true := by
      intro k
      rcases le_total k init.length with hk | hk
      · simpa [List.take_append_of_le_length hk] using hfin k
      · rw [List.take_of_length_le hk]
        simpa [List.take_append_of_le_length le_rfl] using hfin init.length
    have hall :
        isFinite (add (init.foldl (fun acc i => add acc (term i)) seed) (term x)) = true := by
      have h := hfin (init.length + 1)
      rw [List.take_of_length_le (by simp)] at h
      simpa [List.foldl_append] using h
    have ih := ih hinit
    have hu := (unitRoundoffAt_pos fmt).le
    have h1 := one_add_mul_abs_toReal_add_sub_le _ (term x) hfmt hall
    have h2 := abs_toReal_add_sub_le_abs_right _ (term x) hfmt hall
    have hS : |toReal seed + (init.map fun i => toReal (term i)).sum| ≤
        |toReal seed| + (init.map fun i => |toReal (term i)|).sum := by
      have h := Multiset.abs_sum_le_sum_abs
        (s := ((init.map fun i => toReal (term i) : List ℝ) : Multiset ℝ))
      exact (abs_add_le _ _).trans (add_le_add le_rfl
        (by simpa [List.map_map, Function.comp_def] using h))
    have hP : 0 ≤ |toReal seed| + (init.map fun i => |toReal (term i)|).sum :=
      (abs_nonneg _).trans hS
    have hm0 : (0 : ℝ) ≤ init.length := Nat.cast_nonneg _
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      List.length_append, List.length_cons, List.length_nil, zero_add, Nat.cast_add, Nat.cast_one]
    rw [← add_assoc, ← add_assoc]
    generalize toReal (add (init.foldl (fun acc i => add acc (term i)) seed) (term x)) = a
      at h1 h2 ⊢
    generalize toReal (init.foldl (fun acc i => add acc (term i)) seed) = b at ih h1 h2
    generalize toReal (term x) = t at h1 h2 ⊢
    generalize toReal seed + (init.map fun i => toReal (term i)).sum = S at ih hS ⊢
    generalize |toReal seed| + (init.map fun i => |toReal (term i)|).sum = P at ih hS hP ⊢
    generalize (init.length : ℝ) = m at ih hm0 ⊢
    generalize unitRoundoffAt fmt = u at ih h1 hu ⊢
    have hm : 0 ≤ m * u := mul_nonneg hm0 hu
    have hsplit : |a - (S + t)| ≤ |a - (b + t)| + |b - S| := by
      simpa [show a - (b + t) + (b - S) = a - (S + t) by ring] using
        abs_add_le (a - (b + t)) (b - S)
    have ht := abs_nonneg t
    by_cases hx : (1 + u) * |t| ≤ u * P
    · nlinarith [mul_nonneg hu ht, mul_nonneg hm ht]
    · have hbt : |b + t| ≤ |b - S| + |S| + |t| := by
        simpa [show b - S + S + t = b + t by ring] using abs_add_three (b - S) S t
      have hround : (1 + u) * |a - (b + t)| ≤ u * (|b - S| + P + |t|) :=
        h1.trans (mul_le_mul_of_nonneg_left (by linarith) hu)
      -- The second-order term is absorbed: `u * P < (1 + u) * |t|` in this case.
      have habsorb : m * u * (u * P) ≤ m * u * ((1 + u) * |t|) :=
        mul_le_mul_of_nonneg_left (not_le.mp hx).le hm
      have hscaled : (1 + u) * (u * |b - S|) ≤ (1 + u) * (m * u * |t|) := by
        linarith [mul_le_mul_of_nonneg_left ih hu]
      have hsecond : u * |b - S| ≤ m * u * |t| :=
        le_of_mul_le_mul_left hscaled (by linarith)
      linarith [mul_le_mul_of_nonneg_left hsplit (by linarith : (0 : ℝ) ≤ 1 + u)]

/-- A left-to-right sum from a seed of real value zero: adding the `n` terms of a list in order
has error at most `(n - 1) * u / (1 + u) * ∑ |term i|` against the exact sum, when the result is
finite. The first addition is exact, so `n` terms take `n - 1` roundings, with natural
subtraction (Rump 2012; Jeannerod and Rump 2013, 2018). -/
theorem one_add_mul_abs_toReal_foldl_add_sub_le_of_toReal_eq_zero (hfmt : fmt.isIEEE = true)
    (hseed : toReal seed = 0)
    (hsum : isFinite (l.foldl (fun acc i => add acc (term i)) seed) = true) :
    (1 + unitRoundoffAt fmt) * |toReal (l.foldl (fun acc i => add acc (term i)) seed) -
        (l.map fun i => toReal (term i)).sum| ≤
      (l.length - 1 : ℕ) * unitRoundoffAt fmt * (l.map fun i => |toReal (term i)|).sum := by
  cases l with
  | nil => simp [hseed]
  | cons i l =>
    have hterm := isFinite_term_of_isFinite_foldl_add hfmt hsum i (by simp)
    have hnext : isFinite (add seed (term i)) = true := by
      simpa using isFinite_foldl_add_take hfmt hsum 1
    have hfirst : toReal (add seed (term i)) = toReal (term i) := by
      rw [toReal_add_eq_roundAt _ _ hfmt hnext, hseed, zero_add, roundAt_toReal_eq _ hterm]
    have h := one_add_mul_abs_toReal_foldl_add_sub_le (l := l) (term := term)
      (seed := add seed (term i)) hfmt (by simpa using hsum)
    simpa [hfirst] using h

/-- A left-to-right sum of `n` terms from a seed of real value zero has error at most
`(n - 1) * u * ∑ |term i|` against the exact sum, when the result is finite (Rump 2012). -/
theorem abs_toReal_foldl_add_sub_le (hfmt : fmt.isIEEE = true) (hseed : toReal seed = 0)
    (hsum : isFinite (l.foldl (fun acc i => add acc (term i)) seed) = true) :
    |toReal (l.foldl (fun acc i => add acc (term i)) seed) -
        (l.map fun i => toReal (term i)).sum| ≤
      (l.length - 1 : ℕ) * unitRoundoffAt fmt * (l.map fun i => |toReal (term i)|).sum :=
  (le_mul_of_one_le_left (abs_nonneg _)
    (le_add_of_nonneg_right (unitRoundoffAt_pos fmt).le)).trans
    (one_add_mul_abs_toReal_foldl_add_sub_le_of_toReal_eq_zero hfmt hseed hsum)

/-- A finite product whose exact value is zero or in the normal range has relative error at most
`u / (1 + u)`. -/
theorem one_add_mul_abs_toReal_mul_sub_le (x y : Model fmt) (hfmt : fmt.isIEEE = true)
    (hout : isFinite (mul x y) = true) (hnormal : NoUnderflowAt fmt (toReal x * toReal y)) :
    (1 + unitRoundoffAt fmt) * |toReal (mul x y) - toReal x * toReal y| ≤
      unitRoundoffAt fmt * |toReal x * toReal y| := by
  rw [toReal_mul_eq_roundAt x y hfmt hout]
  rcases hnormal with hzero | hnormal
  · simp [hzero]
  · exact one_add_mul_abs_roundAt_sub_le fmt hnormal

/-- The inner product loop `acc := acc + left i * right i` over `n` indices, from a seed of real
value zero, has error at most `n * u * ∑ |left i * right i|` against the exact inner product,
when the result is finite and no exact product is in the subnormal range. The constant is linear
in `n`, with no restriction on `n` and no term of second order (Jeannerod and Rump 2013). -/
theorem abs_toReal_foldl_add_mul_sub_le (hfmt : fmt.isIEEE = true) (hseed : toReal seed = 0)
    (hsum : isFinite (l.foldl (fun acc i => add acc (mul (left i) (right i))) seed) = true)
    (hnormal : ∀ i ∈ l, NoUnderflowAt fmt (toReal (left i) * toReal (right i))) :
    |toReal (l.foldl (fun acc i => add acc (mul (left i) (right i))) seed) -
        (l.map fun i => toReal (left i) * toReal (right i)).sum| ≤
      l.length * unitRoundoffAt fmt *
        (l.map fun i => |toReal (left i) * toReal (right i)|).sum := by
  have hu := unitRoundoffAt_pos fmt
  have hproducts := isFinite_term_of_isFinite_foldl_add hfmt hsum
  have hfold := one_add_mul_abs_toReal_foldl_add_sub_le_of_toReal_eq_zero hfmt hseed hsum
  -- The rounded products against the exact ones, and their magnitudes.
  have hterms : (1 + unitRoundoffAt fmt) *
        |(l.map fun i => toReal (mul (left i) (right i))).sum -
          (l.map fun i => toReal (left i) * toReal (right i)).sum| ≤
        unitRoundoffAt fmt * (l.map fun i => |toReal (left i) * toReal (right i)|).sum ∧
      (1 + unitRoundoffAt fmt) * (l.map fun i => |toReal (mul (left i) (right i))|).sum ≤
        (1 + 2 * unitRoundoffAt fmt) *
          (l.map fun i => |toReal (left i) * toReal (right i)|).sum := by
    clear hfold hsum
    induction l with
    | nil => simp
    | cons i l ih =>
      have hp := one_add_mul_abs_toReal_mul_sub_le (left i) (right i) hfmt
        (hproducts i (by simp)) (hnormal i (by simp))
      obtain ⟨ih1, ih2⟩ := ih (fun j hj => hnormal j (List.mem_cons_of_mem _ hj))
        (fun j hj => hproducts j (List.mem_cons_of_mem _ hj))
      simp only [List.map_cons, List.sum_cons]
      generalize toReal (mul (left i) (right i)) = q at hp ⊢
      generalize toReal (left i) * toReal (right i) = t at hp ⊢
      constructor
      · have h := abs_add_le (q - t)
          ((l.map fun i => toReal (mul (left i) (right i))).sum -
            (l.map fun i => toReal (left i) * toReal (right i)).sum)
        rw [show q - t + ((l.map fun i => toReal (mul (left i) (right i))).sum -
            (l.map fun i => toReal (left i) * toReal (right i)).sum) =
          q + (l.map fun i => toReal (mul (left i) (right i))).sum -
            (t + (l.map fun i => toReal (left i) * toReal (right i)).sum) by ring] at h
        linarith [mul_le_mul_of_nonneg_left h (by linarith : (0 : ℝ) ≤ 1 + unitRoundoffAt fmt)]
      · have h := abs_sub_abs_le_abs_sub q t
        nlinarith [abs_nonneg t, abs_nonneg q]
  obtain ⟨hdiff, hsize⟩ := hterms
  cases l with
  | nil => simp [hseed]
  | cons i l =>
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hfold ⊢
    generalize toReal ((i :: l).foldl (fun acc i => add acc (mul (left i) (right i))) seed) = r
      at hfold ⊢
    generalize ((i :: l).map fun i => toReal (mul (left i) (right i))).sum = Q at hfold hdiff
    generalize ((i :: l).map fun i => toReal (left i) * toReal (right i)).sum = T at hdiff ⊢
    generalize ((i :: l).map fun i => |toReal (mul (left i) (right i))|).sum = A
      at hfold hsize
    have hB : 0 ≤ ((i :: l).map fun i => |toReal (left i) * toReal (right i)|).sum :=
      List.sum_nonneg fun a ha => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
        exact abs_nonneg _
    generalize ((i :: l).map fun i => |toReal (left i) * toReal (right i)|).sum = B
      at hdiff hsize hB ⊢
    have hN : (0 : ℝ) ≤ l.length := Nat.cast_nonneg _
    generalize (l.length : ℝ) = N at hfold hN ⊢
    generalize unitRoundoffAt fmt = u at hfold hdiff hsize hu ⊢
    have hsplit : |r - T| ≤ |r - Q| + |Q - T| := by
      simpa using abs_add_le (r - Q) (Q - T)
    -- `(1 + u)² |r - T| ≤ u B (N + 2 N u + 1 + u) ≤ (1 + u)² (N + 1) u B`.
    have h1 : (1 + u) * ((1 + u) * |r - T|) ≤ N * u * ((1 + 2 * u) * B) + (1 + u) * (u * B) := by
      have := mul_le_mul_of_nonneg_left hsize (mul_nonneg hN hu.le)
      nlinarith [mul_le_mul_of_nonneg_left hsplit (by linarith : (0 : ℝ) ≤ 1 + u)]
    have h2 : (1 + u) * ((1 + u) * |r - T|) ≤ (1 + u) * ((1 + u) * ((N + 1) * u * B)) := by
      nlinarith [mul_nonneg (mul_nonneg hN hu.le) (mul_nonneg hu.le hB),
        mul_nonneg hu.le (mul_nonneg hu.le hB), mul_nonneg (mul_nonneg hu.le hu.le)
          (mul_nonneg hu.le hB), mul_nonneg hu.le hB]
    exact le_of_mul_le_mul_left (le_of_mul_le_mul_left h2 (by linarith)) (by linarith)

end FloatLib.Floats.Formats.BinaryInterchange.Model
