/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Trig
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.List.GetD

/-!
# Bounds on series with rational coefficients

These are the theorems that `interval` applies when a goal bounds a polynomial or a series over its
whole domain. The coefficients are lists of rationals, such as the decoded values of binary64 data
or a list written in the source, and a packed row holds each list as integers at one common
denominator `d`.

For example, the coefficients `[1/2, 1, 1/2]` have the denominator `2` and the row `[1, 2, 1]`.
The polynomial `1/2 + cos u + 1/2 cos (2u) = cos u (1 + cos u)` has the minimum `-1/4` at
`cos u = -1/2`, and the factor `[1, 1, 1]` proves it exactly, while the coefficients alone only
give `1/2 - 3/2 = -1`.

## Main definitions

* `series f xs`: the value `∑ k < xs.length, xs[k] * f k` of a list of rationals against a basis
  `f : ℕ → R` of a division ring, such as `cos (k u)` and `sin (k u)` on the circle, `xᵏ` on an
  interval, `T k (y)` for a Chebyshev series or `zᵏ` on the unit circle of `ℂ`.
* `rowCheck w g n d A xs`: the kernel check that the packed row `A` holds the `n` rationals `xs`
  at the denominator `d`, with entries in `[-2 ^ g, 2 ^ g)`, at two integer products per entry and
  one masked addition for the range.

## Main statements

* `series_add`, `series_smul`, `series_single` and `sum_eq_series`: a goal written with sums, sums
  of sums and multiples comes to the form `series f xs`, which is what the tactic does before any
  check runs.
* `trig_sos`, `norm_sos` and `power_sos`: every family turns one sum-of-squares check, or one
  centre-dominance check when there is no certificate, into `0 ≤ kT (K F) + kc` for the value `F`
  of the series and a positive scale `K`. `trig_sos` is for real trigonometric polynomials
  `∑ aₖ cos (k u) + ∑ bₖ sin (k u)` at every `u`, with `K = 2 d`; `norm_sos` for the norm square
  `‖∑ aₖ zᵏ + i ∑ bₖ zᵏ‖²` of a polynomial with Gaussian rational coefficients at every `z` of the
  unit circle, with `K = d ^ 2`; and `power_sos` for `∑ aₖ xᵏ` at every `x` of `[lo, hi]`, through
  Horner's rule in the kernel, with `K = d (2 D) ^ (n - 1)`.
* `bound_le_of_sos`, `bound_lt_of_sos`, `le_bound_of_sos` and `lt_bound_of_sos`: from there,
  `lo ≤ F`, `lo < F`, `F ≤ hi` and `F < hi`, with `kT K lo + kc ≤ 0` (or `< 0`) decided on
  rationals.

A Chebyshev series at a point of `[-1, 1]` is the cosine case through `forall_Icc_chebyshev`.

## Implementation notes

Every family concludes the same shape, `0 ≤ kT (K F) + kc`, so the tactic needs one set of four
bound lemmas, not four per family. The scale `K` is a natural number cast to `ℝ`, which the tactic
reads straight off the conclusion, so adding a family means adding one theorem and nothing in the
bound lemmas.

`series` uses `List.getD` and `Finset.range`, the forms in which goals are usually written, while
the checks link the list to its row entry by entry with `rowCheck`. A list that a goal writes as a
`Finset.sum` of `(xs.getD k 0 : ℝ) * f k` is linked by `rfl`, with no rewriting at all.

## References

* Siegfried M. Rump, *Verification methods: rigorous results using floating-point arithmetic*,
  Acta Numerica 19 (2010), 287–449, <https://doi.org/10.1017/S096249291000005X>, for the
  certificate style: an untrusted computation, then a cheap exact check.

## Tags

coefficient bound, series, certificate, sum of squares
-/

@[expose] public section

namespace FloatLib.Numerics.Coeff

open Packed Finset Complex

/-! ### The value of a coefficient list -/

/-- The value `∑ k < xs.length, xs[k] * f k` of a list of rational coefficients against a basis. -/
def series {R : Type*} [DivisionRing R] (f : ℕ → R) (xs : List ℚ) : R :=
  ∑ k ∈ range xs.length, (xs.getD k 0 : R) * f k

section Series

variable {R : Type*} [DivisionRing R] (f : ℕ → R)

private theorem series_eq_range {xs : List ℚ} {N : ℕ} (hl : xs.length ≤ N) :
    series f xs = ∑ k ∈ range N, (xs.getD k 0 : R) * f k := by
  refine Finset.sum_subset (range_subset_range.mpr hl) fun k _ hk => ?_
  rw [List.getD_eq_default _ _ (by simpa using hk), Rat.cast_zero, zero_mul]

/-- The empty list has value zero. -/
@[simp] theorem series_nil : series f [] = 0 := by simp [series]

private theorem getD_add : ∀ (xs ys : List ℚ) (k : ℕ),
    (add xs ys).getD k 0 = xs.getD k 0 + ys.getD k 0
  | [], ys, k => by simp only [add, List.getD_nil, zero_add]
  | x :: xs, [], k => by simp only [add, List.getD_nil, add_zero]
  | x :: xs, y :: ys, 0 => by simp only [add, List.getD_cons_zero]
  | x :: xs, y :: ys, k + 1 => by simp only [add, List.getD_cons_succ, getD_add xs ys k]

/-- `series` adds up over the lanewise sum of two lists. -/
theorem series_add [CharZero R] (xs ys : List ℚ) :
    series f (add xs ys) = series f xs + series f ys := by
  rw [series_eq_range f (N := (add xs ys).length) le_rfl,
    series_eq_range f (N := (add xs ys).length) (by rw [length_add]; omega),
    series_eq_range f (N := (add xs ys).length) (by rw [length_add]; omega), ← sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getD_add, Rat.cast_add, add_mul]

/-- `series` commutes with scaling. -/
theorem series_smul [CharZero R] (q : ℚ) (xs : List ℚ) :
    series f (smul q xs) = q * series f xs := by
  simp only [series, smul, List.length_map, mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (mem_range.mp hk), List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (mem_range.mp hk)]
  simp [mul_assoc]

/-- A single coefficient `q` in lane `m` is the monomial `q * f m`. -/
theorem series_single (m : ℕ) (q : ℚ) : series f (List.replicate m 0 ++ [q]) = q * f m := by
  simp only [series, List.length_append, List.length_replicate, List.length_cons, List.length_nil,
    sum_range_succ]
  rw [Finset.sum_eq_zero fun k hk => by
    rw [List.getD_append _ _ _ _ (by simpa using hk), List.getD_replicate 0 (mem_range.mp hk)]
    simp, zero_add,
    List.getD_append_right _ _ _ _ (by simp), List.length_replicate, Nat.sub_self]
  simp

/-- A finite sum whose terms are the coefficients of a list times the basis is the value of the
list, for any list no longer than the sum. This is how a block `∑ k ∈ range n, a k * f k` of a goal
becomes `series f xs`. -/
theorem sum_eq_series {n : ℕ} {xs : List ℚ} {t : ℕ → R} (hl : xs.length ≤ n)
    (h : ∀ k < n, t k = (xs.getD k 0 : R) * f k) : ∑ k ∈ range n, t k = series f xs := by
  rw [series_eq_range f hl]
  exact Finset.sum_congr rfl fun k hk => h k (mem_range.mp hk)

end Series

/-! ### Links between rationals and packed rows -/

/-- The packed row `A` of width `w` holds the `n` rationals `xs` at the common denominator `d`:
entry `k` is `xs[k] * d`, and every entry lies in `[-2 ^ g, 2 ^ g)`. -/
def rowCheck (w g n d A : ℕ) (xs : List ℚ) : Bool :=
  Nat.beq xs.length n && Nat.blt 0 d && guard w g n A && linked w d A 0 xs

private theorem rowCheck_sound {R : Type*} [Field R] [CharZero R] {w g n d A : ℕ} {xs : List ℚ}
    (h : rowCheck w g n d A xs = true) :
    xs.length = n ∧ 0 < d ∧ guard w g n A = true ∧
      ∀ k < n, ((xs.getD k 0 : ℚ) : R) = entry w k A / d := by
  simp only [rowCheck, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at h
  obtain ⟨⟨⟨hl, hd⟩, hg⟩, hlink⟩ := h
  refine ⟨hl, hd, hg, fun k hk => ?_⟩
  have hk' : k < xs.length := hl ▸ hk
  have e := linked_sound hlink k hk'
  rw [zero_add] at e
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some,
    eq_div_iff (Nat.cast_ne_zero.mpr hd.ne'), ← Rat.num_div_den xs[k]]
  have hden : (xs[k].den : R) ≠ 0 := by exact_mod_cast xs[k].den_pos.ne'
  push_cast
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  exact_mod_cast e

/-- `d` times the value of a linked list is the sum over the lanes of its row. -/
private theorem series_of_rowCheck {R : Type*} [Field R] [CharZero R] {w g n d A : ℕ}
    {xs : List ℚ} (h : rowCheck w g n d A xs = true) (f : ℕ → R) :
    (d : R) * series f xs = ∑ k ∈ range n, (entry w k A : R) * f k := by
  obtain ⟨hl, hd, -, hx⟩ := rowCheck_sound (R := R) h
  have hd' : (d : R) ≠ 0 := by exact_mod_cast hd.ne'
  rw [series, hl, mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hx k (mem_range.mp hk)]
  field_simp

/-! ### From a check to a bound -/

/-- `lo ≤ F` from `0 ≤ kT (K F) + kc` with `kT > 0` and `kT K lo + kc ≤ 0`. -/
theorem bound_le_of_sos {F lo' : ℝ} {kT kc : ℤ} {K : ℕ} {lo : ℚ}
    (h : 0 ≤ (kT : ℝ) * (K * F) + kc) (hK : 0 < K) (hkT : 0 < kT)
    (hlo : (kT : ℚ) * K * lo + kc ≤ 0) (hlo' : lo' = lo) : lo' ≤ F := by
  have h' : (kT : ℝ) * K * lo + kc ≤ 0 := by exact_mod_cast hlo
  have hp : (0 : ℝ) < kT * K := by positivity
  subst hlo'
  nlinarith

/-- `lo < F` from `0 ≤ kT (K F) + kc` with `kT > 0` and `kT K lo + kc < 0`. -/
theorem bound_lt_of_sos {F lo' : ℝ} {kT kc : ℤ} {K : ℕ} {lo : ℚ}
    (h : 0 ≤ (kT : ℝ) * (K * F) + kc) (hK : 0 < K) (hkT : 0 < kT)
    (hlo : (kT : ℚ) * K * lo + kc < 0) (hlo' : lo' = lo) : lo' < F := by
  have h' : (kT : ℝ) * K * lo + kc < 0 := by exact_mod_cast hlo
  have hp : (0 : ℝ) < kT * K := by positivity
  subst hlo'
  nlinarith

/-- `F ≤ hi` from `0 ≤ kT (K F) + kc` with `kT < 0` and `kT K hi + kc ≤ 0`. -/
theorem le_bound_of_sos {F hi' : ℝ} {kT kc : ℤ} {K : ℕ} {hi : ℚ}
    (h : 0 ≤ (kT : ℝ) * (K * F) + kc) (hK : 0 < K) (hkT : kT < 0)
    (hhi : (kT : ℚ) * K * hi + kc ≤ 0) (hhi' : hi' = hi) : F ≤ hi' := by
  have h' : (kT : ℝ) * K * hi + kc ≤ 0 := by exact_mod_cast hhi
  have hk : (kT : ℝ) < 0 := by exact_mod_cast hkT
  have hp : (0 : ℝ) < -kT * K := by
    have : (0 : ℝ) < K := by exact_mod_cast hK
    nlinarith
  subst hhi'
  nlinarith

/-- `F < hi` from `0 ≤ kT (K F) + kc` with `kT < 0` and `kT K hi + kc < 0`. -/
theorem lt_bound_of_sos {F hi' : ℝ} {kT kc : ℤ} {K : ℕ} {hi : ℚ}
    (h : 0 ≤ (kT : ℝ) * (K * F) + kc) (hK : 0 < K) (hkT : kT < 0)
    (hhi : (kT : ℚ) * K * hi + kc < 0) (hhi' : hi' = hi) : F < hi' := by
  have h' : (kT : ℝ) * K * hi + kc < 0 := by exact_mod_cast hhi
  have hk : (kT : ℝ) < 0 := by exact_mod_cast hkT
  have hp : (0 : ℝ) < -kT * K := by
    have : (0 : ℝ) < K := by exact_mod_cast hK
    nlinarith
  subst hhi'
  nlinarith

/-! ### The three families -/

/-- Real trigonometric polynomials on the circle. The rows `A` and `B` hold the cosine and the sine
coefficients `a` and `b` at the denominator `d`; one check on their unfolded rows, centred at
`n - 1`, gives `0 ≤ kT (2 d (∑ aₖ cos (k u) + ∑ bₖ sin (k u))) + kc` for every `u`. -/
theorem trig_sos {w g gt gh na nb n m m' d kH A B p q : ℕ} {kT kc : ℤ} {a b : List ℚ}
    (hA : rowCheck w g na d A a = true) (hB : rowCheck w g nb d B b = true) (hg : g + 2 ≤ w)
    (hna : na ≤ n) (hnb : nb ≤ n)
    (hc : sosCheck w gt gh n m m' kT kc kH
      (ofInt w (2 * n - 1) (shift w (n - na) (unfold w na A)))
      (ofInt w (2 * n - 1) (shift w (n - nb) (unfold w nb B true))) p q = true) (u : ℝ) :
    0 ≤ (kT : ℝ) * (((2 * d : ℕ) : ℝ) *
      (series (fun k => Real.cos (k * u)) a + series (fun k => Real.sin (k * u)) b)) + kc := by
  have h := trig_sosCheck (rowCheck_sound (R := ℝ) hA).2.2.1 (rowCheck_sound (R := ℝ) hB).2.2.1
    hg hna hnb hc u
  rw [← series_of_rowCheck hA, ← series_of_rowCheck hB] at h
  push_cast
  linarith

/-- Norms of polynomials with Gaussian rational coefficients on the unit circle. The rows `A` and
`B` hold the real and imaginary parts `a` and `b` at the denominator `d`; one check on the rows
of `|A + i B|²` that `sqRe` and `sqIm` compute gives `0 ≤ kT (d ^ 2 ‖∑ aₖ zᵏ + i ∑ bₖ zᵏ‖²) + kc`
for every `z` with `‖z‖ = 1`. -/
theorem norm_sos {w g gt gh na nb n m m' d kH A B p q : ℕ} {kT kc : ℤ} {a b : List ℚ}
    (hA : rowCheck w g na d A a = true) (hB : rowCheck w g nb d B b = true)
    (hna : na ≤ n) (hnb : nb ≤ n)
    (hroom : (na + nb) * 2 ^ g * ((na + nb) * 2 ^ g) < 2 ^ (w - 1))
    (hc : sosCheck w gt gh n m m' kT kc kH (ofInt w (2 * n - 1) (sqRe w n na nb A B))
      (ofInt w (2 * n - 1) (sqIm w n na nb A B)) p q = true) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (kT : ℝ) * (((d ^ 2 : ℕ) : ℝ) *
      ‖series (fun k => z ^ k) a + I * series (fun k => z ^ k) b‖ ^ 2) + kc := by
  have h := normSq_sosCheck (rowCheck_sound (R := ℂ) hA).2.2.1
    (rowCheck_sound (R := ℂ) hB).2.2.1 hna hnb hroom hc hz
  have lv : ∀ {n D : ℕ} {xs : List ℚ}, rowCheck w g n d D xs = true →
      laurent (entries w n D) 0 z = (d : ℂ) * series (fun k => z ^ k) xs := by
    intro n D xs hD
    rw [series_of_rowCheck hD, laurent, neg_zero, zpow_zero, one_mul, aeval_ofCoeffList,
      length_entries]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
      rw [length_entries]; exact mem_range.mp hk), Option.getD_some, getElem_entries]
  rw [lv hA, lv hB, show (d : ℂ) * series (fun k => z ^ k) a + I * ((d : ℂ) *
      series (fun k => z ^ k) b) = (d : ℂ) * (series (fun k => z ^ k) a +
        I * series (fun k => z ^ k) b) by ring, norm_mul, Complex.norm_natCast, mul_pow] at h
  push_cast
  linarith

/-- Power series on an interval. The row `A` holds the coefficients `a` at the denominator `d`,
and `M / D` and `R / D` are the midpoint and the radius of `[lo, hi]`; one check on the row that
Horner's rule builds in the kernel gives `0 ≤ kT (d (2 D) ^ (n - 1) ∑ aₖ xᵏ) + kc` for every `x`
in `[lo, hi]`. -/
theorem power_sos {w g gt gh n m m' d D K kH A p q : ℕ} {M R kT kc : ℤ} {a : List ℚ} {lo hi : ℚ}
    (hA : rowCheck w g n d A a = true) (hK : l1 [0, 2 * (D : ℤ)] ≤ K ∧ l1 [R, 2 * M, R] ≤ K)
    (hroom : n * 2 ^ g * K ^ (n - 1) < 2 ^ (w - 1)) (hD : 0 < D)
    (hM : (M : ℚ) = (lo + hi) / 2 * D) (hR : (R : ℚ) = (hi - lo) / 2 * D)
    (hc : sosCheck w gt gh n m m' kT kc kH
      (ofInt w (2 * n - 1) (horner w n (shift w 1 (2 * (D : ℤ)))
        (Int.add R (Int.add (shift w 1 (2 * M)) (shift w 2 R))) A))
      (ofInt w (2 * n - 1) 0) p q = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi,
      0 ≤ (kT : ℝ) * (((d * (2 * D) ^ (n - 1) : ℕ) : ℝ) * series (fun k => x ^ k) a) + kc := by
  have hl := (rowCheck_sound (R := ℝ) hA).1
  refine forall_Icc_of_cos fun u => ?_
  have h := power_sosCheck (rowCheck_sound (R := ℝ) hA).2.2.1 hK hroom hc u
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hM' : (M : ℝ) = (lo + hi) / 2 * D := by exact_mod_cast hM
  have hR' : (R : ℝ) = (hi - lo) / 2 * D := by exact_mod_cast hR
  have e : ∑ k ∈ range n, (entry w k A : ℝ) * (2 * M + 2 * R * Real.cos u) ^ k *
      (2 * (D : ℤ) : ℝ) ^ (n - 1 - k) = (2 * D : ℝ) ^ (n - 1) *
        ∑ k ∈ range n, (entry w k A : ℝ) *
          (((lo : ℝ) + hi) / 2 + ((hi : ℝ) - lo) / 2 * Real.cos u) ^ k := by
    rw [mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n - 1 := by have := mem_range.mp hk; omega
    rw [hM', hR', show (2 : ℝ) * ((lo + hi) / 2 * D) + 2 * ((hi - lo) / 2 * D) * Real.cos u =
      2 * D * ((lo + hi) / 2 + (hi - lo) / 2 * Real.cos u) by ring, mul_pow]
    push_cast
    rw [show (2 * (D : ℝ)) ^ (n - 1) = (2 * D) ^ k * (2 * D) ^ (n - 1 - k) by
      rw [← pow_add, Nat.add_sub_cancel' hk']]
    ring
  rw [e, ← series_of_rowCheck hA] at h
  push_cast
  linarith

end FloatLib.Numerics.Coeff
