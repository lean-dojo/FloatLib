/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Laurent
public import FloatLib.Numerics.Packed.Window
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Trigonometric polynomials, and polynomials on an interval

A real trigonometric polynomial `∑ k < n, aₖ cos (k u) + bₖ sin (k u)` is a two-sided row on the
circle. With `z = exp (u i)`, `2 cos (k u) = z ^ k + z ^ (-k)`, so twice the cosine part is the
Laurent polynomial of `mirror a = aₙ₋₁, …, a₁, 2 a₀, a₁, …, aₙ₋₁` centred at lane `n - 1`
(`laurent_mirror`), and the sine part is `1 / (2 i)` times the row `mirror b (odd := true)`
(`laurent_mirror_odd`). The kernel builds these rows from half rows with one reversal each
(`Packed.unfold`), so no certificate ever has to check that its row is symmetric.

A polynomial `∑ aₖ xᵏ` on `[lo, hi]` becomes one too: at `x = m + r cos u`, with the midpoint `m`
and the radius `r`, it is a cosine polynomial of the same degree, and Horner's rule in the kernel
computes its row (`Packed.horner`). This is the change of variables behind Chebyshev series, done
in integers.

For example, `1 + 2 cos u + cos (2 u)` has the half row `[1, 2, 1]`, so its `l1` bound is `4`,
attained at `u = 0`. It equals `2 cos u (1 + cos u)`, whose minimum on the circle is `-1/2`. And
`1 + sin u` is `|1 - i z|² / 2` on the circle, so the factor `[1, 0] + i [0, -1]` proves its
minimum `0` exactly: its sine term needs the imaginary part.

## Main definitions

* `hilbert xs c z`: the Hilbert transform of a row, the Fourier multiplier `-i sgn m` applied
  through `Packed.signRow`.

## Main statements

* `abs_cos_sum_le` and `abs_sin_sum_le`: the sup norm is at most the `l1` norm of the half row.
* `trig_sosCheck`: one sum-of-squares check, with a factor `p + i q` of Gaussian integers, bounds a
  trigonometric polynomial with cosine and sine terms from one side.
* `power_sosCheck`: the same for a polynomial on an interval, through Horner's rule.
* `hasDerivAt_cos_sum`, `hasDerivAt_sin_sum` and `hasDerivAt_cos_ramp`: differentiation
  multiplies coefficient `k` by `k` and swaps cosines and sines, and `Packed.ramp` computes that
  row in the kernel.
* `hilbert_mirror` and `hilbert_mirror_odd`: the Hilbert transform maps `cos (k u)` to
  `sin (k u)` and `sin (k u)` to `-cos (k u)` for `k ≥ 1`, which on half rows is a relabelling.
* `chebyshev_cos`, `forall_Icc_chebyshev` and `forall_Icc_of_cos`: a Chebyshev series is a cosine
  polynomial, so bounds on the circle hold on `[-1, 1]`, and on any interval.

## Implementation notes

The Chebyshev bridge is Mathlib's `Polynomial.Chebyshev.T_real_cos`, `Tₖ (cos u) = cos (k u)`,
applied term by term, so a Chebyshev series needs no packed program of its own: its coefficients
are the half row of a cosine polynomial as they stand. I find that a nice bit of economy. The
power basis needs `Packed.horner` only because its coefficients are not already in that form.

## References

* Lloyd N. Trefethen, *Approximation Theory and Approximation Practice*, SIAM (2013), chapters 2
  and 3, for Chebyshev polynomials as cosines and the substitution `x = cos u`,
  <https://people.maths.ox.ac.uk/trefethen/ATAP/>.
* Yitzhak Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University
  Press (2004), <https://doi.org/10.1017/CBO9781139165372>, chapter 3 on the conjugate function.

## Tags

trigonometric polynomial, Chebyshev series, Hilbert transform, sum of squares
-/

@[expose] public section

namespace FloatLib.Numerics.Coeff

open Complex ComplexConjugate Finset
open FloatLib.Numerics.Packed

/-! ### Rows on the circle -/

/-- At `z = exp (u * I)` a row is the trigonometric polynomial
`∑ k, xs[k] * exp ((k - c) * u * I)`. -/
theorem laurent_exp (xs : List ℤ) (c : ℤ) (u : ℝ) :
    laurent xs c (exp (u * I)) =
      ∑ k ∈ range xs.length, (xs.getD k 0 : ℂ) * exp (((((k : ℤ) - c : ℤ) : ℝ) * u : ℝ) * I) := by
  rw [laurent, aeval_ofCoeffList, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← exp_int_mul, ← exp_nat_mul, mul_left_comm, ← exp_add]
  congr 2
  push_cast
  ring

/-- The real part of a row on the circle is a cosine sum: lane `k` contributes
`xs[k] * cos ((k - c) u)`. -/
theorem re_laurent_exp (xs : List ℤ) (c : ℤ) (u : ℝ) :
    (laurent xs c (exp (u * I))).re =
      ∑ k ∈ range xs.length, (xs.getD k 0 : ℝ) * Real.cos ((((k : ℤ) - c : ℤ) : ℝ) * u) := by
  rw [laurent_exp, re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((xs.getD k 0 : ℤ) : ℂ) = ((xs.getD k 0 : ℝ) : ℂ) by push_cast; rfl, re_ofReal_mul,
    exp_ofReal_mul_I_re]

/-- The imaginary part of a row on the circle is a sine sum: lane `k` contributes
`xs[k] * sin ((k - c) u)`. -/
theorem im_laurent_exp (xs : List ℤ) (c : ℤ) (u : ℝ) :
    (laurent xs c (exp (u * I))).im =
      ∑ k ∈ range xs.length, (xs.getD k 0 : ℝ) * Real.sin ((((k : ℤ) - c : ℤ) : ℝ) * u) := by
  rw [laurent_exp, im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((xs.getD k 0 : ℤ) : ℂ) = ((xs.getD k 0 : ℝ) : ℂ) by push_cast; rfl, im_ofReal_mul,
    exp_ofReal_mul_I_im]

/-- The two halves of a mirrored row: the constant in the centre and
`w = ∑ j, as[j] z ^ (j + 1)` on the right, whose conjugate, or its negative for odd rows, sits on
the left. -/
private theorem laurent_mirror_cons (a₀ : ℤ) (as : List ℤ) (odd : Bool) (u : ℝ) :
    laurent (mirror (a₀ :: as) odd) as.length (exp (u * I)) =
      cond odd (laurent as (-1) (exp (u * I)) - conj (laurent as (-1) (exp (u * I))))
        (2 * a₀ + (laurent as (-1) (exp (u * I)) + conj (laurent as (-1) (exp (u * I))))) := by
  have hz := norm_exp_ofReal_mul_I u
  have hz0 : exp (u * I) ≠ 0 := exp_ne_zero _
  generalize exp (u * I) = z at hz hz0
  have hrev : ∀ (A : List ℤ) (c : ℤ), c = A.length →
      laurent A.reverse c z = conj (laurent A (-1) z) := by
    intro A c hc
    rw [laurent_reverse hz0, conj_laurent hz, hc]
    ring_nf
  have hcons : ∀ (x : ℤ) (A : List ℤ), laurent (x :: A) 0 z = x + laurent A (-1) z := by
    intro x A
    rw [laurent_cons hz0]
    simp
  have hneg : laurent (as.map (- ·)) (-1) z = -laurent as (-1) z := by
    have h := laurent_smul (-1) as (-1) z
    simp only [smul, neg_mul, one_mul, Int.cast_neg, Int.cast_one] at h
    exact h
  cases odd
  · show laurent (as.reverse ++ (2 * a₀) :: as) as.length z = _
    rw [laurent_append hz0, List.length_reverse, sub_self, hrev _ _ rfl, hcons, Bool.cond_false]
    push_cast
    ring
  · show laurent ((as.map (- ·)).reverse ++ 0 :: as) as.length z = _
    rw [laurent_append hz0, List.length_reverse, List.length_map, sub_self,
      hrev _ _ (by rw [List.length_map]), hcons, hneg, map_neg, Bool.cond_true]
    push_cast
    ring

private theorem sum_succ (f : ℕ → ℝ) (a₀ : ℤ) (as : List ℤ) :
    ∑ k ∈ range (as.length + 1), ((a₀ :: as).getD k 0 : ℝ) * f k =
      a₀ * f 0 + ∑ j ∈ range as.length, (as.getD j 0 : ℝ) * f (j + 1) := by
  rw [sum_range_succ', add_comm]
  simp

private theorem shift_cast (j : ℕ) : (((j : ℤ) - -1 : ℤ) : ℝ) = (j : ℝ) + 1 := by
  push_cast; ring

/-- Twice a cosine polynomial is the mirrored row centred at lane `n - 1`. -/
theorem laurent_mirror (a : List ℤ) (u : ℝ) :
    laurent (mirror a) (a.length - 1 : ℕ) (exp (u * I)) =
      ((2 * ∑ k ∈ range a.length, (a.getD k 0 : ℝ) * Real.cos (k * u) : ℝ) : ℂ) := by
  cases a with
  | nil => simp [mirror]
  | cons a₀ as =>
      rw [List.length_cons, Nat.add_sub_cancel, laurent_mirror_cons, Bool.cond_false, add_conj,
        re_laurent_exp, sum_succ]
      simp only [shift_cast, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one, Nat.cast_add,
        Nat.cast_one]
      push_cast
      ring

/-- Twice `i` times a sine polynomial is the odd mirrored row centred at lane `n - 1`. -/
theorem laurent_mirror_odd (a : List ℤ) (u : ℝ) :
    laurent (mirror a true) (a.length - 1 : ℕ) (exp (u * I)) =
      2 * I * ((∑ k ∈ range a.length, (a.getD k 0 : ℝ) * Real.sin (k * u) : ℝ) : ℂ) := by
  cases a with
  | nil => simp [mirror]
  | cons a₀ as =>
      rw [List.length_cons, Nat.add_sub_cancel, laurent_mirror_cons, Bool.cond_true, sub_conj,
        im_laurent_exp, sum_succ]
      simp only [shift_cast, Nat.cast_zero, zero_mul, Real.sin_zero, mul_zero, zero_add,
        Nat.cast_add, Nat.cast_one]
      push_cast
      ring

/-! ### Sup bounds -/

/-- A cosine polynomial is bounded by the `l1` norm of its coefficients. -/
theorem abs_cos_sum_le (a : List ℤ) (u : ℝ) :
    |∑ k ∈ range a.length, (a.getD k 0 : ℝ) * Real.cos (k * u)| ≤ l1 a := by
  have h := norm_laurent_le (norm_exp_ofReal_mul_I u) (mirror a) (a.length - 1 : ℕ)
  rw [laurent_mirror, norm_real, Real.norm_eq_abs, abs_mul, abs_two] at h
  have := l1_mirror_le a false
  have : (l1 (mirror a) : ℝ) ≤ 2 * l1 a := by exact_mod_cast this
  linarith

/-- A sine polynomial is bounded by the `l1` norm of its coefficients. -/
theorem abs_sin_sum_le (a : List ℤ) (u : ℝ) :
    |∑ k ∈ range a.length, (a.getD k 0 : ℝ) * Real.sin (k * u)| ≤ l1 a := by
  have h := norm_laurent_le (norm_exp_ofReal_mul_I u) (mirror a true) (a.length - 1 : ℕ)
  rw [laurent_mirror_odd, norm_mul, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    Complex.norm_two] at h
  have := l1_mirror_le a true
  have : (l1 (mirror a true) : ℝ) ≤ 2 * l1 a := by exact_mod_cast this
  linarith

/-! ### Sums of squares on cosine polynomials -/

private theorem getD_entries {w n u k : Nat} (hk : k < n) :
    (entries w n u).getD k 0 = entry w k u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [length_entries]; exact hk),
    Option.getD_some, getElem_entries]

/-- A sum over the entries of a packed row, written with `getD`, is the sum over its lanes. -/
theorem sum_getD_entries (w n a : Nat) (f : ℕ → ℝ) :
    ∑ k ∈ range (entries w n a).length, ((entries w n a).getD k 0 : ℝ) * f k =
      ∑ k ∈ range n, (entry w k a : ℝ) * f k := by
  rw [length_entries]
  exact Finset.sum_congr rfl fun k hk => by rw [getD_entries (Finset.mem_range.mp hk)]

/-- A half row unfolded and moved up to centre `n - 1`: on the circle it is the two-sided row of
the half row, whatever the padding. -/
private theorem laurent_shift_unfold {w g k n h : ℕ} (hh : guard w g k h = true) (hg : g + 2 ≤ w)
    (hk : k ≤ n) (hn : 0 < n) (odd : Bool) {z : ℂ} (hz : z ≠ 0) :
    laurent (entries w (2 * n - 1) (ofInt w (2 * n - 1) (shift w (n - k) (unfold w k h odd))))
        (n - 1 : ℕ) z =
      laurent (mirror (entries w k h) odd) ((entries w k h).length - 1 : ℕ) z := by
  obtain ⟨hgw, hlt, hb⟩ := guard_sound hh
  have hw : 1 ≤ w := by omega
  have hfit : ∀ x ∈ List.replicate (n - k) 0 ++ mirror (entries w k h) odd, Fits w x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rw [List.eq_of_mem_replicate hx]
      have : (0 : ℤ) < 2 ^ (w - 1) := by positivity
      exact ⟨by linarith, this⟩
    · exact fits_of_mem_mirror hg hb odd x hx
  have hlen : (List.replicate (n - k) 0 ++ mirror (entries w k h) odd).length ≤ 2 * n - 1 := by
    rw [List.length_append, List.length_replicate, length_mirror, length_entries]; omega
  rw [unfold_eq hw hlt, shift_eval, entries_ofInt_eval hw hlen hfit, laurent_append_zeros hz,
    laurent_pad hz, length_entries]
  rcases k with _ | k
  · simp [entries, mirror]
  · congr 1; push_cast; omega

/-- One sum-of-squares check bounds a trigonometric polynomial with both cosine and sine terms
from one side. The target is the pair of two-sided rows that `Packed.unfold` builds from the
guarded half rows `A` of the cosine coefficients and `B` of the sine coefficients, moved up to the
common centre `n - 1`; a pass gives `0 ≤ 2 kT ∑ (Aₖ cos (k u) + Bₖ sin (k u)) + kc`, a lower bound
for `kT > 0` and an upper bound for `kT < 0`. With `nb = 0` there are no sine terms, and then the
factor can be real (`m' = 0`). -/
theorem trig_sosCheck {w g gt gh na nb n m m' kH A B p q : ℕ} {kT kc : ℤ}
    (hA : guard w g na A = true) (hB : guard w g nb B = true) (hg : g + 2 ≤ w)
    (hna : na ≤ n) (hnb : nb ≤ n)
    (hc : sosCheck w gt gh n m m' kT kc kH
      (ofInt w (2 * n - 1) (shift w (n - na) (unfold w na A)))
      (ofInt w (2 * n - 1) (shift w (n - nb) (unfold w nb B true))) p q = true) (u : ℝ) :
    0 ≤ (kT : ℝ) * (2 * (∑ k ∈ range na, (entry w k A : ℝ) * Real.cos (k * u) +
      ∑ k ∈ range nb, (entry w k B : ℝ) * Real.sin (k * u))) + kc := by
  have hz := norm_exp_ofReal_mul_I u
  have hz0 : exp (u * I) ≠ 0 := exp_ne_zero _
  obtain ⟨hn, -, -⟩ := sosCheck_sound hc
  -- the check on the circle at `exp (u i)`, with the two unfolded rows read as cosines and sines
  have h := laurent_sosCheck hc hz
  rw [laurent_shift_unfold hA hg hna hn false hz0, laurent_shift_unfold hB hg hnb hn true hz0,
    laurent_mirror, laurent_mirror_odd, sum_getD_entries, sum_getD_entries] at h
  generalize ∑ k ∈ range na, (entry w k A : ℝ) * Real.cos (k * u) = X at h ⊢
  generalize ∑ k ∈ range nb, (entry w k B : ℝ) * Real.sin (k * u) = Y at h ⊢
  have e : ((2 * X : ℝ) : ℂ) - I * (2 * I * ((Y : ℝ) : ℂ)) = ((2 * (X + Y) : ℝ) : ℂ) := by
    push_cast
    linear_combination (-2 * (Y : ℂ)) * I_sq
  rw [e, ofReal_re] at h
  have : (0 : ℝ) ≤ kH * ‖laurent (entries w m p) 0 (exp (u * I)) +
      I * laurent (entries w m' q) 0 (exp (u * I))‖ ^ 2 := by positivity
  linarith

/-! ### Power series on an interval -/

/-- The value of `[R, 2 M, R]` at lane `1` on the circle: the affine function `2 M + 2 R cos u`. -/
private theorem laurent_affine (M R : ℤ) (u : ℝ) :
    laurent [R, 2 * M, R] 1 (exp (u * I)) = ((2 * M + 2 * R * Real.cos u : ℝ) : ℂ) := by
  have h := laurent_mirror [M, R] u
  simp only [List.length_cons, List.length_nil, Finset.sum_range_succ, Finset.sum_range_zero,
    List.getD_cons_zero, List.getD_cons_succ, Nat.cast_zero, zero_mul, Real.cos_zero, mul_one,
    Nat.cast_one, one_mul, zero_add, Nat.add_sub_cancel] at h
  rw [show [R, 2 * M, R] = mirror [M, R] from rfl]
  rw [h]
  push_cast
  ring

/-- A power series on an interval from one sum-of-squares check, after the substitution
`x = (M + R cos u) / D`. The target is the row that Horner's rule `Packed.horner` builds from the
guarded row `A` of the coefficients and the rows `[0, 2 D]` and `[R, 2 M, R]`, and a pass gives
`0 ≤ kT ∑ Aₖ (2 M + 2 R cos u) ^ k (2 D) ^ (n - 1 - k) + kc` for every `u`, which is
`kT (2 D) ^ (n - 1) ∑ Aₖ xᵏ + kc` at `x = (M + R cos u) / D`. The headroom
`n 2 ^ g K ^ (n - 1) < 2 ^ (w - 1)` keeps the composed row inside its lanes. -/
theorem power_sosCheck {w g gt gh n m m' kH K A p q : ℕ} {M R D kT kc : ℤ}
    (hA : guard w g n A = true) (hK : l1 [0, 2 * D] ≤ K ∧ l1 [R, 2 * M, R] ≤ K)
    (hroom : n * 2 ^ g * K ^ (n - 1) < 2 ^ (w - 1))
    (hc : sosCheck w gt gh n m m' kT kc kH
      (ofInt w (2 * n - 1) (horner w n (shift w 1 (2 * D))
        (Int.add R (Int.add (shift w 1 (2 * M)) (shift w 2 R))) A))
      (ofInt w (2 * n - 1) 0) p q = true) (u : ℝ) :
    0 ≤ (kT : ℝ) * ∑ k ∈ range n,
        (entry w k A : ℝ) * (2 * M + 2 * R * Real.cos u) ^ k * (2 * D) ^ (n - 1 - k) + kc := by
  have hz := norm_exp_ofReal_mul_I u
  have hz0 : exp (u * I) ≠ 0 := exp_ne_zero _
  obtain ⟨hn, -, -⟩ := sosCheck_sound hc
  obtain ⟨hgw, -, -⟩ := guard_sound hA
  have hw : 1 ≤ w := by omega
  have ea : shift w 1 (2 * D) = eval (2 ^ w) [0, 2 * D] := by
    rw [show ([0, 2 * D] : List ℤ) = List.replicate 1 0 ++ [2 * D] from rfl, ← shift_eval]
    simp [eval]
  have eb : Int.add R (Int.add (shift w 1 (2 * M)) (shift w 2 R)) = eval (2 ^ w) [R, 2 * M, R] := by
    simp only [shift, pow2_eq, Nat.mul_eq, Int.mul_def, Int.add_def, Int.ofNat_eq_natCast, eval]
    push_cast
    ring
  have hs : entries w (2 * n - 1) (ofInt w (2 * n - 1) 0) = List.replicate (2 * n - 1) 0 := by
    have := entries_ofInt_eval (w := w) (n := 2 * n - 1) hw (xs := []) (by simp) (by simp)
    simpa [eval] using this
  rw [ea, eb] at hc
  have h := laurent_sosCheck hc hz
  rw [entries_ofInt_horner (e := 2) (N := 2 * n - 1) hA (by simp) (by simp) (by omega) hK.1 hK.2
      hroom,
    laurent_append_zeros hz0, hs,
    laurent_zeros, mul_zero, sub_zero,
    show ((n - 1 : ℕ) : ℤ) = ((entries w n A).length : ℤ) - 1 by rw [length_entries]; omega,
    (laurent_compose hz0 _ _ _).1, laurent_affine,
    show laurent [0, 2 * D] 1 (exp (u * I)) = ((2 * D : ℝ) : ℂ) by
      rw [laurent_cons hz0, laurent_cons hz0, laurent_nil]; push_cast; norm_num,
    length_entries] at h
  have e : ∑ k ∈ range n, ((entries w n A).getD k 0 : ℂ) *
      ((2 * M + 2 * R * Real.cos u : ℝ) : ℂ) ^ k * ((2 * D : ℝ) : ℂ) ^ (n - 1 - k) =
        ((∑ k ∈ range n, (entry w k A : ℝ) * (2 * M + 2 * R * Real.cos u) ^ k *
          (2 * D) ^ (n - 1 - k) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [getD_entries (Finset.mem_range.mp hk)]
  rw [e, ofReal_re] at h
  have : (0 : ℝ) ≤ kH * ‖laurent (entries w m p) 0 (exp (u * I)) +
      I * laurent (entries w m' q) 0 (exp (u * I))‖ ^ 2 := by positivity
  linarith

/-! ### Derivatives -/

/-- Differentiating a cosine polynomial multiplies coefficient `k` by `-k` and turns it into a sine
polynomial. -/
theorem hasDerivAt_cos_sum (a : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u => ∑ k ∈ range n, a k * Real.cos (k * u))
      (-∑ k ∈ range n, k * a k * Real.sin (k * u)) u := by
  rw [← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun k _ => ?_
  have := ((hasDerivAt_id u).const_mul (k : ℝ)).cos.const_mul (a k)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- Differentiating a sine polynomial multiplies coefficient `k` by `k` and turns it into a cosine
polynomial. -/
theorem hasDerivAt_sin_sum (a : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    HasDerivAt (fun u => ∑ k ∈ range n, a k * Real.sin (k * u))
      (∑ k ∈ range n, k * a k * Real.cos (k * u)) u := by
  refine HasDerivAt.fun_sum fun k _ => ?_
  have := ((hasDerivAt_id u).const_mul (k : ℝ)).sin.const_mul (a k)
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

/-- The derivative of the cosine polynomial of a guarded packed row, with coefficients scaled by
`q`, is the sine polynomial of the row that `Packed.ramp` computes, when
`n * 2 ^ g ≤ 2 ^ (w - 1)`. -/
theorem hasDerivAt_cos_ramp {w g n a : Nat} (ha : guard w g n a = true)
    (hroom : n * 2 ^ g ≤ 2 ^ (w - 1)) (q u : ℝ) :
    HasDerivAt (fun u => ∑ k ∈ range n, q * entry w k a * Real.cos (k * u))
      (-∑ k ∈ range n, q * entry w k (ofInt w n (ramp w n a)) * Real.sin (k * u)) u := by
  have hd := hasDerivAt_cos_sum (fun k => q * entry w k a) n u
  convert hd using 3 with k hk
  have hk' := Finset.mem_range.mp hk
  have e := congrArg (fun l => l.getD k 0) (entries_ramp ha hroom)
  simp only [getD_entries hk', List.getD_eq_getElem?_getD, List.getElem?_mapIdx] at e
  rw [List.getElem?_eq_getElem (by rw [length_entries]; exact hk'), getElem_entries] at e
  simp only [Option.map_some, Option.getD_some] at e
  rw [e]
  push_cast
  ring

/-! ### The Hilbert transform -/

/-- The Hilbert transform of the trigonometric polynomial of a row centred at lane `c`: the
Fourier multiplier `-i sgn m` on the coefficient of `exp (m u i)`. `Packed.signs` computes the
signed row in the kernel. -/
noncomputable def hilbert (xs : List ℤ) (c : ℕ) (z : ℂ) : ℂ := -I * laurent (signRow c xs) c z

/-- The Hilbert transform takes `2 ∑ aₖ cos (k u)` to `2 ∑ aₖ sin (k u)`. -/
theorem hilbert_mirror (a : List ℤ) (u : ℝ) :
    hilbert (mirror a) (a.length - 1) (exp (u * I)) =
      ((2 * ∑ k ∈ range a.length, (a.getD k 0 : ℝ) * Real.sin (k * u) : ℝ) : ℂ) := by
  rw [hilbert, signRow_mirror, laurent_mirror_odd, ofReal_mul, ofReal_ofNat]
  linear_combination (-2 * ((∑ k ∈ range a.length, (a.getD k 0 : ℝ) * Real.sin (k * u) : ℝ) : ℂ)) *
    I_sq

/-- The Hilbert transform takes `2 i ∑ aₖ sin (k u)` to `-2 i ∑_{k ≥ 1} aₖ cos (k u)`. -/
theorem hilbert_mirror_odd (a : List ℤ) (u : ℝ) :
    hilbert (mirror a true) (a.length - 1) (exp (u * I)) =
      -I * ((2 * ∑ k ∈ range a.length, ((a.set 0 0).getD k 0 : ℝ) * Real.cos (k * u) : ℝ) : ℂ) := by
  have hl : (a.set 0 0).length = a.length := by simp
  rw [hilbert, signRow_mirror_odd, ← hl, laurent_mirror]

/-! ### Chebyshev series on an interval -/

/-- A Chebyshev series at `cos u` is the cosine polynomial with the same coefficients. -/
theorem chebyshev_cos (a : ℕ → ℝ) (n : ℕ) (u : ℝ) :
    ∑ k ∈ range n, a k * (Polynomial.Chebyshev.T ℝ k).eval (Real.cos u) =
      ∑ k ∈ range n, a k * Real.cos (k * u) := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.Chebyshev.T_real_cos]
  norm_cast

/-- A property of `(lo + hi) / 2 + (hi - lo) / 2 * cos u` for every `u` holds on `[lo, hi]`, so
bounds on the circle become bounds on an interval. -/
theorem forall_Icc_of_cos {lo hi : ℝ} {P : ℝ → Prop}
    (hP : ∀ u, P ((lo + hi) / 2 + (hi - lo) / 2 * Real.cos u)) : ∀ x ∈ Set.Icc lo hi, P x := by
  intro x ⟨hx1, hx2⟩
  rcases (hx1.trans hx2).lt_or_eq with hlt | heq
  -- pull `x` back to the circle: it is the point `u = arccos ((2 x - lo - hi) / (hi - lo))`
  · have hd : 0 < hi - lo := sub_pos.mpr hlt
    have t1 : -1 ≤ (2 * x - lo - hi) / (hi - lo) := by
      rw [le_div_iff₀ hd]; linarith
    have t2 : (2 * x - lo - hi) / (hi - lo) ≤ 1 := by
      rw [div_le_iff₀ hd]; linarith
    have := hP (Real.arccos ((2 * x - lo - hi) / (hi - lo)))
    have e : (lo + hi) / 2 + (hi - lo) / 2 * ((2 * x - lo - hi) / (hi - lo)) = x := by
      field_simp; ring
    rwa [Real.cos_arccos t1 t2, e] at this
  -- a one-point interval is the value at any `u`
  · subst heq
    have e : (lo + lo) / 2 + (lo - lo) / 2 * Real.cos 0 = x := by ring_nf; linarith
    exact e ▸ hP 0

/-- A property of a cosine polynomial at every `u` holds for the Chebyshev series with the same
coefficients at every point of `[-1, 1]`. This is the step from the circle to an interval that
`interval` takes for a Chebyshev series. -/
theorem forall_Icc_chebyshev {a : ℕ → ℝ} {n : ℕ} {P : ℝ → Prop}
    (h : ∀ u, P (∑ k ∈ range n, a k * Real.cos (k * u))) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1, P (∑ k ∈ range n, a k * (Polynomial.Chebyshev.T ℝ k).eval x) := by
  intro x hx
  have := h (Real.arccos x)
  rwa [← chebyshev_cos, Real.cos_arccos hx.1 hx.2] at this

end FloatLib.Numerics.Coeff
