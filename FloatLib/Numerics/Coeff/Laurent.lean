/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Packed.Horner
public import FloatLib.Numerics.Packed.Sos
public import Mathlib.Algebra.Polynomial.CoeffList
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic

/-!
# Laurent polynomials of integer rows

A row of integers `x₀, …, xₙ₋₁` together with a centre lane `c` stands for the Laurent polynomial
`∑ k, xₖ z ^ (k - c)`, and on the unit circle `z = exp (u i)` for the trigonometric polynomial
`∑ k, xₖ exp ((k - c) u i)`. A row of dyadic or decimal coefficients that share one exponent is
such an integer row times one rational scale, so everything here is stated for integers and the
scale multiplies through. A pair of rows `(t, s)` stands for the complex row `t - i s`, which is
how a polynomial with Gaussian-integer coefficients, or a Hermitian row with sine terms, is kept.

On the row `[3, -2, 1]` with centre `1`, the `l1` bound is `6`, attained at `z = -1`, where
`3 z⁻¹ - 2 + z = -6`.

## Main definitions

* `laurent xs c z`: the value `z ^ (-c) * aeval z (Polynomial.ofCoeffList xs)`. The polynomial
  part is Mathlib's `ofCoeffList`, the polynomial with coefficient list `xs`.

## Main statements

* `laurent_conv`: products of polynomials are Cauchy products of rows, which is the Kronecker
  identity `Packed.eval_conv` read at every integer (`ofCoeffList_conv`).
* `norm_laurent_le`: on the unit circle the value is bounded by the `l1` norm of the row.
* `laurent_reverse`, `conj_laurent` and `laurent_autocorr`: reversing a row substitutes `z⁻¹`
  for `z`, which on the circle is complex conjugation, so `h ⋆ reverse h` is `|h|²`;
  `laurent_normSq` says the same for a Gaussian-integer row `p + i q` and the two rows of
  `Packed.normSq`.
* `re_laurent_nonneg`: a pair of rows whose centre entry is at least the sum of the absolute values
  of all the other entries of both rows has a nonnegative real part on the circle.
* `laurent_compose`: the row of Horner's rule `Packed.compose` is the composed polynomial.
* `laurent_sosCheck`: a passing sum-of-squares check gives `kH |p + i q|² ≤ kT Re (t - i s) + kc`
  on the circle, and `normSq_sosCheck` applies it to the norm square of a polynomial.
* `norm_laurent_le_absSum` and `laurent_entries_mul`: one `absSum` bounds a packed row on the
  circle, and the Kronecker product multiplies two of them.

## Implementation notes

Everything is proved for finite integer rows, directly from the kernel programs' specifications,
so a theorem here is one rewrite away from a `decide +kernel` check. The bridge from rows to
polynomials is `Polynomial.funext`: two integer polynomials that agree at every integer are equal,
and at an integer `b` the Kronecker identities of `FloatLib.Numerics.Packed` are exactly such
agreements.

Coefficient-space bounds of this kind are the setting of the radii polynomial method and of
a posteriori Chebyshev and Fourier models in proof assistants. The certificate-based approach of
Bréhard, Mahboubi and Pous checks approximations in Coq the same way, with an untrusted oracle and a
trusted checker. RadiiPolynomial realizes sequence spaces on the circle in Lean, with a conjugate
reflection `conjReflL` and a lift `circleLift` to continuous functions on the circle; here
`conj_laurent` and `Coeff.Wiener.eval` do those two jobs. PlasmaLean checks Kronecker-packed balls
in Lean's kernel.
None of their code is copied: the proofs here are for the integer rows that the kernel programs
produce.

## References

* Florent Bréhard, Assia Mahboubi and Damien Pous, *A certificate-based approach to formally
  verified approximations*, ITP 2019, <https://doi.org/10.4230/LIPIcs.ITP.2019.8>, with the code
  at <https://github.com/damien-pous/approx-models>.
* Sarah Day, Jean-Philippe Lessard and Konstantin Mischaikow, *Validated continuation for
  equilibria of PDEs*, SIAM J. Numer. Anal. 45 (2007), 1398–1424,
  <https://doi.org/10.1137/050645968>, for the radii polynomial method.
* Fengyang Wang, Konstantin Mischaikow and Marcio Gameiro, *A Lean 4 Framework for the Radii
  Polynomial Method*, arXiv:2610.02335 (2026), <https://arxiv.org/abs/2610.02335>, with the code at
  <https://github.com/IlPreteRosso/RadiiPolynomial>.
* Siddhartha Gadgil, PlasmaLean, <https://github.com/siddhartha-gadgil/PlasmaLean>.

## Tags

Laurent polynomial, trigonometric polynomial, unit circle, Kronecker substitution
-/

@[expose] public section

namespace FloatLib.Numerics.Coeff

open Polynomial Complex ComplexConjugate
open FloatLib.Numerics.Packed

/-! ### Rows as polynomials

A row is the coefficient list, constant term first, of Mathlib's `Polynomial.ofCoeffList`. These
lemmas say how `ofCoeffList` meets the row operations of `FloatLib.Numerics.Packed`, and all of
them come from the Kronecker identities of the integer rows by `Polynomial.funext`: two integer
polynomials that agree at every integer are equal. -/

/-- `Packed.eval b` is the value of `ofCoeffList` at `b`. -/
theorem eval_ofCoeffList (b : ℤ) (xs : List ℤ) : (ofCoeffList xs).eval b = Packed.eval b xs := by
  induction xs with
  | nil => simp [Packed.eval]
  | cons x xs ih => simp [ofCoeffList_cons, Packed.eval, ih]

/-- The polynomial of a lanewise sum. -/
theorem ofCoeffList_add (xs ys : List ℤ) :
    ofCoeffList (add xs ys) = ofCoeffList xs + ofCoeffList ys :=
  Polynomial.funext fun b => by simp [eval_ofCoeffList, eval_add]

/-- The polynomial of a lanewise difference. -/
theorem ofCoeffList_sub (xs ys : List ℤ) :
    ofCoeffList (sub xs ys) = ofCoeffList xs - ofCoeffList ys :=
  Polynomial.funext fun b => by simp [eval_ofCoeffList, eval_sub]

/-- The polynomial of a Cauchy product is the product of the polynomials. -/
theorem ofCoeffList_conv (xs ys : List ℤ) :
    ofCoeffList (conv xs ys) = ofCoeffList xs * ofCoeffList ys :=
  Polynomial.funext fun b => by simp [eval_ofCoeffList, eval_conv]

/-- A row of zeros is the zero polynomial. -/
@[simp] theorem ofCoeffList_replicate_zero (k : ℕ) : ofCoeffList (List.replicate k (0 : ℤ)) = 0 :=
  Polynomial.funext fun b => by simp [eval_ofCoeffList]

/-- The polynomial of one row followed by another. -/
theorem ofCoeffList_append (xs ys : List ℤ) :
    ofCoeffList (xs ++ ys) = ofCoeffList xs + X ^ xs.length * ofCoeffList ys :=
  Polynomial.funext fun b => by simp [eval_ofCoeffList, eval_append]

private theorem aeval_cons (z : ℂ) (x : ℤ) (xs : List ℤ) :
    aeval z (ofCoeffList (x :: xs)) = x + z * aeval z (ofCoeffList xs) := by
  simp [ofCoeffList_cons]

private theorem aeval_append (z : ℂ) (xs ys : List ℤ) :
    aeval z (ofCoeffList (xs ++ ys)) =
      aeval z (ofCoeffList xs) + z ^ xs.length * aeval z (ofCoeffList ys) := by
  simp [ofCoeffList_append]

/-- The value of `ofCoeffList xs` at `z` as a sum. -/
theorem aeval_ofCoeffList (z : ℂ) (xs : List ℤ) :
    aeval z (ofCoeffList xs) = ∑ k ∈ Finset.range xs.length, (xs.getD k 0 : ℂ) * z ^ k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.length_cons, Finset.sum_range_succ', aeval_cons, ih, Finset.mul_sum, add_comm]
      simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring

/-! ### Values -/

/-- The value at `z` of the Laurent polynomial `∑ k, xs[k] * z ^ (k - c)` of an integer row whose
lane `c` holds the constant term. At `z = exp (u * I)` it is the trigonometric polynomial
`∑ k, xs[k] * exp ((k - c) * u * I)`. -/
noncomputable def laurent (xs : List ℤ) (c : ℤ) (z : ℂ) : ℂ :=
  z ^ (-c) * aeval z (ofCoeffList xs)

/-- `laurent` adds up. -/
theorem laurent_add (xs ys : List ℤ) (c : ℤ) (z : ℂ) :
    laurent (add xs ys) c z = laurent xs c z + laurent ys c z := by
  simp [laurent, ofCoeffList_add, mul_add]

/-- `laurent` commutes with scaling. -/
theorem laurent_smul (a : ℤ) (xs : List ℤ) (c : ℤ) (z : ℂ) :
    laurent (smul a xs) c z = a * laurent xs c z := by
  simp [laurent, Packed.smul]; ring

/-- `laurent` takes differences to differences. -/
theorem laurent_sub (xs ys : List ℤ) (c : ℤ) (z : ℂ) :
    laurent (sub xs ys) c z = laurent xs c z - laurent ys c z := by
  simp [laurent, ofCoeffList_sub, mul_sub]

/-- The Laurent polynomial of a Cauchy product is the product, with the centres added. -/
theorem laurent_conv {z : ℂ} (hz : z ≠ 0) (xs ys : List ℤ) (c d : ℤ) :
    laurent (conv xs ys) (c + d) z = laurent xs c z * laurent ys d z := by
  simp only [laurent, ofCoeffList_conv, map_mul, neg_add, zpow_add₀ hz]
  ring

/-- A row whose only nonzero entry is `a`, in lane `c`, stands for the constant `a`. -/
theorem laurent_single {z : ℂ} (hz : z ≠ 0) (c : ℕ) (a : ℤ) :
    laurent (List.replicate c 0 ++ [a]) c z = a := by
  rw [laurent, aeval_append, ofCoeffList_replicate_zero, map_zero, aeval_cons,
    List.length_replicate,
    zpow_neg, zpow_natCast]
  simp [hz]

/-- In a normed ring, the polynomial of a row at a point of norm at most one is at most the `l1`
norm of the row. -/
theorem norm_aeval_ofCoeffList_le {A : Type*} [NormedRing A] [NormOneClass A] {z : A}
    (hz : ‖z‖ ≤ 1) (xs : List ℤ) : ‖aeval z (ofCoeffList xs)‖ ≤ l1 xs := by
  induction xs with
  | nil => simp [l1]
  | cons x xs ih =>
      rw [ofCoeffList_cons, map_add, map_mul, aeval_C, aeval_X, algebraMap_int_eq, eq_intCast,
        l1_cons, Nat.cast_add]
      have hx : ‖(x : A)‖ ≤ x.natAbs := by
        obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg x
        · simpa using Nat.norm_cast_le (α := A) m
        · simpa using Nat.norm_cast_le (α := A) m
      calc ‖(x : A) + z * aeval z (ofCoeffList xs)‖ ≤
            ‖(x : A)‖ + ‖z‖ * ‖aeval z (ofCoeffList xs)‖ :=
            (norm_add_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        _ ≤ x.natAbs + 1 * l1 xs := by gcongr
        _ = x.natAbs + l1 xs := by rw [one_mul]

/-- On the unit circle the value of a row is at most its `l1` norm. -/
theorem norm_laurent_le {z : ℂ} (hz : ‖z‖ = 1) (xs : List ℤ) (c : ℤ) :
    ‖laurent xs c z‖ ≤ l1 xs := by
  rw [laurent, norm_mul, norm_zpow, hz, one_zpow, one_mul]
  exact norm_aeval_ofCoeffList_le hz.le xs

/-- The empty row stands for zero. -/
@[simp] theorem laurent_nil (c : ℤ) (z : ℂ) : laurent [] c z = 0 := by simp [laurent]

/-- The value of one row followed by another, which is centred `xs.length` lanes lower. -/
theorem laurent_append {z : ℂ} (hz : z ≠ 0) (xs ys : List ℤ) (c : ℤ) :
    laurent (xs ++ ys) c z = laurent xs c z + laurent ys (c - xs.length) z := by
  rw [laurent, laurent, laurent, aeval_append, show -(c - (xs.length : ℤ)) = -c + xs.length by ring,
    zpow_add₀ hz, zpow_natCast]
  ring

/-- The value of a row that starts with `x`. -/
theorem laurent_cons {z : ℂ} (hz : z ≠ 0) (x : ℤ) (xs : List ℤ) (c : ℤ) :
    laurent (x :: xs) c z = x * z ^ (-c) + laurent xs (c - 1) z := by
  rw [laurent, laurent, aeval_cons, show -(c - 1) = -c + 1 by ring, zpow_add₀ hz, zpow_one]
  ring

/-- Reversing a row substitutes `z⁻¹` for `z` and reflects the centre. -/
theorem laurent_reverse {z : ℂ} (hz : z ≠ 0) (xs : List ℤ) (c : ℤ) :
    laurent xs.reverse c z = laurent xs (xs.length - 1 - c) z⁻¹ := by
  induction xs generalizing c with
  | nil => simp
  | cons x xs ih =>
      rw [List.reverse_cons, laurent_append hz, ih, List.length_reverse, laurent_cons hz,
        laurent_nil, laurent_cons (inv_ne_zero hz), List.length_cons, inv_zpow', neg_neg]
      push_cast
      ring_nf

/-- On the unit circle, conjugation substitutes `z⁻¹` for `z`. -/
theorem conj_laurent {z : ℂ} (hz : ‖z‖ = 1) (xs : List ℤ) (c : ℤ) :
    conj (laurent xs c z) = laurent xs c z⁻¹ := by
  rw [laurent, laurent, map_mul, map_zpow₀, ← inv_eq_conj hz, aeval_ofCoeffList, aeval_ofCoeffList,
    map_sum]
  simp [map_mul, map_pow, inv_eq_conj hz]

/-- The autocorrelation `h ⋆ reverse h` is `|h|²` on the unit circle. -/
theorem laurent_autocorr {z : ℂ} (hz : ‖z‖ = 1) (h : List ℤ) :
    laurent (conv h h.reverse) (h.length - 1 : ℕ) z = (‖laurent h 0 z‖ ^ 2 : ℝ) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  cases h with
  | nil => simp [conv, laurent]
  | cons x xs =>
      have := laurent_conv hz0 (x :: xs) (x :: xs).reverse 0 ((x :: xs).length - 1 : ℕ)
      rw [zero_add] at this
      have hc : ((x :: xs).length : ℤ) - 1 - ((x :: xs).length - 1 : ℕ) = 0 := by simp
      rw [this, laurent_reverse hz0, hc, ← conj_laurent hz, mul_conj']
      simp

/-- A row of zeros stands for zero, whatever its centre. -/
@[simp] theorem laurent_zeros (k : ℕ) (c : ℤ) (z : ℂ) : laurent (List.replicate k 0) c z = 0 := by
  simp [laurent]

/-- Zeros in front of a row move its centre up by as many lanes. -/
theorem laurent_pad {z : ℂ} (hz : z ≠ 0) (k : ℕ) (xs : List ℤ) (c : ℤ) :
    laurent (List.replicate k 0 ++ xs) c z = laurent xs (c - k) z := by
  rw [laurent_append hz, laurent_zeros, zero_add, List.length_replicate]

/-- Zeros after a row change nothing. -/
theorem laurent_append_zeros {z : ℂ} (hz : z ≠ 0) (xs : List ℤ) (k : ℕ) (c : ℤ) :
    laurent (xs ++ List.replicate k 0) c z = laurent xs c z := by
  rw [laurent_append hz, laurent_zeros, add_zero]

/-- On the unit circle the reversed row, centred at its last lane, is the conjugate. -/
theorem laurent_reverse_conj {z : ℂ} (hz : ‖z‖ = 1) (P : List ℤ) :
    laurent P.reverse ((P.length : ℤ) - 1) z = conj (laurent P 0 z) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  rw [laurent_reverse hz0, conj_laurent hz, show (P.length : ℤ) - 1 - ((P.length : ℤ) - 1) = 0 by
    ring]

private theorem laurent_split {z : ℂ} (hz : z ≠ 0) (A B : List ℤ) (x : ℤ) :
    laurent (A ++ x :: B) A.length z = x + laurent (A ++ 0 :: B) A.length z := by
  rw [laurent_append hz, laurent_append hz, sub_self, laurent_cons hz, laurent_cons hz]
  simp only [neg_zero, zpow_zero, mul_one, Int.cast_zero, zero_add]
  ring

/-- The real part of a row on the unit circle is at least twice its centre entry minus its `l1`
norm: the centre counts once, every other entry at most its absolute value. -/
private theorem re_laurent_ge {z : ℂ} (hz : ‖z‖ = 1) (e : List ℤ) (c : ℕ) :
    2 * (e.getD c 0 : ℝ) - l1 e ≤ (laurent e c z).re := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  by_cases hc : c < e.length
  -- split off the centre `x`: the rest is bounded by its `l1` norm, `l1 e - |x|`
  · obtain ⟨A, x, B, rfl, hA⟩ : ∃ A x B, e = A ++ x :: B ∧ A.length = c :=
      ⟨e.take c, e[c], e.drop (c + 1),
        by rw [← List.drop_eq_getElem_cons hc, List.take_append_drop], List.length_take_of_le hc.le⟩
    subst hA
    have hx : (A ++ x :: B).getD A.length 0 = x := by simp
    have hl1 : (l1 (A ++ x :: B) : ℤ) = l1 (A ++ 0 :: B) + |x| := by
      simp [l1, List.map_append, List.sum_append]; ring
    have hb := norm_laurent_le hz (A ++ 0 :: B) A.length
    have hre := Complex.abs_re_le_norm (laurent (A ++ 0 :: B) A.length z)
    rw [hx, laurent_split hz0, add_re, intCast_re]
    have h' : ((l1 (A ++ x :: B) : ℤ) : ℝ) = l1 (A ++ 0 :: B) + |(x : ℝ)| := by
      exact_mod_cast hl1
    push_cast at h'
    have := abs_le.mp hre
    have := le_abs_self (x : ℝ)
    linarith
  -- a centre beyond the row is a zero entry, and the bound is `-l1 e`
  · have hx : e.getD c 0 = 0 := by simp [hc]
    have hb := norm_laurent_le hz e c
    have hre := Complex.abs_re_le_norm (laurent e c z)
    rw [hx, Int.cast_zero, mul_zero, zero_sub]
    have := abs_le.mp hre
    linarith

/-- The certificate for a nonnegative real part. The pair of rows `(e, f)` stands for
`e - i f`; if the centre entry `e[c]` is at least the sum of the absolute values of all the other
entries of both rows, `l1 e + l1 f ≤ 2 e[c]`, then the real part is nonnegative on the whole unit
circle. With `f = []` this is the familiar diagonal dominance of a real row. -/
theorem re_laurent_nonneg {z : ℂ} (hz : ‖z‖ = 1) {e f : List ℤ} {c : ℕ}
    (h : ((l1 e + l1 f : ℕ) : ℤ) ≤ 2 * e.getD c 0) :
    0 ≤ (laurent e c z - I * laurent f c z).re := by
  have he := re_laurent_ge hz e c
  have hf := norm_laurent_le hz f c
  have him := abs_le.mp (Complex.abs_im_le_norm (laurent f c z))
  have h' : ((l1 e : ℝ) + l1 f) ≤ 2 * (e.getD c 0 : ℝ) := by exact_mod_cast h
  rw [sub_re, I_mul_re]
  linarith

/-! ### Squares of Gaussian-integer rows -/

/-- The value of `normSq`: on the unit circle its two rows, read as `t - i s` at centre `n - 1`,
are `|P + i Q|²`. -/
theorem laurent_normSq {z : ℂ} (hz : ‖z‖ = 1) {n : ℕ} (hn : 0 < n) {P Q : List ℤ}
    (hP : P.length ≤ n) (hQ : Q.length ≤ n) :
    laurent (Packed.normSq n P Q).1 (n - 1 : ℕ) z -
        I * laurent (Packed.normSq n P Q).2 (n - 1 : ℕ) z =
      (‖laurent P 0 z + I * laurent Q 0 z‖ ^ 2 : ℝ) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have cP : ((n - 1 : ℕ) : ℤ) - ((n - P.length : ℕ) : ℤ) = (P.length : ℤ) - 1 := by omega
  have cQ : ((n - 1 : ℕ) : ℤ) - ((n - Q.length : ℕ) : ℤ) = (Q.length : ℤ) - 1 := by omega
  -- each of the four products is a value times a conjugate, because reversal is conjugation
  have pp : laurent (conv P P.reverse) ((P.length : ℤ) - 1) z =
      laurent P 0 z * conj (laurent P 0 z) := by
    rw [show (P.length : ℤ) - 1 = 0 + ((P.length : ℤ) - 1) by ring, laurent_conv hz0,
      laurent_reverse_conj hz]
  have qq : laurent (conv Q Q.reverse) ((Q.length : ℤ) - 1) z =
      laurent Q 0 z * conj (laurent Q 0 z) := by
    rw [show (Q.length : ℤ) - 1 = 0 + ((Q.length : ℤ) - 1) by ring, laurent_conv hz0,
      laurent_reverse_conj hz]
  have qp : laurent (conv Q.reverse P) ((Q.length : ℤ) - 1) z =
      conj (laurent Q 0 z) * laurent P 0 z := by
    rw [show (Q.length : ℤ) - 1 = ((Q.length : ℤ) - 1) + 0 by ring, laurent_conv hz0,
      laurent_reverse_conj hz]
  have pq : laurent (conv P.reverse Q) ((P.length : ℤ) - 1) z =
      conj (laurent P 0 z) * laurent Q 0 z := by
    rw [show (P.length : ℤ) - 1 = ((P.length : ℤ) - 1) + 0 by ring, laurent_conv hz0,
      laurent_reverse_conj hz]
  -- then `(P + i Q) conj (P + i Q) = P P̄ + Q Q̄ - i (Q̄ P - P̄ Q)` is the convention `t - i s`
  simp only [Packed.normSq, laurent_add, laurent_sub, laurent_pad hz0, cP, cQ, pp, qq, qp, pq]
  rw [Complex.ofReal_pow, ← mul_conj', map_add, map_mul, conj_I]
  linear_combination (laurent Q 0 z * conj (laurent Q 0 z)) * I_sq

/-! ### Horner's rule on the circle -/

/-- The value of the homogeneous form that `Packed.compose` builds: for rows `a` and `b` centred at
lane `1`, the composed row centred at `cs.length - 1` is `∑ k, cs[k] b(z) ^ k a(z) ^ (len - 1 - k)`,
and the power is `a(z) ^ len`. -/
theorem laurent_compose {z : ℂ} (hz : z ≠ 0) (a b : List ℤ) :
    ∀ cs : List ℤ,
      laurent (compose a b cs).1 ((cs.length : ℤ) - 1) z =
          ∑ k ∈ Finset.range cs.length,
            (cs.getD k 0 : ℂ) * laurent b 1 z ^ k * laurent a 1 z ^ (cs.length - 1 - k) ∧
        laurent (compose a b cs).2 cs.length z = laurent a 1 z ^ cs.length
  | [] => by simp [laurent, ofCoeffList_cons]
  | c :: cs => by
      obtain ⟨ih1, ih2⟩ := laurent_compose hz a b cs
      have hconv := laurent_conv hz (compose a b cs).1 b ((cs.length : ℤ) - 1) 1
      rw [sub_add_cancel] at hconv
      refine ⟨?_, ?_⟩
      · rw [compose_cons, List.length_cons, Nat.cast_succ, add_sub_cancel_right, laurent_add,
          laurent_smul, ih2, hconv, ih1, Finset.sum_range_succ', Finset.sum_mul]
        simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one,
          Nat.add_sub_cancel, Nat.sub_zero]
        congr 1
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [show cs.length - (k + 1) = cs.length - 1 - k by omega, pow_succ]
        ring
      · rw [compose_cons, List.length_cons, Nat.cast_succ, laurent_conv hz, ih2, pow_succ]

/-! ### Packed checks on the circle -/

/-- One `absSum` bounds a guarded packed row on the unit circle, when `n * 2 ^ g < 2 ^ (w - 1)`. -/
theorem norm_laurent_le_absSum {w g n u : Nat} (hu : guard w g n u = true)
    (hroom : n * 2 ^ g < 2 ^ (w - 1)) {z : ℂ} (hz : ‖z‖ = 1) (c : ℤ) :
    ‖laurent (entries w n u) c z‖ ≤ absSum w n (toInt w n u) := by
  rw [absSum_toInt hu hroom]
  exact norm_laurent_le hz _ c

/-- The Kronecker product of two guarded packed rows is the product of their Laurent polynomials,
under the headroom condition of `Packed.entries_mul`. -/
theorem laurent_entries_mul {w gx gy n m u v : Nat} (hu : guard w gx n u = true)
    (hv : guard w gy m v = true) (hroom : n * 2 ^ gx * (m * 2 ^ gy) < 2 ^ (w - 1)) (hn : 0 < n)
    (hm : 0 < m) {z : ℂ} (hz : z ≠ 0) (c d : ℤ) :
    laurent (entries w (n + m - 1) (ofInt w (n + m - 1) (toInt w n u * toInt w m v))) (c + d) z =
      laurent (entries w n u) c z * laurent (entries w m v) d z := by
  rw [entries_mul hu hv hroom hn hm, laurent_conv hz]

/-- The value of the rows that `sosCheck` tests: `kT (T - i S) + kc - kH |P + i Q|²` on the unit
circle. -/
theorem laurent_sosDefect {z : ℂ} (hz : ‖z‖ = 1) {n : ℕ} (hn : 0 < n) (kT kc : ℤ) (kH : ℕ)
    (T S : List ℤ) {P Q : List ℤ} (hP : P.length ≤ n) (hQ : Q.length ≤ n) :
    laurent (sosDefect n kT kc kH T S P Q).1 (n - 1 : ℕ) z -
        I * laurent (sosDefect n kT kc kH T S P Q).2 (n - 1 : ℕ) z =
      kT * (laurent T (n - 1 : ℕ) z - I * laurent S (n - 1 : ℕ) z) + kc -
        kH * (‖laurent P 0 z + I * laurent Q 0 z‖ ^ 2 : ℝ) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have h := laurent_normSq hz hn hP hQ
  simp only [sosDefect, laurent_sub, laurent_add, laurent_smul, laurent_single hz0]
  rw [← h]
  push_cast
  ring

/-- A passing sum-of-squares check bounds the target on the unit circle:
`kH |p(z) + i q(z)|² ≤ kT Re (t(z) - i s(z)) + kc` for the factor `(p, q)` and the target `(t, s)`
centred at lane `n - 1`. -/
theorem laurent_sosCheck {w gt gh n m m' kH t s p q : Nat} {kT kc : ℤ}
    (hc : sosCheck w gt gh n m m' kT kc kH t s p q = true) {z : ℂ} (hz : ‖z‖ = 1) :
    kH * ‖laurent (entries w m p) 0 z + I * laurent (entries w m' q) 0 z‖ ^ 2 ≤
      kT * (laurent (entries w (2 * n - 1) t) (n - 1 : ℕ) z -
        I * laurent (entries w (2 * n - 1) s) (n - 1 : ℕ) z).re + kc := by
  obtain ⟨hn, hm, hm', hcert⟩ := sosCheck_sound hc
  have h0 := re_laurent_nonneg hz hcert
  rw [laurent_sosDefect hz hn kT kc kH _ _ (by rw [length_entries]; exact hm)
    (by rw [length_entries]; exact hm')] at h0
  simp only [sub_re, add_re, mul_re, intCast_re, intCast_im, zero_mul, sub_zero, natCast_re,
    natCast_im, ofReal_re, ofReal_im, mul_zero] at h0 ⊢
  linarith

/-- The norm square of a Gaussian-integer polynomial from one sum-of-squares check: for guarded
rows `A` and `B` with `((na + nb) 2 ^ g)² < 2 ^ (w - 1)`, a check on the target `|A + i B|²` that
`sqRe` and `sqIm` compute gives `0 ≤ kT |A(z) + i B(z)|² + kc` on the unit circle. -/
theorem normSq_sosCheck {w g gt gh na nb n m m' kH A B p q : Nat} {kT kc : ℤ}
    (hA : guard w g na A = true) (hB : guard w g nb B = true) (hna : na ≤ n) (hnb : nb ≤ n)
    (hroom : (na + nb) * 2 ^ g * ((na + nb) * 2 ^ g) < 2 ^ (w - 1))
    (hc : sosCheck w gt gh n m m' kT kc kH (ofInt w (2 * n - 1) (sqRe w n na nb A B))
      (ofInt w (2 * n - 1) (sqIm w n na nb A B)) p q = true) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ (kT : ℝ) * ‖laurent (entries w na A) 0 z + I * laurent (entries w nb B) 0 z‖ ^ 2 + kc := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  obtain ⟨hn, -, -⟩ := (sosCheck_sound hc)
  obtain ⟨hgw, hA', hAb⟩ := guard_sound hA
  obtain ⟨-, hB', hBb⟩ := guard_sound hB
  have hw : 1 ≤ w := by omega
  have hl := length_normSq_le hn (P := entries w na A) (Q := entries w nb B)
    (by rw [length_entries]; exact hna) (by rw [length_entries]; exact hnb)
  have h1 := l1_normSq_le hAb hBb n
  rw [length_entries, length_entries] at h1
  have h := laurent_sosCheck hc hz
  rw [sqRe_eq hw hA' hB', sqIm_eq hw hA' hB',
    entries_ofInt_eval hw hl.1 (fits_of_l1_lt (by omega)),
    entries_ofInt_eval hw hl.2 (fits_of_l1_lt (by omega)), laurent_append_zeros hz0,
    laurent_append_zeros hz0, laurent_normSq hz hn (by rw [length_entries]; exact hna)
      (by rw [length_entries]; exact hnb), ofReal_re] at h
  have hp : (0 : ℝ) ≤
      kH * ‖laurent (entries w m p) 0 z + I * laurent (entries w m' q) 0 z‖ ^ 2 := by
    positivity
  linarith

end FloatLib.Numerics.Coeff
