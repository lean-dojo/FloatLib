/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Coeff.Laurent
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Wiener algebra

An absolutely summable two-sided sequence `c : ℤ → ℂ` stands for the continuous function
`f u = ∑ n, c n * exp (n u i)` on the circle. These sequences form the Wiener algebra `Wiener`:
the norm is `‖c‖ = ∑ n, ‖c n‖`, the product is convolution, `(c * d) n = ∑ k, c k * d (n - k)`,
and evaluation at a point is an algebra map whose value is at most the norm. So a bound on a few
coefficients and a norm bound on the rest bound the function everywhere, and products of functions
are products of sequences.

For example, `ofRow [1, 2, 1] 1` is `exp (-u i) + 2 + exp (u i) = 2 + 2 cos u`, of norm `4`, the
value at `u = 0`.

## Main definitions

* `Wiener`: `ℓ¹(ℤ)`, Mathlib's `lp (fun _ : ℤ => ℂ) 1`, with the convolution product. It is a
  complete normed commutative `ℂ`-algebra with `‖1‖ = 1`, so Mathlib's results on Banach algebras,
  such as the Neumann series, apply to it.
* `Wiener.single n c`: the sequence that is `c` at `n`, the function `c * exp (n u i)`.
* `Wiener.eval u`: evaluation at the point `u` of the circle, as an algebra map to `ℂ`.
* `Wiener.ofRow xs c`: the element of a finite integer row with centre lane `c`, the data of
  `Coeff.laurent`.

## Main statements

* `Wiener.norm_eval_le` and `Wiener.continuous_eval_apply`: an element is bounded by its norm on
  the circle, and it is a continuous function there.
* `Wiener.eval_ofRow`: the value of a row at `u` is `laurent xs c (exp (u i))`.
* `Wiener.ofRow_conv` and `Wiener.ofRow_sub`: Cauchy products and differences of rows are
  products and differences in the algebra.
* `Wiener.norm_ofRow_le`: the norm of a row is at most `l1 xs`, which one `Packed.absSum`
  computes.

## Implementation notes

`Wiener` is a type synonym rather than an abbreviation, so that the pointwise product and the
pointwise `star` of `lp` do not apply to it. Its ring structure is built by hand: convolution is
summable because the double series `∑ k, ∑ n, ‖f k‖ ‖g (n - k)‖` is, and the change of index
`(n, k) ↦ (k, n - k)` turns the sum of a convolution into the product of two sums. Wiener's lemma,
that an element with no zero on the circle is a unit, is the qualitative fact behind
`Coeff.inv_of_defect`; the defect version says the same thing with a number attached, which is what
a certificate needs.

This approach follows PlasmaLean, which constructs the same `ℓ¹(ℤ)` ring for its KAM
certificates (`ConvAlgebra`).
RadiiPolynomial realizes weighted sequence spaces on the circle with the same product rule. The
proofs here are our own.

## References

* Norbert Wiener, *Tauberian theorems*, Ann. of Math. 33 (1932), 1–100,
  <https://doi.org/10.2307/1968102>.
* Yitzhak Katznelson, *An Introduction to Harmonic Analysis*, third edition, Cambridge University
  Press (2004), <https://doi.org/10.1017/CBO9781139165372>, for the algebra of absolutely
  convergent Fourier series and Wiener's lemma.
* Siddhartha Gadgil, PlasmaLean, `PlasmaLean/Certificates/ConvAlgebra.lean`,
  <https://github.com/siddhartha-gadgil/PlasmaLean>.
* Fengyang Wang, Konstantin Mischaikow and Marcio Gameiro, *A Lean 4 Framework for the Radii
  Polynomial Method*, arXiv:2610.02335 (2026), <https://arxiv.org/abs/2610.02335>, with the code at
  <https://github.com/IlPreteRosso/RadiiPolynomial>.

## Tags

Wiener algebra, ℓ¹, convolution, Banach algebra, Fourier series
-/

@[expose] public section

namespace FloatLib.Numerics.Coeff

open Complex Polynomial

/-- The Wiener algebra: absolutely summable sequences `c : ℤ → ℂ`, standing for the functions
`∑ n, c n * exp (n * u * I)` on the circle, with the `ℓ¹` norm and the convolution product. -/
def Wiener : Type := lp (fun _ : ℤ => ℂ) 1

namespace Wiener

noncomputable instance : NormedAddCommGroup Wiener :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : ℤ => ℂ) 1))

noncomputable instance : NormedSpace ℂ Wiener :=
  inferInstanceAs (NormedSpace ℂ (lp (fun _ : ℤ => ℂ) 1))

instance : CompleteSpace Wiener := inferInstanceAs (CompleteSpace (lp (fun _ : ℤ => ℂ) 1))

instance : CoeFun Wiener fun _ => ℤ → ℂ := ⟨fun (f : lp (fun _ : ℤ => ℂ) 1) => ⇑f⟩

/-- Two elements with the same coefficients are equal. -/
@[ext] theorem ext {f g : Wiener} (h : ∀ n, f n = g n) : f = g :=
  lp.ext (funext h)

/-- The coefficients of a sum. -/
@[simp] theorem add_apply (f g : Wiener) (n : ℤ) : (f + g) n = f n + g n := rfl

/-- The coefficients of a difference. -/
@[simp] theorem sub_apply (f g : Wiener) (n : ℤ) : (f - g) n = f n - g n := rfl

/-- The coefficients of zero. -/
@[simp] theorem zero_apply (n : ℤ) : (0 : Wiener) n = 0 := rfl

/-- The coefficients of a multiple. -/
@[simp] theorem smul_apply (c : ℂ) (f : Wiener) (n : ℤ) : (c • f) n = c * f n := rfl

/-- The norm is the sum of the absolute values of the coefficients. -/
theorem norm_def (f : Wiener) : ‖f‖ = ∑' n, ‖f n‖ := by
  have := lp.norm_eq_tsum_rpow (E := fun _ : ℤ => ℂ) (p := 1) (by norm_num) f
  simp only [ENNReal.toReal_one, Real.rpow_one, ne_eq, one_ne_zero, not_false_eq_true,
    div_self] at this
  exact this

/-- The coefficients of an element have summable absolute values. -/
theorem summable_norm (f : Wiener) : Summable fun n => ‖f n‖ := by
  have := (lp.memℓp (E := fun _ : ℤ => ℂ) (p := 1) f).summable (by norm_num)
  simp only [ENNReal.toReal_one, Real.rpow_one] at this
  exact this

/-- A coefficient is at most the norm. -/
theorem norm_apply_le (f : Wiener) (n : ℤ) : ‖f n‖ ≤ ‖f‖ :=
  lp.norm_apply_le_norm (E := fun _ : ℤ => ℂ) one_ne_zero f n

/-! ### Convolution -/

/-- The pairs `(n, k)` of a convolution are the pairs `(k, n - k)` of a product. -/
private def convEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun q := (q.1 + q.2, q.1)
  invFun p := (p.2, p.1 - p.2)
  left_inv q := by simp
  right_inv p := by simp

private theorem summable_conv_norm {R : Type*} [NormedRing R] {f g : ℤ → R}
    (hf : Summable fun k => ‖f k‖) (hg : Summable fun k => ‖g k‖) :
    Summable fun p : ℤ × ℤ => ‖f p.2‖ * ‖g (p.1 - p.2)‖ := by
  rw [← convEquiv.summable_iff]
  convert hf.mul_of_nonneg hg (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) using 2 with q
  simp [convEquiv]

/-- The sum of a convolution is the product of the sums. -/
private theorem tsum_conv {R : Type*} [NormedRing R] [CompleteSpace R] {f g : ℤ → R}
    (hf : Summable fun k => ‖f k‖) (hg : Summable fun k => ‖g k‖) :
    ∑' n, ∑' k, f k * g (n - k) = (∑' k, f k) * ∑' m, g m := by
  have hs : Summable fun p : ℤ × ℤ => f p.2 * g (p.1 - p.2) :=
    .of_norm_bounded (summable_conv_norm hf hg) fun _ => norm_mul_le _ _
  rw [tsum_mul_tsum_of_summable_norm hf hg, ← hs.tsum_prod' fun n => hs.prod_factor n,
    ← convEquiv.tsum_eq]
  simp [convEquiv]

private theorem summable_mul_shift (f g : Wiener) (n : ℤ) :
    Summable fun k => ‖f k * g (n - k)‖ :=
  .of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun _ => (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_apply_le g _)
      (norm_nonneg _)))
    ((summable_norm f).mul_right ‖g‖)

/-- The convolution of two elements has summable absolute values, so it is an element. -/
theorem summable_conv (f g : Wiener) :
    Summable fun n => ‖∑' k, f k * g (n - k)‖ := by
  refine .of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun n => (norm_tsum_le_tsum_norm (summable_mul_shift f g n)).trans
      (Summable.tsum_le_tsum (fun k => norm_mul_le _ _) (summable_mul_shift f g n)
        ((summable_conv_norm (summable_norm f) (summable_norm g)).prod_factor n)))
    (summable_conv_norm (summable_norm f) (summable_norm g)).prod

noncomputable instance : Mul Wiener :=
  ⟨fun f g => ⟨fun n => ∑' k, f k * g (n - k),
    by exact memℓp_gen (by simpa using summable_conv f g)⟩⟩

/-- The coefficients of a product are the convolution of the coefficients. -/
theorem mul_apply (f g : Wiener) (n : ℤ) : (f * g) n = ∑' k, f k * g (n - k) := rfl

/-- The sequence that is `c` at `n` and zero elsewhere, the function `c * exp (n * u * I)`. -/
noncomputable def single (n : ℤ) (c : ℂ) : Wiener := lp.single 1 n c

/-- The coefficients of `single n c`. -/
theorem single_apply (n : ℤ) (c : ℂ) (m : ℤ) : single n c m = if m = n then c else 0 := by
  simp [single, Pi.single_apply]

/-- The norm of `single n c` is `‖c‖`. -/
@[simp] theorem norm_single (n : ℤ) (c : ℂ) : ‖single n c‖ = ‖c‖ :=
  lp.norm_single (E := fun _ : ℤ => ℂ) (by norm_num) n c

noncomputable instance : One Wiener := ⟨single 0 1⟩

/-- The unit is the constant function `1`, the sequence that is `1` at `0`. -/
theorem one_def : (1 : Wiener) = single 0 1 := rfl

private theorem single_mul (n : ℤ) (c : ℂ) (g : Wiener) (m : ℤ) :
    (single n c * g) m = c * g (m - n) := by
  rw [mul_apply, tsum_eq_single n fun k hk => by simp [single_apply, hk]]
  simp [single_apply]

private theorem mul_comm' (f g : Wiener) : f * g = g * f := by
  ext n
  rw [mul_apply, mul_apply, ← (Equiv.subLeft n).tsum_eq]
  simp [mul_comm]

private theorem mul_add' (f g h : Wiener) : f * (g + h) = f * g + f * h := by
  ext n
  simp only [mul_apply, add_apply, mul_add]
  exact (Summable.of_norm (summable_mul_shift f g n)).tsum_add
    (Summable.of_norm (summable_mul_shift f h n))

private theorem mul_assoc' (f g h : Wiener) : f * g * h = f * (g * h) := by
  ext n
  simp only [mul_apply]
  have e1 : ∀ j, (∑' k, f k * g (j - k)) * h (n - j) = ∑' k, f k * g (j - k) * h (n - j) :=
    fun j => tsum_mul_right.symm
  have e2 : ∀ k, f k * ∑' m, g m * h (n - k - m) = ∑' j, f k * g (j - k) * h (n - j) := by
    intro k
    rw [← tsum_mul_left, ← (Equiv.subRight k).tsum_eq]
    refine tsum_congr fun j => ?_
    simp only [Equiv.subRight_apply, sub_sub_sub_cancel_right]
    ring
  simp only [e1, e2]
  have hb : Summable fun p : ℤ × ℤ => ‖f p.2 * g (p.1 - p.2) * h (n - p.1)‖ := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
      ((summable_conv_norm (summable_norm f) (summable_norm g)).mul_right ‖h‖)
    calc ‖f p.2 * g (p.1 - p.2) * h (n - p.1)‖ ≤ ‖f p.2‖ * ‖g (p.1 - p.2)‖ * ‖h (n - p.1)‖ :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ ‖f p.2‖ * ‖g (p.1 - p.2)‖ * ‖h‖ := by gcongr; exact norm_apply_le h _
  have hs := Summable.of_norm hb
  refine (hs.tsum_comm' (fun j => hs.prod_factor j) fun k => ?_).symm
  refine Summable.of_norm <| .of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_)
    ((((summable_norm g).comp_injective (Equiv.subRight k).injective).mul_left ‖f k‖).mul_right
      ‖h‖)
  calc ‖f k * g (j - k) * h (n - j)‖ ≤ ‖f k‖ * ‖g (j - k)‖ * ‖h (n - j)‖ :=
        (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
    _ ≤ ‖f k‖ * ‖g (j - k)‖ * ‖h‖ := by gcongr; exact norm_apply_le h _

noncomputable instance : CommRing Wiener :=
  { (inferInstance : AddCommGroup Wiener) with
    mul_assoc := fun f g h => by exact mul_assoc' f g h
    one_mul := fun g => by ext m; rw [one_def, single_mul]; simp
    mul_one := fun f => by ext m; rw [mul_comm', one_def, single_mul]; simp
    zero_mul := fun g => by ext m; simp [mul_apply]
    mul_zero := fun f => by ext m; simp [mul_apply]
    left_distrib := fun f g h => by exact mul_add' f g h
    right_distrib := fun f g h => by rw [mul_comm', mul_add', mul_comm' h, mul_comm' h]
    mul_comm := fun f g => by exact mul_comm' f g }

private theorem norm_mul_le' (f g : Wiener) : ‖f * g‖ ≤ ‖f‖ * ‖g‖ := by
  have hn := summable_conv_norm (summable_norm f) (summable_norm g)
  rw [norm_def, norm_def f, norm_def g,
    ← tsum_conv (f := fun k => ‖f k‖) (g := fun k => ‖g k‖) (by simpa using summable_norm f)
      (by simpa using summable_norm g)]
  refine Summable.tsum_le_tsum (fun n => ?_) (summable_conv f g) hn.prod
  exact (norm_tsum_le_tsum_norm (summable_mul_shift f g n)).trans
    (Summable.tsum_le_tsum (fun k => norm_mul_le _ _) (summable_mul_shift f g n) (hn.prod_factor n))

noncomputable instance : NormedCommRing Wiener :=
  { (inferInstance : NormedAddCommGroup Wiener), (inferInstance : CommRing Wiener) with
    norm_mul_le := fun f g => by exact norm_mul_le' f g }

instance : NormOneClass Wiener := ⟨by rw [one_def, norm_single, norm_one]⟩

noncomputable instance : Algebra ℂ Wiener :=
  Algebra.ofModule
    (fun c f g => by ext n; simp only [mul_apply, smul_apply, mul_assoc, tsum_mul_left])
    (fun c f g => by ext n; simp only [mul_apply, smul_apply, mul_left_comm _ c, tsum_mul_left])

noncomputable instance : NormedAlgebra ℂ Wiener := { norm_smul_le := norm_smul_le }

/-- Products of single coefficients multiply the coefficients and add the frequencies. -/
theorem single_mul_single (n m : ℤ) (c d : ℂ) :
    single n c * single m d = single (n + m) (c * d) := by
  ext k
  rw [single_mul, single_apply, single_apply]
  by_cases h : k = n + m
  · simp [h]
  · have : k - n ≠ m := fun h' => h (by omega)
    simp [h, this]

/-! ### Values on the circle -/

private theorem norm_exp_int (n : ℤ) (u : ℝ) : ‖exp (n * u * I)‖ = 1 := by
  have : (n : ℂ) * u * I = ((n * u : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, norm_exp_ofReal_mul_I]

private theorem exp_int_add (a b : ℤ) (u : ℝ) :
    exp (((a + b : ℤ) : ℂ) * u * I) = exp (a * u * I) * exp (b * u * I) := by
  rw [← exp_add]; push_cast; ring_nf

private theorem summable_eval (f : Wiener) (u : ℝ) :
    Summable fun n : ℤ => ‖f n * exp (n * u * I)‖ := by
  simpa [norm_exp_int] using summable_norm f

/-- The value of an element at the point `u` of the circle, `∑ n, f n * exp (n * u * I)`, as an
algebra map. -/
noncomputable def eval (u : ℝ) : Wiener →ₐ[ℂ] ℂ where
  toFun f := ∑' n : ℤ, f n * exp (n * u * I)
  map_one' := by
    rw [tsum_eq_single 0 fun n hn => by simp [one_def, single_apply, hn]]
    simp [one_def, single_apply]
  map_mul' f g := by
    have h : ∀ n : ℤ, (f * g) n * exp (n * u * I) =
        ∑' k, f k * exp (k * u * I) * (g (n - k) * exp (((n - k : ℤ) : ℂ) * u * I)) := by
      intro n
      rw [mul_apply, ← tsum_mul_right]
      refine tsum_congr fun k => ?_
      rw [show n = k + (n - k) by ring, exp_int_add, add_sub_cancel_left]
      ring
    simp only [h]
    exact tsum_conv (summable_eval f u) (summable_eval g u)
  map_zero' := by simp
  map_add' f g := by
    simp only [add_apply, add_mul]
    exact (Summable.of_norm (summable_eval f u)).tsum_add (Summable.of_norm (summable_eval g u))
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, tsum_eq_single 0 fun n hn => by
      simp [one_def, single_apply, hn]]
    simp [one_def, single_apply]

/-- The value of an element at `u` as a series. -/
theorem eval_apply (u : ℝ) (f : Wiener) : eval u f = ∑' n : ℤ, f n * exp (n * u * I) := rfl

/-- On the circle an element is bounded by its norm. -/
theorem norm_eval_le (u : ℝ) (f : Wiener) : ‖eval u f‖ ≤ ‖f‖ := by
  rw [eval_apply, norm_def]
  refine (norm_tsum_le_tsum_norm (summable_eval f u)).trans (le_of_eq ?_)
  simp [norm_exp_int]

/-- Evaluation at a point is continuous in the element. -/
theorem continuous_eval (u : ℝ) : Continuous (eval u) :=
  AddMonoidHomClass.continuous_of_bound (eval u) 1 fun f => by simpa using norm_eval_le u f

/-- The function of an element is continuous on the circle. -/
theorem continuous_eval_apply (f : Wiener) : Continuous fun u => eval u f := by
  simp only [eval_apply]
  refine continuous_tsum (fun n => ?_) (summable_norm f) fun n u => ?_
  · fun_prop
  · rw [norm_mul, norm_exp_int, mul_one]

/-- The value of `single n c` at `u` is `c * exp (n * u * I)`. -/
theorem eval_single (u : ℝ) (n : ℤ) (c : ℂ) : eval u (single n c) = c * exp (n * u * I) := by
  rw [eval_apply, tsum_eq_single n fun m hm => by simp [single_apply, hm]]
  simp [single_apply]

/-! ### Finite rows -/

/-- The element of the integer row `xs` whose lane `c` holds the constant term:
`∑ k, xs[k] * exp ((k - c) * u * I)`. -/
noncomputable def ofRow (xs : List ℤ) (c : ℤ) : Wiener :=
  single (-c) 1 * aeval (single 1 1) (ofCoeffList xs)

/-- The value of a row on the circle is its Laurent polynomial at `exp (u * I)`. -/
theorem eval_ofRow (u : ℝ) (xs : List ℤ) (c : ℤ) :
    eval u (ofRow xs c) = laurent xs c (exp (u * I)) := by
  have h : aeval (eval u (single 1 1)) (ofCoeffList xs) =
      eval u (aeval (single 1 1) (ofCoeffList xs)) :=
    aeval_algHom_apply ((eval u).restrictScalars ℤ) _ _
  rw [ofRow, map_mul, laurent, ← h, eval_single, eval_single,
    show ((-c : ℤ) : ℂ) * u * I = ((-c : ℤ) : ℂ) * (u * I) by ring, exp_int_mul]
  simp

/-- A Cauchy product of rows is the product in the algebra, with the centres added. -/
theorem ofRow_conv (xs ys : List ℤ) (c d : ℤ) :
    ofRow (Packed.conv xs ys) (c + d) = ofRow xs c * ofRow ys d := by
  have hs : single (-(c + d)) 1 = single (-c) 1 * single (-d) 1 := by
    rw [single_mul_single, mul_one, neg_add]
  rw [ofRow, ofRow, ofRow, ofCoeffList_conv, map_mul, hs]
  ring

/-- A lanewise difference of rows is the difference in the algebra. -/
theorem ofRow_sub (xs ys : List ℤ) (c : ℤ) :
    ofRow (Packed.sub xs ys) c = ofRow xs c - ofRow ys c := by
  rw [ofRow, ofRow, ofRow, ofCoeffList_sub, map_sub, mul_sub]

/-- A row whose only nonzero entry is `a`, in lane `c`, is the constant `a`. -/
theorem ofRow_single (c : ℕ) (a : ℤ) : ofRow (List.replicate c 0 ++ [a]) c = (a : Wiener) := by
  have hpoly : ofCoeffList (List.replicate c 0 ++ [a]) = C a * X ^ c := by
    rw [ofCoeffList_append, List.length_replicate, ofCoeffList_replicate_zero]
    simp [ofCoeffList_cons, mul_comm]
  have hpow : ∀ k : ℕ, single 1 1 ^ k = single k 1 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, ih, single_mul_single]; simp
  rw [ofRow, hpoly, map_mul, aeval_C, aeval_X_pow, hpow, ← mul_assoc, mul_comm (single _ _),
    mul_assoc, single_mul_single, algebraMap_int_eq, eq_intCast]
  simp [← one_def]

/-- The norm of a row is at most its `l1` norm. -/
theorem norm_ofRow_le (xs : List ℤ) (c : ℤ) : ‖ofRow xs c‖ ≤ Packed.l1 xs := by
  refine (norm_mul_le _ _).trans ?_
  rw [norm_single, norm_one, one_mul]
  exact norm_aeval_ofCoeffList_le (by rw [norm_single, norm_one]) xs

end Wiener

end FloatLib.Numerics.Coeff
