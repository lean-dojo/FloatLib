/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.Form
public import FloatLib.Numerics.Enclosure.Interval.ExactProof
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Values of affine forms and their enclosures

`AffineForm.eval a ε` is the real value of a form at an assignment `ε` of its noise symbols, the
center plus `Σ i, coefficients[i] * ε i` (`eval_eq_sum`). The operations of `Form` are exact on
these values (`eval_add`, `eval_neg`, `eval_sub`, `eval_scale`, `eval_deviation`,
`eval_linearMul`), and the error of the affine part of a product is the product of the two
deviations (`mul_sub_eval_linearMul`).

An assignment lies in a box of noise intervals when each value lies in its interval (`MemBox`).
For such an assignment the enclosures of `Form` contain the value of a form (`mem_rangeOn`) and
the product of the values of two forms (`mul_mem_mulRangeOn`). On the unit box, which holds the
assignments with every `|ε i| ≤ 1`, these are `mem_range` and `mul_mem_mulRange`, and the range
is `center ± Σ i, |coefficients[i]|` (`range_lo`, `range_hi`). The proofs apply the containment
theorems of `Interval.Exact` term by term.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Affine

namespace AffineForm

/-- The value `Σ i, cs[i] * ε i` of the noise terms with coefficients `cs` at the assignment
`ε`. -/
noncomputable def dot (ε : Nat → ℝ) : List ℚ → ℝ
  | [] => 0
  | c :: cs => c * ε 0 + dot (fun i => ε (i + 1)) cs

/-- The value of a form at an assignment `ε` of its noise symbols. -/
noncomputable def eval (a : AffineForm) (ε : Nat → ℝ) : ℝ :=
  a.center + dot ε a.coefficients

/-- The value of noise terms is the sum over the positions of the coefficient list. -/
theorem dot_eq_sum (ε : Nat → ℝ) (cs : List ℚ) :
    dot ε cs = ∑ i : Fin cs.length, (cs[i] : ℝ) * ε i := by
  induction cs generalizing ε with
  | nil => simp [dot]
  | cons c cs ih => simp [dot, ih, Fin.sum_univ_succ]

/-- The value of a form is its center plus the sum of its noise terms. -/
theorem eval_eq_sum (a : AffineForm) (ε : Nat → ℝ) :
    a.eval ε = a.center + ∑ i : Fin a.coefficients.length, (a.coefficients[i] : ℝ) * ε i := by
  rw [eval, dot_eq_sum]

/-- Padding the shorter list with zeros and adding entrywise adds the values of the terms. -/
theorem dot_addCoefficients (ε : Nat → ℝ) (xs ys : List ℚ) :
    dot ε (addCoefficients xs ys) = dot ε xs + dot ε ys := by
  induction xs generalizing ε ys with
  | nil => simp [addCoefficients, dot]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addCoefficients, dot]
    | cons y ys =>
      simp only [addCoefficients, dot, ih, Kernel.Q.add_eq, Rat.cast_add]
      ring

/-- Multiplying every coefficient by `q` multiplies the value of the terms by `q`. -/
theorem dot_map_mul (ε : Nat → ℝ) (q : ℚ) (cs : List ℚ) :
    dot ε (cs.map (Kernel.Q.mul q)) = q * dot ε cs := by
  induction cs generalizing ε with
  | nil => simp [dot]
  | cons c cs ih =>
    simp only [List.map_cons, dot, ih, Kernel.Q.mul_eq, Rat.cast_mul]
    ring

/-- Negating every coefficient negates the value of the terms. -/
theorem dot_map_neg (ε : Nat → ℝ) (cs : List ℚ) :
    dot ε (cs.map Kernel.Q.neg) = -dot ε cs := by
  induction cs generalizing ε with
  | nil => simp [dot]
  | cons c cs ih =>
    simp only [List.map_cons, dot, ih, Kernel.Q.neg_eq, Rat.cast_neg]
    ring

/-- Multiplying the assignment by `r` multiplies the value of the terms by `r`. -/
theorem dot_mul_left (r : ℝ) (ε : Nat → ℝ) (cs : List ℚ) :
    dot (fun i => r * ε i) cs = r * dot ε cs := by
  induction cs generalizing ε with
  | nil => simp [dot]
  | cons c cs ih =>
    simp only [dot, ih]
    ring

/-- A constant form has its center as value. -/
@[simp] theorem eval_const (q : ℚ) (ε : Nat → ℝ) : (const q).eval ε = q := by
  simp [const, eval, dot]

/-- The form of the noise symbol `εᵢ` has the value `ε i`. -/
@[simp] theorem eval_noise (i : Nat) (ε : Nat → ℝ) : (noise i).eval ε = ε i := by
  have h (i : Nat) : ∀ ε : Nat → ℝ, dot ε (List.replicate i 0 ++ [1]) = ε i := by
    induction i with
    | zero => simp [dot]
    | succ i ih => simp [List.replicate_succ, dot, ih]
  simp [noise, eval, h]

/-- The value of a sum of forms is the sum of the values. -/
@[simp] theorem eval_add (a b : AffineForm) (ε : Nat → ℝ) :
    (a.add b).eval ε = a.eval ε + b.eval ε := by
  simp only [add, eval, dot_addCoefficients, Kernel.Q.add_eq, Rat.cast_add]
  ring

/-- The value of the negation of a form is the negation of the value. -/
@[simp] theorem eval_neg (a : AffineForm) (ε : Nat → ℝ) : a.neg.eval ε = -a.eval ε := by
  simp only [neg, eval, dot_map_neg, Kernel.Q.neg_eq, Rat.cast_neg]
  ring

/-- The value of a difference of forms is the difference of the values. -/
@[simp] theorem eval_sub (a b : AffineForm) (ε : Nat → ℝ) :
    (a.sub b).eval ε = a.eval ε - b.eval ε := by
  rw [sub, eval_add, eval_neg, sub_eq_add_neg]

/-- Scaling a form by `q` multiplies its value by `q`. -/
@[simp] theorem eval_scale (q : ℚ) (a : AffineForm) (ε : Nat → ℝ) :
    (a.scale q).eval ε = q * a.eval ε := by
  simp only [scale, eval, dot_map_mul, Kernel.Q.mul_eq, Rat.cast_mul]
  ring

/-- The deviation of a form has the value of the form minus its center. -/
@[simp] theorem eval_deviation (a : AffineForm) (ε : Nat → ℝ) :
    a.deviation.eval ε = a.eval ε - a.center := by
  simp [deviation, eval]

/--
The value of the affine part of a product. Writing `a = a₀ + A` and `b = b₀ + B` with centers
`a₀`, `b₀` and deviations `A`, `B`, the product is `a₀ b₀ + a₀ B + b₀ A + A B`. `linearMul`
keeps the first three terms, whose sum is `a₀ b + b₀ a - a₀ b₀`.
-/
@[simp] theorem eval_linearMul (a b : AffineForm) (ε : Nat → ℝ) :
    (a.linearMul b).eval ε =
      a.center * b.eval ε + b.center * a.eval ε - a.center * b.center := by
  simp only [linearMul, eval, dot_addCoefficients, dot_map_mul, Kernel.Q.mul_eq, Rat.cast_mul]
  ring

/-- The error of the affine part of a product is exactly the product of the two deviations. -/
theorem mul_sub_eval_linearMul (a b : AffineForm) (ε : Nat → ℝ) :
    a.eval ε * b.eval ε - (a.linearMul b).eval ε =
      a.deviation.eval ε * b.deviation.eval ε := by
  rw [eval_linearMul, eval_deviation, eval_deviation]
  ring

/-! ## Enclosures -/

/-- An assignment `ε` lies in a box of noise intervals when each value `ε i` lies in `box i`. -/
def MemBox (box : Nat → Interval ℚ) (ε : Nat → ℝ) : Prop :=
  ∀ i, (box i).ContainsReal some (ε i)

/-- `termRange q I` contains `q * x` for every `x` in `I`. -/
theorem mul_mem_termRange (q : ℚ) {I : Interval ℚ} {x : ℝ} (hx : I.ContainsReal some x) :
    (termRange q I).ContainsReal some (q * x) :=
  Interval.Exact.containsReal_mul (Interval.containsReal_point q) hx

/-- `termsRange box cs` contains the value of the terms at every assignment in the box. -/
theorem dot_mem_termsRange {box : Nat → Interval ℚ} {ε : Nat → ℝ} (hε : MemBox box ε)
    (cs : List ℚ) : (termsRange box cs).ContainsReal some (dot ε cs) := by
  induction cs generalizing box ε with
  | nil => simpa [termsRange, dot] using Interval.containsReal_point 0
  | cons c cs ih =>
    exact Interval.Exact.containsReal_add (mul_mem_termRange c (hε 0)) (ih fun i => hε (i + 1))

/-- `rangeOn a box` contains the value of `a` at every assignment in the box. -/
theorem mem_rangeOn (a : AffineForm) {box : Nat → Interval ℚ} {ε : Nat → ℝ}
    (hε : MemBox box ε) : (a.rangeOn box).ContainsReal some (a.eval ε) :=
  Interval.Exact.containsReal_add (Interval.containsReal_point a.center)
    (dot_mem_termsRange hε a.coefficients)

/-- `mulRemainderOn a b box` contains the error of the affine part of the product at every
assignment in the box. -/
theorem mul_sub_eval_linearMul_mem_mulRemainderOn (a b : AffineForm)
    {box : Nat → Interval ℚ} {ε : Nat → ℝ} (hε : MemBox box ε) :
    (a.mulRemainderOn b box).ContainsReal some
      (a.eval ε * b.eval ε - (a.linearMul b).eval ε) := by
  rw [mul_sub_eval_linearMul]
  exact Interval.Exact.containsReal_mul (mem_rangeOn a.deviation hε) (mem_rangeOn b.deviation hε)

/-- `mulRangeOn a b box` contains the product of the values of `a` and `b` at every assignment in
the box. -/
theorem mul_mem_mulRangeOn (a b : AffineForm) {box : Nat → Interval ℚ} {ε : Nat → ℝ}
    (hε : MemBox box ε) : (a.mulRangeOn b box).ContainsReal some (a.eval ε * b.eval ε) := by
  have h := Interval.Exact.containsReal_add (mem_rangeOn (a.linearMul b) hε)
    (mul_sub_eval_linearMul_mem_mulRemainderOn a b hε)
  rwa [add_sub_cancel] at h

/-- An assignment lies in the unit box exactly when every value lies in `[-1, 1]`. -/
theorem memBox_unitBox_iff (ε : Nat → ℝ) : MemBox unitBox ε ↔ ∀ i, |ε i| ≤ 1 := by
  simp [MemBox, unitBox, abs_le]

/-- On the unit box the enclosure of noise terms is `±Σ i, |cs[i]|`. -/
private theorem termsRange_unitBox (cs : List ℚ) :
    (termsRange unitBox cs).lo = -(cs.map fun q => |q|).sum ∧
      (termsRange unitBox cs).hi = (cs.map fun q => |q|).sum := by
  induction cs with
  | nil => simp [termsRange, Interval.point]
  | cons c cs ih =>
    have hc : min (-c) c = -|c| ∧ max (-c) c = |c| := by
      rw [abs_eq_max_neg, ← min_neg_neg, neg_neg, min_comm, max_comm]
      exact ⟨rfl, rfl⟩
    change (Interval.Exact.add (termRange c (unitBox 0)) (termsRange unitBox cs)).lo = _ ∧
      (Interval.Exact.add (termRange c (unitBox 0)) (termsRange unitBox cs)).hi = _
    simp only [Interval.Exact.add_lo, Interval.Exact.add_hi, ih, termRange, Interval.Exact.mul_lo,
      Interval.Exact.mul_hi, Interval.point, unitBox, mul_neg, mul_one, min_self, max_self, hc,
      List.map_cons, List.sum_cons, neg_add, and_self]

/-- The lower end of the range on the unit box is `center - Σ i, |coefficients[i]|`. -/
theorem range_lo (a : AffineForm) :
    a.range.lo = a.center - (a.coefficients.map fun q => |q|).sum := by
  simp [range, rangeOn, (termsRange_unitBox _).1, Interval.point, sub_eq_add_neg]

/-- The upper end of the range on the unit box is `center + Σ i, |coefficients[i]|`. -/
theorem range_hi (a : AffineForm) :
    a.range.hi = a.center + (a.coefficients.map fun q => |q|).sum := by
  simp [range, rangeOn, (termsRange_unitBox _).2, Interval.point]

/-- `range a` contains the value of `a` at every assignment with `|ε i| ≤ 1` for all `i`. -/
theorem mem_range (a : AffineForm) {ε : Nat → ℝ} (hε : ∀ i, |ε i| ≤ 1) :
    a.range.ContainsReal some (a.eval ε) :=
  mem_rangeOn a ((memBox_unitBox_iff ε).2 hε)

/-- `mulRange a b` contains the product of the values of `a` and `b` at every assignment with
`|ε i| ≤ 1` for all `i`. -/
theorem mul_mem_mulRange (a b : AffineForm) {ε : Nat → ℝ} (hε : ∀ i, |ε i| ≤ 1) :
    (a.mulRange b).ContainsReal some (a.eval ε * b.eval ε) :=
  mul_mem_mulRangeOn a b ((memBox_unitBox_iff ε).2 hε)

end AffineForm

end FloatLib.Numerics.Enclosure.Affine
