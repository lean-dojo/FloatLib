/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Affine.FormProof
public import FloatLib.Numerics.Enclosure.Affine.Model

/-!
# What affine models represent

A model represents a real `x` at a noise assignment `ε` when `x` minus the value of its form at
`ε` lies in its remainder (`AffineModel.Represents`). The constant model represents its value, and
a form with remainder zero represents its own value (`represents_const`, `represents_ofAffine`).
Sums, negations and differences preserve what models represent at every assignment
(`Represents.add`, `Represents.neg`, `Represents.sub`), and products and natural powers do when
every `|ε i| ≤ 1` (`Represents.mul`, `Represents.pow`). At such an assignment `range` contains
every represented value (`mem_range`).

The product rests on `dot_mul_dot_mem_quadraticRange`: at an assignment with every `|ε i| ≤ 1`,
the pairwise enclosure contains the product of the values of two lists of noise terms. Its proof
follows the recursion of `quadraticRange`. The product of the first symbols is `ε 0 * ε 0`, in
`[0, 1]`, and the products of `ε 0` with the later symbols are the values of terms at the
assignment `fun i => ε 0 * ε (i + 1)`, which lies in the unit box.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Affine

namespace AffineModel

/-- A model represents `x` at the noise assignment `ε` when `x` minus the value of the form at `ε`
lies in the remainder. -/
def Represents (m : AffineModel) (ε : Nat → ℝ) (x : ℝ) : Prop :=
  m.remainder.ContainsReal some (x - m.affine.eval ε)

/-- The constant model `q` represents `q` at every assignment. -/
@[simp] theorem represents_const (q : ℚ) (ε : Nat → ℝ) : (const q).Represents ε q := by
  simpa [Represents, const] using Interval.containsReal_point 0

/-- An affine form with remainder zero represents its own value at every assignment. -/
@[simp] theorem represents_ofAffine (a : AffineForm) (ε : Nat → ℝ) :
    (ofAffine a).Represents ε (a.eval ε) := by
  simpa [Represents, ofAffine] using Interval.containsReal_point 0

/-- The sum of two models represents the sum of the represented values. -/
theorem Represents.add {a b : AffineModel} {ε : Nat → ℝ} {x y : ℝ} (hx : a.Represents ε x)
    (hy : b.Represents ε y) : (a.add b).Represents ε (x + y) := by
  change (Interval.Exact.add a.remainder b.remainder).ContainsReal some
    (x + y - (a.affine.add b.affine).eval ε)
  convert Interval.Exact.containsReal_add hx hy using 1
  rw [AffineForm.eval_add]
  ring

/-- The negation of a model represents the negation of the represented value. -/
theorem Represents.neg {a : AffineModel} {ε : Nat → ℝ} {x : ℝ} (hx : a.Represents ε x) :
    a.neg.Represents ε (-x) := by
  change (Interval.Exact.neg a.remainder).ContainsReal some (-x - a.affine.neg.eval ε)
  convert Interval.Exact.containsReal_neg hx using 1
  rw [AffineForm.eval_neg]
  ring

/-- The difference of two models represents the difference of the represented values. -/
theorem Represents.sub {a b : AffineModel} {ε : Nat → ℝ} {x y : ℝ} (hx : a.Represents ε x)
    (hy : b.Represents ε y) : (a.sub b).Represents ε (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- The square of a value in `[-1, 1]` lies in `[0, 1]`. -/
theorem mul_self_mem_unitSquare {x : ℝ} (hx : |x| ≤ 1) :
    unitSquare.ContainsReal some (x * x) := by
  rw [Interval.containsReal_some_iff]
  simp only [unitSquare, Rat.cast_zero, Rat.cast_one]
  exact ⟨mul_self_nonneg x, by nlinarith [abs_le.mp hx]⟩

/-- `quadraticRange xs ys` contains the product of the values of the noise terms with
coefficients `xs` and `ys`, at every assignment with `|ε i| ≤ 1` for all `i`. -/
theorem dot_mul_dot_mem_quadraticRange {ε : Nat → ℝ} (hε : ∀ i, |ε i| ≤ 1) (xs ys : List ℚ) :
    (quadraticRange xs ys).ContainsReal some (AffineForm.dot ε xs * AffineForm.dot ε ys) := by
  induction xs generalizing ε ys with
  | nil => simpa [quadraticRange, AffineForm.dot] using Interval.containsReal_point 0
  | cons x xs ih =>
    cases ys with
    | nil => simpa [quadraticRange, AffineForm.dot] using Interval.containsReal_point 0
    | cons y ys =>
      have hcross : AffineForm.MemBox AffineForm.unitBox (fun i => ε 0 * ε (i + 1)) :=
        (AffineForm.memBox_unitBox_iff _).2 fun i => by
          rw [abs_mul]
          exact (mul_le_mul (hε 0) (hε (i + 1)) (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
      have h := Interval.Exact.containsReal_add
        (Interval.Exact.containsReal_add
          (Interval.Exact.containsReal_add
            (AffineForm.mul_mem_termRange (Kernel.Q.mul x y) (mul_self_mem_unitSquare (hε 0)))
            (AffineForm.dot_mem_termsRange hcross (ys.map (Kernel.Q.mul x))))
          (AffineForm.dot_mem_termsRange hcross (xs.map (Kernel.Q.mul y))))
        (ih (ε := fun i => ε (i + 1)) (fun i => hε (i + 1)) ys)
      rw [quadraticRange]
      convert h using 1
      simp only [AffineForm.dot, AffineForm.dot_map_mul, AffineForm.dot_mul_left,
        Kernel.Q.mul_eq, Rat.cast_mul]
      ring

/-- `quadraticRange` of the coefficients of two forms contains the product of their deviations,
at every assignment with `|ε i| ≤ 1` for all `i`. -/
theorem deviation_mul_deviation_mem_quadraticRange (a b : AffineForm) {ε : Nat → ℝ}
    (hε : ∀ i, |ε i| ≤ 1) :
    (quadraticRange a.coefficients b.coefficients).ContainsReal some
      (a.deviation.eval ε * b.deviation.eval ε) := by
  simpa [AffineForm.deviation, AffineForm.eval] using
    dot_mul_dot_mem_quadraticRange hε a.coefficients b.coefficients

/-- The product of two models represents the product of the represented values, at every
assignment with `|ε i| ≤ 1` for all `i`. -/
theorem Represents.mul {a b : AffineModel} {ε : Nat → ℝ} {x y : ℝ} (hx : a.Represents ε x)
    (hy : b.Represents ε y) (hε : ∀ i, |ε i| ≤ 1) : (a.mul b).Represents ε (x * y) := by
  have h := Interval.Exact.containsReal_add
    (Interval.Exact.containsReal_add
      (Interval.Exact.containsReal_add
        (deviation_mul_deviation_mem_quadraticRange a.affine b.affine hε)
        (Interval.Exact.containsReal_mul (AffineForm.mem_range a.affine hε) hy))
      (Interval.Exact.containsReal_mul (AffineForm.mem_range b.affine hε) hx))
    (Interval.Exact.containsReal_mul hx hy)
  change (Interval.Exact.add
    (Interval.Exact.add
      (Interval.Exact.add (quadraticRange a.affine.coefficients b.affine.coefficients)
        (Interval.Exact.mul a.affine.range b.remainder))
      (Interval.Exact.mul b.affine.range a.remainder))
    (Interval.Exact.mul a.remainder b.remainder)).ContainsReal some
      (x * y - (a.affine.linearMul b.affine).eval ε)
  convert h using 1
  rw [← AffineForm.mul_sub_eval_linearMul]
  ring

/-- The binary-exponentiation equation of `pow`: the power `Nat.bit odd n` is one `powStep` from
the power `n`. -/
theorem pow_bit (a : AffineModel) (odd : Bool) (n : Nat) :
    a.pow (Nat.bit odd n) = powStep a odd n (a.pow n) := by
  rw [pow, Nat.binaryRec_eq odd n (Or.inl rfl)]
  rfl

/-- A natural power of a model represents the power of the represented value, at every
assignment with `|ε i| ≤ 1` for all `i`. -/
theorem Represents.pow {a : AffineModel} {ε : Nat → ℝ} {x : ℝ} (hx : a.Represents ε x) (n : Nat)
    (hε : ∀ i, |ε i| ≤ 1) : (a.pow n).Represents ε (x ^ n) := by
  induction n using Nat.binaryRec with
  | zero => simpa [AffineModel.pow] using represents_const 1 ε
  | bit odd n ih =>
    rw [pow_bit]
    cases odd with
    | false =>
      by_cases hn : n = 0
      · subst n
        simpa [powStep] using ih
      · simpa [powStep, hn, Nat.bit_false, two_mul, pow_add] using ih.mul ih hε
    | true =>
      simpa [powStep, Nat.bit_true, two_mul, pow_add, pow_succ, mul_assoc] using
        (ih.mul ih hε).mul hx hε

/-- `range m` contains every value that `m` represents at an assignment with `|ε i| ≤ 1` for all
`i`. -/
theorem mem_range {m : AffineModel} {ε : Nat → ℝ} {x : ℝ} (hx : m.Represents ε x)
    (hε : ∀ i, |ε i| ≤ 1) : m.range.ContainsReal some x := by
  change (Interval.Exact.add m.affine.range m.remainder).ContainsReal some x
  convert Interval.Exact.containsReal_add (AffineForm.mem_range m.affine hε) hx using 1
  ring

end AffineModel

end FloatLib.Numerics.Enclosure.Affine
