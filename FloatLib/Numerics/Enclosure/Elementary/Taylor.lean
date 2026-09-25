/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact Taylor sums by binary splitting

Each Horner step is an affine map with integer coefficients and a positive common denominator.
Composing adjacent blocks uses only integer arithmetic. Binary splitting balances the sizes of
the multiplication operands; rational normalization is needed only once, at the end.

The resulting exponential and logarithm polynomials agree with their finite sums for every
rational argument and every number of terms, without convergence assumptions.
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Taylor

/-- The affine map `tail ↦ (constantTerm + coefficient * tail) / denominator`. -/
structure Block where
  /-- Integer constant in the numerator. -/
  constantTerm : Int
  /-- Integer multiplier of the remaining polynomial tail. -/
  coefficient : Int
  /-- Common denominator of the affine expression. -/
  denominator : Nat
  /-- A positive denominator keeps every block evaluation defined. -/
  denominator_pos : 0 < denominator

/-- Apply a Horner block to the unevaluated tail of the polynomial. -/
def Block.eval (block : Block) (tail : ℚ) : ℚ :=
  ((block.constantTerm : ℚ) + (block.coefficient : ℚ) * tail) / block.denominator

/-- An empty block leaves the tail unchanged. -/
def Block.identity : Block := ⟨0, 1, 1, by decide⟩

/-- Compose consecutive Horner blocks without reducing either fraction. -/
def Block.comp (left right : Block) : Block :=
  ⟨left.constantTerm * right.denominator + left.coefficient * right.constantTerm,
    left.coefficient * right.coefficient,
    left.denominator * right.denominator,
    Nat.mul_pos left.denominator_pos right.denominator_pos⟩

/-- Evaluating the identity block preserves the tail. -/
theorem Block.eval_identity (tail : ℚ) : identity.eval tail = tail := by
  simp [identity, eval]

/-- Evaluating a composite block agrees with evaluating its two blocks in order. -/
theorem Block.eval_comp (left right : Block) (tail : ℚ) :
    (left.comp right).eval tail = left.eval (right.eval tail) := by
  have hl : (left.denominator : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt left.denominator_pos
  have hr : (right.denominator : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt right.denominator_pos
  simp only [comp, eval, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp
  ring

/-- Sequential Horner evaluation, used to specify the composition of a block. -/
def horner (term : Nat → Block) (start : Nat) : Nat → ℚ → ℚ
  | 0, tail => tail
  | n + 1, tail => (term start).eval (horner term (start + 1) n tail)

/-- Horner evaluation over adjacent ranges is the composition of their evaluations. -/
theorem horner_add (term : Nat → Block) (start m n : Nat) (tail : ℚ) :
    horner term start (m + n) tail =
      horner term start m (horner term (start + m) n tail) := by
  induction m generalizing start with
  | zero => simp [horner]
  | succ m ih =>
    simp only [Nat.succ_add, horner, ih]
    congr 2

/-- Compose a range of Horner steps by splitting it into halves. -/
@[specialize] def split (term : Nat → Block) (start length : Nat) : Block :=
  match length with
  | 0 => .identity
  | 1 => term start
  | k@(_ + 2) =>
    (split term start (k / 2)).comp (split term (start + k / 2) ((k + 1) / 2))

/-- Binary splitting gives the same affine map as sequential Horner evaluation. -/
theorem eval_split (term : Nat → Block) (start length : Nat) (tail : ℚ) :
    (split term start length).eval tail = horner term start length tail := by
  fun_induction split generalizing tail with
  | case1 => simp [Block.eval_identity, horner]
  | case2 => simp [horner]
  | case3 start k ih₁ ih₂ =>
    rw [Block.eval_comp, ih₂, ih₁, ← horner_add]
    congr 1
    omega

/-- The exponential Horner step `tail ↦ 1 + x * tail / (k + 1)`. -/
def expStep (x : ℚ) (k : Nat) : Block :=
  ⟨x.den * (k + 1), x.num, x.den * (k + 1),
    Nat.mul_pos x.den_pos (by omega)⟩

/-- An exponential block evaluates to `1 + x / (k + 1) * tail`. -/
theorem eval_expStep (x : ℚ) (k : Nat) (tail : ℚ) :
    (expStep x k).eval tail = 1 + x / (k + 1) * tail := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt x.den_pos
  have hk : (k : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [expStep, Block.eval, Int.cast_mul, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = 1 + ((x.num : ℚ) / x.den) / (k + 1) * tail := by field_simp
    _ = _ := by rw [Rat.num_div_den]

/-- Exponential Horner steps expand into a sum with rising factorial denominators. -/
theorem horner_expStep (x : ℚ) (start n : Nat) :
    horner (expStep x) start n 0 =
      ∑ i ∈ Finset.range n, x ^ i / ((start + 1).ascFactorial i : ℚ) := by
  induction n generalizing start with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, eval_expStep, ih, Finset.sum_range_succ']
    simp only [pow_zero, Nat.ascFactorial_zero, Nat.cast_one, div_one]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.ascFactorial_succ, ← Nat.succ_ascFactorial]
    simp only [Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [div_mul_div_comm]
    congr 1
    ring

/-- The logarithm Horner step `tail ↦ x / (k + 1) + x * tail`. -/
def logStep (x : ℚ) (k : Nat) : Block :=
  ⟨x.num, x.num * (k + 1), x.den * (k + 1),
    Nat.mul_pos x.den_pos (by omega)⟩

/-- A logarithm block evaluates to `x / (k + 1) + x * tail`. -/
theorem eval_logStep (x : ℚ) (k : Nat) (tail : ℚ) :
    (logStep x k).eval tail = x / (k + 1) + x * tail := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt x.den_pos
  have hk : (k : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [logStep, Block.eval, Int.cast_mul, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = ((x.num : ℚ) / x.den) / (k + 1) + ((x.num : ℚ) / x.den) * tail := by
      field_simp
    _ = _ := by rw [Rat.num_div_den]

/-- Logarithm Horner steps expand into a sum with consecutive integer denominators. -/
theorem horner_logStep (x : ℚ) (start n : Nat) :
    horner (logStep x) start n 0 =
      ∑ i ∈ Finset.range n, x ^ (i + 1) / ((start + i + 1 : Nat) : ℚ) := by
  induction n generalizing start with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, eval_logStep, ih, Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.zero_add, Nat.cast_add, Nat.cast_one, pow_one]
    rw [Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_div_assoc]
    congr 1 <;> ring

/-- The first `n` exponential terms, with one final rational normalization. -/
def exp (x : ℚ) (n : Nat) : ℚ :=
  let block := split (expStep x) 0 n
  mkRat block.constantTerm block.denominator

/-- The first `n` terms of `-log (1 - x)`, with one final rational normalization. -/
def logOneSub (x : ℚ) (n : Nat) : ℚ :=
  let block := split (logStep x) 0 n
  mkRat block.constantTerm block.denominator

/-- The exponential evaluation equals the first `n` terms of its Taylor series. -/
theorem exp_eq_sum (x : ℚ) (n : Nat) :
    exp x n = ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ) := by
  have he := eval_split (expStep x) 0 n 0
  simpa [exp, Block.eval, Rat.mkRat_eq_div, horner_expStep, Nat.one_ascFactorial] using he

/-- The logarithm evaluation equals the first `n` terms of the series for `-log (1 - x)`. -/
theorem logOneSub_eq_sum (x : ℚ) (n : Nat) :
    logOneSub x n = ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i + 1 : Nat) : ℚ) := by
  have he := eval_split (logStep x) 0 n 0
  simpa [logOneSub, Block.eval, Rat.mkRat_eq_div, horner_logStep] using he

end FloatLib.Numerics.Enclosure.Taylor
