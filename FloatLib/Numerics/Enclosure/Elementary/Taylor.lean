/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Kernel.ZProof
public import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp

/-!
# Exact Taylor sums by binary splitting

Each Horner step is an affine map with integer coefficients and a positive common denominator, so
composing adjacent blocks needs only integer arithmetic. Binary splitting balances the sizes of the
multiplication operands, and rational normalization happens once, at the end.

The resulting exponential, logarithm, arctangent, sine and cosine polynomials agree with their
finite sums for every rational argument and every number of terms. No convergence assumption is
involved.

Lean's kernel evaluates these definitions when a proof by `decide` reaches an elementary
enclosure, so their bodies are written with the `Int` functions of `FloatLib.Numerics.Kernel.Z`
and bare `Nat` functions, and `split` recurses on a count with `Nat.rec`. The theorems
`Block.comp_def`, `expStep_def`, `logStep_def`, `atanStep_def` state the bodies in ordinary
notation, and `split_zero`, `split_one`, `split_add_two` are the equations of `split`. Compiled
code runs `Compiled.split`, the recursion by pattern matching (`split_eq_compiled`).
-/

@[expose] public section

namespace FloatLib.Numerics.Enclosure.Taylor

open FloatLib.Numerics.Kernel

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
  ⟨Z.add (Z.mul left.constantTerm (Int.ofNat right.denominator))
      (Z.mul left.coefficient right.constantTerm),
    Z.mul left.coefficient right.coefficient,
    Nat.mul left.denominator right.denominator,
    Nat.mul_pos left.denominator_pos right.denominator_pos⟩

/-- The fields of a composite block, in ordinary notation. -/
theorem Block.comp_def (left right : Block) :
    left.comp right =
      ⟨left.constantTerm * right.denominator + left.coefficient * right.constantTerm,
        left.coefficient * right.coefficient,
        left.denominator * right.denominator,
        Nat.mul_pos left.denominator_pos right.denominator_pos⟩ := by
  unfold Block.comp
  simp only [Z.add_eq, Z.mul_eq]
  rfl

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
  simp only [comp_def, eval, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  field_simp
  rw [mul_add]; ac_rfl

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

/--
Horner evaluation of affine steps `tail ↦ a k + m k * tail` from a zero tail is the sum of the
constant terms `a (start + i)`, each weighted by the product of the multipliers before it.
-/
theorem horner_eq_sum_prod (term : Nat → Block) (a m : Nat → ℚ)
    (hterm : ∀ k tail, (term k).eval tail = a k + m k * tail) (start n : Nat) :
    horner term start n 0 =
      ∑ i ∈ Finset.range n, (∏ j ∈ Finset.range i, m (start + j)) * a (start + i) := by
  induction n generalizing start with
  | zero => simp [horner]
  | succ n ih =>
    rw [horner, hterm, ih, Finset.sum_range_succ', Finset.mul_sum, add_comm]
    simp only [Finset.prod_range_zero, one_mul, add_zero, Finset.prod_range_succ']
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [show ∀ j, start + 1 + j = start + (j + 1) by omega]
    ac_rfl

/-- The recursion of `split` by pattern matching, which compiled code runs. -/
@[specialize] def Compiled.split (term : Nat → Block) (start length : Nat) : Block :=
  match length with
  | 0 => .identity
  | 1 => term start
  | k@(_ + 2) =>
    (Compiled.split term start (k / 2)).comp (Compiled.split term (start + k / 2) ((k + 1) / 2))

/--
`split` with a count of the halvings that are still allowed. A range of at most `fuel + 1` steps
is composed completely (`splitFuel_eq`).
-/
noncomputable def splitFuel (term : Nat → Block) (fuel : Nat) : Nat → Nat → Block :=
  Nat.rec (motive := fun _ => Nat → Nat → Block)
    (fun start length =>
      Nat.rec (motive := fun _ => Block) Block.identity (fun _ _ => term start) length)
    (fun _ next start length =>
      Bool.rec (motive := fun _ => Block)
        ((next start (Nat.div length 2)).comp
          (next (Nat.add start (Nat.div length 2)) (Nat.div (Nat.add length 1) 2)))
        (Nat.rec (motive := fun _ => Block) Block.identity (fun _ _ => term start) length)
        (Nat.ble length 1))
    fuel

/--
Compose a range of Horner steps by splitting it into halves: `split_zero`, `split_one` and
`split_add_two` are its equations.
-/
noncomputable def split (term : Nat → Block) (start length : Nat) : Block :=
  splitFuel term length start length

/-- With enough fuel, `splitFuel` is the recursion by pattern matching. -/
theorem splitFuel_eq (term : Nat → Block) (fuel : Nat) :
    ∀ start length : Nat, length ≤ fuel + 1 →
      splitFuel term fuel start length = Compiled.split term start length := by
  induction fuel with
  | zero =>
    intro start length hlength
    match length, hlength with
    | 0, _ => rw [Compiled.split]; rfl
    | 1, _ => rw [Compiled.split]; rfl
  | succ fuel ih =>
    intro start length hlength
    match length, hlength with
    | 0, _ => rw [Compiled.split]; rfl
    | 1, _ => rw [Compiled.split]; rfl
    | k + 2, hk =>
      rw [Compiled.split]
      change (splitFuel term fuel start ((k + 2) / 2)).comp
        (splitFuel term fuel (start + (k + 2) / 2) ((k + 2 + 1) / 2)) = _
      rw [ih _ _ (by omega), ih _ _ (by omega)]

/-- Compiled code runs the recursion by pattern matching. -/
@[csimp] theorem split_eq_compiled : @split = @Compiled.split := by
  funext term start length
  exact splitFuel_eq term length start length (Nat.le_succ length)

/-- An empty range composes to the identity block. -/
theorem split_zero (term : Nat → Block) (start : Nat) : split term start 0 = .identity := by
  rw [split_eq_compiled, Compiled.split]

/-- A range of one step is that step. -/
theorem split_one (term : Nat → Block) (start : Nat) : split term start 1 = term start := by
  rw [split_eq_compiled, Compiled.split]

/-- A longer range is the composition of its two halves. -/
theorem split_add_two (term : Nat → Block) (start k : Nat) :
    split term start (k + 2) =
      (split term start ((k + 2) / 2)).comp
        (split term (start + (k + 2) / 2) ((k + 2 + 1) / 2)) := by
  rw [split_eq_compiled, Compiled.split]

/-- Binary splitting gives the same affine map as sequential Horner evaluation. -/
theorem eval_split (term : Nat → Block) (start length : Nat) (tail : ℚ) :
    (split term start length).eval tail = horner term start length tail := by
  rw [split_eq_compiled]
  fun_induction Compiled.split generalizing tail with
  | case1 => simp [Block.eval_identity, horner]
  | case2 => simp [horner]
  | case3 start k ih₁ ih₂ =>
    rw [Block.eval_comp, ih₂, ih₁, ← horner_add]
    congr 1
    omega

/-- The exponential Horner step `tail ↦ 1 + x * tail / (k + 1)`. -/
def expStep (x : ℚ) (k : Nat) : Block :=
  ⟨Int.ofNat (Nat.mul x.den (Nat.succ k)), x.num, Nat.mul x.den (Nat.succ k),
    Nat.mul_pos x.den_pos (Nat.succ_pos k)⟩

/-- The fields of an exponential step, in ordinary notation. -/
theorem expStep_def (x : ℚ) (k : Nat) :
    expStep x k = ⟨x.den * (k + 1), x.num, x.den * (k + 1), Nat.mul_pos x.den_pos (by omega)⟩ := by
  unfold expStep
  congr 1

/-- An exponential block evaluates to `1 + x / (k + 1) * tail`. -/
theorem eval_expStep (x : ℚ) (k : Nat) (tail : ℚ) :
    (expStep x k).eval tail = 1 + x / (k + 1) * tail := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt x.den_pos
  have hk : (k : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [expStep_def, Block.eval, Int.cast_mul, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = 1 + ((x.num : ℚ) / x.den) / (k + 1) * tail := by field_simp
    _ = _ := by rw [Rat.num_div_den]

/-- Exponential Horner steps expand into a sum with rising factorial denominators. -/
theorem horner_expStep (x : ℚ) (start n : Nat) :
    horner (expStep x) start n 0 =
      ∑ i ∈ Finset.range n, x ^ i / ((start + 1).ascFactorial i : ℚ) := by
  rw [horner_eq_sum_prod _ (fun _ => 1) (fun k => x / (k + 1)) (eval_expStep x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range,
    Nat.ascFactorial_eq_prod_range]
  push_cast
  simp only [mul_one, add_right_comm]

/-- The logarithm Horner step `tail ↦ x / (k + 1) + x * tail`. -/
def logStep (x : ℚ) (k : Nat) : Block :=
  ⟨x.num, Z.mul x.num (Int.ofNat (Nat.succ k)), Nat.mul x.den (Nat.succ k),
    Nat.mul_pos x.den_pos (Nat.succ_pos k)⟩

/-- The fields of a logarithm step, in ordinary notation. -/
theorem logStep_def (x : ℚ) (k : Nat) :
    logStep x k = ⟨x.num, x.num * (k + 1), x.den * (k + 1), Nat.mul_pos x.den_pos (by omega)⟩ := by
  unfold logStep
  rw [Z.mul_eq]
  rfl

/-- A logarithm block evaluates to `x / (k + 1) + x * tail`. -/
theorem eval_logStep (x : ℚ) (k : Nat) (tail : ℚ) :
    (logStep x k).eval tail = x / (k + 1) + x * tail := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt x.den_pos
  have hk : (k : ℚ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  simp only [logStep_def, Block.eval, Int.cast_mul, Int.cast_add, Int.cast_natCast,
    Int.cast_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = ((x.num : ℚ) / x.den) / (k + 1) + ((x.num : ℚ) / x.den) * tail := by
      field_simp
    _ = _ := by rw [Rat.num_div_den]

/-- Logarithm Horner steps expand into a sum with consecutive integer denominators. -/
theorem horner_logStep (x : ℚ) (start n : Nat) :
    horner (logStep x) start n 0 =
      ∑ i ∈ Finset.range n, x ^ (i + 1) / ((start + i + 1 : Nat) : ℚ) := by
  rw [horner_eq_sum_prod _ (fun k => x / (k + 1)) (fun _ => x) (eval_logStep x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_const, Finset.card_range]
  push_cast
  ring

/-- The arctangent Horner step `tail ↦ 1 / (2k + 1) - x ^ 2 * tail`. -/
def atanStep (x : ℚ) (k : Nat) : Block :=
  ⟨Int.ofNat (Nat.pow x.den 2),
    Z.negOfNat (Nat.mul (Nat.pow (Z.natAbs x.num) 2) (Nat.succ (Nat.mul 2 k))),
    Nat.mul (Nat.pow x.den 2) (Nat.succ (Nat.mul 2 k)),
    Nat.mul_pos (Nat.pow_pos x.den_pos) (Nat.succ_pos _)⟩

/-- The fields of an arctangent step, in ordinary notation. -/
theorem atanStep_def (x : ℚ) (k : Nat) :
    atanStep x k =
      ⟨x.den ^ 2, -(x.num ^ 2) * (2 * k + 1), x.den ^ 2 * (2 * k + 1),
        Nat.mul_pos (Nat.pow_pos x.den_pos) (Nat.succ_pos _)⟩ := by
  unfold atanStep
  congr 1
  rw [Z.negOfNat_eq, Z.natAbs_eq]
  change -(((x.num.natAbs ^ 2 * (2 * k + 1) : Nat) : Int)) = _
  push_cast
  rw [sq_abs]
  exact Int.neg_mul_eq_neg_mul _ _

/-- An arctangent block evaluates to `1 / (2k + 1) - x ^ 2 * tail`. -/
theorem eval_atanStep (x : ℚ) (k : Nat) (tail : ℚ) :
    (atanStep x k).eval tail = 1 / (2 * k + 1) - x ^ 2 * tail := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt x.den_pos
  have hk : (2 * k + 1 : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k)
  simp only [atanStep_def, Block.eval, Int.cast_mul, Int.cast_neg, Int.cast_pow, Int.cast_add,
    Int.cast_natCast, Int.cast_ofNat, Int.cast_one, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
    Nat.cast_ofNat, Nat.cast_one]
  calc
    _ = 1 / (2 * k + 1) - ((x.num : ℚ) / x.den) ^ 2 * tail := by
      field_simp
      exact (sub_eq_add_neg _ _).symm
    _ = _ := by rw [Rat.num_div_den]

/-- Arctangent Horner steps expand into a sum of powers of `-x ^ 2` over odd denominators. -/
theorem horner_atanStep (x : ℚ) (start n : Nat) :
    horner (atanStep x) start n 0 =
      ∑ i ∈ Finset.range n, (-x ^ 2) ^ i / ((2 * (start + i) + 1 : Nat) : ℚ) := by
  rw [horner_eq_sum_prod _ (fun k => 1 / (2 * k + 1)) (fun _ => -x ^ 2)
    (fun k tail => by rw [eval_atanStep]; ring)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_const, Finset.card_range]
  push_cast
  exact mul_one_div _ _

/--
The denominator `x.den ^ 2 * ((2k + offset + 1) * (2k + offset + 2))` of a sine or cosine step.
-/
def trigDenominator (x : ℚ) (offset k : Nat) : Nat :=
  Nat.mul (Nat.pow x.den 2)
    (Nat.mul (Nat.succ (Nat.add (Nat.mul 2 k) offset)) (Nat.add (Nat.add (Nat.mul 2 k) offset) 2))

/-- The denominator of a sine or cosine step is positive. -/
theorem trigDenominator_pos (x : ℚ) (offset k : Nat) : 0 < trigDenominator x offset k :=
  Nat.mul_pos (Nat.pow_pos x.den_pos) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))

/--
The sine and cosine Horner step `tail ↦ 1 - x ^ 2 * tail / ((2k + offset + 1) * (2k + offset + 2))`,
with `offset = 1` for sine and `offset = 0` for cosine.
-/
def trigStep (x : ℚ) (offset k : Nat) : Block :=
  ⟨Int.ofNat (trigDenominator x offset k), Z.negOfNat (Nat.pow (Z.natAbs x.num) 2),
    trigDenominator x offset k, trigDenominator_pos x offset k⟩

/-- A sine or cosine block evaluates to `1 - x ^ 2 / ((2k + offset + 1) * (2k + offset + 2)) *
tail`. -/
theorem eval_trigStep (x : ℚ) (offset k : Nat) (tail : ℚ) :
    (trigStep x offset k).eval tail =
      1 - x ^ 2 / ((2 * k + offset + 1) * (2 * k + offset + 2)) * tail := by
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt x.den_pos
  have h₁ : (2 * (k : ℚ) + offset + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k + offset)
  have h₂ : (2 * (k : ℚ) + offset + 2) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (2 * k + offset + 1)
  have hden : (trigDenominator x offset k : ℚ) =
      (x.den : ℚ) ^ 2 * ((2 * k + offset + 1) * (2 * k + offset + 2)) := by
    change ((x.den ^ 2 * ((2 * k + offset + 1) * (2 * k + offset + 2)) : Nat) : ℚ) = _
    push_cast
    rfl
  have hnum : ((Z.negOfNat (Nat.pow (Z.natAbs x.num) 2) : Int) : ℚ) = -(x.num : ℚ) ^ 2 := by
    rw [Z.negOfNat_eq, Z.natAbs_eq]
    change ((-((x.num.natAbs ^ 2 : Nat) : Int) : Int) : ℚ) = _
    push_cast
    rw [sq_abs]
  change (((Int.ofNat (trigDenominator x offset k) : Int) : ℚ) +
    ((Z.negOfNat (Nat.pow (Z.natAbs x.num) 2) : Int) : ℚ) * tail) / (trigDenominator x offset k :
      ℚ) = _
  rw [hnum, show ((Int.ofNat (trigDenominator x offset k) : Int) : ℚ) =
    (trigDenominator x offset k : ℚ) from Int.cast_natCast _, hden]
  calc
    _ = 1 - ((x.num : ℚ) / x.den) ^ 2 / ((2 * k + offset + 1) * (2 * k + offset + 2)) * tail := by
      field_simp
      exact (sub_eq_add_neg _ _).symm
    _ = _ := by rw [Rat.num_div_den]

/-- The product of the first `i` multipliers of the sine or cosine steps. -/
private theorem prod_trigStep (x : ℚ) (offset i : Nat) :
    ∏ j ∈ Finset.range i, -(x ^ 2 / ((2 * (j : ℚ) + offset + 1) * (2 * j + offset + 2))) =
      (-x ^ 2) ^ i * (offset.factorial : ℚ) / ((2 * i + offset).factorial : ℚ) := by
  have hfact : ∀ m : Nat, ((m.factorial : Nat) : ℚ) ≠ 0 := fun m =>
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
  induction i with
  | zero => simp [hfact]
  | succ i ih =>
    have h₁ : (2 * (i : ℚ) + offset + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * i + offset)
    have h₂ : (2 * (i : ℚ) + offset + 2) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero (2 * i + offset + 1)
    have hnext : ((2 * (i + 1) + offset).factorial : ℚ) =
        (2 * (i : ℚ) + offset + 2) * ((2 * i + offset + 1) * ((2 * i + offset).factorial : ℚ)) := by
      rw [show 2 * (i + 1) + offset = (2 * i + offset + 1) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast
      ring
    rw [Finset.prod_range_succ, ih, hnext]
    field_simp
    ring

/-- Sine and cosine Horner steps expand into the alternating sum over factorials. -/
theorem horner_trigStep (x : ℚ) (offset n : Nat) :
    horner (trigStep x offset) 0 n 0 =
      ∑ i ∈ Finset.range n,
        (-x ^ 2) ^ i * (offset.factorial : ℚ) / ((2 * i + offset).factorial : ℚ) := by
  rw [horner_eq_sum_prod _ (fun _ => 1)
    (fun k => -(x ^ 2 / ((2 * (k : ℚ) + offset + 1) * (2 * k + offset + 2))))
    (fun k tail => by rw [eval_trigStep]; ring)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.zero_add, mul_one]
  exact prod_trigStep x offset i

/-- Sum of the first `n` exponential terms, with one final rational normalization. -/
def exp (x : ℚ) (n : Nat) : ℚ :=
  let block := split (expStep x) 0 n
  mkRat block.constantTerm block.denominator

/-- Sum of the first `n` terms of `-log (1 - x)`, with one final rational normalization. -/
def logOneSub (x : ℚ) (n : Nat) : ℚ :=
  let block := split (logStep x) 0 n
  mkRat block.constantTerm block.denominator

/-- Sum of the first `n` arctangent terms, with one final rational normalization. -/
def atan (x : ℚ) (n : Nat) : ℚ :=
  let block := split (atanStep x) 0 n
  x * mkRat block.constantTerm block.denominator

/-- Sum of the first `n` nonzero terms of the sine series, with one final normalization. -/
def sin (x : ℚ) (n : Nat) : ℚ :=
  let block := split (trigStep x 1) 0 n
  x * mkRat block.constantTerm block.denominator

/-- Sum of the first `n` nonzero terms of the cosine series, with one final normalization. -/
def cos (x : ℚ) (n : Nat) : ℚ :=
  let block := split (trigStep x 0) 0 n
  mkRat block.constantTerm block.denominator

/-- `exp x n` is the sum of the first `n` terms of the exponential series. -/
theorem exp_eq_sum (x : ℚ) (n : Nat) :
    exp x n = ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ) := by
  have he := eval_split (expStep x) 0 n 0
  simpa [exp, Block.eval, Rat.mkRat_eq_div, horner_expStep, Nat.one_ascFactorial] using he

/-- `logOneSub x n` is the sum of the first `n` terms of the series for `-log (1 - x)`. -/
theorem logOneSub_eq_sum (x : ℚ) (n : Nat) :
    logOneSub x n = ∑ i ∈ Finset.range n, x ^ (i + 1) / ((i + 1 : Nat) : ℚ) := by
  have he := eval_split (logStep x) 0 n 0
  simpa [logOneSub, Block.eval, Rat.mkRat_eq_div, horner_logStep] using he

/-- `atan x n` is the sum of the first `n` terms of the arctangent series. -/
theorem atan_eq_sum (x : ℚ) (n : Nat) :
    atan x n = ∑ i ∈ Finset.range n, (-1) ^ i * x ^ (2 * i + 1) / ((2 * i + 1 : Nat) : ℚ) := by
  have he := eval_split (atanStep x) 0 n 0
  simp only [Block.eval, mul_zero, add_zero] at he
  rw [atan, Rat.mkRat_eq_div, he, horner_atanStep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_pow, ← pow_mul, pow_succ, Nat.zero_add]
  ring

/-- `sin x n` is the sum of the first `n` nonzero terms of the sine series. -/
theorem sin_eq_sum (x : ℚ) (n : Nat) :
    sin x n = ∑ i ∈ Finset.range n, (-1) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℚ) := by
  have he := eval_split (trigStep x 1) 0 n 0
  simp only [Block.eval, mul_zero, add_zero] at he
  rw [sin, Rat.mkRat_eq_div, he, horner_trigStep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_pow, ← pow_mul, pow_succ, Nat.factorial_one, Nat.cast_one]
  ring

/-- `cos x n` is the sum of the first `n` nonzero terms of the cosine series. -/
theorem cos_eq_sum (x : ℚ) (n : Nat) :
    cos x n = ∑ i ∈ Finset.range n, (-1) ^ i * x ^ (2 * i) / ((2 * i).factorial : ℚ) := by
  have he := eval_split (trigStep x 0) 0 n 0
  simp only [Block.eval, mul_zero, add_zero] at he
  rw [cos, Rat.mkRat_eq_div, he, horner_trigStep]
  apply Finset.sum_congr rfl
  intro i _
  rw [neg_pow, ← pow_mul, Nat.factorial_zero, Nat.cast_one, Nat.add_zero]
  ac_rfl

end FloatLib.Numerics.Enclosure.Taylor

namespace FloatLib.Numerics.Enclosure.Taylor.Compiled.split

-- The docstring names a lemma that Lean generates for the matcher, which `auxLemma` reports.
set_option linter.auxLemma false in
/-- The split matcher returns its corresponding branch when the length is zero. -/
add_decl_doc match_1.congr_eq_1

end FloatLib.Numerics.Enclosure.Taylor.Compiled.split

namespace FloatLib.Numerics.Enclosure.Taylor.Compiled.split

-- The docstring names a lemma that Lean generates for the matcher, which `auxLemma` reports.
set_option linter.auxLemma false in
/-- The split matcher returns its corresponding branch when the length is one. -/
add_decl_doc match_1.congr_eq_2

end FloatLib.Numerics.Enclosure.Taylor.Compiled.split

namespace FloatLib.Numerics.Enclosure.Taylor.Compiled.split

-- The docstring names a lemma that Lean generates for the matcher, which `auxLemma` reports.
set_option linter.auxLemma false in
/-- The split matcher returns its recursive branch when the length is at least two. -/
add_decl_doc match_1.congr_eq_3

end FloatLib.Numerics.Enclosure.Taylor.Compiled.split
