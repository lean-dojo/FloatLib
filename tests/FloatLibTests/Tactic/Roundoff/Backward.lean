/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Util.CollectAxioms
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Tactic.FloatDecide
public import FloatLib.Tactic.Roundoff
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Backward-error theorems from `roundoff (backward := true)`

Each check states the theorem that the command generates, so a change of a generated statement
fails here. The programs are those of the forward tests: Horner's rule written out and over an
array, dot products over `Fin n`, a list of pairs and vectors, a row of a matrix-vector product,
one output of a linear layer, a plain sum, a fused multiply-add, and a bfloat16 dot product
accumulated in binary32.

* A dot product is the exact dot product of a perturbed left factor. The entry at index `j` of
  `n` takes one rounding of its product and one of each of the `n - j` additions after it, so its
  bound is `(1 + u) ^ (n - 1 - j + 2) - 1`, and the products that may underflow leave the absolute
  term `η * (1 + u) * ∑ k < n, (1 + u) ^ k`.
* A sum, and a dot product whose products are exact, have no absolute term: the statement is an
  equality.
* The premise is that the computed value is finite, as long as finiteness passes from each
  result to its operands; the range premise of an exact product stays. At concrete binary32
  inputs the kernel decides it (`float_decide`), so the theorems are not vacuous.
* `(perturb := [y])` and `(factor := right)` move the perturbation to the other factor, and an
  input read twice is left unperturbed when the other inputs can take the roundings.
* The rows of a matrix-vector product combine into one perturbed matrix.
* The backward statement of a sum or a dot product gives its forward bound in closed form, and
  a relative one when the terms have one sign.
* A square takes a rounding as its square root in both reads, so a square, a sum of squares, a
  squared distance and a Euclidean norm are the exact ones of perturbed inputs. The two entries
  of a squared difference take one perturbation.
* A step may perturb several entries, as one with two products does, and may contain a loop:
  the sum of the entries of a matrix perturbs each entry by the roundings of its row and of the
  rows after it. A loop whose state is a pair is followed through one numerical component.
* A branch keeps the condition of the program and takes a rounding in both alternatives, so a
  perceptron with one hidden layer of rectifiers is the exact one for perturbed weights. A
  maximum or minimum of finite values is exact and takes a rounding in both operands.
* A rounding that no input of its own operation takes moves onto the other factor of the
  product around it. So a polynomial in monomial form and Estrin's scheme, where the point is
  read several times and stays unperturbed, are the exact ones for perturbed coefficients, and
  a dot product with centered data is the exact one for perturbed weights.
* A product of entries is the exact product of perturbed entries, each within one rounding.
  The underflow of the products stays a recurrence over the steps, because the slope of a step
  in its accumulator is an entry.
* A value that is computed from floating-point values is never taken as exact data: a
  real-valued definition of the program is expanded, the cast of an integer computed from
  comparisons of floating-point values is refused, and so is a rounding function of FloatLib
  applied to a real. A literal is the real number that the format stores.
* A sum with a literal, a square added to its own base, a cube, a difference that cancels a
  shared input, a correctly rounded exponential, a loop of quotients whose roundings all move
  onto its start and a compensated sum are refused, each with the reason.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

section Configured

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

local notation "u" => Model.unitRoundoffAt format

local notation "η" => Model.underflowErrorAt format

/-- Horner's rule for `a x² + b x + c`. -/
def horner (a b c x : Value) : Value :=
  (a * x + b) * x + c

/-- Horner's rule is the exact polynomial with perturbed coefficients. -/
roundoff (backward := true) theorem horner_backward :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (horner a b c x)

/-- The coefficients take four, three and one rounding, and the two products that may underflow
leave an absolute term. The evaluation point, read twice, is not perturbed. -/
example (a b c x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (horner a b c x) = true) :
    ∃ δa δb δc : ℝ, |δa| ≤ (1 + u) ^ 4 - 1 ∧ |δb| ≤ (1 + u) ^ 3 - 1 ∧ |δc| ≤ u ∧
      |ExecFloat.Binary.toReal (horner a b c x) -
          ((ExecFloat.Binary.toReal a * (1 + δa) * ExecFloat.Binary.toReal x +
              ExecFloat.Binary.toReal b * (1 + δb)) * ExecFloat.Binary.toReal x +
            ExecFloat.Binary.toReal c * (1 + δc))| ≤
        (η * (1 + u) * |ExecFloat.Binary.toReal x| * (1 + u) + η) * (1 + u) :=
  horner_backward a b c x hformat hfinite

/-- The dot product of two functions on `Fin n`, from zero. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

/-- The dot product is the exact dot product of a perturbed left factor. -/
roundoff (backward := true) theorem dot_backward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

/-- The statement at every length: a finite result is the only premise. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 2) - 1) ∧
      |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j)) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  dot_backward x y hformat hfinite

/-- One bound for every entry: `(1 + u) ^ (n + 1) - 1`, as in the textbook statement. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n + 1) - 1) ∧
      |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j)) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k := by
  obtain ⟨δ, hδ, hmain⟩ := dot_backward x y hformat hfinite
  refine ⟨δ, fun j => (hδ j).trans (sub_le_sub_right (pow_le_pow_right₀ ?_ ?_) 1), hmain⟩
  · linarith [Model.unitRoundoffAt_pos format]
  · have := j.isLt
    omega

/-- The same dot product with the right factor perturbed. -/
roundoff (backward := true) (perturb := [y]) theorem dot_backward_right :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 2) - 1) ∧
      |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (x j) * (ExecFloat.Binary.toReal (y j) * (1 + δ j))) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  dot_backward_right x y hformat hfinite

/-- `(factor := right)` gives the rounding of each product to its right factor. -/
roundoff (backward := true) (factor := right) theorem dot_backward_factor :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 2) - 1) ∧
      |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (x j) * (ExecFloat.Binary.toReal (y j) * (1 + δ j))) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  dot_backward_factor x y hformat hfinite

/-- The dot product of a list of pairs. -/
def dotList (pairs : List (Value × Value)) : Value :=
  pairs.foldl (fun sum pair => sum + pair.1 * pair.2) 0

/-- Over a list the perturbations are a list of the same length, beside the pairs. -/
roundoff (backward := true) theorem dotList_backward :=
  fun (pairs : List (Value × Value)) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dotList pairs)

example (pairs : List (Value × Value)) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dotList pairs) = true) :
    ∃ δs : List ℝ, (δs.length = pairs.length ∧ ∀ (k : ℕ) (_ : k < pairs.length)
        (hp : k < δs.length), |δs[k]| ≤ (1 + u) ^ (pairs.length - 1 - k + 2) - 1) ∧
      |ExecFloat.Binary.toReal (dotList pairs) - (pairs.zip δs).foldl (fun s entry =>
          s + ExecFloat.Binary.toReal entry.1.1 * (1 + entry.2) *
            ExecFloat.Binary.toReal entry.1.2) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range pairs.length, (1 + u) ^ k :=
  dotList_backward pairs hformat hfinite

/-- Horner's rule over the coefficients of an array, highest degree first. -/
def hornerArray (coefficients : Array Value) (x : Value) : Value :=
  coefficients.foldl (fun value coefficient => value * x + coefficient) 0

/-- Horner's rule is the exact polynomial with perturbed coefficients. -/
roundoff (backward := true) theorem hornerArray_backward :=
  fun (coefficients : Array Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (hornerArray coefficients x)

/-- The coefficient at position `k` of `n` takes `2 (n - 1 - k) + 1` roundings, and the absolute
term grows with the powers of `|x|`. -/
example (coefficients : Array Value) (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (hornerArray coefficients x) = true) :
    ∃ δs : List ℝ, (δs.length = coefficients.toList.length ∧
        ∀ (k : ℕ) (_ : k < coefficients.toList.length) (hp : k < δs.length),
          |δs[k]| ≤ (1 + u) ^ (2 * (coefficients.toList.length - 1 - k) + 1) - 1) ∧
      |ExecFloat.Binary.toReal (hornerArray coefficients x) -
          (coefficients.toList.zip δs).foldl (fun s entry =>
            s * ExecFloat.Binary.toReal x + ExecFloat.Binary.toReal entry.1 * (1 + entry.2)) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range coefficients.toList.length,
          (|ExecFloat.Binary.toReal x| * ((1 + u) * (1 + u))) ^ k :=
  hornerArray_backward coefficients x hformat hfinite

/-- Horner's rule from its leading coefficient: the start takes the roundings of every step. -/
roundoff (backward := true) theorem hornerLead_backward :=
  fun (lead : Value) (coefficients : List Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (coefficients.foldl (fun value coefficient => value * x + coefficient) lead)

example (lead : Value) (coefficients : List Value) (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (coefficients.foldl (fun value coefficient => value * x + coefficient) lead) = true) :
    ∃ (δ₀ : ℝ) (δs : List ℝ), |δ₀| ≤ (1 + u) ^ (2 * coefficients.length) - 1 ∧
      (δs.length = coefficients.length ∧ ∀ (k : ℕ) (_ : k < coefficients.length)
        (hp : k < δs.length), |δs[k]| ≤ (1 + u) ^ (2 * (coefficients.length - 1 - k) + 1) - 1) ∧
      |ExecFloat.Binary.toReal
            (coefficients.foldl (fun value coefficient => value * x + coefficient) lead) -
          (coefficients.zip δs).foldl (fun s entry =>
            s * ExecFloat.Binary.toReal x + ExecFloat.Binary.toReal entry.1 * (1 + entry.2))
            (ExecFloat.Binary.toReal lead * (1 + δ₀))| ≤
        η * (1 + u) * ∑ k ∈ Finset.range coefficients.length,
          (|ExecFloat.Binary.toReal x| * ((1 + u) * (1 + u))) ^ k :=
  hornerLead_backward lead coefficients x hformat hfinite

/-- Row `i` of the product of a matrix with a vector. -/
def mulVec {m n : Nat} (A : Matrix (Fin m) (Fin n) Value) (v : Fin n → Value) (i : Fin m) :
    Value :=
  Fin.foldl n (fun sum j => sum + A i j * v j) 0

/-- Each entry of the product is the exact entry for a perturbed row of the matrix. -/
roundoff (backward := true) theorem mulVec_backward :=
  fun {m n : Nat} (A : Matrix (Fin m) (Fin n) Value) (v : Fin n → Value) (i : Fin m)
    (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mulVec A v i)

/-- The rows combine: each row of the matrix is read by one entry of the product, so the computed
product is the exact product of one perturbed matrix with the vector, up to the absolute term. -/
example {m n : Nat} (A : Matrix (Fin m) (Fin n) Value) (v : Fin n → Value)
    (hformat : format.isIEEE = true)
    (hfinite : ∀ i, ExecFloat.Binary.isFinite (mulVec A v i) = true) :
    ∃ δ : Fin m → Fin n → ℝ, (∀ i j, |δ i j| ≤ (1 + u) ^ (n - 1 - j + 2) - 1) ∧
      ∀ i, |ExecFloat.Binary.toReal (mulVec A v i) - (List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (A i j) * (1 + δ i j) * ExecFloat.Binary.toReal (v j)) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k := by
  choose δ hδ hmain using fun i => mulVec_backward A v i hformat (hfinite i)
  exact ⟨δ, hδ, hmain⟩

/-- One output of a linear layer: a dot product of weights and inputs, plus a bias. -/
def linear {n : Nat} (w x : Fin n → Value) (b : Value) : Value :=
  Fin.foldl n (fun s j => s + w j * x j) 0 + b

/-- The output is the exact output for perturbed weights and a perturbed bias: the rounding of
the last addition moves onto the bias and onto every weight. -/
roundoff (backward := true) theorem linear_backward :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (linear w x b)

example {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (linear w x b) = true) :
    ∃ (δb : ℝ) (δw : Fin n → ℝ), |δb| ≤ u ∧ (∀ j, |δw j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal (linear w x b) -
          ((List.finRange n).foldl (fun s j =>
              s + ExecFloat.Binary.toReal (w j) * (1 + δw j) * ExecFloat.Binary.toReal (x j)) 0 +
            ExecFloat.Binary.toReal b * (1 + δb))| ≤
        η * (1 + u) * (∑ k ∈ Finset.range n, (1 + u) ^ k) * (1 + u) :=
  linear_backward w x b hformat hfinite

/-- The sum of a function on `Fin n`. -/
def sum {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j) 0

/-- A sum has no absolute term, since an addition has no underflow error: the computed sum is the
exact sum of perturbed terms. -/
roundoff (backward := true) theorem sum_backward :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sum x)

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (sum x) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 1) - 1) ∧
      ExecFloat.Binary.toReal (sum x) =
        (List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (x j) * (1 + δ j)) 0 :=
  sum_backward x hformat hfinite

/-- The backward statement gives a forward bound in closed form: the error of the sum is at most
the sum of the terms' magnitudes, each weighted by the bound of its perturbation. -/
example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (sum x) = true) :
    |ExecFloat.Binary.toReal (sum x) -
        (List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (x j)) 0| ≤
      ((List.finRange n).map fun j : Fin n =>
        ((1 + u) ^ (n - 1 - j + 1) - 1) * |ExecFloat.Binary.toReal (x j)|).sum := by
  obtain ⟨δ, hδ, hsum⟩ := sum_backward x hformat hfinite
  rw [hsum]
  refine List.abs_foldl_add_sub_le _ _ _ _ fun j _ => ?_
  rw [show ExecFloat.Binary.toReal (x j) * (1 + δ j) - ExecFloat.Binary.toReal (x j) =
    δ j * ExecFloat.Binary.toReal (x j) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_right (hδ j) (abs_nonneg _)

/-- The forward bound of the dot product from its backward statement: each product weighted by
the bound of its perturbation, plus the absolute term. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
        s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0| ≤
      ((List.finRange n).map fun j : Fin n => ((1 + u) ^ (n - 1 - j + 2) - 1) *
        |ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)|).sum +
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k := by
  obtain ⟨δ, hδ, hmain⟩ := dot_backward x y hformat hfinite
  have hforward := List.abs_foldl_add_sub_le (List.finRange n)
    (fun j => ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j))
    (fun j => ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j))
    (fun j : Fin n => ((1 + u) ^ (n - 1 - j + 2) - 1) *
      |ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)|) fun j _ => by
        rw [show ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j) -
          ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j) =
            δ j * (ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) by ring, abs_mul]
        exact mul_le_mul_of_nonneg_right (hδ j) (abs_nonneg _)
  have htriangle := abs_sub_le (ExecFloat.Binary.toReal (dot x y))
    ((List.finRange n).foldl (fun s j =>
      s + ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j)) 0)
    ((List.finRange n).foldl (fun s j =>
      s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0)
  linarith

/-- Without cancellation the backward statement gives a relative forward bound in closed form:
a dot product of nonnegative factors is within `(1 + u) ^ (n + 1) - 1` of the exact one,
relative to it, plus the absolute term. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true)
    (hx : ∀ j, 0 ≤ ExecFloat.Binary.toReal (x j)) (hy : ∀ j, 0 ≤ ExecFloat.Binary.toReal (y j)) :
    |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
        s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0| ≤
      ((1 + u) ^ (n + 1) - 1) * (List.finRange n).foldl (fun s j =>
        s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0 +
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k := by
  obtain ⟨δ, hδ, hmain⟩ := dot_backward x y hformat hfinite
  have hforward := List.abs_foldl_add_sub_le_mul (List.finRange n)
    (fun j => ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j))
    (fun j => ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j))
    ((1 + u) ^ (n + 1) - 1) fun j _ => by
      have hterm := mul_nonneg (hx j) (hy j)
      rw [show ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j) -
        ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j) =
          δ j * (ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) by ring, abs_mul,
        abs_of_nonneg hterm]
      refine mul_le_mul_of_nonneg_right
        ((hδ j).trans (sub_le_sub_right (pow_le_pow_right₀ ?_ ?_) 1)) hterm
      · linarith [Model.unitRoundoffAt_pos format]
      · have := j.isLt
        omega
  have htriangle := abs_sub_le (ExecFloat.Binary.toReal (dot x y))
    ((List.finRange n).foldl (fun s j =>
      s + ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j)) 0)
    ((List.finRange n).foldl (fun s j =>
      s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0)
  linarith

/-- Horner's rule over `Fin n`, from zero. -/
def hornerFin {n : Nat} (a : Fin n → Value) (x : Value) : Value :=
  Fin.foldl n (fun s j => s * x + a j) 0

/-- Horner's rule is the exact one on perturbed coefficients. -/
roundoff (backward := true) theorem hornerFin_backward :=
  fun {n : Nat} (a : Fin n → Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (hornerFin a x)

/-- The forward bound of Horner's rule from its backward statement: Horner's rule on the
magnitudes, each coefficient weighted by the bound of its perturbation, plus the absolute
term. -/
example {n : Nat} (a : Fin n → Value) (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (hornerFin a x) = true) :
    |ExecFloat.Binary.toReal (hornerFin a x) - (List.finRange n).foldl (fun s j =>
        s * ExecFloat.Binary.toReal x + ExecFloat.Binary.toReal (a j)) 0| ≤
      (List.finRange n).foldl (fun e (j : Fin n) => e * |ExecFloat.Binary.toReal x| +
        ((1 + u) ^ (2 * (n - 1 - j) + 1) - 1) * |ExecFloat.Binary.toReal (a j)|) 0 +
        η * (1 + u) *
          ∑ k ∈ Finset.range n, (|ExecFloat.Binary.toReal x| * ((1 + u) * (1 + u))) ^ k := by
  obtain ⟨δ, hδ, hmain⟩ := hornerFin_backward a x hformat hfinite
  have hforward := List.abs_foldl_affine_sub_le (List.finRange n)
    (fun _ => ExecFloat.Binary.toReal x)
    (fun j => ExecFloat.Binary.toReal (a j) * (1 + δ j))
    (fun j => ExecFloat.Binary.toReal (a j))
    (fun j : Fin n => ((1 + u) ^ (2 * (n - 1 - j) + 1) - 1) * |ExecFloat.Binary.toReal (a j)|)
    (fun j _ => by
      rw [show ExecFloat.Binary.toReal (a j) * (1 + δ j) - ExecFloat.Binary.toReal (a j) =
        δ j * ExecFloat.Binary.toReal (a j) by ring, abs_mul]
      exact mul_le_mul_of_nonneg_right (hδ j) (abs_nonneg _)) 0 0
  rw [sub_self, abs_zero] at hforward
  have htriangle := abs_sub_le (ExecFloat.Binary.toReal (hornerFin a x))
    ((List.finRange n).foldl (fun s j =>
      s * ExecFloat.Binary.toReal x + ExecFloat.Binary.toReal (a j) * (1 + δ j)) 0)
    ((List.finRange n).foldl (fun s j =>
      s * ExecFloat.Binary.toReal x + ExecFloat.Binary.toReal (a j)) 0)
  linarith

/-- An input read twice is left unperturbed when the other inputs take the roundings. -/
roundoff (backward := true) theorem shared_backward :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (x * y + x * z)

example (x y z : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (x * y + x * z) = true) :
    ∃ δy δz : ℝ, |δy| ≤ (1 + u) ^ 2 - 1 ∧ |δz| ≤ (1 + u) ^ 2 - 1 ∧
      |ExecFloat.Binary.toReal (x * y + x * z) -
          (ExecFloat.Binary.toReal x * (ExecFloat.Binary.toReal y * (1 + δy)) +
            ExecFloat.Binary.toReal x * (ExecFloat.Binary.toReal z * (1 + δz)))| ≤
        (η + η) * (1 + u) :=
  shared_backward x y z hformat hfinite

/-- A quotient takes its rounding in the numerator, and keeps a finite divisor as a premise. -/
roundoff (backward := true) theorem quotient_backward :=
  fun (a b c : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((a + b) / c)

example (a b c : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite ((a + b) / c) = true ∧
      ExecFloat.Binary.isFinite c = true) :
    ∃ δa δb : ℝ, |δa| ≤ (1 + u) ^ 2 - 1 ∧ |δb| ≤ (1 + u) ^ 2 - 1 ∧
      |ExecFloat.Binary.toReal ((a + b) / c) -
          (ExecFloat.Binary.toReal a * (1 + δa) + ExecFloat.Binary.toReal b * (1 + δb)) /
            ExecFloat.Binary.toReal c| ≤ η :=
  quotient_backward a b c hformat hfinite

/-- With `mixed`, the forward bound and the backward statement stand together under the range
conditions of the forward bound, which give the finiteness the backward statement needs. -/
roundoff (backward := true) mixed theorem dot_both :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

/-- The backward statement of the mixed form, under the conditions of the forward bound. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) := fun hvalid =>
  show ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 2) - 1) ∧
      |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j)) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k from
    (dot_both x y hformat hvalid).2

/-- `(backward := false)` is the forward command. -/
roundoff (backward := false) mixed theorem sum_forward :=
  fun (a b : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (a + b)

example (a b : Value) (hformat : format.isIEEE = true) := fun hvalid =>
  show MixedError (ExecFloat.Binary.toReal (a + b))
      (ExecFloat.Binary.toReal a + ExecFloat.Binary.toReal b) u 0 from
    (sum_forward a b hformat hvalid).2

/-! ### Squares -/

/-- A square is the exact square of a perturbed input: both reads take the square root of the
factor of the rounding. -/
roundoff (backward := true) theorem square_backward :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x * x)

example (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (x * x) = true) :
    ∃ δx : ℝ, |δx| ≤ u ∧
      |ExecFloat.Binary.toReal (x * x) -
          ExecFloat.Binary.toReal x * (1 + δx) * (ExecFloat.Binary.toReal x * (1 + δx))| ≤ η :=
  square_backward x hformat hfinite

/-- A sum of squares is the exact sum of squares of perturbed entries. -/
roundoff (backward := true) theorem sumSquares_backward :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value))

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 2) - 1) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)) -
          (List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (x j) * (1 + δ j) *
            (ExecFloat.Binary.toReal (x j) * (1 + δ j))) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  sumSquares_backward x hformat hfinite

/-- A squared distance: the two entries of a difference take the same perturbation. -/
roundoff (backward := true) theorem distance_backward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (Fin.foldl n (fun s j => s + (x j - y j) * (x j - y j)) (0 : Value))

example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => s + (x j - y j) * (x j - y j)) (0 : Value)) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal
            (Fin.foldl n (fun s j => s + (x j - y j) * (x j - y j)) (0 : Value)) -
          (List.finRange n).foldl (fun s j => s +
            (ExecFloat.Binary.toReal (x j) * (1 + δ j) -
                ExecFloat.Binary.toReal (y j) * (1 + δ j)) *
              (ExecFloat.Binary.toReal (x j) * (1 + δ j) -
                ExecFloat.Binary.toReal (y j) * (1 + δ j))) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  distance_backward x y hformat hfinite

/-- A fourth power: the square of a square splits the outer rounding twice. -/
roundoff (backward := true) theorem fourth_backward :=
  fun (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((x * x) * (x * x))

/-- A sum of squares takes a later rounding as the square root in each entry. -/
roundoff (backward := true) theorem shiftedSquares_backward :=
  fun {n : Nat} (x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value) + b)

example {n : Nat} (x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value) + b) = true) :
    ∃ (δb : ℝ) (δ : Fin n → ℝ), |δb| ≤ u ∧ (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value) + b) -
          ((List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (x j) * (1 + δ j) *
              (ExecFloat.Binary.toReal (x j) * (1 + δ j))) 0 +
            ExecFloat.Binary.toReal b * (1 + δb))| ≤
        η * (1 + u) * (∑ k ∈ Finset.range n, (1 + u) ^ k) * (1 + u) :=
  shiftedSquares_backward x b hformat hfinite

/-- The Euclidean norm is the exact norm of a perturbed vector. The argument of the square root
takes the square of its rounding, so each entry takes that rounding once more than it must. The
premises are that the sum of squares is finite and not negative. -/
roundoff (backward := true) theorem norm_backward :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (ExecFloat.sqrt (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)))

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hsign : ExecFloat.Binary.isZero (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)) = true ∨
      ExecFloat.Binary.signBit (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)) = false)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)) = true) :
    ∃ δ : Fin n → ℝ, (∀ j, |δ j| ≤ (1 + u) ^ (n - 1 - j + 4) - 1) ∧
      |ExecFloat.Binary.toReal
            (ExecFloat.sqrt (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value))) -
          √((List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (x j) * (1 + δ j) *
            (ExecFloat.Binary.toReal (x j) * (1 + δ j))) 0)| ≤
        √(η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k) * (1 + u) + η :=
  norm_backward x hformat ⟨hsign, hfinite⟩

/-! ### Several perturbations in a step, and loops inside a step -/

/-- Two products in a step: each left factor takes its own perturbation. The first product is
rounded once more, by the addition of the second. -/
roundoff (backward := true) theorem twoProducts_backward :=
  fun {n : Nat} (a b x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + a j * x j + b j * y j) (0 : Value))

example {n : Nat} (a b x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => s + a j * x j + b j * y j) (0 : Value)) = true) :
    ∃ δa δb : Fin n → ℝ, (∀ j, |δa j| ≤ (1 + u) ^ (2 * (n - 1 - j) + 3) - 1) ∧
      (∀ j, |δb j| ≤ (1 + u) ^ (2 * (n - 1 - j) + 2) - 1) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + a j * x j + b j * y j) (0 : Value)) -
          (List.finRange n).foldl (fun s j =>
            s + ExecFloat.Binary.toReal (a j) * (1 + δa j) * ExecFloat.Binary.toReal (x j) +
              ExecFloat.Binary.toReal (b j) * (1 + δb j) * ExecFloat.Binary.toReal (y j)) 0| ≤
        (η * (1 + u) + η) * (1 + u) * ∑ k ∈ Finset.range n, ((1 + u) * (1 + u)) ^ k :=
  twoProducts_backward a b x y hformat hfinite

/-- The sum of the entries of a matrix, row by row: entry `(i, j)` takes the additions of its
row from `j` on and those of the rows from `i` on. No operation can underflow, so the statement
is an equality. -/
roundoff (backward := true) theorem total_backward :=
  fun {m n : Nat} (A : Fin m → Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (Fin.foldl m (fun s i => s + Fin.foldl n (fun t j => t + A i j) 0) (0 : Value))

example {m n : Nat} (A : Fin m → Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl m (fun s i => s + Fin.foldl n (fun t j => t + A i j) 0) (0 : Value)) = true) :
    ∃ δA : Fin m → Fin n → ℝ,
      (∀ i j, |δA i j| ≤ (1 + u) ^ (n - 1 - j + (m - 1 - i) + 2) - 1) ∧
      ExecFloat.Binary.toReal
          (Fin.foldl m (fun s i => s + Fin.foldl n (fun t j => t + A i j) 0) (0 : Value)) =
        (List.finRange m).foldl (fun s i => s + (List.finRange n).foldl (fun t j =>
          t + ExecFloat.Binary.toReal (A i j) * (1 + δA i j)) 0) 0 :=
  total_backward A hformat hfinite

/-- A bilinear form `y^T A x`: the left factor of each row and the entries of the row take
perturbations. -/
roundoff (backward := true) theorem bilinear_backward :=
  fun {m n : Nat} (A : Fin m → Fin n → Value) (x : Fin n → Value) (y : Fin m → Value)
    (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (Fin.foldl m (fun s i => s + y i * Fin.foldl n (fun t j => t + A i j * x j) 0) (0 : Value))

/-- The entries of a list of lists, row by row. The bound of an entry reads the length of its
own row. -/
roundoff (backward := true) theorem rows_backward :=
  fun (rows : List (List Value)) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (rows.foldl (fun s row => s + row.foldl (fun t a => t + a) 0) (0 : Value))

/-- A sum counted beside its terms: the loop carries the sum and the number of terms, and the
analysis follows the sum. -/
def countedSum (values : List Value) : Value :=
  (values.foldl (fun (state : Value × Nat) value => (state.1 + value, state.2 + 1)) (0, 0)).1

roundoff (backward := true) theorem countedSum_backward :=
  fun (values : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (countedSum values)

example (values : List Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (countedSum values) = true) :
    ∃ δ : List ℝ, (δ.length = values.length ∧ ∀ k (_ : k < values.length) (hp : k < δ.length),
        |δ[k]| ≤ (1 + u) ^ (values.length - 1 - k + 1) - 1) ∧
      ExecFloat.Binary.toReal (countedSum values) =
        (values.zip δ).foldl
          (fun s entry => s + ExecFloat.Binary.toReal entry.1 * (1 + entry.2)) 0 :=
  countedSum_backward values hformat hfinite

/-! ### Branches -/

/-- The rectifier, as a branch on the sign of its argument. -/
def relu (z : Value) : Value := if z > 0 then z else 0

/-- One neuron: the reference keeps the branch the program takes, on the computed
pre-activation, and that this pre-activation is finite is the premise. -/
roundoff (backward := true) theorem neuron_backward :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (relu (linear w x b))

example {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (linear w x b) = true) :
    ∃ (δb : ℝ) (δw : Fin n → ℝ), |δb| ≤ u ∧ (∀ j, |δw j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal (relu (linear w x b)) -
          (if linear w x b > 0 then
            (List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (w j) * (1 + δw j) *
              ExecFloat.Binary.toReal (x j)) 0 + ExecFloat.Binary.toReal b * (1 + δb)
          else 0)| ≤
        if linear w x b > 0 then η * (1 + u) * (∑ k ∈ Finset.range n, (1 + u) ^ k) * (1 + u)
        else 0 :=
  neuron_backward w x b hformat hfinite

/-- One output of a perceptron with one hidden layer of rectifiers. -/
def perceptron {n h : Nat} (W : Fin h → Fin n → Value) (b v : Fin h → Value) (c : Value)
    (x : Fin n → Value) : Value :=
  Fin.foldl h (fun s k => s + v k * relu (linear (W k) x (b k))) 0 + c

/-- The perceptron is the exact one for perturbed weights and biases of both layers. -/
roundoff (backward := true) theorem perceptron_backward :=
  fun {n h : Nat} (W : Fin h → Fin n → Value) (b v : Fin h → Value) (c : Value)
    (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (perceptron W b v c x)

/-- The output bias takes one rounding, an output weight those of its product and of the later
additions, a hidden bias one, and a hidden weight those of its own dot product. The premises are
a finite output and finite pre-activations. The absolute term, here left unnamed, is the
accumulated underflow of the products. -/
example {n h : Nat} (W : Fin h → Fin n → Value) (b v : Fin h → Value) (c : Value)
    (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (perceptron W b v c x) = true)
    (hhidden : ∀ k, ExecFloat.Binary.isFinite (linear (W k) x (b k)) = true) :
    ∃ (δc : ℝ) (δv δb : Fin h → ℝ) (δW : Fin h → Fin n → ℝ) (budget : ℝ),
      |δc| ≤ u ∧ (∀ k, |δv k| ≤ (1 + u) ^ (h - 1 - k + 3) - 1) ∧ (∀ k, |δb k| ≤ u) ∧
      (∀ k j, |δW k j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal (perceptron W b v c x) -
          ((List.finRange h).foldl (fun s k => s + ExecFloat.Binary.toReal (v k) * (1 + δv k) *
            (if linear (W k) x (b k) > 0 then
              (List.finRange n).foldl (fun t j => t + ExecFloat.Binary.toReal (W k j) *
                (1 + δW k j) * ExecFloat.Binary.toReal (x j)) 0 +
                  ExecFloat.Binary.toReal (b k) * (1 + δb k)
            else 0)) 0 + ExecFloat.Binary.toReal c * (1 + δc))| ≤ budget := by
  obtain ⟨δc, δv, δb, δW, hc, hv, hb, hW, hmain⟩ := perceptron_backward W b v c x hformat
    ⟨hfinite, List.AllSteps.of_forall _ _ _ _ fun _ k => hhidden k⟩
  exact ⟨δc, δv, δb, δW, _, hc, hv, hb, hW, hmain⟩

/-- A maximum of finite values is exact and takes a rounding in both operands. -/
roundoff (backward := true) theorem maximum_backward :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (max x y + z)

example (x y z : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (max x y + z) = true)
    (hx : ExecFloat.Binary.isFinite x = true) (hy : ExecFloat.Binary.isFinite y = true) :
    ∃ δx δy δz : ℝ, |δx| ≤ u ∧ |δy| ≤ u ∧ |δz| ≤ u ∧
      ExecFloat.Binary.toReal (max x y + z) =
        max (ExecFloat.Binary.toReal x * (1 + δx)) (ExecFloat.Binary.toReal y * (1 + δy)) +
          ExecFloat.Binary.toReal z * (1 + δz) :=
  maximum_backward x y z hformat ⟨hfinite, hx, hy⟩

/-- The rectifier as a maximum with zero: the reference is the rectifier of the exact
pre-activation of perturbed weights, with no condition on a computed value. -/
roundoff (backward := true) theorem rectifier_backward :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (max (linear w x b) 0)

example {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (linear w x b) = true) :
    ∃ (δb : ℝ) (δw : Fin n → ℝ), |δb| ≤ u ∧ (∀ j, |δw j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal (max (linear w x b) 0) -
          max ((List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (w j) * (1 + δw j) *
            ExecFloat.Binary.toReal (x j)) 0 + ExecFloat.Binary.toReal b * (1 + δb)) 0| ≤
        η * (1 + u) * (∑ k ∈ Finset.range n, (1 + u) ^ k) * (1 + u) :=
  rectifier_backward w x b hformat hfinite

/-! ### Roundings that move onto the other factor of a product -/

/-- A polynomial in monomial form. The point `x` is read three times, with roundings that
differ, so it stays unperturbed, and the rounding of `x * x` moves onto `a`. -/
roundoff (backward := true) theorem monomial_backward :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (a * (x * x) + b * x + c)

example (a b c x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (a * (x * x) + b * x + c) = true) :
    ∃ δa δb δc : ℝ, |δa| ≤ (1 + u) ^ 4 - 1 ∧ |δb| ≤ (1 + u) ^ 3 - 1 ∧ |δc| ≤ u ∧
      |ExecFloat.Binary.toReal (a * (x * x) + b * x + c) -
          (ExecFloat.Binary.toReal a * (1 + δa) *
              (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x) +
            ExecFloat.Binary.toReal b * (1 + δb) * ExecFloat.Binary.toReal x +
            ExecFloat.Binary.toReal c * (1 + δc))| ≤
        (|ExecFloat.Binary.toReal a| * η * (1 + u) + η + η) * (1 + u) * (1 + u) :=
  monomial_backward a b c x hformat hfinite

/-- Estrin's scheme for a cubic: the rounding of `x * x` moves onto `c + d * x`, and from there
onto `c` and `d`. -/
roundoff (backward := true) theorem estrin_backward :=
  fun (a b c d x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((a + b * x) + (c + d * x) * (x * x))

example (a b c d x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite ((a + b * x) + (c + d * x) * (x * x)) = true) :
    ∃ δa δb δc δd : ℝ, |δa| ≤ (1 + u) ^ 2 - 1 ∧ |δb| ≤ (1 + u) ^ 3 - 1 ∧
      |δc| ≤ (1 + u) ^ 4 - 1 ∧ |δd| ≤ (1 + u) ^ 5 - 1 ∧
      |ExecFloat.Binary.toReal ((a + b * x) + (c + d * x) * (x * x)) -
          (ExecFloat.Binary.toReal a * (1 + δa) +
              ExecFloat.Binary.toReal b * (1 + δb) * ExecFloat.Binary.toReal x +
            (ExecFloat.Binary.toReal c * (1 + δc) +
                ExecFloat.Binary.toReal d * (1 + δd) * ExecFloat.Binary.toReal x) *
              (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x))| ≤
        (η * (1 + u) + ((η * (1 + u) * |ExecFloat.Binary.toReal (x * x)| +
              (|ExecFloat.Binary.toReal (c + d * x)| + η * (1 + u)) * η) * (1 + u) + η)) *
          (1 + u) :=
  estrin_backward a b c d x hformat hfinite

/-- Estrin's scheme for a quartic with the square bound once. The rounding of each square moves
onto the coefficients beside it, and those of `x2 * x2` onto `a4`. The absolute term is left to
the generated statement. -/
roundoff (backward := true) theorem quartic_backward :=
  fun (a0 a1 a2 a3 a4 x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (let x2 := x * x; (a0 + a1 * x) + (a2 + a3 * x) * x2 + a4 * (x2 * x2))

example (a0 a1 a2 a3 a4 x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      ((a0 + a1 * x) + (a2 + a3 * x) * (x * x) + a4 * ((x * x) * (x * x))) = true) :
    ∃ δa0 δa1 δa2 δa3 δa4 : ℝ, |δa0| ≤ (1 + u) ^ 3 - 1 ∧ |δa1| ≤ (1 + u) ^ 4 - 1 ∧
      |δa2| ≤ (1 + u) ^ 5 - 1 ∧ |δa3| ≤ (1 + u) ^ 6 - 1 ∧ |δa4| ≤ (1 + u) ^ 5 - 1 ∧
      ∃ absolute : ℝ,
        |ExecFloat.Binary.toReal
              (let x2 := x * x; (a0 + a1 * x) + (a2 + a3 * x) * x2 + a4 * (x2 * x2)) -
            (ExecFloat.Binary.toReal a0 * (1 + δa0) +
                ExecFloat.Binary.toReal a1 * (1 + δa1) * ExecFloat.Binary.toReal x +
              (ExecFloat.Binary.toReal a2 * (1 + δa2) +
                  ExecFloat.Binary.toReal a3 * (1 + δa3) * ExecFloat.Binary.toReal x) *
                (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x) +
              ExecFloat.Binary.toReal a4 * (1 + δa4) *
                (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x *
                  (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x)))| ≤ absolute := by
  obtain ⟨δa0, δa1, δa2, δa3, δa4, h0, h1, h2, h3, h4, hmain⟩ :=
    quartic_backward a0 a1 a2 a3 a4 x hformat hfinite
  exact ⟨δa0, δa1, δa2, δa3, δa4, h0, h1, h2, h3, h4, _, hmain⟩

/-- A cubic split into its even and odd parts: each rounding of `x * x` moves onto the
coefficient beside it. -/
roundoff (backward := true) theorem evenOdd_backward :=
  fun (a b c d x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((a + c * (x * x)) + x * (b + d * (x * x)))

example (a b c d x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite ((a + c * (x * x)) + x * (b + d * (x * x))) = true) :
    ∃ δa δc δb δd : ℝ, |δa| ≤ (1 + u) ^ 2 - 1 ∧ |δc| ≤ (1 + u) ^ 4 - 1 ∧
      |δb| ≤ (1 + u) ^ 3 - 1 ∧ |δd| ≤ (1 + u) ^ 5 - 1 ∧
      ∃ absolute : ℝ,
        |ExecFloat.Binary.toReal ((a + c * (x * x)) + x * (b + d * (x * x))) -
            (ExecFloat.Binary.toReal a * (1 + δa) +
                ExecFloat.Binary.toReal c * (1 + δc) *
                  (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x) +
              ExecFloat.Binary.toReal x *
                (ExecFloat.Binary.toReal b * (1 + δb) +
                  ExecFloat.Binary.toReal d * (1 + δd) *
                    (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x)))| ≤ absolute := by
  obtain ⟨δa, δc, δb, δd, ha, hc, hb, hd, hmain⟩ := evenOdd_backward a b c d x hformat hfinite
  exact ⟨δa, δc, δb, δd, ha, hc, hb, hd, _, hmain⟩

/-- A dot product with centered data, perturbed in the weights only: the rounding of
`x j - m` moves onto `w j`. -/
roundoff (backward := true) (perturb := [w]) theorem centered_backward :=
  fun {n : Nat} (w x : Fin n → Value) (m : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + (x j - m) * w j) (0 : Value))

example {n : Nat} (w x : Fin n → Value) (m : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => s + (x j - m) * w j) (0 : Value)) = true) :
    ∃ δw : Fin n → ℝ, (∀ j, |δw j| ≤ (1 + u) ^ (n - 1 - j + 3) - 1) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + (x j - m) * w j) (0 : Value)) -
          (List.finRange n).foldl (fun s j => s +
            (ExecFloat.Binary.toReal (x j) - ExecFloat.Binary.toReal m) *
              (ExecFloat.Binary.toReal (w j) * (1 + δw j))) 0| ≤
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  centered_backward w x m hformat hfinite

/-- A weighted sum of cubes: both roundings of `x j * x j * x j` move onto `w j`. The absolute
term of a step depends on its entries, so it stays a recurrence over the steps. -/
roundoff (backward := true) theorem cubes_backward :=
  fun {n : Nat} (w x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + w j * (x j * x j * x j)) (0 : Value))

example {n : Nat} (w x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => s + w j * (x j * x j * x j)) (0 : Value)) = true) :
    ∃ δw : Fin n → ℝ, (∀ j, |δw j| ≤ (1 + u) ^ (n - 1 - j + 4) - 1) ∧
      |ExecFloat.Binary.toReal
            (Fin.foldl n (fun s j => s + w j * (x j * x j * x j)) (0 : Value)) -
          (List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (w j) * (1 + δw j) *
            (ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (x j) *
              ExecFloat.Binary.toReal (x j))) 0| ≤
        List.foldBackwardAbsolute (fun (s : Value) j => s + w j * (x j * x j * x j))
          (fun _ => 1) (1 + u)
          (fun _ j => (|ExecFloat.Binary.toReal (w j)| *
              (η * |ExecFloat.Binary.toReal (x j)| * (1 + u) + η) * (1 + u) + η) * (1 + u))
          0 (List.finRange n) :=
  cubes_backward w x hformat hfinite

/-- A square takes the two roundings of a cube as their square root in both reads. -/
roundoff (backward := true) theorem squareCube_backward :=
  fun (w b x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((w * w) * (x * x * x) + b * x)

example (w b x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite ((w * w) * (x * x * x) + b * x) = true) :
    ∃ δw δb : ℝ, |δw| ≤ (1 + u) ^ 5 - 1 ∧ |δb| ≤ (1 + u) ^ 2 - 1 ∧
      |ExecFloat.Binary.toReal ((w * w) * (x * x * x) + b * x) -
          (ExecFloat.Binary.toReal w * (1 + δw) * (ExecFloat.Binary.toReal w * (1 + δw)) *
              (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x *
                ExecFloat.Binary.toReal x) +
            ExecFloat.Binary.toReal b * (1 + δb) * ExecFloat.Binary.toReal x)| ≤
        ((η * |ExecFloat.Binary.toReal (x * x * x)| +
              (|ExecFloat.Binary.toReal (w * w)| + η) *
                (η * |ExecFloat.Binary.toReal x| * (1 + u) + η)) * (1 + u) + η + η) *
          (1 + u) :=
  squareCube_backward w b x hformat hfinite

/-- Two squares, a quotient, a negation and a maximum pass a rounding on to the factor that
takes it. -/
roundoff (backward := true) theorem twoSquares_backward :=
  fun (a b c x y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((x * x) * (y * y) * a + b * x + c * y)

roundoff (backward := true) theorem scaledRatio_backward :=
  fun (a b x y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((x * x) / y * a + b * x)

roundoff (backward := true) theorem negated_backward :=
  fun (a b x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (-(x * x) * a + b * x)

example (a b x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (-(x * x) * a + b * x) = true) :
    ∃ δa δb : ℝ, |δa| ≤ (1 + u) ^ 3 - 1 ∧ |δb| ≤ (1 + u) ^ 2 - 1 ∧
      |ExecFloat.Binary.toReal (-(x * x) * a + b * x) -
          (-(ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x) *
              (ExecFloat.Binary.toReal a * (1 + δa)) +
            ExecFloat.Binary.toReal b * (1 + δb) * ExecFloat.Binary.toReal x)| ≤
        (η * |ExecFloat.Binary.toReal a| * (1 + u) + η + η) * (1 + u) :=
  negated_backward a b x hformat hfinite

roundoff (backward := true) theorem largerTimesCube_backward :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (max a b * (x * x * x) + c * x)

example (a b c x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (max a b * (x * x * x) + c * x) = true ∧
      ExecFloat.Binary.isFinite a = true ∧ ExecFloat.Binary.isFinite b = true) :
    ∃ δa δb δc : ℝ, |δa| ≤ (1 + u) ^ 4 - 1 ∧ |δb| ≤ (1 + u) ^ 4 - 1 ∧
      |δc| ≤ (1 + u) ^ 2 - 1 ∧
      |ExecFloat.Binary.toReal (max a b * (x * x * x) + c * x) -
          (max (ExecFloat.Binary.toReal a * (1 + δa)) (ExecFloat.Binary.toReal b * (1 + δb)) *
              (ExecFloat.Binary.toReal x * ExecFloat.Binary.toReal x *
                ExecFloat.Binary.toReal x) +
            ExecFloat.Binary.toReal c * (1 + δc) * ExecFloat.Binary.toReal x)| ≤
        (|ExecFloat.Binary.toReal (max a b)| *
              (η * |ExecFloat.Binary.toReal x| * (1 + u) + η) * (1 + u) + η + η) * (1 + u) :=
  largerTimesCube_backward a b c x hformat hfinite

/-! ### Products of entries -/

/-- A product of entries from one: each entry takes the rounding of its own product. The
underflow of a product is carried through the later ones by the recurrence
`List.foldBackwardAbsolute`, with the slope `|x j| * (1 + u)` of a step in its accumulator. -/
roundoff (backward := true) theorem productOfEntries_backward :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) (1 : Value))

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => s * x j) (1 : Value)) = true) :
    ∃ δx : Fin n → ℝ, (∀ j, |δx j| ≤ u) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) (1 : Value)) -
          (List.finRange n).foldl
            (fun s j => s * (ExecFloat.Binary.toReal (x j) * (1 + δx j))) 1| ≤
        List.foldBackwardAbsolute (fun (s : Value) j => s * x j)
          (fun j => |ExecFloat.Binary.toReal (x j)| * (1 + u)) 1 (fun _ _ => η) 1
          (List.finRange n) :=
  productOfEntries_backward x hformat hfinite

/-- A product from an input. With the rounding of each product on its left factor, the
accumulator, no entry would be perturbed, so the right factors take the roundings and the start
stays as it is. -/
roundoff (backward := true) theorem product_backward :=
  fun {n : Nat} (x : Fin n → Value) (p : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) p)

example {n : Nat} (x : Fin n → Value) (p : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (Fin.foldl n (fun s j => s * x j) p) = true) :
    ∃ δx : Fin n → ℝ, (∀ j, |δx j| ≤ u) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) p) -
          (List.finRange n).foldl
            (fun s j => s * (ExecFloat.Binary.toReal (x j) * (1 + δx j)))
            (ExecFloat.Binary.toReal p)| ≤
        List.foldBackwardAbsolute (fun (s : Value) j => s * x j)
          (fun j => |ExecFloat.Binary.toReal (x j)| * (1 + u)) 1 (fun _ _ => η) p
          (List.finRange n) :=
  product_backward x p hformat hfinite

/-- The product of a list. -/
roundoff (backward := true) theorem productList_backward :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (xs.foldl (fun p x => p * x) (1 : Value))

example (xs : List Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (xs.foldl (fun p x => p * x) (1 : Value)) = true) :
    ∃ δs : List ℝ, (δs.length = xs.length ∧
        ∀ (k : ℕ) (_ : k < xs.length) (hp : k < δs.length), |δs[k]| ≤ u) ∧
      |ExecFloat.Binary.toReal (xs.foldl (fun p x => p * x) (1 : Value)) -
          (xs.zip δs).foldl
            (fun p entry => p * (ExecFloat.Binary.toReal entry.1 * (1 + entry.2))) 1| ≤
        List.foldBackwardAbsolute (fun (p : Value) x => p * x)
          (fun x => |ExecFloat.Binary.toReal x| * (1 + u)) 1 (fun _ _ => η) 1 xs :=
  productList_backward xs hformat hfinite

/-- A product of products, and a step that adds an entry and multiplies by another. In the
second the accumulator takes the rounding of each sum, so `a j` takes those of the later
steps, and `x j` its own product's. -/
roundoff (backward := true) theorem productPairs_backward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun p j => p * (x j * y j)) (1 : Value))

roundoff (backward := true) (factor := right) theorem scaledSum_backward :=
  fun {n : Nat} (a x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => (s + a j) * x j) (0 : Value))

example {n : Nat} (a x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => (s + a j) * x j) (0 : Value)) = true) :
    ∃ δa δx : Fin n → ℝ, (∀ j, |δa j| ≤ (1 + u) ^ (n - 1 - j + 1) - 1) ∧ (∀ j, |δx j| ≤ u) ∧
      |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => (s + a j) * x j) (0 : Value)) -
          (List.finRange n).foldl (fun s j =>
            (s + ExecFloat.Binary.toReal (a j) * (1 + δa j)) *
              (ExecFloat.Binary.toReal (x j) * (1 + δx j))) 0| ≤
        List.foldBackwardAbsolute (fun (s : Value) j => (s + a j) * x j)
          (fun j => |ExecFloat.Binary.toReal (x j)| * (1 + u)) (1 + u) (fun _ _ => η) 0
          (List.finRange n) :=
  scaledSum_backward a x hformat hfinite

/-- A product of the larger of two entries: both take the rounding. -/
roundoff (backward := true) theorem productOfMaxima_backward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun p j => p * max (x j) (y j)) (1 : Value))

/-- A product of entries inside a larger computation: the loop from a literal takes no further
factor, so the rounding of the outer product moves onto `a`. -/
roundoff (backward := true) theorem productThen_backward :=
  fun {n : Nat} (x : Fin n → Value) (a b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun p j => p * x j) (1 : Value) * a + b)

/-! ### Values that are not exact data -/

/-- A real-valued definition of the program is expanded, so the rounding inside it is analyzed:
the statement is that of `x * x`, about the definition. -/
noncomputable def squared (x : Value) : ℝ := ExecFloat.Binary.toReal (x * x)

roundoff (backward := true) theorem squared_backward :=
  fun (x : Value) (hformat : format.isIEEE = true) => squared x

example (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (x * x) = true) :
    ∃ δx : ℝ, |δx| ≤ u ∧
      |squared x - ExecFloat.Binary.toReal x * (1 + δx) * (ExecFloat.Binary.toReal x * (1 + δx))| ≤
        η :=
  squared_backward x hformat hfinite

/-- The number of positive values among two, computed from floating-point comparisons. -/
def positives (x y : Value) : ℕ := (if x > 0 then 1 else 0) + (if y > 0 then 1 else 0)

/--
error: roundoff: ↑(positives x y) casts an integer computed from real or floating-point values, so the reference would keep them; compute it from index data
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem positives_backward :=
  fun (x y : Value) => ((positives x y : ℕ) : ℝ)

/--
error: roundoff: ↑(positives x y) casts an integer computed from real or floating-point values, so the reference would keep them; compute it from index data
-/
#guard_msgs (error, whitespace := lax) in
roundoff closed theorem positives_closed :=
  fun (x y : Value) => ((positives x y : ℕ) : ℝ)

/--
error: roundoff: `Model.roundAt format r` has no backward-error form: the backward-error mode has no rule for `FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt` of a computed value. Use `roundoff mixed theorem` for a forward bound.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem roundedReal_backward :=
  fun (r : ℝ) => Model.roundAt format r

/-! ### Computations without a backward-error form -/

/--
error: roundoff: `ExecFloat.Binary.toReal (x * x)` has no backward-error form: its rounding cannot be moved onto the inputs, because `ExecFloat.Binary.toReal x` is read more than once, with roundings that differ, so it takes no perturbation. Use `roundoff mixed theorem` for a forward bound, or choose the perturbed inputs with `(perturb := [...])`.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem squarePlus_backward :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x * x + x)

/--
error: roundoff: `ExecFloat.Binary.toReal (x + y)` has no backward-error form: its rounding cannot be moved onto the inputs, because `ExecFloat.Binary.toReal x` is read more than once, with roundings that differ, so it takes no perturbation. Use `roundoff mixed theorem` for a forward bound, or choose the perturbed inputs with `(perturb := [...])`.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem cancellation_backward :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((x + y) - (x + z))

/--
error: roundoff: `ExecFloat.Binary.CorrectlyRounded.exp (x * y)` has no backward-error form: the backward-error mode has no rule for it. Use `roundoff mixed theorem` for a forward bound.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem exponential_backward :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.exp (x * y))

/--
error: roundoff: `ExecFloat.Binary.toReal (x * x)` has no backward-error form: its rounding cannot be moved onto the inputs, because `ExecFloat.Binary.toReal x` is read more than once, with roundings that differ, so it takes no perturbation. Use `roundoff mixed theorem` for a forward bound, or choose the perturbed inputs with `(perturb := [...])`.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem cube_backward :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x * x * x)

/--
error: roundoff: `ExecFloat.Binary.toReal ((a * x + b) * x + c)` has no backward-error form: its rounding cannot be moved onto the inputs, because `ExecFloat.Binary.toReal c` is not among the inputs chosen with `perturb`. Use `roundoff mixed theorem` for a forward bound, or choose the perturbed inputs with `(perturb := [...])`.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) (perturb := [x]) theorem hornerPoint_backward :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((a * x + b) * x + c)

/--
error: roundoff: no entry of the loop step takes a perturbation, so the loop has no backward-error form in its entries: each rounding moved onto the accumulator. Use `roundoff mixed theorem` for a forward bound.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem quotients_backward :=
  fun {n : Nat} (x : Fin n → Value) (p : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s / x j) p)

/--
error: roundoff: the loop step has an absolute error and multiplies its accumulator by a perturbed loop of its own or by a quotient with a perturbed divisor, which the backward-error mode does not carry through the loop. Use `roundoff mixed theorem` for a forward bound.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem productOfRowSums_backward :=
  fun {m n : Nat} (A : Fin m → Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (Fin.foldl m (fun p i => p * Fin.foldl n (fun s j => s + A i j) (0 : Value)) (1 : Value))

/--
error: roundoff: the loop step reads `state.2` of its state, and the backward-error mode follows one numerical component of the state of a loop. Use `roundoff mixed theorem` for a forward bound.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem compensated_backward :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((xs.foldl (fun (state : Value × Value) x =>
      let y := x - state.2
      let t := state.1 + y
      (t, (t - state.1) - y)) (0, 0)).1)

/-- error: roundoff: `z` is not an input of the computation -/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) (perturb := [z]) theorem unknownInput_backward :=
  fun (x y : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x + y)

end Configured

/--
error: roundoff: `(x + 1).toReal` has no backward-error form: its rounding cannot be moved onto the inputs, because `1` takes no perturbation. Use `roundoff mixed theorem` for a forward bound, or choose the perturbed inputs with `(perturb := [...])`.
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem literal_backward :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (x + 1)

/-- A quotient by the literal `4` and a product with the literal `1e-5`: the reference keeps
each literal as binary32 stores it, and the input takes the rounding. -/
roundoff (backward := true) theorem quarter32_backward :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (x / 4)

example (x : Binary32) (hfinite : ExecFloat.Binary.isFinite (x / 4) = true) :
    ∃ δx : ℝ, |δx| ≤ Model.unitRoundoffAt FloatFormat.binary32 ∧
      |ExecFloat.Binary.toReal (x / 4) -
          ExecFloat.Binary.toReal x * (1 + δx) / (((4 : ℕ) : ℚ) : ℝ)| ≤
        Model.underflowErrorAt FloatFormat.binary32 :=
  quarter32_backward x hfinite

roundoff (backward := true) theorem scaled32_backward :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (x * 1e-5)

example (x : Binary32) (hfinite : ExecFloat.Binary.isFinite (x * 1e-5) = true) :
    ∃ δx : ℝ, |δx| ≤ Model.unitRoundoffAt FloatFormat.binary32 ∧
      |ExecFloat.Binary.toReal (x * 1e-5) -
          ExecFloat.Binary.toReal x * (1 + δx) *
            Model.roundAt FloatFormat.binary32 ((1e-5 : ℚ) : ℝ)| ≤
        Model.underflowErrorAt FloatFormat.binary32 :=
  scaled32_backward x hfinite

/--
error: roundoff: a required numerical condition is false: `ExecFloat.Binary.toReal x / ExecFloat.Binary.toReal 0` divides by zero
-/
#guard_msgs (error, whitespace := lax) in
roundoff (backward := true) theorem byZero32_backward :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (x / 0)

/-- A dot product of binary32 values of a fixed length: the format's premise is decided. -/
roundoff (backward := true) theorem dot32_backward :=
  fun (x y : Fin 4 → Binary32) =>
    ExecFloat.Binary.toReal (Fin.foldl 4 (fun s j => s + x j * y j) (0 : Binary32))

/-- The premise is satisfiable: at concrete entries the kernel computes that the dot product is
finite, so the theorem says something. -/
example := dot32_backward (fun _ => 0.1) (fun _ => 3) (by float_decide)

/-- Horner's rule in binary32, and its premise at concrete values. -/
roundoff (backward := true) theorem horner32_backward :=
  fun (a b c x : Binary32) => ExecFloat.Binary.toReal ((a * x + b) * x + c)

example : ∃ δa δb δc : ℝ, |δa| ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ 4 - 1 ∧
    |δb| ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ 3 - 1 ∧
    |δc| ≤ Model.unitRoundoffAt FloatFormat.binary32 ∧
    |ExecFloat.Binary.toReal (((1.5 : Binary32) * 3 + 2.25) * 3 + 0.1) -
        ((ExecFloat.Binary.toReal (1.5 : Binary32) * (1 + δa) *
              ExecFloat.Binary.toReal (3 : Binary32) +
            ExecFloat.Binary.toReal (2.25 : Binary32) * (1 + δb)) *
          ExecFloat.Binary.toReal (3 : Binary32) +
            ExecFloat.Binary.toReal (0.1 : Binary32) * (1 + δc))| ≤
      (Model.underflowErrorAt FloatFormat.binary32 *
            (1 + Model.unitRoundoffAt FloatFormat.binary32) *
          |ExecFloat.Binary.toReal (3 : Binary32)| *
            (1 + Model.unitRoundoffAt FloatFormat.binary32) +
          Model.underflowErrorAt FloatFormat.binary32) *
        (1 + Model.unitRoundoffAt FloatFormat.binary32) :=
  horner32_backward 1.5 2.25 0.1 3 (by float_decide)

example (x y : Fin 4 → Binary32)
    (hfinite : ExecFloat.Binary.isFinite (Fin.foldl 4 (fun s j => s + x j * y j) (0 : Binary32)) =
      true) :
    ∃ δ : Fin 4 → ℝ,
      (∀ j, |δ j| ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ (4 - 1 - j.val + 2) - 1) ∧
      |ExecFloat.Binary.toReal (Fin.foldl 4 (fun s j => s + x j * y j) (0 : Binary32)) -
          (List.finRange 4).foldl (fun s j =>
            s + ExecFloat.Binary.toReal (x j) * (1 + δ j) * ExecFloat.Binary.toReal (y j)) 0| ≤
        Model.underflowErrorAt FloatFormat.binary32 *
            (1 + Model.unitRoundoffAt FloatFormat.binary32) *
          ∑ k ∈ Finset.range 4, (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ k :=
  dot32_backward x y hfinite

/-- A fused multiply-add rounds once: the product and the addend take one rounding. -/
roundoff (backward := true) theorem fma_backward :=
  fun (fmt : FloatFormat) (_hfmt : fmt.isIEEE = true) (x y z : Model fmt) =>
    Model.toReal (Model.fma x y z)

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (x y z : Model fmt)
    (hfinite : Model.isFinite (Model.fma x y z) = true) :
    ∃ δx δz : ℝ, |δx| ≤ Model.unitRoundoffAt fmt ∧ |δz| ≤ Model.unitRoundoffAt fmt ∧
      |Model.toReal (Model.fma x y z) -
          (Model.toReal x * (1 + δx) * Model.toReal y + Model.toReal z * (1 + δz))| ≤
        Model.underflowErrorAt fmt :=
  fma_backward fmt hfmt x y z hfinite

/-- Horner's rule with fused multiply-adds: each coefficient takes one rounding for each
fused operation from its own on, half of what the separate products and sums give. -/
roundoff (backward := true) theorem fmaHorner_backward :=
  fun (fmt : FloatFormat) (_hfmt : fmt.isIEEE = true) (a b c x : Model fmt) =>
    Model.toReal (Model.fma (Model.fma a x b) x c)

example (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (a b c x : Model fmt)
    (hfinite : Model.isFinite (Model.fma (Model.fma a x b) x c) = true) :
    ∃ δa δb δc : ℝ, |δa| ≤ (1 + Model.unitRoundoffAt fmt) ^ 2 - 1 ∧
      |δb| ≤ (1 + Model.unitRoundoffAt fmt) ^ 2 - 1 ∧ |δc| ≤ Model.unitRoundoffAt fmt ∧
      |Model.toReal (Model.fma (Model.fma a x b) x c) -
          ((Model.toReal a * (1 + δa) * Model.toReal x + Model.toReal b * (1 + δb)) *
              Model.toReal x + Model.toReal c * (1 + δc))| ≤
        Model.underflowErrorAt fmt * |Model.toReal x| * (1 + Model.unitRoundoffAt fmt) +
          Model.underflowErrorAt fmt :=
  fmaHorner_backward fmt hfmt a b c x hfinite

/-- A bfloat16 dot product accumulated in binary32: the widening casts and the products are
exact, so only the additions round. -/
roundoff (backward := true) theorem wideDot_backward :=
  fun (xs : List (Model FloatFormat.bfloat16 × Model FloatFormat.bfloat16)) =>
    Model.toReal (xs.foldl (fun acc pair => Model.add acc
      (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
        (Model.cast _ FloatFormat.binary32 pair.2))) (Model.zero _ false))

/-- The statement is an equality, with the binary32 unit roundoff in the bounds. The premise
keeps the range condition of each exact product beside the finiteness of the result. -/
example (xs : List (Model FloatFormat.bfloat16 × Model FloatFormat.bfloat16))
    (hfinite : Model.isFinite (xs.foldl (fun acc pair => Model.add acc
      (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
        (Model.cast _ FloatFormat.binary32 pair.2))) (Model.zero _ false)) = true)
    (hnormal : List.AllSteps (fun acc pair => Model.add acc
        (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
          (Model.cast _ FloatFormat.binary32 pair.2)))
      (fun _ pair => Model.toReal pair.1 * Model.toReal pair.2 = 0 ∨
        Model.minNormalAt FloatFormat.binary32 ≤ |Model.toReal pair.1 * Model.toReal pair.2|)
      (Model.zero _ false) xs) :
    ∃ δs : List ℝ, (δs.length = xs.length ∧ ∀ (k : ℕ) (_ : k < xs.length) (hp : k < δs.length),
        |δs[k]| ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) ^ (xs.length - 1 - k + 1) - 1) ∧
      Model.toReal (xs.foldl (fun acc pair => Model.add acc
          (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
            (Model.cast _ FloatFormat.binary32 pair.2))) (Model.zero _ false)) =
        (xs.zip δs).foldl (fun s entry =>
          s + Model.toReal entry.1.1 * (1 + entry.2) * Model.toReal entry.1.2) 0 :=
  wideDot_backward xs ⟨hfinite, hnormal⟩

/-- A sum narrowed to bfloat16 takes one rounding of each format. -/
roundoff (backward := true) theorem narrowed_backward :=
  fun (x y : Model FloatFormat.binary32) =>
    Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.bfloat16 (Model.add x y))

example (x y : Model FloatFormat.binary32)
    (hfinite : Model.isFinite
      (Model.cast FloatFormat.binary32 FloatFormat.bfloat16 (Model.add x y)) = true) :
    ∃ δx δy : ℝ,
      |δx| ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) *
        (1 + Model.unitRoundoffAt FloatFormat.bfloat16) - 1 ∧
      |δy| ≤ (1 + Model.unitRoundoffAt FloatFormat.binary32) *
        (1 + Model.unitRoundoffAt FloatFormat.bfloat16) - 1 ∧
      |Model.toReal (Model.cast FloatFormat.binary32 FloatFormat.bfloat16 (Model.add x y)) -
          (Model.toReal x * (1 + δx) + Model.toReal y * (1 + δy))| ≤
        Model.underflowErrorAt FloatFormat.bfloat16 :=
  narrowed_backward x y hfinite

-- The generated theorems and the lemmas they are built from rest on the three standard axioms.
run_cmd do
  for name in [``horner_backward, ``dot_backward, ``dot_backward_right, ``dot_backward_factor,
      ``dotList_backward, ``hornerArray_backward, ``hornerLead_backward, ``mulVec_backward,
      ``linear_backward, ``sum_backward, ``shared_backward, ``quotient_backward, ``dot_both,
      ``square_backward, ``sumSquares_backward, ``distance_backward, ``fourth_backward,
      ``shiftedSquares_backward, ``hornerFin_backward, ``twoProducts_backward,
      ``total_backward, ``bilinear_backward, ``rows_backward, ``countedSum_backward,
      ``neuron_backward, ``perceptron_backward, ``norm_backward, ``maximum_backward,
      ``rectifier_backward, ``monomial_backward, ``estrin_backward, ``centered_backward,
      ``cubes_backward, ``squareCube_backward, ``twoSquares_backward, ``scaledRatio_backward,
      ``negated_backward, ``largerTimesCube_backward, ``quartic_backward,
      ``fmaHorner_backward, ``evenOdd_backward, ``productOfEntries_backward, ``product_backward,
      ``squared_backward, ``quarter32_backward, ``scaled32_backward,
      ``productList_backward, ``productPairs_backward, ``scaledSum_backward,
      ``productOfMaxima_backward, ``productThen_backward,
      ``dot32_backward, ``fma_backward, ``wideDot_backward, ``narrowed_backward,
      ``List.fold_backward, ``List.fold_backward_exact, ``List.fold_backward_fixed,
      ``List.fold_backward_fixed_exact, ``List.fold_backward_finRange,
      ``List.fold_backward_exact_finRange, ``List.fold_backward_fixed_finRange,
      ``List.fold_backward_fixed_exact_finRange, ``List.foldBackwardAbsolute_le_geom,
      ``List.AllSteps.of_foldl, ``List.abs_foldl_affine_sub_le, ``List.abs_foldl_add_sub_le,
      ``List.abs_foldl_add_sub_le_mul, ``FloatLib.Numerics.Backward.round,
      ``FloatLib.Numerics.Backward.scale_sq, ``FloatLib.Numerics.Backward.scale_ite,
      ``FloatLib.Numerics.Backward.scale_sqrt, ``FloatLib.Numerics.Backward.sqrt,
      ``FloatLib.Numerics.Backward.scale_max, ``FloatLib.Numerics.Backward.maximum,
      ``FloatLib.Numerics.Backward.scale_min, ``FloatLib.Numerics.Backward.minimum,
      ``FloatLib.Numerics.Backward.branch, ``FloatLib.Numerics.Backward.forall_getElem_map,
      ``FloatLib.Numerics.Backward.move_left, ``FloatLib.Numerics.Backward.move_right,
      ``FloatLib.Numerics.Backward.restate, ``FloatLib.Numerics.Backward.one_add_scale_nonneg,
      ``FloatLib.Numerics.Backward.abs_sub_le_of_eq_mul_le,
      ``FloatLib.Numerics.Backward.abs_perturbed_le, ``FloatLib.Numerics.Backward.abs_mul_le_mul,
      ``FloatLib.Numerics.MixedError.eq_mul_factor_add_offset] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward
