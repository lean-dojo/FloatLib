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

/-!
# Forward bounds in closed form from `roundoff closed theorem`

Each check states the theorem that the command generates, so a change of a generated statement
fails here.

* The bound of a dot product is the sum of the magnitudes of its products, each weighted by the
  bound of its own perturbation, plus the underflow term: the textbook bound, with the exponent
  of each entry. Its premise is a finite result.
* A loop whose step multiplies its accumulator, as Horner's rule does, accumulates the changes
  of its steps through the exact loop.
* A loop inside a step gives a double sum, and a list a sum over its positions.
* Each read is bounded by itself. The reads of one input may take different perturbations, and
  a literal or an input that every step of a loop reads may take a rounding. So `x * x + x`,
  `x + 1`, a difference that cancels a shared input and a product of entries, which have no
  backward-error form, have closed forward bounds.
* A quotient by a computed divisor has the premise that the change of the divisor is below its
  magnitude.
* The exponential of an input takes a rounding as an input does, and the rounding of an
  exponential or a logarithm of a computed value stays on its result. So a sum of exponentials,
  a softmax weight and a log-sum-exp have closed forward bounds.
* A correctly rounded call in a format without variables, such as a binary64 exponential, is
  analyzed like one in a format variable.
* A product whose rounding is given to the entries and a quotient by a perturbed divisor inside
  a loop step are refused.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

section Configured

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

local notation "u" => Model.unitRoundoffAt format

local notation "η" => Model.underflowErrorAt format

/-- The dot product of two functions on `Fin n`, from zero. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

/-- The forward bound of the dot product in closed form. -/
roundoff closed theorem dot_closed :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

/-- The statement at every length: the product at index `j` is weighted by
`(1 + u) ^ (n - 1 - j + 2) - 1`, and a finite result is the only premise. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
        s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0| ≤
      ∑ j : Fin n, |ExecFloat.Binary.toReal (x j)| * ((1 + u) ^ (n - 1 - j + 2) - 1) *
        |ExecFloat.Binary.toReal (y j)| + η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  dot_closed x y hformat hfinite

/-- One weight for every product: `(1 + u) ^ (n + 1) - 1`, as in the textbook statement. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (dot x y) = true) :
    |ExecFloat.Binary.toReal (dot x y) - (List.finRange n).foldl (fun s j =>
        s + ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)) 0| ≤
      ((1 + u) ^ (n + 1) - 1) * ∑ j : Fin n, |ExecFloat.Binary.toReal (x j)| *
        |ExecFloat.Binary.toReal (y j)| + η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k := by
  refine (dot_closed x y hformat hfinite).trans (add_le_add ?_ le_rfl)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hweight : (1 + u) ^ (n - 1 - j + 2) - 1 ≤ (1 + u) ^ (n + 1) - 1 := by
    refine sub_le_sub_right (pow_le_pow_right₀ ?_ ?_) 1
    · linarith [Model.unitRoundoffAt_pos format]
    · have := j.isLt
      omega
  calc |ExecFloat.Binary.toReal (x j)| * ((1 + u) ^ (n - 1 - j + 2) - 1) *
        |ExecFloat.Binary.toReal (y j)|
      ≤ |ExecFloat.Binary.toReal (x j)| * ((1 + u) ^ (n + 1) - 1) *
        |ExecFloat.Binary.toReal (y j)| := by gcongr
    _ = ((1 + u) ^ (n + 1) - 1) * (|ExecFloat.Binary.toReal (x j)| *
        |ExecFloat.Binary.toReal (y j)|) := by ring

/-- A sum has no underflow term. -/
roundoff closed theorem sum_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + x j) (0 : Value))

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (Fin.foldl n (fun s j => s + x j) (0 : Value)) = true) :
    |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + x j) (0 : Value)) -
        (List.finRange n).foldl (fun s j => s + ExecFloat.Binary.toReal (x j)) 0| ≤
      ∑ j : Fin n, |ExecFloat.Binary.toReal (x j)| * ((1 + u) ^ (n - 1 - j + 1) - 1) :=
  sum_closed x hformat hfinite

/-- Horner's rule: the changes of the coefficients are accumulated through the exact loop, each
multiplied by `|x|` at every later step. -/
roundoff closed theorem horner_closed :=
  fun {n : Nat} (a : Fin n → Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x + a j) (0 : Value))

example {n : Nat} (a : Fin n → Value) (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl n (fun s j => s * x + a j) (0 : Value)) = true) :
    |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x + a j) (0 : Value)) -
        (List.finRange n).foldl (fun s j =>
          s * ExecFloat.Binary.toReal x + ExecFloat.Binary.toReal (a j)) 0| ≤
      (List.finRange n).foldl (fun e (j : Fin n) => e * |ExecFloat.Binary.toReal x| +
        |ExecFloat.Binary.toReal (a j)| * ((1 + u) ^ (2 * (n - 1 - j) + 1) - 1)) 0 +
        η * (1 + u) *
          ∑ k ∈ Finset.range n, (|ExecFloat.Binary.toReal x| * ((1 + u) * (1 + u))) ^ k :=
  horner_closed a x hformat hfinite

/-- Horner's rule over a list of coefficients: the changes are accumulated over the positions. -/
roundoff closed theorem hornerList_closed :=
  fun (coefficients : List Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (coefficients.foldl (fun value coefficient => value * x + coefficient) 0)

/-- A sum over a list is bounded by a sum over its positions. -/
roundoff closed theorem sumList_closed :=
  fun (xs : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (xs.foldl (fun s x => s + x) (0 : Value))

example (xs : List Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (xs.foldl (fun s x => s + x) (0 : Value)) = true) :
    |ExecFloat.Binary.toReal (xs.foldl (fun s x => s + x) (0 : Value)) -
        xs.foldl (fun s x => s + ExecFloat.Binary.toReal x) 0| ≤
      ∑ k : Fin xs.length,
        |ExecFloat.Binary.toReal xs[k.1]| * ((1 + u) ^ (xs.length - 1 - k + 1) - 1) :=
  sumList_closed xs hformat hfinite

/-- One output of a linear layer: the bias takes the rounding of its addition. -/
roundoff closed theorem linear_closed :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + w j * x j) 0 + b)

example {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (Fin.foldl n (fun s j => s + w j * x j) 0 + b) = true) :
    |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + w j * x j) 0 + b) -
        ((List.finRange n).foldl (fun s j =>
          s + ExecFloat.Binary.toReal (w j) * ExecFloat.Binary.toReal (x j)) 0 +
            ExecFloat.Binary.toReal b)| ≤
      ∑ j : Fin n, |ExecFloat.Binary.toReal (w j)| * ((1 + u) ^ (n - 1 - j + 3) - 1) *
          |ExecFloat.Binary.toReal (x j)| + |ExecFloat.Binary.toReal b| * u +
        η * (1 + u) * (∑ k ∈ Finset.range n, (1 + u) ^ k) * (1 + u) :=
  linear_closed w x b hformat hfinite

/-- The sum of the entries of a matrix: a double sum, without an underflow term. -/
roundoff closed theorem total_closed :=
  fun {m n : Nat} (A : Fin m → Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (Fin.foldl m (fun s i => s + Fin.foldl n (fun t j => t + A i j) 0) (0 : Value))

example {m n : Nat} (A : Fin m → Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite
      (Fin.foldl m (fun s i => s + Fin.foldl n (fun t j => t + A i j) 0) (0 : Value)) = true) :
    |ExecFloat.Binary.toReal
          (Fin.foldl m (fun s i => s + Fin.foldl n (fun t j => t + A i j) 0) (0 : Value)) -
        (List.finRange m).foldl (fun s i => s + (List.finRange n).foldl (fun t j =>
          t + ExecFloat.Binary.toReal (A i j)) 0) 0| ≤
      ∑ i : Fin m, ∑ j : Fin n, |ExecFloat.Binary.toReal (A i j)| *
        ((1 + u) ^ (n - 1 - j + (m - 1 - i) + 2) - 1) :=
  total_closed A hformat hfinite

/-- `x * x + x` has no backward-error form, since the two readings of `x` in the square take a
rounding that the third does not. Its forward bound treats each reading by itself. -/
roundoff closed theorem squarePlus_closed :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x * x + x)

/-- The rectifier, as a branch on the sign of its argument. -/
def relu (z : Value) : Value := if z > 0 then z else 0

/-- One output of a perceptron with one hidden layer of rectifiers. -/
def perceptron {n h : Nat} (W : Fin h → Fin n → Value) (b v : Fin h → Value) (c : Value)
    (x : Fin n → Value) : Value :=
  Fin.foldl h (fun s k => s + v k * relu (Fin.foldl n (fun t j => t + W k j * x j) 0 + b k)) 0 + c

/-- The perceptron: the bound follows the program, a sum over the hidden units of sums over
their weights, under the branch that each rectifier takes. -/
roundoff closed theorem perceptron_closed :=
  fun {n h : Nat} (W : Fin h → Fin n → Value) (b v : Fin h → Value) (c : Value)
    (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (perceptron W b v c x)

/-- The Euclidean norm. -/
roundoff closed theorem norm_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal
      (ExecFloat.sqrt (Fin.foldl n (fun ss j => ss + x j * x j) (0 : Value)))

/-! ### Literals, repeated reads, products and quotients

For a forward bound each read is bounded by itself, so an exact constant and an input that
every step of a loop reads may take a rounding too. -/

/-- A literal takes its share of the rounding of a sum. -/
roundoff closed theorem literal_closed :=
  fun (x : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x + 1)

example (x : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (x + 1) = true) :
    |ExecFloat.Binary.toReal (x + 1) - (ExecFloat.Binary.toReal x + 1)| ≤
      |ExecFloat.Binary.toReal x| * u + |(1 : ℝ)| * u :=
  literal_closed x hformat hfinite

/-- Cancellation between computed sums has no backward-error form, and a forward bound. -/
roundoff closed theorem cancellation_closed :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal ((x + y) - (x + z))

/-- A product of entries from an input: every rounding moves onto the accumulator, so the start
takes all `n`, and its change is carried through the exact product. The underflow of the
products is accumulated by the recurrence `List.foldBackwardAbsolute`. -/
roundoff closed theorem product_closed :=
  fun {n : Nat} (x : Fin n → Value) (p : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) p)

example {n : Nat} (x : Fin n → Value) (p : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (Fin.foldl n (fun s j => s * x j) p) = true) :
    |ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) p) -
        (List.finRange n).foldl (fun s j => s * ExecFloat.Binary.toReal (x j))
          (ExecFloat.Binary.toReal p)| ≤
      (List.finRange n).foldl (fun e (j : Fin n) => e * |ExecFloat.Binary.toReal (x j)|)
          (|ExecFloat.Binary.toReal p| * ((1 + u) ^ n - 1)) +
        List.foldBackwardAbsolute (fun s j => s * x j)
          (fun j : Fin n => |ExecFloat.Binary.toReal (x j)|) (1 + u) (fun _ _ => η) p
          (List.finRange n) :=
  product_closed x p hformat hfinite

/-- A quotient by a computed divisor: the premise asks that the change of the divisor is below
its magnitude. -/
roundoff closed theorem quotient_closed :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (x / (y + z))

example (x y z : Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (x / (y + z)) = true)
    (hdivisor : ExecFloat.Binary.isFinite (y + z) = true)
    (hapart : |ExecFloat.Binary.toReal y| * u + |ExecFloat.Binary.toReal z| * u <
      |ExecFloat.Binary.toReal y + ExecFloat.Binary.toReal z|) :
    |ExecFloat.Binary.toReal (x / (y + z)) -
        ExecFloat.Binary.toReal x / (ExecFloat.Binary.toReal y + ExecFloat.Binary.toReal z)| ≤
      (|ExecFloat.Binary.toReal x| * u * |ExecFloat.Binary.toReal y + ExecFloat.Binary.toReal z| +
          |ExecFloat.Binary.toReal x| *
            (|ExecFloat.Binary.toReal y| * u + |ExecFloat.Binary.toReal z| * u)) /
        (|ExecFloat.Binary.toReal y + ExecFloat.Binary.toReal z| *
          (|ExecFloat.Binary.toReal y + ExecFloat.Binary.toReal z| -
            (|ExecFloat.Binary.toReal y| * u + |ExecFloat.Binary.toReal z| * u))) + η :=
  quotient_closed x y z hformat ⟨hfinite, hdivisor, hapart⟩

/-- The two schedules of the target gradient of cross-entropy. -/
roundoff closed theorem gradientSubtracted_closed :=
  fun (s : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (1 / (1 + s) - 1)

roundoff closed theorem gradientDivided_closed :=
  fun (s : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (-(s / (1 + s)))

/-! ### Exponentials and logarithms

The exponential of an input is an exact function of the inputs and takes a rounding as an input
does. The rounding of an exponential or a logarithm of a computed value stays on its result. -/

/-- The sum of the correctly rounded exponentials of a function on `Fin n`. -/
def expSum {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun s i => s + ExecFloat.Binary.CorrectlyRounded.exp (x i)) 0

/-- A sum of exponentials: each exponential is weighted by its own roundings. -/
roundoff closed theorem expSum_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (expSum x)

example {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true)
    (hfinite : ExecFloat.Binary.isFinite (expSum x) = true)
    (hrange : ∀ i, ExecFloat.Binary.isFinite (x i) = true ∧
      Real.exp (ExecFloat.Binary.toReal (x i)) <
        ↑(Model.Transcendentals.Certified.overflowThreshold format)) :
    |ExecFloat.Binary.toReal (expSum x) -
        (List.finRange n).foldl (fun s i => s + Real.exp (ExecFloat.Binary.toReal (x i))) 0| ≤
      ∑ i : Fin n, |Real.exp (ExecFloat.Binary.toReal (x i))| * ((1 + u) ^ (n - 1 - i + 2) - 1) +
        η * (1 + u) * ∑ k ∈ Finset.range n, (1 + u) ^ k :=
  expSum_closed x hformat ⟨hfinite, List.AllSteps.of_forall _ _ _ _ fun _ i => hrange i⟩

/-- A softmax weight: a quotient by the perturbed sum, under the premise that the change of the
sum is below the sum. -/
roundoff closed theorem softmax_closed :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.exp (x 0) / expSum x)

/-- A log-sum-exp: the logarithm of the perturbed sum, then the rounding of the logarithm. -/
roundoff closed theorem logSumExp_closed :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.log (expSum x))

/-- The exponential of a computed product. -/
roundoff closed theorem exponential_closed :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.exp (x * y))

/-! ### Computations without a closed forward bound -/

/--
error: roundoff: the loop step multiplies its accumulator by a perturbed entry and has an absolute error, which the closed forward bound does not carry through the loop. Use `roundoff mixed theorem` for a forward bound.
-/
#guard_msgs (error, whitespace := lax) in
roundoff closed (factor := right) theorem productRight_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s * x j) (1 : Value))

/--
error: roundoff: the divisor `ExecFloat.Binary.toReal (x j) + 1` is perturbed inside a loop step, and the closed forward bound does not divide by a perturbed value there. Use `roundoff mixed theorem`.
-/
#guard_msgs (error, whitespace := lax) in
roundoff closed theorem ratios_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (Fin.foldl n (fun s j => s + x j / (x j + 1)) (0 : Value))

end Configured

/-- A dot product of binary32 values of a fixed length: the format's premise is decided. -/
roundoff closed theorem dot32_closed :=
  fun (x y : Fin 4 → Binary32) =>
    ExecFloat.Binary.toReal (Fin.foldl 4 (fun s j => s + x j * y j) (0 : Binary32))

/-- The premise is satisfiable: at concrete entries the kernel computes that the dot product is
finite. -/
example := dot32_closed (fun _ => 0.1) (fun _ => 3) (by float_decide)

/-- A binary64 exponential minus one. The rounding and the finiteness theorems of the
exponential both ask for an IEEE encoding, a test that counts down from the exponent bias when
it is unfolded, so their premises are matched by what they state. -/
roundoff closed theorem expSubOne64_closed :=
  fun (x : Binary64) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.exp x -
      (ExecFloat.Binary.ofRat (1 : ℚ) .nearest : Binary64))

/-- A bfloat16 dot product accumulated in binary32: the products are exact, so only the
additions weigh on the entries, and there is no underflow term. -/
roundoff closed theorem wideDot_closed :=
  fun (xs : List (Model FloatFormat.bfloat16 × Model FloatFormat.bfloat16)) =>
    Model.toReal (xs.foldl (fun acc pair => Model.add acc
      (Model.mul (Model.cast _ FloatFormat.binary32 pair.1)
        (Model.cast _ FloatFormat.binary32 pair.2))) (Model.zero _ false))

-- The generated theorems and the lemmas they are built from rest on the three standard axioms.
run_cmd do
  for name in [``dot_closed, ``sum_closed, ``horner_closed, ``hornerList_closed,
      ``sumList_closed, ``linear_closed, ``total_closed, ``squarePlus_closed,
      ``perceptron_closed, ``norm_closed, ``dot32_closed, ``expSubOne64_closed, ``wideDot_closed,
      ``literal_closed,
      ``cancellation_closed, ``product_closed, ``quotient_closed, ``gradientSubtracted_closed,
      ``gradientDivided_closed, ``expSum_closed, ``softmax_closed, ``logSumExp_closed,
      ``exponential_closed, ``FloatLib.Numerics.Backward.deviation_div,
      ``FloatLib.Numerics.Backward.deviation_node, ``FloatLib.Numerics.Backward.deviation_exp,
      ``FloatLib.Numerics.Backward.deviation_log,
      ``List.abs_foldl_sub_foldl_le, ``List.abs_foldl_finRange_sub_le,
      ``List.abs_foldl_zip_sub_foldl_le, ``List.foldl_finRange_add_eq_sum,
      ``FloatLib.Numerics.Backward.deviation_leaf, ``FloatLib.Numerics.Backward.deviation_mul,
      ``FloatLib.Numerics.Backward.forward] do
    let axioms ← Lean.collectAxioms name
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unexpected axiom {dependency}"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed
