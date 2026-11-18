/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import FloatLib.Tactic.Roundoff
import FloatLib.Floats.Formats.BinaryInterchange.Configured

/-!
# The forward bounds of the roundoff benchmark

The programs whose generated forward bounds `benchmarks/roundoff/bounds.py` evaluates against
measured errors: a sum, a dot product, Horner's rule, an entry of a matrix product, a softmax
weight, a log-sum-exp, the two schedules of the Softmax Collapse target gradient, one output of a
linear layer and one output of a two-layer perceptron. Each `#check` prints the theorem that
`roundoff mixed theorem` generates; `bounds.py` follows its recurrences. `#roundoff_shape` says
whether the bound is relative. The last two sections generate the backward-error theorems of the
programs that have one and their forward bounds in closed form (`roundoff closed theorem`);
`bounds.py` evaluates the closed forms. Then come the cancellation cases, a scaled difference
that does not round and a relative entropy in two forms, and last an interval endpoint computed
in a directed rounding attribute, by two operations and by one fused multiply-add, and one call
of `expm1x` in closed form.
-/

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace FloatLibBenchmarks.Roundoff

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- A sum, left to right from zero. -/
def sum {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j) 0

roundoff mixed theorem sum_forward :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sum x)
#check @sum_forward
#roundoff_shape sum_forward

/-- A dot product, left to right from zero. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

roundoff mixed theorem dot_forward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)
#check @dot_forward
#roundoff_shape dot_forward

/-- Horner's rule over a list of coefficients, highest degree first. -/
def horner (coefficients : List Value) (x : Value) : Value :=
  coefficients.foldl (fun value coefficient => value * x + coefficient) 0

roundoff mixed theorem horner_forward :=
  fun (coefficients : List Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (horner coefficients x)
#check @horner_forward
#roundoff_shape horner_forward

/-- Entry `(i, j)` of a matrix product. -/
def matmul {m k n : Nat} (A : Fin m → Fin k → Value) (B : Fin k → Fin n → Value) (i : Fin m)
    (j : Fin n) : Value :=
  Fin.foldl k (fun s l => s + A i l * B l j) 0

roundoff mixed theorem matmul_forward :=
  fun {m k n : Nat} (A : Fin m → Fin k → Value) (B : Fin k → Fin n → Value) (i : Fin m)
    (j : Fin n) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (matmul A B i j)
#check @matmul_forward
#roundoff_shape matmul_forward

/-- The sum of the correctly rounded exponentials of a function on `Fin n`. -/
def expSum {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun s i => s + ExecFloat.Binary.CorrectlyRounded.exp (x i)) 0

/-- The first softmax weight. -/
def softmax {n : Nat} (x : Fin (n + 1) → Value) : Value :=
  ExecFloat.Binary.CorrectlyRounded.exp (x 0) / expSum x

roundoff mixed theorem softmax_forward :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (softmax x)
#check @softmax_forward
#roundoff_shape softmax_forward

/-- The logarithm of a sum of exponentials. -/
def logSumExp {n : Nat} (x : Fin (n + 1) → Value) : Value :=
  ExecFloat.Binary.CorrectlyRounded.log (expSum x)

roundoff mixed theorem logSumExp_forward :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (logSumExp x)
#check @logSumExp_forward
#roundoff_shape logSumExp_forward

/-- The target gradient of cross-entropy as `1 / (1 + s) - 1`. -/
roundoff mixed theorem targetGradientOld_forward :=
  fun (s : Value) (_hformat : format.isIEEE = true) (_hs : ExecFloat.Binary.isFinite s = true)
    (_hpos : 0 < ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (1 / (1 + s) - 1)
#check @targetGradientOld_forward
#roundoff_shape targetGradientOld_forward

/-- The same gradient as `-(s / (1 + s))`. -/
roundoff mixed theorem targetGradientNew_forward :=
  fun (s : Value) (_hformat : format.isIEEE = true) (_hs : ExecFloat.Binary.isFinite s = true)
    (_hpos : 0 < ExecFloat.Binary.toReal s) =>
    ExecFloat.Binary.toReal (-(s / (1 + s)))
#check @targetGradientNew_forward
#roundoff_shape targetGradientNew_forward

/-- One output of a linear layer. -/
def linear {n : Nat} (w x : Fin n → Value) (b : Value) : Value :=
  Fin.foldl n (fun s j => s + w j * x j) 0 + b

roundoff mixed theorem linear_forward :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (linear w x b)
#check @linear_forward
#roundoff_shape linear_forward

/-- The rectifier, as a maximum with zero. -/
def relu (z : Value) : Value := if z > 0 then z else 0

/-- One output of a perceptron with one hidden layer. -/
def mlp {n h : Nat} (W : Fin h → Fin n → Value) (b : Fin h → Value) (v : Fin h → Value)
    (c : Value) (x : Fin n → Value) : Value :=
  Fin.foldl h (fun s k => s + v k * relu (linear (W k) x (b k))) 0 + c

roundoff mixed theorem mlp_forward :=
  fun {n h : Nat} (W : Fin h → Fin n → Value) (b : Fin h → Value) (v : Fin h → Value)
    (c : Value) (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mlp W b v c x)
#check @mlp_forward
#roundoff_shape mlp_forward

/-! ## Backward-error theorems -/

roundoff (backward := true) theorem sum_backward :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sum x)
#check @sum_backward

roundoff (backward := true) theorem dot_backward :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)
#check @dot_backward

roundoff (backward := true) theorem horner_backward :=
  fun (coefficients : List Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (horner coefficients x)
#check @horner_backward

roundoff (backward := true) theorem matmul_backward :=
  fun {m k n : Nat} (A : Fin m → Fin k → Value) (B : Fin k → Fin n → Value) (i : Fin m)
    (j : Fin n) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (matmul A B i j)
#check @matmul_backward

roundoff (backward := true) theorem linear_backward :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (linear w x b)
#check @linear_backward

/-! ## Forward bounds in closed form -/

roundoff closed theorem sum_closed :=
  fun {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (sum x)
#check @sum_closed

roundoff closed theorem dot_closed :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)
#check @dot_closed

roundoff closed theorem horner_closed :=
  fun (coefficients : List Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (horner coefficients x)
#check @horner_closed

roundoff closed theorem matmul_closed :=
  fun {m k n : Nat} (A : Fin m → Fin k → Value) (B : Fin k → Fin n → Value) (i : Fin m)
    (j : Fin n) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (matmul A B i j)
#check @matmul_closed

roundoff closed theorem linear_closed :=
  fun {n : Nat} (w x : Fin n → Value) (b : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (linear w x b)
#check @linear_closed

roundoff closed theorem mlp_closed :=
  fun {n h : Nat} (W : Fin h → Fin n → Value) (b : Fin h → Value) (v : Fin h → Value)
    (c : Value) (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mlp W b v c x)
#check @mlp_closed

roundoff closed theorem softmax_closed :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (softmax x)
#check @softmax_closed

roundoff closed theorem logSumExp_closed :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (logSumExp x)
#check @logSumExp_closed

roundoff closed theorem targetGradientOld_closed :=
  fun (s : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (1 / (1 + s) - 1)
#check @targetGradientOld_closed

roundoff closed theorem targetGradientNew_closed :=
  fun (s : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal (-(s / (1 + s)))
#check @targetGradientNew_closed

/-- The perceptron also has a backward-error theorem. -/
roundoff (backward := true) theorem mlp_backward :=
  fun {n h : Nat} (W : Fin h → Fin n → Value) (b : Fin h → Value) (v : Fin h → Value)
    (c : Value) (x : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mlp W b v c x)
#check @mlp_backward

/-! ## Cancellation cases

A difference of two values within a factor of two of each other, scaled; the relative entropy of
two distributions, as the sum of `p j * (log (p j) - log (q j))`, whose terms cancel, and as the
sum of `p j * expm1x (log (q j) - log (p j))`, whose terms are nonnegative. The script evaluates
their bounds where the distributions are close. -/

/-- A scaled difference whose operands are within a factor of two: the subtraction is exact. -/
roundoff mixed theorem scaledDifference_forward :=
  fun (x y z : Value) (hformat : format.isIEEE = true)
      (hlow : ExecFloat.Binary.toReal y / 2 ≤ ExecFloat.Binary.toReal x)
      (hhigh : ExecFloat.Binary.toReal x ≤ 2 * ExecFloat.Binary.toReal y) =>
    ExecFloat.Binary.toReal ((x - y) * z)
#check @scaledDifference_forward

/-- The same difference with no fact about its operands: the subtraction rounds. -/
roundoff mixed theorem scaledDifference_unknown :=
  fun (x y z : Value) (hformat : format.isIEEE = true) => ExecFloat.Binary.toReal ((x - y) * z)
#check @scaledDifference_unknown

roundoff closed theorem scaledDifference_closed :=
  fun (x y z : Value) (hformat : format.isIEEE = true)
      (hlow : ExecFloat.Binary.toReal y / 2 ≤ ExecFloat.Binary.toReal x)
      (hhigh : ExecFloat.Binary.toReal x ≤ 2 * ExecFloat.Binary.toReal y) =>
    ExecFloat.Binary.toReal ((x - y) * z)
#check @scaledDifference_closed

/-- The relative entropy as the sum of `p j * (log (p j) - log (q j))`. -/
def entropyDifference {n : Nat} (p q : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + p j * (ExecFloat.Binary.CorrectlyRounded.log (p j) -
    ExecFloat.Binary.CorrectlyRounded.log (q j))) 0

roundoff mixed theorem entropyDifference_forward :=
  fun {n : Nat} (p q : Fin n → Value) (hformat : format.isIEEE = true)
      (hp : ∀ j, 0 < ExecFloat.Binary.toReal (p j))
      (hq : ∀ j, 0 < ExecFloat.Binary.toReal (q j)) =>
    ExecFloat.Binary.toReal (entropyDifference p q)
#check @entropyDifference_forward
#roundoff_shape entropyDifference_forward

/-- The relative entropy as the sum of the nonnegative terms
`p j * expm1x (log (q j) - log (p j))`. -/
def entropyStable {n : Nat} (p q : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + p j * ExecFloat.Binary.CorrectlyRounded.expm1x
    (ExecFloat.Binary.CorrectlyRounded.log (q j) - ExecFloat.Binary.CorrectlyRounded.log (p j))) 0

roundoff mixed theorem entropyStable_forward :=
  fun {n : Nat} (p q : Fin n → Value) (hformat : format.isIEEE = true)
      (hp : ∀ j, 0 < ExecFloat.Binary.toReal (p j))
      (hq : ∀ j, 0 < ExecFloat.Binary.toReal (q j)) =>
    ExecFloat.Binary.toReal (entropyStable p q)
#check @entropyStable_forward
#roundoff_shape entropyStable_forward

/-! ## A rounding attribute and a function near zero

The lower endpoint of `x * y + z`, both operations rounded toward negative infinity, the same
endpoint by one fused multiply-add, and one call of `expm1x` in closed form. The script
evaluates the first two bounds against the measured error and the third against the value of
the function near zero. -/

/-- The lower endpoint of `x * y + z`. -/
def lowerAffine (x y z : Value) : Value :=
  ExecFloat.Binary.add (ExecFloat.Binary.mul x y (mode := .down)) z (mode := .down)

roundoff mixed theorem lowerAffine_forward :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (lowerAffine x y z)
#check @lowerAffine_forward

/-- The same endpoint by one fused multiply-add rounded toward negative infinity. -/
def lowerFused (x y z : Value) : Value :=
  ExecFloat.Binary.fma x y z (mode := .down)

roundoff mixed theorem lowerFused_forward :=
  fun (x y z : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (lowerFused x y z)
#check @lowerFused_forward

roundoff closed theorem expm1xCall_closed :=
  fun (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.CorrectlyRounded.expm1x x)
#check @expm1xCall_closed

end FloatLibBenchmarks.Roundoff
