/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Roundoff analysis of loops over FloatLib's containers

`roundoff theorem` and `roundoff mixed theorem` infer an error bound from the code alone, for
every IEEE format, storage plan and codec. Here the code loops over the containers FloatLib
registers with the analysis: a dot product over a list of pairs, Horner's rule over the
coefficients of an array and of a vector, dot products over vectors and over functions on `Fin n`,
and a matrix-vector product. Each loop is analyzed once for a symbolic accumulator and lifted
through the traversal by `List.fold_error` or `List.fold_mixedError`, without unrolling it, so the
theorems hold at every length. The conditions concern the states the loop visits
(`List.AllSteps`). Horner's rule on configured and on descriptor-model scalars, and a fused
multiply-add of the descriptor model, which rounds once, need no loop. A call of the correctly
rounded exponential contributes one rounding at its real result: the unit roundoff and the
underflow allowance in a mixed bound. A loop over `Fin n` is a registered reduction, written as its
list loop: a sum of exponentials is nonnegative, and the sum in the denominator of a softmax weight
is analyzed as that loop, so its finiteness and its distance from zero need no conditions of their
own. A loop that carries a count or a flag beside its sum is analyzed as the loop of the sum alone
(`foldl_fst`). A rule stated at a vector coordinate `(i, ())` applies at the coordinate a matrix
coordinate projects and at a pair whose unit component is computed.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.Roundoff

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- Horner's rule for `a x² + b x + c`. -/
def horner (a b c x : Value) : Value :=
  (a * x + b) * x + c

/-- Horner's rule is finite and has a mixed bound against `(a x + b) x + c` on the decoded
inputs, under range conditions on the inputs. -/
roundoff mixed theorem horner_error :=
  fun (a b c x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (horner a b c x)

/-- The dot product of a list of pairs, summed left to right from zero. -/
def dot (pairs : List (Value × Value)) : Value :=
  pairs.foldl (fun sum pair => sum + pair.1 * pair.2) 0

/-- The list dot product is within its accumulated absolute error of the real dot product of the
decoded pairs, when every visited partial sum and product is finite. -/
roundoff theorem dot_error :=
  fun (pairs : List (Value × Value)) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot pairs)

/-- The list dot product is finite and has a mixed bound against the real dot product, under range
conditions at the visited steps. -/
roundoff mixed theorem dot_mixedError :=
  fun (pairs : List (Value × Value)) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot pairs)

/-- Horner's rule over the coefficients of an array, highest degree first. -/
def hornerArray (coefficients : Array Value) (x : Value) : Value :=
  coefficients.foldl (fun value coefficient => value * x + coefficient) 0

/-- Horner's rule over an array is within its accumulated absolute error of the real polynomial,
when every visited intermediate is finite. -/
roundoff theorem horner_array_error :=
  fun (coefficients : Array Value) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (hornerArray coefficients x)

/-- Horner's rule over the coefficients of a vector, highest degree first. -/
def hornerVector {n : Nat} (coefficients : Vector Value n) (x : Value) : Value :=
  coefficients.foldl (fun value coefficient => value * x + coefficient) 0

/-- Horner's rule over a vector is finite and has a mixed bound against the real polynomial, under
range conditions at the visited steps. -/
roundoff mixed theorem horner_vector_mixedError :=
  fun {n : Nat} (coefficients : Vector Value n) (x : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (hornerVector coefficients x)

/-- The dot product of two vectors, read by index. -/
def dotVector {n : Nat} (x y : Vector Value n) : Value :=
  Fin.foldl n (fun sum i => sum + x[i] * y[i]) 0

/-- The vector dot product is within its accumulated absolute error of the real dot product of
the stored entries, when every visited partial sum and product is finite. -/
roundoff theorem dot_vector_error :=
  fun {n : Nat} (x y : Vector Value n) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dotVector x y)

/-- The dot product of two functions on `Fin n`. -/
def dotFin {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun sum i => sum + x i * y i) 0

/-- The dot product on `Fin n` is within its accumulated absolute error of the real dot product,
when every visited partial sum and product is finite. -/
roundoff theorem dot_fin_error :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dotFin x y)

/-- Row `i` of the product of a matrix with a vector. -/
def mulVec {m n : Nat} (A : Matrix (Fin m) (Fin n) Value) (v : Fin n → Value) (i : Fin m) : Value :=
  Fin.foldl n (fun sum j => sum + A i j * v j) 0

/-- Each entry of the matrix-vector product is within its accumulated absolute error of the real
product, when every visited partial sum and product is finite. -/
roundoff theorem mulVec_error :=
  fun {m n : Nat} (A : Matrix (Fin m) (Fin n) Value) (v : Fin n → Value) (i : Fin m)
    (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mulVec A v i)

/-- Each entry of the matrix-vector product is finite and has a mixed bound against the real
product, under range conditions at the visited steps. -/
roundoff mixed theorem mulVec_mixedError :=
  fun {m n : Nat} (A : Matrix (Fin m) (Fin n) Value) (v : Fin n → Value) (i : Fin m)
    (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (mulVec A v i)

/-- Horner's rule on descriptor-model values. -/
def hornerModel (a b c x : Model format) : Model format :=
  Model.add (Model.mul (Model.add (Model.mul a x) b) x) c

/-- Horner's rule on model values has a mixed bound with relative error, as on configured values,
under range conditions on the inputs. A model observation states no finiteness conjunct. The model
rules come from `Analysis.MixedError.Rounding`. -/
roundoff mixed theorem horner_model_mixedError :=
  fun (a b c x : Model format) (hformat : format.isIEEE = true) =>
    Model.toReal (hornerModel a b c x)

/-- The exponential of a product, by FloatLib's correctly rounded `exp`. -/
def expProduct (x y : Value) : Value :=
  ExecFloat.Binary.CorrectlyRounded.exp (x * y)

/-- A call of the correctly rounded exponential contributes the mixed error of one rounding, the
unit roundoff and the underflow allowance, at its real result, with the product's rounding
propagated through `Real.exp`, under range conditions below the overflow threshold. No dictionary
is involved. -/
roundoff mixed theorem exp_product_mixedError :=
  fun (x y : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (expProduct x y)

/-- The sum of the correctly rounded exponentials of a function on `Fin n`. -/
def expSum {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun sum i => sum + ExecFloat.Binary.CorrectlyRounded.exp (x i)) 0

/-- A sum of exponentials is nonnegative at every length, with no condition: every exponential
and every partial sum is. -/
theorem expSum_nonneg {n : Nat} (x : Fin n → Value) (hformat : format.isIEEE = true) :
    0 ≤ ExecFloat.Binary.toReal (expSum x) := by
  roundoff

/-- The first softmax weight of a function on `Fin (n + 1)`. -/
def softmaxWeight {n : Nat} (x : Fin (n + 1) → Value) : Value :=
  ExecFloat.Binary.CorrectlyRounded.exp (x 0) / expSum x

/-- The softmax weight is finite and has a mixed bound against the exact weight of the decoded
inputs, under range conditions on the inputs and budgets at the visited steps. -/
roundoff mixed theorem softmax_weight_mixedError :=
  fun {n : Nat} (x : Fin (n + 1) → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (softmaxWeight x)

/-- A sum counted beside its terms: the loop carries the sum and the number of terms. -/
def countedSum (values : List Value) : Value :=
  (values.foldl (fun (state : Value × Nat) value => (state.1 + value, state.2 + 1)) (0, 0)).1

/-- The counted sum is the sum the loop computes beside the count, within its accumulated absolute
error of the real sum. -/
roundoff theorem counted_sum_error :=
  fun (values : List Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (countedSum values)

/-- A dot product that records beside it whether a zero factor occurred. -/
def flaggedDot (pairs : List (Value × Value)) : Value :=
  (pairs.foldl (fun (state : Value × Bool) pair =>
    (state.1 + pair.1 * pair.2, state.2 || pair.1 == 0 || pair.2 == 0)) (0, false)).1

/-- The flagged dot product is finite and has the mixed bound of the dot product its loop computes
beside the flag. -/
roundoff mixed theorem flagged_dot_mixedError :=
  fun (pairs : List (Value × Value)) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (flaggedDot pairs)

/-- A finite fused multiply-add of the descriptor model rounds once. -/
theorem fma_error (x y z : Model format) (hformat : format.isIEEE = true)
    (hresult : Model.isFinite (Model.fma x y z) = true) :
    |Model.toReal (Model.fma x y z) - (Model.toReal x * Model.toReal y + Model.toReal z)| ≤
      Model.halfUlpAt format (Model.toReal x * Model.toReal y + Model.toReal z) := by
  roundoff

/-- An entry of a stored function at the first component of a vector coordinate, as a tensor read
takes it. -/
def unitEntry (xs : Fin 2 → Value) (c : Fin 2 × Unit) : Value := xs c.1

omit [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)] in
/-- An entry read at a coordinate `(i, ())` is the stored value. -/
theorem unitEntry_mixedError (xs : Fin 2 → Value) (i : Fin 2) :
    MixedError (ExecFloat.Binary.toReal (unitEntry xs (i, ())))
      (ExecFloat.Binary.toReal (xs i)) 0 0 :=
  MixedError.of_eq rfl

section Coordinates

attribute [local roundoff_rule] unitEntry_mixedError

/-- An entry read at the coordinate that a matrix coordinate projects is the stored value. -/
roundoff mixed theorem unitEntry_snd_mixedError :=
  fun (xs : Fin 2 → Value) (c : Fin 3 × Fin 2 × Unit) =>
    id (ExecFloat.Binary.toReal (unitEntry xs c.2))

/-- An entry read at a pair whose unit component is computed is the stored value. -/
roundoff mixed theorem unitEntry_pair_mixedError :=
  fun (xs : Fin 2 → Value) (i : Fin 2) (c : Fin 3 × Unit) =>
    id (ExecFloat.Binary.toReal (unitEntry xs (i, c.2)))

end Coordinates

end FloatLibTests.Conformance.BinaryInterchange.Roundoff
