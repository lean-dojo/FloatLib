/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Numerics.ErrorBound.SumLoop
public meta import Lean.Elab.Command

/-!
# Roundoff analysis of C kernels

The kernels of a C inference loop, as written: the scale of an RMS normalization,
`1 / sqrtf(ss / n + eps)` after a sum of squares, a maximum loop that branches on the rounded
accumulator, a quotient by an exact literal, a call of a function the program takes under a
contract, and the integer rounding and casts of an int8 quantization. The sign of the sum of
squares is derived, so the square root keeps a relative error and divides the absolute one by
about `2 √x₀`, and the sign of the rounded operand gives the square root's domain; the maximum
step has the real value `max`, is finite with its operands and keeps zero budgets zero; the
literal `4` converts exactly, and a literal such as `1e-5` needs no premise; and the argument
error of the contracted call is propagated through its model. The generated bound of a dot
product is restated in closed form by `List.abs_sub_le_of_sumFold`, and its range conditions
follow from bounds on its terms by `List.allSteps_sumFold_of_abs_le`. Absolute statements name
their parts and spell a catalogued format by its name, as mixed ones do. A RoPE row, a difference
of two products, is analyzed in a small part of the default budget. C's `(float) size` keeps the
sign of its integer, so dividing by it leaves the square root no domain premise, and an integer
known to be at most `2 ^ 24` in magnitude converts exactly. The range of the `int8_t` cast is a
condition on reals, on the bound of the rounded quotient.
-/

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

variable {format : FloatFormat} {plan : Configured.StoragePlan format} {code : Type}
  [ExecFloat.ModelCodec plan (Model format) code]
  [ExecFloat.Backend.PolicyFor (Configured.Family format code plan)]

local notation "Value" => ExecFloat (Configured.Family format code plan)

/-- The sum of squares of a function on `Fin n`, from zero. -/
def sumsq {n : Nat} (x : Fin n → Value) : Value :=
  Fin.foldl n (fun ss j => ss + x j * x j) 0

/-- The scale `1 / sqrt (ss / count + eps)` of an RMS normalization. -/
def scale {n : Nat} (x : Fin n → Value) (count eps : Value) : Value :=
  1 / ExecFloat.sqrt (sumsq x / count + eps)

/-- The scale is finite and has a mixed bound against `1 / √(∑ x² / count + eps)`; the sign of the
sum of squares is derived, not assumed. -/
roundoff mixed theorem scale_mixedError :=
  fun {n : Nat} (x : Fin n → Value) (count eps : Value) (hformat : format.isIEEE = true)
      (hcount : 0 < ExecFloat.Binary.toReal count) (heps : 0 < ExecFloat.Binary.toReal eps) =>
    ExecFloat.Binary.toReal (scale x count eps)

/-- The scale is within an absolute budget of `1 / √(∑ x² / count + eps)`. -/
roundoff theorem scale_error :=
  fun {n : Nat} (x : Fin n → Value) (count eps : Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (scale x count eps)

/-- The maximum of a function on `Fin (n + 1)` by the C loop
`if (x[i] > m) m = x[i]`. -/
def peak {n : Nat} (x : Fin (n + 1) → Value) : Value :=
  Fin.foldl n (fun m (i : Fin n) => if x i.succ > m then x i.succ else m) (x 0)

/-- The C maximum loop is exact against the real maximum of the decoded entries. -/
roundoff mixed theorem peak_mixedError :=
  fun {n : Nat} (x : Fin (n + 1) → Value) => ExecFloat.Binary.toReal (peak x)

/-- A quarter of a binary32 value, by the literal `4`. -/
def quarter (x : Binary32) : Binary32 := x / 4

/-- The quotient by the literal `4` rounds once; the literal carries no conversion error. -/
roundoff mixed theorem quarter_mixedError :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (quarter x)

/-- A product passed to a function the program takes. -/
def scaled (f : Value → Value) (x y : Value) : Value := f (x * y)

/-- Under a contract with mixed error `(u, η)` against `Real.exp`, the call has a mixed bound
against `exp (x * y)` on the decoded inputs: the product's rounding is propagated through the
model. -/
roundoff mixed theorem scaled_mixedError :=
  fun (f : Value → Value) (hformat : format.isIEEE = true)
      (hf : ∀ a : Value, ExecFloat.Binary.isFinite a = true →
        ExecFloat.Binary.isFinite (f a) = true ∧
        MixedError (ExecFloat.Binary.toReal (f a)) (Real.exp (ExecFloat.Binary.toReal a))
          (Model.unitRoundoffAt format) (Model.underflowErrorAt format))
      (x y : Value) =>
    ExecFloat.Binary.toReal (scaled f x y)

/-- The dot product of two functions on `Fin n`, from zero. -/
def dot {n : Nat} (x y : Fin n → Value) : Value :=
  Fin.foldl n (fun s j => s + x j * y j) 0

/-- The dot product is finite and has a mixed bound against the real dot product. -/
roundoff mixed theorem dot_mixedError :=
  fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) =>
    ExecFloat.Binary.toReal (dot x y)

/-- The generated bound of the dot product in closed form:
`((1 + u)^n - 1) * ∑ |x y| + (1 + u)^n * ∑ (u * |x y| + η)`. -/
example := fun {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) hvalid =>
  List.abs_sub_le_of_sumFold (Model.unitRoundoffAt format) (Model.unitRoundoffAt_pos _).le _ _
    (fun j : Fin n => Model.unitRoundoffAt format *
      |ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)| +
        Model.underflowErrorAt format)
    (fun _ => add_nonneg (mul_nonneg (Model.unitRoundoffAt_pos _).le (abs_nonneg _))
      (Model.underflowErrorAt_pos _).le) _ _ (dot_mixedError x y hformat hvalid).2

/-- The range conditions of the dot product follow from bounds on its terms: finite entries,
products at most `b`, `(1 + u)^(n + 1) ≤ 2` and `2 (n + 1) (b + η)` at most the largest finite
value. -/
example {n : Nat} (x y : Fin n → Value) (hformat : format.isIEEE = true) (b : ℝ)
    (hx : ∀ j, ExecFloat.Binary.isFinite (x j) = true)
    (hy : ∀ j, ExecFloat.Binary.isFinite (y j) = true)
    (hb : ∀ j, |ExecFloat.Binary.toReal (x j) * ExecFloat.Binary.toReal (y j)| ≤ b)
    (hgrowth : (1 + Model.unitRoundoffAt format) ^ (n + 1) ≤ 2)
    (hrange : 2 * (n + 1) * (b + Model.underflowErrorAt format) ≤
      Model.toReal (Model.posMaxFinite format)) :
    ExecFloat.Binary.isFinite (dot x y) = true :=
  (dot_mixedError x y hformat ((List.AllSteps.of_forall _ _ _ _ fun _ j => hx j).and
    ((List.AllSteps.of_forall _ _ _ _ fun _ j => hy j).and
      (List.allSteps_sumFold_of_abs_le _ _ b _ (Model.unitRoundoffAt_pos _).le
        (Model.underflowErrorAt_pos _).le _ _ _
        (fun _ => add_nonneg (mul_nonneg (Model.unitRoundoffAt_pos _).le (abs_nonneg _))
          (Model.underflowErrorAt_pos _).le) _ _
        (fun j _ => hb j) (fun _ _ => le_rfl) (by simpa using hgrowth)
        (by simpa using hrange))))).1

/-- `round(v)` at binary32, to nearest with ties away from zero. -/
def round32 (v : Binary32) : Binary32 := ExecFloat.Binary.roundToIntegral v .nearestAway

/-- Rounding to an integral value has absolute error one half against its operand. -/
roundoff mixed theorem round32_mixedError :=
  fun (v : Binary32) => ExecFloat.Binary.toReal (round32 v)

/-- `(float) n` at binary32. -/
def ofInt32 (n : Int) : Binary32 := ExecFloat.Binary.ofRat (n : ℚ)

/-- The conversion of an integer has relative error `u` and no absolute error. -/
roundoff mixed theorem ofInt32_mixedError :=
  fun (n : Int) => ExecFloat.Binary.toReal (ofInt32 n)

/-- `(int8_t) round(x / s)` has absolute error one half and the quotient's rounding against
`x / s`, when that bound keeps the integer below `2 ^ 7` in magnitude. -/
roundoff mixed theorem quantize_mixedError :=
  fun (x s : Binary32) =>
    (((Int8.ofInt ((ExecFloat.Binary.toInt? (x / s) .nearestAway).getD 0)).toInt : ℤ) : ℝ)

/-- The C maximum loop over the entries `X 1, …, X (size - 1)` of a function on `Nat`, from
`X 0`, at binary32. -/
def peak32 (X : Nat → Binary32) (size : Nat) : Binary32 :=
  Fin.foldl (size - 1) (fun m (i : Fin (size - 1)) => if X (i + 1) > m then X (i + 1) else m) (X 0)

/-- With finite entries the maximum is finite and exact, with no other condition. -/
roundoff mixed theorem peak32_mixedError :=
  fun (X : Nat → Binary32) (size : Nat) (hX : ∀ k, ExecFloat.Binary.isFinite (X k) = true) =>
    ExecFloat.Binary.toReal (peak32 X size)

/-- The scale of an RMS normalization with the literal `1e-5` at binary32. -/
def scale32 {n : Nat} (x : Fin n → Binary32) (count : Binary32) : Binary32 :=
  1 / ExecFloat.sqrt (Fin.foldl n (fun ss j => ss + x j * x j) 0 / count + 1e-5)

/-- The scale has a mixed bound; the literal's range and finiteness are decided, not assumed. -/
roundoff mixed theorem scale32_mixedError :=
  fun {n : Nat} (x : Fin n → Binary32) (count : Binary32)
      (hcount : 0 < ExecFloat.Binary.toReal count) =>
    ExecFloat.Binary.toReal (scale32 x count)

/-- The scale's absolute bound; the literal's finiteness is decided, not assumed. -/
roundoff theorem scale32_error :=
  fun {n : Nat} (x : Fin n → Binary32) (count : Binary32) =>
    ExecFloat.Binary.toReal (scale32 x count)

/-- The quarter's absolute bound. -/
roundoff theorem quarter_error :=
  fun (x : Binary32) => ExecFloat.Binary.toReal (quarter x)

open Lean Elab Command in
-- The maximum loop with finite entries has no premise and zero budgets; no scale has a square-root
-- domain premise, and a literal leaves none. An absolute statement names its parts by `let` and
-- spells the format constants `FloatFormat.binary32`, while its values keep the program's storage
-- plan.
run_cmd do
  let statement (name : Name) : CommandElabM Expr := do
    let some info := (← getEnv).find? name | throwError "missing {name}"
    liftTermElabM <| Meta.forallTelescope info.type fun _ body => Meta.zetaReduce body
  let peak ← statement ``peak32_mixedError
  unless peak.isAppOf ``And && (peak.getArg! 1).isAppOfArity ``MixedError 4 &&
      ((peak.getArg! 1).getArg! 2).nat? == some 0 && ((peak.getArg! 1).getArg! 3).nat? == some 0 do
    throwError "peak32_mixedError has a premise or a budget: {peak}"
  for name in #[``scale_mixedError, ``scale32_mixedError] do
    let scale ← statement name
    if (scale.find? (·.isConstOf ``ExecFloat.Binary.signBit)).isSome then
      throwError "{name} keeps the square root's domain premise"
  let scale ← statement ``scale32_mixedError
  if (scale.find? fun term => term.isAppOf ``ExecFloat.Binary.isFinite &&
      term.getAppArgs.back?.any (·.isAppOf ``OfScientific.ofScientific)).isSome then
    throwError "scale32_mixedError assumes its literal finite"
  let scale ← statement ``scale32_error
  if (scale.find? fun term => term.isAppOf ``Model.isFinite &&
      term.getAppArgs.back?.any (·.isAppOf ``Model.ofRat)).isSome then
    throwError "scale32_error assumes its literal finite"
  let some info := (← getEnv).find? ``quarter_error | throwError "missing quarter_error"
  unless (info.type.find? (·.isLet)).isSome do throwError "quarter_error names no part"
  unless (info.type.find? fun term => term.isAppOf ``Model.halfUlpAt &&
      term.getAppArgs[0]?.any (·.isConstOf ``FloatFormat.binary32)).isSome do
    throwError "quarter_error does not name its format"
  if (info.type.find? fun term => term.isAppOf ``Configured.StoragePlan.forKnownWidth &&
      term.getAppArgs[0]?.any (·.isConstOf ``FloatFormat.binary32)).isSome then
    throwError "quarter_error respells a storage plan"

/-- One row of a C RoPE rotation at binary32: a difference of two products. -/
def rotate32 (v0 v1 c s : Binary32) : Binary32 := v0 * c - v1 * s

open Lean Elab Command in
-- The sign premise of Sterbenz's rule on the two products is settled without comparing their code,
-- so the whole analysis takes a small part of the default budget, as the sum row does.
run_cmd do
  let start ← IO.getNumHeartbeats
  elabCommand (← `(command| roundoff mixed theorem $(mkIdent `rotate32_mixedError) :=
    fun (v0 v1 c s : Binary32) => ExecFloat.Binary.toReal (rotate32 v0 v1 c s)))
  let used := ((← IO.getNumHeartbeats) - start) / 1000
  if used > 20000 then throwError "rotate32_mixedError used {used} heartbeats"

/-- The scale of an RMS normalization that divides by C's `(float) size` at binary32. -/
def scaleSize32 (X : Nat → Binary32) (size : Nat) : Binary32 :=
  1 / ExecFloat.sqrt (Fin.foldl size (fun ss (j : Fin size) => ss + X j * X j) 0 /
    ExecFloat.Binary.ofRat (size : ℚ) + 1e-5)

/-- The sign of the converted size is derived, so the square root has no domain premise. -/
roundoff mixed theorem scaleSize32_mixedError :=
  fun (X : Nat → Binary32) (size : Nat) (hsize : 0 < size) =>
    ExecFloat.Binary.toReal (scaleSize32 X size)

/-- A conversion of a natural number is nonnegative, finite or not. -/
example (n : Nat) :
    0 ≤ ExecFloat.Binary.toReal (ExecFloat.Binary.ofRat (n : ℚ) : Binary32) := by
  roundoff

/-- A conversion of a positive integer is positive when it is finite. -/
example (n : Int) (hn : 0 < n)
    (hfinite : ExecFloat.Binary.isFinite (ExecFloat.Binary.ofRat (n : ℚ) : Binary32) = true) :
    0 < ExecFloat.Binary.toReal (ExecFloat.Binary.ofRat (n : ℚ) : Binary32) := by
  roundoff

open Lean Elab Command in
-- The converted size keeps its sign, so no square-root domain premise is left.
run_cmd do
  let some info := (← getEnv).find? ``scaleSize32_mixedError | throwError "missing statement"
  if (info.type.find? (·.isConstOf ``ExecFloat.Binary.signBit)).isSome then
    throwError "scaleSize32_mixedError keeps the square root's domain premise"

/-- `(float) n` of an integer of magnitude at most `2 ^ 24` is exact at binary32. -/
roundoff mixed theorem ofSmallInt32_mixedError :=
  fun (n : Int) (hn : |n| ≤ 2 ^ 24) => ExecFloat.Binary.toReal (ofInt32 n)

/-- `(float) size` of a size of at most `4096` is exact at binary32. -/
roundoff mixed theorem ofSize32_mixedError :=
  fun (size : Nat) (hsize : size ≤ 4096) =>
    ExecFloat.Binary.toReal (ExecFloat.Binary.ofRat (size : ℚ) : Binary32)

open Lean Elab Command in
-- A small integer converts exactly, from the bound in a hypothesis; without one the conversion
-- keeps relative error `u`.
run_cmd do
  for name in #[``ofSmallInt32_mixedError, ``ofSize32_mixedError] do
    let some info := (← getEnv).find? name | throwError "missing {name}"
    let mixed ← liftTermElabM do
      Meta.forallTelescope (← Meta.zetaReduce info.type) fun _ body => pure body
    unless mixed.isAppOf ``And && (mixed.getArg! 1).isAppOfArity ``MixedError 4 &&
        ((mixed.getArg! 1).getArg! 2).nat? == some 0 &&
        ((mixed.getArg! 1).getArg! 3).nat? == some 0 do
      throwError "{name} is not exact: {mixed}"

/-- `(int8_t) round(x / s)` within an absolute budget of `x / s`. -/
roundoff theorem quantize_error :=
  fun (x s : Binary32) =>
    (((Int8.ofInt ((ExecFloat.Binary.toInt? (x / s) .nearestAway).getD 0)).toInt : ℤ) : ℝ)

open Lean Elab Command in
-- The range of the int8 cast is a condition on reals, a bound of the integer's enclosure by
-- `2 ^ 7`, and no premise reads the computed integer.
run_cmd do
  for name in #[``quantize_mixedError, ``quantize_error] do
    let some info := (← getEnv).find? name | throwError "missing {name}"
    let mut work ← liftTermElabM do
      Meta.forallTelescope (← Meta.zetaReduce info.type) fun binders _ =>
        binders.mapM fun binder => Meta.inferType binder
    let mut premises := #[]
    while 0 < work.size do
      let condition := work.back!
      work := work.pop
      if condition.isAppOfArity ``And 2 then
        work := (work.push (condition.getArg! 0)).push (condition.getArg! 1)
      else premises := premises.push condition
    let computed (condition : Expr) :=
      (condition.find? (·.isAppOf ``ExecFloat.Binary.toInt?)).isSome
    if let some condition := premises.find? computed then
      throwError "{name} assumes a range of the computed integer: {condition}"
    unless premises.any (fun condition => condition.isAppOfArity ``LT.lt 4 &&
        (condition.getArg! 3).isAppOf ``HPow.hPow) do
      throwError "{name} has no range condition on reals"

end FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels
