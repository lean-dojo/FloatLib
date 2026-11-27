/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic

/-!
# Why an interval evaluation has no enclosure

`Expr.evalZero?` returns `none` when a variable has no interval or the backend rejects an
operation, and it doesn't say which. `Expr.diagnose` runs the same evaluation and keeps the
reason. On success it returns the enclosure. Otherwise it returns the first obstruction in
evaluation order: a variable that the environment has no interval for, or the first node whose
operation the backend rejects, with the decoded enclosures of its operands. When an end of one of
those enclosures doesn't decode, such as an infinity or a NaN of a float format, it reports that
instead. Take `1 / x` with `x` in `[-1, 1]` on the binary grid of quarters: the evaluation is
`none`, and the diagnosis is the division, with its operands decoded as `[1, 1]` and `[-1, 1]`.

The diagnosis keeps the evaluation, so it never disagrees with `Expr.evalZero?`, and a product
with a factor that is exactly zero is zero here as there, whatever the other factor is.

## Main definitions

* `Obstruction`: a variable without an interval, an operation that the backend rejects with the
  decoded enclosures of its operands, or such an operation with an operand end that doesn't
  decode.
* `Diagnosis β`: the value of an evaluation, or the obstruction that left it without one.
* `Expr.diagnose e B env`: the diagnosis of evaluating `e` with the backend `B` in `env`.

## Main statements

* `Expr.value?_diagnose`: the value of the diagnosis is `Expr.evalZero?`.
* `Expr.diagnose_eq_success_iff`: the diagnosis is a success with `I` exactly when the evaluation
  gives `I`.

## Implementation notes

`Expr.diagnose` is recursion by pattern matching, which compiled code runs as written and Lean's
kernel reduces, for any backend: exact rationals, the binary grid, or an outward rounding into a
float format.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Why an evaluation with the zero rule has no enclosure: the first obstruction in evaluation
order, as `Expr.diagnose` reports it. -/
inductive Obstruction where
  /-- The environment has no interval for the variable `index`. -/
  | missingVariable (index : Nat)
  /-- The backend rejected the operation at `node`. `inputs` are the decoded enclosures of its
  operands, in order, and a constant has none. -/
  | rejected (node : Expr) (inputs : List (Interval ℚ))
  /-- The backend rejected the operation at `node`, and an end of one of its operand enclosures
  does not decode. -/
  | undecodable (node : Expr)
  deriving DecidableEq, Repr

/-- The report that the backend `B` rejected the operation at `node` on the operand enclosures
`inputs`: `rejected` with their decoded intervals, or `undecodable` when an end of one of them
does not decode. -/
def Obstruction.rejection {α : Type*} (B : Backend α) (node : Expr)
    (inputs : List (Interval α)) : Obstruction :=
  match inputs.mapM (Interval.decode? B.decode) with
  | some decoded => .rejected node decoded
  | none => .undecodable node

/-- What `Expr.diagnose` reports about an evaluation: its value, of type `β`, or the obstruction
that left it without one. -/
inductive Diagnosis (β : Type*) where
  /-- The evaluation succeeded with this value. -/
  | success (value : β)
  /-- The evaluation stopped at this obstruction. -/
  | failure (obstruction : Obstruction)
  deriving DecidableEq, Repr

namespace Diagnosis

variable {α β γ : Type*}

/-- The value of a success, and `none` for a failure. -/
def value? : Diagnosis β → Option β
  | .success value => some value
  | .failure _ => none

/-- The obstruction of a failure, and `none` for a success. -/
def obstruction? : Diagnosis β → Option Obstruction
  | .success _ => none
  | .failure obstruction => some obstruction

/-- Continue a success with `next`, and keep a failure as it is. -/
def bind (d : Diagnosis β) (next : β → Diagnosis γ) : Diagnosis γ :=
  match d with
  | .success value => next value
  | .failure obstruction => .failure obstruction

/-- The result `result` of the backend's operation at `node` on the operand enclosures `inputs`:
a success, or the backend's rejection (`Obstruction.rejection`) when there is no result. -/
def ofResult (B : Backend α) (node : Expr) (inputs : List (Interval α))
    (result : Option (Interval α)) : Diagnosis (Interval α) :=
  match result with
  | some I => .success I
  | none => .failure (Obstruction.rejection B node inputs)

/-- The step of `Expr.diagnose` at the binary operation `node`, with operator `op`, from the
diagnoses of its operands. Its value is that of `Expr.zeroBinary?`. Without one, it reports the
first operand that failed, or the backend's rejection of the operation. -/
def zeroBinary (B : Backend α) (op : BinaryOp) (node : Expr)
    (left right : Diagnosis (Interval α)) : Diagnosis (Interval α) :=
  match Expr.zeroBinary? B op left.value? right.value? with
  | some K => .success K
  | none => left.bind fun I => right.bind fun J => .failure (Obstruction.rejection B node [I, J])

/-- A success has its value. -/
@[simp] theorem value?_success (value : β) : (success value).value? = some value := rfl

/-- A failure has no value. -/
@[simp] theorem value?_failure (obstruction : Obstruction) :
    (failure obstruction : Diagnosis β).value? = none := rfl

/-- A diagnosis has the value `value` exactly when it is the success with that value. -/
theorem value?_eq_some_iff {d : Diagnosis β} {value : β} :
    d.value? = some value ↔ d = .success value := by
  cases d <;> simp

/-- A continued diagnosis has a value when both steps have one. -/
@[simp] theorem value?_bind (d : Diagnosis β) (next : β → Diagnosis γ) :
    (d.bind next).value? = d.value?.bind fun value => (next value).value? := by
  cases d <;> rfl

/-- The value of an operation's result is that result. -/
@[simp] theorem value?_ofResult (B : Backend α) (node : Expr) (inputs : List (Interval α))
    (result : Option (Interval α)) : (ofResult B node inputs result).value? = result := by
  cases result <;> rfl

/-- The value of the step at a binary operation is the step of `Expr.evalZero?` on the values of
the operands. -/
@[simp] theorem value?_zeroBinary (B : Backend α) (op : BinaryOp) (node : Expr)
    (left right : Diagnosis (Interval α)) :
    (zeroBinary B op node left right).value? =
      Expr.zeroBinary? B op left.value? right.value? := by
  unfold zeroBinary
  cases Expr.zeroBinary? B op left.value? right.value? <;> simp

end Diagnosis

mutual
/--
Evaluate `e` as `Expr.evalZero?` does and keep the reason for a failure: the enclosure, or the
first obstruction in evaluation order. That is a variable that `env` has no interval for, or the
first node whose operation the backend rejects, with the decoded enclosures of its operands
(`Obstruction.rejection`). A product with a factor that is the point zero, and a quotient with
such a numerator, have the enclosure of that zero, as in `Expr.evalZero?`. The value of the
diagnosis is the evaluation (`Expr.value?_diagnose`).

Compiled code diagnoses both operands of a binary operation, so a diagnosis costs at most one
evaluation of each node.
-/
def Expr.diagnose {α : Type*} (e : Expr) (B : Backend α) (env : Nat → Option (Interval α)) :
    Diagnosis (Interval α) :=
  match e with
  | .const q => Diagnosis.ofResult B (.const q) [] (B.const? q)
  | .var i =>
    match env i with
    | some I => .success I
    | none => .failure (.missingVariable i)
  | .unary op a =>
    (Expr.diagnose a B env).bind fun I => Diagnosis.ofResult B (.unary op a) [I] (B.unary? op I)
  | .binary op a b =>
    Diagnosis.zeroBinary B op (.binary op a b) (Expr.diagnose a B env) (Expr.diagnose b B env)
  | .ternary op a b c =>
    (Expr.diagnose a B env).bind fun I => (Expr.diagnose b B env).bind fun J =>
      (Expr.diagnose c B env).bind fun K =>
        Diagnosis.ofResult B (.ternary op a b c) [I, J, K] (B.ternary? op I J K)
  | .call index args =>
    (Expr.diagnoseArgs args B env).bind fun inputs =>
      Diagnosis.ofResult B (.call index args) inputs (B.call? index inputs)
termination_by structural e

/-- Diagnose the arguments of a registered call in order: their enclosures, or the first
obstruction. -/
def Expr.diagnoseArgs {α : Type*} (args : List Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Diagnosis (List (Interval α)) :=
  match args with
  | [] => .success []
  | arg :: args =>
    (Expr.diagnose arg B env).bind fun I =>
      (Expr.diagnoseArgs args B env).bind fun rest => .success (I :: rest)
termination_by structural args
end

/-- **The diagnosis keeps the evaluation.** The value of `e.diagnose B env` is
`e.evalZero? B env`, for every expression, backend and environment. -/
@[simp] theorem Expr.value?_diagnose {α : Type*} (e : Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : (e.diagnose B env).value? = e.evalZero? B env := by
  refine Expr.rec
    (motive_1 := fun e => (e.diagnose B env).value? = e.evalZero? B env)
    (motive_2 := fun args =>
      (Expr.diagnoseArgs args B env).value? = Expr.evalZeroArgs? args B env)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro q
    rw [Expr.diagnose, Diagnosis.value?_ofResult, Expr.evalZero?_const]
  · intro i
    rw [Expr.diagnose, Expr.evalZero?_var]
    cases env i <;> rfl
  · intro op a ha
    rw [Expr.diagnose, Expr.evalZero?_unary, Diagnosis.value?_bind, ha]
    simp only [Diagnosis.value?_ofResult]
  · intro op a b ha hb
    rw [Expr.diagnose, Expr.evalZero?_binary, Diagnosis.value?_zeroBinary, ha, hb]
  · intro op a b c ha hb hc
    rw [Expr.diagnose, Expr.evalZero?_ternary]
    simp only [Diagnosis.value?_bind, Diagnosis.value?_ofResult, ha, hb, hc]
    rfl
  · intro index args hargs
    rw [Expr.diagnose, Expr.evalZero?_call, Diagnosis.value?_bind, hargs]
    simp only [Diagnosis.value?_ofResult]
  · rw [Expr.diagnoseArgs, Expr.evalZeroArgs?_nil]
    rfl
  · intro arg args ha hargs
    rw [Expr.diagnoseArgs, Expr.evalZeroArgs?_cons]
    simp only [Diagnosis.value?_bind, Diagnosis.value?_success, ha, hargs]
    rfl

/-- **Success is the evaluation's success.** `e.diagnose B env` reports success with the
enclosure `I` exactly when `e.evalZero? B env = some I`, so every failure explains an evaluation
without a result. -/
theorem Expr.diagnose_eq_success_iff {α : Type*} {e : Expr} {B : Backend α}
    {env : Nat → Option (Interval α)} {I : Interval α} :
    e.diagnose B env = .success I ↔ e.evalZero? B env = some I := by
  rw [← Expr.value?_diagnose, Diagnosis.value?_eq_some_iff]

end FloatLib.Numerics.Interval
