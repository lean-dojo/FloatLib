/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import Mathlib.Data.Rat.Defs

/-!
# Interval expressions and endpoint backends

An expression records numerical operations and says nothing about how endpoints are represented. A
`Backend` supplies the executable enclosures, with its real-containment contract stated in `Real`,
so the same expression can run with exact rational endpoints, on an integer binary grid, or through
a format-specific outward rounder.

Evaluation returns `none` when an input is missing or a backend can't enclose an operation. A
backend may reject division across zero, for instance, or an interval outside a function's domain.
`Expr.containsReal_eval?` relates a successful evaluation to real evaluation.

`Expr.eval?` is written with the recursor of `Expr`, so that Lean's kernel takes a few steps per
node of an expression. Its equations by pattern matching are the theorems `Expr.eval?_const` to
`Expr.eval?_call`, and compiled code runs `Expr.Compiled.eval?`, the recursion by pattern
matching.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Accuracy controls shared by built-in operations and user enclosures. -/
structure Backend.Config where
  /-- Fractional endpoint bits, also used for square-root approximations. -/
  precision : Nat := 64
  /-- Approximation degree for elementary functions. -/
  degree : Nat := 16
  deriving DecidableEq, Repr, Inhabited

/-- An executable rational enclosure for an operation with a fixed number of real arguments.
Constants have arity zero. `Extension.Sound` supplies its separate containment contract. -/
structure Extension where
  /-- Number of real arguments. -/
  arity : Nat
  /-- Enclose the operation, or reject an unsupported input domain. -/
  enclose? : Backend.Config → List (Interval ℚ) → Option (Interval ℚ)

/-- Adapt a constant enclosure to the common argument-list interface. -/
def Extension.constant (bounds : Backend.Config → Option (Interval ℚ)) : Extension :=
  ⟨0, fun config inputs => match inputs with
    | [] => bounds config
    | _ => none⟩

/-- Adapt a unary enclosure to the common argument-list interface. -/
def Extension.unary (bounds : Backend.Config → Interval ℚ → Option (Interval ℚ)) : Extension :=
  ⟨1, fun config inputs => match inputs with
    | [I] => bounds config I
    | _ => none⟩

/-- Adapt a binary enclosure to the common argument-list interface. -/
def Extension.binary
    (bounds : Backend.Config → Interval ℚ → Interval ℚ → Option (Interval ℚ)) : Extension :=
  ⟨2, fun config inputs => match inputs with
    | [I, J] => bounds config I J
    | _ => none⟩

/-- Unary operations supported by the common interval expression language. -/
inductive UnaryOp where
  /-- The negation `-x`. -/
  | neg
  /-- The absolute value `|x|`. -/
  | abs
  /-- The reciprocal `x⁻¹`. -/
  | inv
  /-- The power `x ^ exponent` with a natural exponent. -/
  | pow (exponent : Nat)
  /-- The exponential. -/
  | exp
  /-- The natural logarithm. -/
  | log
  /-- The sine. -/
  | sin
  /-- The cosine. -/
  | cos
  /-- The tangent. -/
  | tan
  /-- The inverse sine. -/
  | asin
  /-- The inverse cosine. -/
  | acos
  /-- The inverse tangent. -/
  | atan
  /-- The hyperbolic sine. -/
  | sinh
  /-- The hyperbolic cosine. -/
  | cosh
  /-- The hyperbolic tangent. -/
  | tanh
  /-- The square root. -/
  | sqrt
  deriving DecidableEq, Repr

/-- Binary operations supported by the common interval expression language. -/
inductive BinaryOp where
  /-- The sum `x + y`. -/
  | add
  /-- The difference `x - y`. -/
  | sub
  /-- The product `x * y`. -/
  | mul
  /-- The quotient `x / y`. -/
  | div
  /-- The smaller of `x` and `y`. -/
  | min
  /-- The larger of `x` and `y`. -/
  | max
  deriving DecidableEq, Repr

/-- Three-input operations supported by the common interval expression language. -/
inductive TernaryOp where
  /-- The fused multiply-add `x * y + z`. -/
  | fma
  deriving DecidableEq, Repr

/-- A real expression with rational constants, numbered variables, and registered calls. -/
inductive Expr where
  /-- A rational constant. -/
  | const (value : ℚ)
  /-- The input at position `index`. -/
  | var (index : Nat)
  /-- A unary operation applied to an expression. -/
  | unary (op : UnaryOp) (arg : Expr)
  /-- A binary operation applied to two expressions. -/
  | binary (op : BinaryOp) (left right : Expr)
  /-- A three-input operation applied to three expressions. -/
  | ternary (op : TernaryOp) (first second third : Expr)
  /-- The registered extension at position `index` applied to its arguments. -/
  | call (index : Nat) (args : List Expr)
  deriving Repr

mutual
/-- Structural Boolean comparison, including registered argument lists. -/
def Expr.beq : Expr → Expr → Bool
  | .const a, .const b => decide (a = b)
  | .var a, .var b => decide (a = b)
  | .unary op a, .unary op' b => decide (op = op') && a.beq b
  | .binary op a b, .binary op' a' b' => decide (op = op') && a.beq a' && b.beq b'
  | .ternary op a b c, .ternary op' a' b' c' =>
    decide (op = op') && a.beq a' && b.beq b' && c.beq c'
  | .call i args, .call j args' => decide (i = j) && Expr.beqArgs args args'
  | _, _ => false
termination_by structural a => a

/-- Structural comparison of the argument lists of registered calls. -/
def Expr.beqArgs : List Expr → List Expr → Bool
  | [], [] => true
  | a :: as, b :: bs => a.beq b && Expr.beqArgs as bs
  | _, _ => false
termination_by structural as => as
end

/-- Boolean expression comparison is exact. -/
theorem Expr.beq_eq_true_iff (a b : Expr) : a.beq b = true ↔ a = b := by
  refine Expr.rec
    (motive_1 := fun a => ∀ b, a.beq b = true ↔ a = b)
    (motive_2 := fun as => ∀ bs, Expr.beqArgs as bs = true ↔ as = bs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b
  · intro q b
    cases b <;> simp [Expr.beq]
  · intro i b
    cases b <;> simp [Expr.beq]
  · intro op a ha b
    cases b <;> simp [Expr.beq, ha]
  · intro op a b ha hb other
    cases other <;> simp [Expr.beq, ha, hb, and_assoc]
  · intro op a b c ha hb hc other
    cases other <;> simp [Expr.beq, ha, hb, hc, and_assoc]
  · intro i args ha b
    cases b <;> simp [Expr.beq, ha]
  · intro bs
    cases bs <;> simp [Expr.beqArgs]
  · intro a as ha has bs
    cases bs <;> simp [Expr.beqArgs, ha, has]

instance : DecidableEq Expr := fun a b =>
  decidable_of_iff (a.beq b = true) (Expr.beq_eq_true_iff a b)

/-- Build an addition expression. Evaluation uses the selected backend. -/
instance : Add Expr where
  add := .binary .add

/-- Build a multiplication expression. Evaluation uses the selected backend. -/
instance : Mul Expr where
  mul := .binary .mul

/--
Executable interval operations for an endpoint representation.

The decoder identifies the exact rational value of each usable endpoint. Operations may work on the
representation itself, without decoding intermediate results. Using an evaluation in a theorem also
needs `Backend.Sound`, the proof contract.
-/
structure Backend (α : Type*) where
  /-- Exact rational interpretation of a finite endpoint. -/
  decode : α → Option ℚ
  /-- Enclose a rational constant. -/
  const? : ℚ → Option (Interval α)
  /-- Enclose a unary operation, or reject its domain or unavailable output range. -/
  unary? : UnaryOp → Interval α → Option (Interval α)
  /-- Enclose a binary operation, or reject its domain or unavailable output range. -/
  binary? : BinaryOp → Interval α → Interval α → Option (Interval α)
  /-- Enclose a three-input operation, or reject an unavailable output range. -/
  ternary? : TernaryOp → Interval α → Interval α → Interval α → Option (Interval α)
  /-- Enclose a registered operation. An unavailable index must fail. -/
  call? : Nat → List (Interval α) → Option (Interval α) := fun _ _ => none

mutual
/--
The evaluation of an expression as compiled code runs it: recursion by pattern matching. It is
`Expr.eval?` (`Expr.eval?_eq_compiled`).
-/
def Expr.Compiled.eval? {α : Type*} (e : Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Option (Interval α) :=
  match e with
  | .const q => B.const? q
  | .var i => env i
  | .unary op a => (Expr.Compiled.eval? a B env).bind (B.unary? op)
  | .binary op a b => do
    let I ← Expr.Compiled.eval? a B env
    let J ← Expr.Compiled.eval? b B env
    B.binary? op I J
  | .ternary op a b c => do
    let I ← Expr.Compiled.eval? a B env
    let J ← Expr.Compiled.eval? b B env
    let K ← Expr.Compiled.eval? c B env
    B.ternary? op I J K
  | .call index args => (Expr.Compiled.evalArgs? args B env).bind (B.call? index)
termination_by structural e

/-- The evaluation of the arguments of a registered call as compiled code runs it. -/
def Expr.Compiled.evalArgs? {α : Type*} (args : List Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Option (List (Interval α)) :=
  match args with
  | [] => some []
  | arg :: args => do
    let I ← Expr.Compiled.eval? arg B env
    let rest ← Expr.Compiled.evalArgs? args B env
    return I :: rest
termination_by structural args
end

/-- The step of `Expr.eval?` at a unary operation: a failed argument fails. -/
noncomputable def Expr.evalUnary? {α : Type*} (B : Backend α) (op : UnaryOp)
    (arg : Option (Interval α)) : Option (Interval α) :=
  Option.rec (motive := fun _ => Option (Interval α)) none (fun I => B.unary? op I) arg

/-- The step of `Expr.eval?` at a binary operation: a failed argument fails. -/
noncomputable def Expr.evalBinary? {α : Type*} (B : Backend α) (op : BinaryOp)
    (left right : Option (Interval α)) : Option (Interval α) :=
  Option.rec (motive := fun _ => Option (Interval α)) none
    (fun I => Option.rec (motive := fun _ => Option (Interval α)) none
      (fun J => B.binary? op I J) right) left

/-- The step of `Expr.eval?` at a three-input operation: a failed argument fails. -/
noncomputable def Expr.evalTernary? {α : Type*} (B : Backend α) (op : TernaryOp)
    (first second third : Option (Interval α)) : Option (Interval α) :=
  Option.rec (motive := fun _ => Option (Interval α)) none
    (fun I => Option.rec (motive := fun _ => Option (Interval α)) none
      (fun J => Option.rec (motive := fun _ => Option (Interval α)) none
        (fun K => B.ternary? op I J K) third) second) first

/-- The step of `Expr.eval?` at a registered call: failed arguments fail. -/
noncomputable def Expr.evalCall? {α : Type*} (B : Backend α) (index : Nat)
    (args : Option (List (Interval α))) : Option (Interval α) :=
  Option.rec (motive := fun _ => Option (Interval α)) none (fun inputs => B.call? index inputs)
    args

/-- The step of `Expr.evalArgs?` at one more argument: a failed argument fails the list. -/
noncomputable def Expr.evalCons? {α : Type*} (head : Option (Interval α))
    (tail : Option (List (Interval α))) : Option (List (Interval α)) :=
  Option.rec (motive := fun _ => Option (List (Interval α))) none
    (fun I => Option.rec (motive := fun _ => Option (List (Interval α))) none
      (fun rest => some (I :: rest)) tail) head

/--
Evaluate an expression with the selected backend and variable intervals.

The environment may be partial. Missing variables and failed operations propagate as `none`, and no
default numerical value is substituted.

The definition is the recursor of `Expr` applied to one step per constructor, which Lean's kernel
evaluates in a few steps per node. `Expr.eval?_const`, `Expr.eval?_var`, `Expr.eval?_unary`,
`Expr.eval?_binary`, `Expr.eval?_ternary` and `Expr.eval?_call` state the recursion by pattern
matching, and compiled code runs that recursion (`Expr.eval?_eq_compiled`).
-/
noncomputable def Expr.eval? {α : Type*} (e : Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Option (Interval α) :=
  Expr.rec (motive_1 := fun _ => Option (Interval α))
    (motive_2 := fun _ => Option (List (Interval α)))
    (fun q => B.const? q)
    (fun i => env i)
    (fun op _ arg => Expr.evalUnary? B op arg)
    (fun op _ _ left right => Expr.evalBinary? B op left right)
    (fun op _ _ _ first second third => Expr.evalTernary? B op first second third)
    (fun index _ args => Expr.evalCall? B index args)
    (some [])
    (fun _ _ head tail => Expr.evalCons? head tail)
    e

/--
Evaluate all arguments of a registered call, preserving failure and argument order
(`Expr.evalArgs?_nil`, `Expr.evalArgs?_cons`).
-/
noncomputable def Expr.evalArgs? {α : Type*} (args : List Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Option (List (Interval α)) :=
  Expr.rec_1 (motive_1 := fun _ => Option (Interval α))
    (motive_2 := fun _ => Option (List (Interval α)))
    (fun q => B.const? q)
    (fun i => env i)
    (fun op _ arg => Expr.evalUnary? B op arg)
    (fun op _ _ left right => Expr.evalBinary? B op left right)
    (fun op _ _ _ first second third => Expr.evalTernary? B op first second third)
    (fun index _ args => Expr.evalCall? B index args)
    (some [])
    (fun _ _ head tail => Expr.evalCons? head tail)
    args

section Equations

variable {α : Type*} (B : Backend α) (env : Nat → Option (Interval α))

/-- A constant evaluates to the backend's enclosure of it. -/
theorem Expr.eval?_const (q : ℚ) : (Expr.const q).eval? B env = B.const? q := rfl

/-- A variable evaluates to its interval in the environment. -/
theorem Expr.eval?_var (i : Nat) : (Expr.var i).eval? B env = env i := rfl

/-- A unary operation evaluates its argument and applies the backend's operation. -/
theorem Expr.eval?_unary (op : UnaryOp) (a : Expr) :
    (Expr.unary op a).eval? B env = (a.eval? B env).bind (B.unary? op) := by
  change Expr.evalUnary? B op (a.eval? B env) = _
  cases a.eval? B env <;> rfl

/-- A binary operation evaluates its arguments in order and applies the backend's operation. -/
theorem Expr.eval?_binary (op : BinaryOp) (a b : Expr) :
    (Expr.binary op a b).eval? B env = (do
      let I ← a.eval? B env
      let J ← b.eval? B env
      B.binary? op I J) := by
  change Expr.evalBinary? B op (a.eval? B env) (b.eval? B env) = _
  cases a.eval? B env <;> cases b.eval? B env <;> rfl

/-- A three-input operation evaluates its arguments in order and applies the backend's. -/
theorem Expr.eval?_ternary (op : TernaryOp) (a b c : Expr) :
    (Expr.ternary op a b c).eval? B env = (do
      let I ← a.eval? B env
      let J ← b.eval? B env
      let K ← c.eval? B env
      B.ternary? op I J K) := by
  change Expr.evalTernary? B op (a.eval? B env) (b.eval? B env) (c.eval? B env) = _
  cases a.eval? B env <;> cases b.eval? B env <;> cases c.eval? B env <;> rfl

/-- A registered call evaluates its arguments and applies the backend's call. -/
theorem Expr.eval?_call (index : Nat) (args : List Expr) :
    (Expr.call index args).eval? B env = (Expr.evalArgs? args B env).bind (B.call? index) := by
  change Expr.evalCall? B index (Expr.evalArgs? args B env) = _
  cases Expr.evalArgs? args B env <;> rfl

/-- No arguments evaluate to the empty list. -/
theorem Expr.evalArgs?_nil : Expr.evalArgs? [] B env = some [] := rfl

/-- Arguments evaluate in order, and a failed one fails the list. -/
theorem Expr.evalArgs?_cons (arg : Expr) (args : List Expr) :
    Expr.evalArgs? (arg :: args) B env = (do
      let I ← arg.eval? B env
      let rest ← Expr.evalArgs? args B env
      return I :: rest) := by
  change Expr.evalCons? (arg.eval? B env) (Expr.evalArgs? args B env) = _
  cases arg.eval? B env <;> cases Expr.evalArgs? args B env <;> rfl

/-- The kernel form and the compiled form of the evaluation agree on every expression. -/
theorem Expr.eval?_eq (e : Expr) : e.eval? B env = Expr.Compiled.eval? e B env := by
  refine Expr.rec
    (motive_1 := fun e => e.eval? B env = Expr.Compiled.eval? e B env)
    (motive_2 := fun args => Expr.evalArgs? args B env = Expr.Compiled.evalArgs? args B env)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro q
    rw [Expr.eval?_const, Expr.Compiled.eval?]
  · intro i
    rw [Expr.eval?_var, Expr.Compiled.eval?]
  · intro op a ha
    rw [Expr.eval?_unary, Expr.Compiled.eval?, ha]
  · intro op a b ha hb
    rw [Expr.eval?_binary, Expr.Compiled.eval?, ha, hb]
  · intro op a b c ha hb hc
    rw [Expr.eval?_ternary, Expr.Compiled.eval?, ha, hb, hc]
  · intro index args hargs
    rw [Expr.eval?_call, Expr.Compiled.eval?, hargs]
  · rw [Expr.evalArgs?_nil, Expr.Compiled.evalArgs?]
  · intro arg args ha hargs
    rw [Expr.evalArgs?_cons, Expr.Compiled.evalArgs?, ha, hargs]

end Equations

/-- Compiled code runs the recursion by pattern matching in place of `Expr.eval?`. -/
@[csimp] theorem Expr.eval?_eq_compiled : @Expr.eval? = @Expr.Compiled.eval? := by
  funext α e B env
  exact Expr.eval?_eq B env e

end FloatLib.Numerics.Interval

namespace FloatLib.Numerics.Interval.BinaryOp

/-- Reconstruct a `BinaryOp` constructor from its constructor index. -/
add_decl_doc ofNat_ctorIdx

end FloatLib.Numerics.Interval.BinaryOp

namespace FloatLib.Numerics.Interval.Expr

/-- Recursive hypotheses for the expression lists nested inside an interval expression. -/
add_decl_doc FloatLib.Numerics.Interval.Expr.below_1

end FloatLib.Numerics.Interval.Expr

namespace FloatLib.Numerics.Interval.Expr

/-- Course-of-values recursion over expression lists, with hypotheses for every nested child. -/
add_decl_doc FloatLib.Numerics.Interval.Expr.brecOn_1

end FloatLib.Numerics.Interval.Expr

namespace FloatLib.Numerics.Interval.TernaryOp

/-- Reconstruct a `TernaryOp` constructor from its constructor index. -/
add_decl_doc ofNat_ctorIdx

end FloatLib.Numerics.Interval.TernaryOp
