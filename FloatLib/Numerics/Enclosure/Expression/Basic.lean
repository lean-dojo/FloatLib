/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Interval.Basic
public import Mathlib.Data.Rat.Defs

/-!
# Interval expressions and endpoint backends

An expression records the numerical operations independently of its endpoint representation.
`Backend` supplies executable enclosures; its real-containment contract is stated in `Real`.
The same expression can therefore run with exact rational endpoints, an integer binary grid,
or a format-specific outward rounder.

Evaluation returns `none` when an input is missing or a backend cannot enclose an operation.
In particular, a backend may reject division across zero or an interval outside a function's
domain. Success is related to real evaluation by `Expr.containsReal_eval?`.
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
  | neg
  | abs
  | inv
  | pow (exponent : Nat)
  | exp
  | log
  | sin
  | cos
  | tan
  | asin
  | acos
  | atan
  | sinh
  | cosh
  | tanh
  | sqrt
  deriving DecidableEq, Repr

/-- Binary operations supported by the common interval expression language. -/
inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | min
  | max
  deriving DecidableEq, Repr

/-- Three-input operations supported by the common interval expression language. -/
inductive TernaryOp where
  | fma
  deriving DecidableEq, Repr

/-- A real expression with rational constants, numbered variables, and registered calls. -/
inductive Expr where
  | const (value : ℚ)
  | var (index : Nat)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | ternary (op : TernaryOp) (first second third : Expr)
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

/-- Build an addition expression; evaluation uses the selected backend. -/
instance : Add Expr where
  add := .binary .add

/-- Build a multiplication expression; evaluation uses the selected backend. -/
instance : Mul Expr where
  mul := .binary .mul

/--
Executable interval operations for an endpoint representation.

The decoder identifies the exact rational value of each usable endpoint. Operations may work
directly on the representation without decoding intermediate results. `Backend.Sound` is the
separate proof contract required to use an evaluation in a theorem.
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
  /-- Enclose a registered operation; unavailable indices must fail. -/
  call? : Nat → List (Interval α) → Option (Interval α) := fun _ _ => none

mutual
/--
Evaluate an expression with the selected backend and variable intervals.

The environment may be partial. Missing variables and failed operations propagate as `none`;
no default numerical value is substituted.
-/
def Expr.eval? {α : Type*} (e : Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Option (Interval α) :=
  match e with
  | .const q => B.const? q
  | .var i => env i
  | .unary op a => (a.eval? B env).bind (B.unary? op)
  | .binary op a b => do
    let I ← a.eval? B env
    let J ← b.eval? B env
    B.binary? op I J
  | .ternary op a b c => do
    let I ← a.eval? B env
    let J ← b.eval? B env
    let K ← c.eval? B env
    B.ternary? op I J K
  | .call index args => (Expr.evalArgs? args B env).bind (B.call? index)
termination_by structural e

/-- Evaluate all arguments of a registered call, preserving failure and argument order. -/
def Expr.evalArgs? {α : Type*} (args : List Expr) (B : Backend α)
    (env : Nat → Option (Interval α)) : Option (List (Interval α)) :=
  match args with
  | [] => some []
  | arg :: args => do
    let I ← arg.eval? B env
    let rest ← Expr.evalArgs? args B env
    return I :: rest
termination_by structural args
end

end FloatLib.Numerics.Interval
