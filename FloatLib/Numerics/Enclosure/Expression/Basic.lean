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

/-- A real expression with rational constants and numbered variables. -/
inductive Expr where
  | const (value : ℚ)
  | var (index : Nat)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | ternary (op : TernaryOp) (first second third : Expr)
  deriving DecidableEq, Repr

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

end FloatLib.Numerics.Interval
