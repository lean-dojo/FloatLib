/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Hyperbolic.Runtime
public import FloatLib.Numerics.Enclosure.Trigonometric.Reduction.Runtime
public import FloatLib.Numerics.Enclosure.Expression.Basic

/-!
# The factors of the complex exponential and hyperbolic functions

Each part of `exp (a + i b)`, `sinh (a + i b)` and `cosh (a + i b)` is a product of an unbounded
factor (`exp a`, `sinh a` or `cosh a`) and a bounded one (`cos b` or `sin b`). `Growth` and `Trig`
name the two families, with the exact comparator of the first and the convergent enclosures of
the second.

`Admissible` is the condition under which the product is not rational, which is when the
comparison of `ProductComparison` terminates: the unbounded factor is positive, the bounded one
is not zero, and the argument is not zero.
-/

@[expose] public section

namespace FloatLib.Numerics.ProductComparison

/-- The unbounded factor of a part: `exp a`, `sinh a` or `cosh a`. -/
inductive Growth where
  /-- The exponential `exp a`. -/
  | exp
  /-- The hyperbolic sine `sinh a`. -/
  | sinh
  /-- The hyperbolic cosine `cosh a`. -/
  | cosh
  deriving DecidableEq, Repr

/-- Reconstruct a `Growth` constructor from its constructor index. -/
add_decl_doc Growth.ofNat_ctorIdx

/-- The bounded factor of a part: `cos b` or `sin b`. -/
inductive Trig where
  /-- The cosine `cos b`. -/
  | cos
  /-- The sine `sin b`. -/
  | sin
  deriving DecidableEq, Repr

/-- Reconstruct a `Trig` constructor from its constructor index. -/
add_decl_doc Trig.ofNat_ctorIdx

/-- The exact comparison of the unbounded factor at `a` with a rational boundary. -/
def Growth.compare : Growth → ℚ → ℚ → Ordering
  | .exp => ElementaryComparison.compareExp
  | .sinh => HyperbolicComparison.compareSinh
  | .cosh => HyperbolicComparison.compareCosh

/--
Enclosures of the bounded factor at `b`, by argument reduction, at the degrees `2 ^ n`. They
converge (`Trig.converges_reduced`), and `Trig.intervals` puts faster ones before them.
-/
def Trig.reduced : Trig → ℚ → Nat → RationalInterval
  | .cos, b, n => Enclosure.cosReduced b (2 ^ n)
  | .sin, b, n => Enclosure.sinReduced b (2 ^ n)

/-- The bounded factor as an operation of interval expressions. -/
def Trig.op : Trig → Interval.UnaryOp
  | .cos => .cos
  | .sin => .sin

/--
The product of the two factors at `a` and `b` is irrational: the hyperbolic sine is taken at a
positive `a`, the sine at a nonzero `b`, and `a` and `b` are not both zero.
-/
def Admissible (growth : Growth) (trig : Trig) (a b : ℚ) : Prop :=
  (growth = .sinh → 0 < a) ∧ (trig = .sin → b ≠ 0) ∧ ¬(a = 0 ∧ b = 0)

instance (growth : Growth) (trig : Trig) (a b : ℚ) : Decidable (Admissible growth trig a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end FloatLib.Numerics.ProductComparison
