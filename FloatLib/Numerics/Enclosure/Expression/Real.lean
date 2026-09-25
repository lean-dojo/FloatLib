/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic
public import FloatLib.Numerics.Enclosure.Interval.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Sound interval evaluation of real expressions

Each backend operation must enclose its real result for every real member of the input intervals.
Structural induction then gives the same guarantee for a complete expression. The theorem does
not restrict variable values to rationals or to the interval's endpoint representation.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Real interpretation of a unary expression operation. -/
noncomputable def UnaryOp.eval : UnaryOp → ℝ → ℝ
  | .neg => Neg.neg
  | .abs => _root_.abs
  | .inv => Inv.inv
  | .pow n => (· ^ n)
  | .exp => Real.exp
  | .log => Real.log
  | .sin => Real.sin
  | .cos => Real.cos
  | .tan => Real.tan
  | .asin => Real.arcsin
  | .acos => Real.arccos
  | .atan => Real.arctan
  | .sinh => Real.sinh
  | .cosh => Real.cosh
  | .tanh => Real.tanh
  | .sqrt => Real.sqrt

/-- Real interpretation of a binary expression operation. -/
noncomputable def BinaryOp.eval : BinaryOp → ℝ → ℝ → ℝ
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .div => (· / ·)
  | .min => Min.min
  | .max => Max.max

/-- Real interpretation of a three-input expression operation. -/
noncomputable def TernaryOp.eval : TernaryOp → ℝ → ℝ → ℝ → ℝ
  | .fma => fun x y z => x * y + z

/-- Evaluate an expression at arbitrary real variable values. -/
noncomputable def Expr.eval (e : Expr) (env : Nat → ℝ) : ℝ :=
  match e with
  | .const q => q
  | .var i => env i
  | .unary op a => op.eval (a.eval env)
  | .binary op a b => op.eval (a.eval env) (b.eval env)
  | .ternary op a b c => op.eval (a.eval env) (b.eval env) (c.eval env)

/-- Containment contracts for all successful operations of an interval backend. -/
structure Backend.Sound {α : Type*} (B : Backend α) : Prop where
  /-- The constant enclosure contains its exact rational value. -/
  const : ∀ {q I}, B.const? q = some I → I.ContainsReal B.decode q
  /-- Unary operations enclose the result at every real input member. -/
  unary : ∀ {op I J x}, B.unary? op I = some J →
    I.ContainsReal B.decode x → J.ContainsReal B.decode (op.eval x)
  /-- Binary operations enclose the result at every pair of real input members. -/
  binary : ∀ {op I J K x y}, B.binary? op I J = some K →
    I.ContainsReal B.decode x → J.ContainsReal B.decode y →
      K.ContainsReal B.decode (op.eval x y)
  /-- Three-input operations enclose the result at every combination of real input members. -/
  ternary : ∀ {op I J K L x y z}, B.ternary? op I J K = some L →
    I.ContainsReal B.decode x → J.ContainsReal B.decode y →
      K.ContainsReal B.decode z → L.ContainsReal B.decode (op.eval x y z)

/--
A successful expression evaluation encloses the exact real value throughout the input box.

Only variables actually supplied by the interval environment need a membership proof. A missing
variable prevents successful evaluation, so it cannot create an unproved assumption.
-/
theorem Expr.containsReal_eval? {α : Type*} (e : Expr) {B : Backend α}
    (hB : B.Sound) {env : Nat → Option (Interval α)} {values : Nat → ℝ}
    (henv : ∀ i I, env i = some I → I.ContainsReal B.decode (values i))
    {I : Interval α} (h : e.eval? B env = some I) :
    I.ContainsReal B.decode (e.eval values) := by
  induction e generalizing I with
  | const q => exact hB.const h
  | var i => exact henv i I h
  | unary op a ha =>
    cases harg : a.eval? B env with
    | none => simp [eval?, harg] at h
    | some J =>
      exact hB.unary (by simpa [eval?, harg] using h) (ha harg)
  | binary op a b ha hb =>
    cases hleft : a.eval? B env with
    | none => simp [eval?, hleft] at h
    | some J =>
      cases hright : b.eval? B env with
      | none => simp [eval?, hleft, hright] at h
      | some K =>
        exact hB.binary (by simpa [eval?, hleft, hright] using h) (ha hleft) (hb hright)
  | ternary op a b c ha hb hc =>
    cases hfirst : a.eval? B env with
    | none => simp [eval?, hfirst] at h
    | some J =>
      cases hsecond : b.eval? B env with
      | none => simp [eval?, hfirst, hsecond] at h
      | some K =>
        cases hthird : c.eval? B env with
        | none => simp [eval?, hfirst, hsecond, hthird] at h
        | some L =>
          exact hB.ternary (by simpa [eval?, hfirst, hsecond, hthird] using h)
            (ha hfirst) (hb hsecond) (hc hthird)

end FloatLib.Numerics.Interval
