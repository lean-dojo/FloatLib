/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic
public import FloatLib.Numerics.Enclosure.Interval.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Sound interval evaluation of real expressions

Each backend operation must enclose its real result for every real member of the input intervals.
Structural induction then gives the same guarantee for a complete expression. The theorem does
not restrict variable values to rationals or to the interval's endpoint representation.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Curried real functions; arity zero is a real constant. -/
def RealFunction : Nat → Type
  | 0 => ℝ
  | n + 1 => ℝ → RealFunction n

/-- Apply a curried real function to its argument list.
Successful extension evaluation checks the arity before this interpretation is used. -/
noncomputable def RealFunction.apply {n : Nat} (f : RealFunction n) (args : List ℝ) : ℝ :=
  match n with
  | 0 => f
  | n + 1 => RealFunction.apply (n := n) (f (args.headD 0)) args.tail

/-- A successful user enclosure contains the result for every real input member.
The argument count is checked by the common evaluator, independently of the user's procedure. -/
def Extension.Sound (E : Extension) (f : RealFunction E.arity) : Prop :=
  ∀ (config : Backend.Config) (inputs : List (Interval ℚ)) (output : Interval ℚ)
    (values : List ℝ), E.enclose? config inputs = some output → inputs.length = E.arity →
    List.Forall₂ (fun I x => I.ContainsReal some x) inputs values →
    output.ContainsReal some (RealFunction.apply f values)

/-- A certified constant enclosure satisfies the common extension contract. -/
theorem Extension.constant_sound (bounds : Backend.Config → Option (Interval ℚ)) (c : ℝ)
    (h : ∀ config output, bounds config = some output → output.ContainsReal some c) :
    (Extension.constant bounds).Sound c := by
  intro config inputs output values hout _ hx
  cases hx with
  | nil => exact h config output hout
  | cons => simp [Extension.constant] at hout

/-- Rational lower and upper bounds for a real constant, indexed by requested precision. -/
structure ConstantBounds (c : ℝ) where
  /-- Compute the lower and upper endpoints. -/
  bounds : Nat → Interval ℚ
  /-- The constant lies between those endpoints at every precision. -/
  valid : ∀ precision, ((bounds precision).lo : ℝ) ≤ c ∧ c ≤ ((bounds precision).hi : ℝ)

/-- Adapt proved constant bounds to the general enclosure evaluator. -/
def ConstantBounds.toExtension {c : ℝ} (certificate : ConstantBounds c) : Extension :=
  Extension.constant (fun config => some (certificate.bounds config.precision))

/-- Ordinary endpoint inequalities suffice to certify a constant enclosure. -/
theorem ConstantBounds.toExtension_sound {c : ℝ} (certificate : ConstantBounds c) :
    certificate.toExtension.Sound c := by
  apply Extension.constant_sound
  intro config output h
  cases Option.some.inj h
  exact (containsReal_some_iff _ _).mpr (certificate.valid config.precision)

/-- Lift an existing unary containment theorem to a registered enclosure. -/
theorem Extension.unary_sound
    (bounds : Backend.Config → Interval ℚ → Option (Interval ℚ)) (f : ℝ → ℝ)
    (h : ∀ config I J x, bounds config I = some J → I.ContainsReal some x →
      J.ContainsReal some (f x)) : (Extension.unary bounds).Sound f := by
  intro config inputs output values hout _ hx
  cases hx with
  | nil => simp [Extension.unary] at hout
  | @cons I x inputs values hi ht =>
    cases ht with
    | nil => exact h config I output x hout hi
    | cons => simp [Extension.unary] at hout

/-- Lift an existing binary containment theorem to a registered enclosure. -/
theorem Extension.binary_sound
    (bounds : Backend.Config → Interval ℚ → Interval ℚ → Option (Interval ℚ)) (f : ℝ → ℝ → ℝ)
    (h : ∀ config I J K x y, bounds config I J = some K → I.ContainsReal some x →
      J.ContainsReal some y → K.ContainsReal some (f x y)) :
    (Extension.binary bounds).Sound f := by
  intro config inputs output values hout _ hx
  cases hx with
  | nil => simp [Extension.binary] at hout
  | @cons I x inputs values hi ht =>
    cases ht with
    | nil => simp [Extension.binary] at hout
    | @cons J y inputs values hj ht =>
      cases ht with
      | nil => exact h config I J output x y hout hi hj
      | cons => simp [Extension.binary] at hout

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

mutual
/-- Evaluate an expression at arbitrary real variable values. -/
noncomputable def Expr.eval (e : Expr) (env : Nat → ℝ)
    (functions : Nat → List ℝ → ℝ := fun _ _ => 0) : ℝ :=
  match e with
  | .const q => q
  | .var i => env i
  | .unary op a => op.eval (a.eval env functions)
  | .binary op a b => op.eval (a.eval env functions) (b.eval env functions)
  | .ternary op a b c =>
    op.eval (a.eval env functions) (b.eval env functions) (c.eval env functions)
  | .call index args => functions index (Expr.evalArgs args env functions)
termination_by structural e

/-- Real interpretation of the ordered arguments of a registered call. -/
noncomputable def Expr.evalArgs (args : List Expr) (env : Nat → ℝ)
    (functions : Nat → List ℝ → ℝ) : List ℝ :=
  match args with
  | [] => []
  | arg :: args => arg.eval env functions :: Expr.evalArgs args env functions
termination_by structural args
end

/-- Containment contracts for all successful operations of an interval backend. -/
structure Backend.Sound {α : Type*} (B : Backend α)
    (functions : Nat → List ℝ → ℝ := fun _ _ => 0) : Prop where
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
  /-- Registered operations enclose all real tuples in their input intervals. -/
  call : ∀ {index inputs output values}, B.call? index inputs = some output →
    List.Forall₂ (fun I x => I.ContainsReal B.decode x) inputs values →
    output.ContainsReal B.decode (functions index values)

/--
A successful expression evaluation encloses the exact real value throughout the input box.

Only variables actually supplied by the interval environment need a membership proof. A missing
variable prevents successful evaluation, so it cannot create an unproved assumption.
-/
theorem Expr.containsReal_eval? {α : Type*} (e : Expr) {B : Backend α}
    {functions : Nat → List ℝ → ℝ} (hB : B.Sound functions)
    {env : Nat → Option (Interval α)} {values : Nat → ℝ}
    (henv : ∀ i I, env i = some I → I.ContainsReal B.decode (values i))
    {I : Interval α} (h : e.eval? B env = some I) :
    I.ContainsReal B.decode (e.eval values functions) := by
  revert I
  refine Expr.rec
    (motive_1 := fun e => ∀ {I}, e.eval? B env = some I →
      I.ContainsReal B.decode (e.eval values functions))
    (motive_2 := fun args => ∀ {inputs},
      Expr.evalArgs? args B env = some inputs →
      List.Forall₂ (fun I x => I.ContainsReal B.decode x) inputs
        (Expr.evalArgs args values functions))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro q I h
    simpa only [eval] using hB.const (by simpa only [eval?] using h)
  · intro i I h
    simpa only [eval] using henv i I (by simpa only [eval?] using h)
  · intro op a ha I h
    cases harg : a.eval? B env with
    | none => simp [eval?, harg] at h
    | some J => simpa only [eval] using hB.unary (by simpa [eval?, harg] using h) (ha harg)
  · intro op a b ha hb I h
    cases hleft : a.eval? B env with
    | none => simp [eval?, hleft] at h
    | some J =>
      cases hright : b.eval? B env with
      | none => simp [eval?, hleft, hright] at h
      | some K =>
        simpa only [eval] using
          hB.binary (by simpa [eval?, hleft, hright] using h) (ha hleft) (hb hright)
  · intro op a b c ha hb hc I h
    cases hfirst : a.eval? B env with
    | none => simp [eval?, hfirst] at h
    | some J =>
      cases hsecond : b.eval? B env with
      | none => simp [eval?, hfirst, hsecond] at h
      | some K =>
        cases hthird : c.eval? B env with
        | none => simp [eval?, hfirst, hsecond, hthird] at h
        | some L =>
          simpa only [eval] using
            hB.ternary (by simpa [eval?, hfirst, hsecond, hthird] using h)
            (ha hfirst) (hb hsecond) (hc hthird)
  · intro index args ha I h
    simp only [eval?, Option.bind_eq_some_iff] at h
    obtain ⟨inputs, hinputs, hcall⟩ := h
    simpa only [eval] using hB.call hcall (ha hinputs)
  · intro inputs h
    simp only [Expr.evalArgs?, Option.some.injEq] at h
    subst inputs
    exact .nil
  · intro arg args ha hat inputs h
    simp only [Expr.evalArgs?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    exact .cons (ha hhead) (hat htail)

end FloatLib.Numerics.Interval
