/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Basic
public import FloatLib.Numerics.Enclosure.Interval.Real
public import FloatLib.Numerics.Kernel.QProof
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Sound interval evaluation of real expressions

Each backend operation must enclose its real result for every real member of the input intervals,
and structural induction then gives the same guarantee for a whole expression. Variable values
aren't restricted to rationals or to the interval's endpoint representation.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval

/-- Curried real functions, where arity zero is a real constant. -/
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

/-- A real inside an enclosure that is the point zero is zero. -/
theorem Backend.eq_zero_of_isZero {α : Type*} {B : Backend α} {I : Interval α} {x : ℝ}
    (hx : I.ContainsReal B.decode x) (h : B.isZero I = true) : x = 0 := by
  obtain ⟨a, b, ha, hb, hax, hxb⟩ := hx
  unfold Backend.isZero at h
  cases hlo : B.decode I.lo with
  | none => simp [hlo] at h
  | some lo =>
    cases hhi : B.decode I.hi with
    | none => simp [hlo, hhi] at h
    | some hi =>
      simp only [hlo, hhi, Bool.and_eq_true, Kernel.Q.le_iff] at h
      have hlo' : (lo : ℝ) = a := by simpa [hlo] using ha
      have hhi' : (hi : ℝ) = b := by simpa [hhi] using hb
      have h0 : (0 : ℝ) ≤ lo := by exact_mod_cast h.1
      have h1 : (hi : ℝ) ≤ 0 := by exact_mod_cast h.2
      exact le_antisymm (hxb.trans (hhi' ▸ h1)) ((hlo' ▸ h0).trans hax)

/-- An enclosure from `Expr.zeroOperand?` contains the value of the operation: the operand that
is the point zero is zero, and then so is the product or the quotient. -/
theorem Expr.containsReal_zeroOperand? {α : Type*} {B : Backend α} {op : BinaryOp}
    {left right : Option (Interval α)} {x y : ℝ}
    (hx : ∀ I, left = some I → I.ContainsReal B.decode x)
    (hy : ∀ J, right = some J → J.ContainsReal B.decode y) {K : Interval α}
    (h : Expr.zeroOperand? B op left right = some K) : K.ContainsReal B.decode (op.eval x y) := by
  have first : ∀ I, left = some I → B.isZero I = true → I.ContainsReal B.decode (x * y) ∧
      I.ContainsReal B.decode (x / y) := by
    intro I hI hzero
    have hx0 := Backend.eq_zero_of_isZero (hx I hI) hzero
    have hmul : x * y = x := by rw [hx0, zero_mul]
    have hdiv : x / y = x := by rw [hx0, zero_div]
    rw [hmul, hdiv]
    exact ⟨hx I hI, hx I hI⟩
  have second : ∀ J, right = some J → B.isZero J = true → J.ContainsReal B.decode (x * y) := by
    intro J hJ hzero
    have hy0 := Backend.eq_zero_of_isZero (hy J hJ) hzero
    have hmul : x * y = y := by rw [hy0, mul_zero]
    rw [hmul]
    exact hy J hJ
  cases op with
  | mul =>
    cases left with
    | none =>
      cases right with
      | none => simp [Expr.zeroOperand?] at h
      | some J =>
        simp only [Expr.zeroOperand?] at h
        split_ifs at h with hJ
        rw [← Option.some.inj h]
        exact second J rfl hJ
    | some I =>
      cases right with
      | none =>
        simp only [Expr.zeroOperand?] at h
        split_ifs at h with hI
        rw [← Option.some.inj h]
        exact (first I rfl hI).1
      | some J =>
        simp only [Expr.zeroOperand?] at h
        split_ifs at h with hI hJ
        · rw [← Option.some.inj h]
          exact (first I rfl hI).1
        · rw [← Option.some.inj h]
          exact second J rfl hJ
  | div =>
    cases left with
    | none => simp [Expr.zeroOperand?] at h
    | some I =>
      simp only [Expr.zeroOperand?] at h
      split_ifs at h with hI
      rw [← Option.some.inj h]
      exact (first I rfl hI).2
  | add => simp [Expr.zeroOperand?] at h
  | sub => simp [Expr.zeroOperand?] at h
  | min => simp [Expr.zeroOperand?] at h
  | max => simp [Expr.zeroOperand?] at h

/--
A successful evaluation with the zero rule encloses the exact real value throughout the input
box: where a factor is exactly zero, the product is zero whatever the other factor is.

Only variables actually supplied by the interval environment need a membership proof. A missing
variable prevents successful evaluation, so it cannot create an unproved assumption.
-/
theorem Expr.containsReal_evalZero? {α : Type*} (e : Expr) {B : Backend α}
    {functions : Nat → List ℝ → ℝ} (hB : B.Sound functions)
    {env : Nat → Option (Interval α)} {values : Nat → ℝ}
    (henv : ∀ i I, env i = some I → I.ContainsReal B.decode (values i))
    {I : Interval α} (h : e.evalZero? B env = some I) :
    I.ContainsReal B.decode (e.eval values functions) := by
  revert I
  refine Expr.rec
    (motive_1 := fun e => ∀ {I}, e.evalZero? B env = some I →
      I.ContainsReal B.decode (e.eval values functions))
    (motive_2 := fun args => ∀ {inputs},
      Expr.evalZeroArgs? args B env = some inputs →
      List.Forall₂ (fun I x => I.ContainsReal B.decode x) inputs
        (Expr.evalArgs args values functions))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro q I h
    simpa only [eval] using hB.const (by simpa only [Expr.evalZero?_const] using h)
  · intro i I h
    simpa only [eval] using henv i I (by simpa only [Expr.evalZero?_var] using h)
  · intro op a ha I h
    cases harg : a.evalZero? B env with
    | none => simp [Expr.evalZero?_unary, harg] at h
    | some J =>
      simpa only [eval] using hB.unary (by simpa [Expr.evalZero?_unary, harg] using h) (ha harg)
  · intro op a b ha hb I h
    rw [Expr.evalZero?_binary] at h
    simp only [eval]
    have zero : Expr.zeroOperand? B op (a.evalZero? B env) (b.evalZero? B env) = some I →
        I.ContainsReal B.decode (op.eval (a.eval values functions) (b.eval values functions)) :=
      Expr.containsReal_zeroOperand? (fun _ hJ => ha hJ) (fun _ hJ => hb hJ)
    cases hleft : a.evalZero? B env with
    | none =>
      rw [hleft] at h zero
      exact zero h
    | some J =>
      cases hright : b.evalZero? B env with
      | none =>
        rw [hleft, hright] at h zero
        exact zero h
      | some K =>
        rw [hleft, hright] at h zero
        cases hop : B.binary? op J K with
        | none => exact zero (by simpa only [Expr.zeroBinary?, hop] using h)
        | some L =>
          have hL : L = I := by simpa only [Expr.zeroBinary?, hop, Option.some.injEq] using h
          exact hL ▸ hB.binary hop (ha hleft) (hb hright)
  · intro op a b c ha hb hc I h
    cases hfirst : a.evalZero? B env with
    | none => simp [Expr.evalZero?_ternary, hfirst] at h
    | some J =>
      cases hsecond : b.evalZero? B env with
      | none => simp [Expr.evalZero?_ternary, hfirst, hsecond] at h
      | some K =>
        cases hthird : c.evalZero? B env with
        | none => simp [Expr.evalZero?_ternary, hfirst, hsecond, hthird] at h
        | some L =>
          simpa only [eval] using
            hB.ternary (by simpa [Expr.evalZero?_ternary, hfirst, hsecond, hthird] using h)
            (ha hfirst) (hb hsecond) (hc hthird)
  · intro index args ha I h
    simp only [Expr.evalZero?_call, Option.bind_eq_some_iff] at h
    obtain ⟨inputs, hinputs, hcall⟩ := h
    simpa only [eval] using hB.call hcall (ha hinputs)
  · intro inputs h
    simp only [Expr.evalZeroArgs?_nil, Option.some.injEq] at h
    subst inputs
    exact .nil
  · intro arg args ha hat inputs h
    simp only [Expr.evalZeroArgs?_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨head, hhead, tail, htail, rfl⟩ := h
    exact .cons (ha hhead) (hat htail)

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
    I.ContainsReal B.decode (e.eval values functions) :=
  e.containsReal_evalZero? hB henv (e.evalZero?_of_eval? B env h)

end FloatLib.Numerics.Interval
