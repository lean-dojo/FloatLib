/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Monotone
public meta import FloatLib.Tactic.Interval.Constraints.Witness

/-!
# A comparison whose two sides meet at an end of the range

An enclosure does not separate `1 + x` from `Real.exp x` on a box that contains `0`, however
small the box is, because the two are equal there. The difference of the two sides still has a
sign when it has one at the end of the range and its derivative has one beyond:
`Real.exp x - (1 + x)` vanishes at `0` and its derivative `Real.exp x - 1` is nonnegative for
`0 < x`. `byDerivative` proves a comparison in one real variable `x` this way, when the
hypotheses bound `x` on one side or on both by terms without variables and one comparison
between two sides in `x` is to be refuted. For the difference `f` of the two sides and an end
`a` of the range, the step proves

* the derivative of `f` at every `t` of the range, by the rules of the elementary functions
  (`derivativeProof`), with the denominators and the arguments of logarithms and square roots
  shown to be nonzero there;
* the sign of `f a`, by `norm_num` or by the route itself;
* the sign of the derivative strictly inside the range, by the route itself, which may pass to
  the next derivative in the same way.

The theorems are `le_of_deriv_nonneg` and `lt_of_deriv_pos` from a lower end, and
`le_of_deriv_nonpos` and `lt_of_deriv_neg` from an upper end. Before the route is asked for the
sign of the derivative, the derivative is evaluated at four points of the range; where its sign
is wrong from some point on, the range is cut before that point, the part at the end is proved
by the derivative, and the rest is left to the route (`fromEnd`).

A comparison whose larger side is an absolute value `|a|` is taken as the two comparisons with
`a` and with `-a`. The step looks at one variable and at the ends of its range: a comparison
with two variables, or one whose two sides meet inside the range, is not proved here.

## Main definitions

* `chainRules`: the rules for the derivatives of the elementary functions.
* `derivativeProof`: the derivative of a term in one variable, with its proof.
* `onRange`, `fromEnd`: the step on a range, and from one end with a cut of the range.
* `byDerivative`: the step.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- The chain rules of the elementary functions: the function, its rule, and what the rule asks
of the argument `a` of the function: nothing (`none`), `a ≠ 0` (`some none`), or that a
function of `a` does not vanish (`some (some g)` for `g a ≠ 0`). -/
def chainRules : List (Name × Name × Option (Option Name)) :=
  [ (``Real.exp, ``HasDerivAt.exp, none), (``Real.sin, ``HasDerivAt.sin, none)
  , (``Real.cos, ``HasDerivAt.cos, none), (``Real.sinh, ``HasDerivAt.sinh, none)
  , (``Real.cosh, ``HasDerivAt.cosh, none), (``Real.arctan, ``HasDerivAt.arctan, none)
  , (``Real.tanh, ``hasDerivAt_tanh_comp, none)
  , (``Real.log, ``HasDerivAt.log, some none), (``Real.sqrt, ``HasDerivAt.sqrt, some none)
  , (``Real.tan, ``hasDerivAt_tan_comp, some (some ``Real.cos)) ]

/--
A proof of `HasDerivAt g d t` for the function `g` that a real term `e` is of the variable `t`,
with some derivative `d`: by the rules for sums, differences, products, quotients, inverses,
negatives and powers with a natural exponent, and by `chainRules`. `nonzero` proves that a term
is not zero at `t`, for the denominators and the arguments that the rules ask it of. The result
is `none` when `e` has another operation of `t`, or when `nonzero` fails.
-/
partial def derivativeProof (t : Lean.Expr) (nonzero : Lean.Expr → TacticM (Option Lean.Expr))
    (e : Lean.Expr) : TacticM (Option Lean.Expr) := do
  let e := e.consumeMData
  unless e.containsFVar t.fvarId! do return some (← mkAppM ``hasDerivAt_const #[t, e])
  if e == t then return some (← mkAppM ``hasDerivAt_id' #[t])
  let unary (rule : Name) (a : Lean.Expr) (condition : Option Lean.Expr) :
      TacticM (Option Lean.Expr) := do
    let some ha ← derivativeProof t nonzero a | return none
    match condition with
    | none => return some (← mkAppM rule #[ha])
    | some c =>
      let some hc ← nonzero c | return none
      return some (← mkAppM rule #[ha, hc])
  let binary (rule : Name) (a b : Lean.Expr) : TacticM (Option Lean.Expr) := do
    let some ha ← derivativeProof t nonzero a | return none
    let some hb ← derivativeProof t nonzero b | return none
    return some (← mkAppM rule #[ha, hb])
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => binary ``HasDerivAt.add a b
  | HSub.hSub _ _ _ _ a b => binary ``HasDerivAt.sub a b
  | HMul.hMul _ _ _ _ a b => binary ``HasDerivAt.mul a b
  | Neg.neg _ _ a => unary ``HasDerivAt.neg a none
  | Inv.inv _ _ a => unary ``HasDerivAt.inv a (some a)
  | HDiv.hDiv _ _ _ _ a b =>
    let some ha ← derivativeProof t nonzero a | return none
    unless b.containsFVar t.fvarId! do return some (← mkAppM ``HasDerivAt.div_const #[ha, b])
    let some hb ← derivativeProof t nonzero b | return none
    let some hc ← nonzero b | return none
    return some (← mkAppM ``HasDerivAt.div #[ha, hb, hc])
  | HPow.hPow _ exponent _ _ a n =>
    unless exponent.isConstOf ``Nat && !n.containsFVar t.fvarId! do return none
    let some ha ← derivativeProof t nonzero a | return none
    return some (← mkAppM ``HasDerivAt.pow #[ha, n])
  | _ =>
    let .const function _ := e.getAppFn | return none
    unless e.getAppNumArgs == 1 do return none
    let some (_, rule, condition) := chainRules.find? (·.1 == function) | return none
    let a := e.appArg!
    unary rule a <| condition.map fun inner => match inner with
      | none => a
      | some g => mkApp (mkConst g) a

/-- The rules that bring a derivative from the form of the derivative rules to a term of the
variable: the operations of functions at a point, and the zeros and ones of constant parts. -/
def derivativeCleanup : MetaM SimpTheorems :=
  [``Pi.add_apply, ``Pi.sub_apply, ``Pi.mul_apply, ``Pi.neg_apply, ``Pi.pow_apply,
    ``Pi.div_apply, ``Pi.inv_apply, ``Function.comp_apply, ``mul_one, ``one_mul, ``mul_zero,
    ``zero_mul, ``add_zero, ``zero_add, ``sub_zero, ``zero_sub, ``neg_zero, ``zero_div,
    ``pow_one, ``Nat.cast_ofNat, ``Nat.cast_one].foldlM
    (fun rules name => rules.addConst name) ({} : SimpTheorems)

/-- The two sides of a comparison of real numbers and whether it is strict: `(a, b, strict)`
for `a ≤ b` and `a < b`, also written with `≥` and `>`. -/
def realComparison? (type : Lean.Expr) : MetaM (Option (Q(ℝ) × Q(ℝ) × Bool)) := do
  let type ← whnfR type
  match_expr type with
  | LE.le α _ a b => return if α.isConstOf ``Real then some (a, b, false) else none
  | LT.lt α _ a b => return if α.isConstOf ``Real then some (a, b, true) else none
  | GE.ge α _ a b => return if α.isConstOf ``Real then some (b, a, false) else none
  | GT.gt α _ a b => return if α.isConstOf ``Real then some (b, a, true) else none
  | _ => return none

/-- A proof of a closed proposition by `norm_num`, if it finds one. -/
def normNumProof? (statement : Q(Prop)) : TacticM (Option Lean.Expr) := do
  let goal ← mkFreshExprMVar statement
  let saved ← saveState
  try
    let remaining ← Lean.Elab.Tactic.run goal.mvarId! (evalTactic (← `(tactic| norm_num)))
    if remaining.isEmpty then return some (← instantiateMVars goal)
    saved.restore
    return none
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    saved.restore
    return none

/-- The derivative in a proof of `HasDerivAt g d t` by the rules, brought to a term of the
variable (`derivativeCleanup`), with the proof for that term. -/
def cleanDerivative (rule : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let arguments := (← instantiateMVars (← inferType rule)).getAppArgs
  let some raw := arguments[arguments.size - 2]?
    | throwError "interval: a derivative rule states no derivative"
  let context ← Simp.mkContext (simpTheorems := #[← derivativeCleanup])
    (congrTheorems := ← getSimpCongrTheorems)
  let (cleaned, _) ← Lean.Meta.simp raw context (simprocs := #[← Simp.getSimprocs])
  return (cleaned.expr, ← mkAppM ``HasDerivAt.congr_deriv #[rule, ← cleaned.getProof])

/-- The comparison that the step refutes: `p < q`, or `p ≤ q`, in the variable `x`. -/
structure Comparison where
  /-- The hypothesis. -/
  proof : Lean.Expr
  /-- The smaller side. -/
  p : Q(ℝ)
  /-- The larger side. -/
  q : Q(ℝ)
  /-- Whether the comparison is strict. -/
  strict : Bool
  /-- The variable. -/
  x : Q(ℝ)

/-- The end of the range of the variable from which the step starts. -/
structure Anchor where
  /-- Whether it is the lower end. -/
  lower : Bool
  /-- The end. -/
  point : Q(ℝ)
  /-- The hypothesis that the variable is beyond the end. -/
  proof : Lean.Expr
  /-- Whether the variable is strictly beyond it. -/
  strict : Bool

/-- `s` is beyond the end: `a ≤ s` for a lower end `a` and `s ≤ a` for an upper end. -/
def Anchor.beyond (anchor : Anchor) (strict : Bool) (s : Q(ℝ)) : Q(Prop) :=
  have a : Q(ℝ) := anchor.point
  match anchor.lower, strict with
  | true, false => q($a ≤ $s)
  | true, true => q($a < $s)
  | false, false => q($s ≤ $a)
  | false, true => q($s < $a)

/-- `s` is before `w`, as seen from the end: `s ≤ w` from a lower end and `w ≤ s` from an upper
end. -/
def Anchor.before (anchor : Anchor) (strict : Bool) (s w : Q(ℝ)) : Q(Prop) :=
  match anchor.lower, strict with
  | true, false => q($s ≤ $w)
  | true, true => q($s < $w)
  | false, false => q($w ≤ $s)
  | false, true => q($w < $s)

/-- From `s` before `x` and `x` before `w`, that `s` is before `w`: strictly when one of the two
is strict. -/
def Anchor.chain (anchor : Anchor) (strict₁ : Bool) (h₁ : Lean.Expr) (strict₂ : Bool)
    (h₂ : Lean.Expr) : MetaM Lean.Expr :=
  let (first, second, strictFirst, strictSecond) :=
    if anchor.lower then (h₁, h₂, strict₁, strict₂) else (h₂, h₁, strict₂, strict₁)
  mkAppM (match strictFirst, strictSecond with
    | false, false => ``le_trans
    | true, false => ``lt_of_lt_of_le
    | false, true => ``lt_of_le_of_lt
    | true, true => ``lt_trans) #[first, second]

/--
Close a goal `False` by the sign of the derivative on the whole range between the end and `far`,
the bound of the variable on the other side if there is one: `far` is the proof that the
variable is before it, the bound, and whether it is strict, and then the range is open there.
`value` proves `0 ≤ f a` at the end `a` for the difference `f` of the two sides, or `0 < f a`
when `positive` says so, and `probe` is a point of the range. The rest is proved here: the
derivative of `f` at every `t` of the range, where a term that must not vanish is given to
`prove` with the sign that it has at `probe`, and the sign of the derivative strictly inside.
The result says whether the goal was closed.
-/
def onRange (prove : MVarId → TacticM Bool) (precision degree : Nat) (goal : MVarId)
    (c : Comparison) (anchor : Anchor) (far : Option (Lean.Expr × Q(ℝ) × Bool))
    (probe : Q(ℝ)) (value : Lean.Expr) (positive : Bool) : TacticM Bool := goal.withContext do
  have p : Q(ℝ) := c.p
  have q : Q(ℝ) := c.q
  have x : Q(ℝ) := c.x
  have a : Q(ℝ) := anchor.point
  have difference : Q(ℝ) := q($p - $q)
  have atEnd : Q(ℝ) := difference.replaceFVar x a
  -- where the value is only nonnegative, a comparison that is not strict needs a derivative
  -- that is positive, and a variable strictly beyond the end
  let increasing := !positive && !c.strict
  if increasing && !anchor.strict then return false
  -- the derivative on the range, and the statement of its sign: both are closed terms
  let closed? ← withLCtx {} #[] <| withLocalDeclD `t q(ℝ) fun (t : Q(ℝ)) =>
    withLocalDeclD `near (anchor.beyond false t) fun near => do
    let withFar (k : Array Lean.Expr → TacticM (Option (Lean.Expr × Lean.Expr × Lean.Expr))) :
        TacticM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) :=
      match far with
      | some (_, w, strict) =>
        withLocalDeclD `far (anchor.before strict t w) fun h => k #[t, near, h]
      | none => k #[t, near]
    withFar fun binders => do
      let nonzero (term : Lean.Expr) : TacticM (Option Lean.Expr) := do
        have term : Q(ℝ) := term
        if let some proof ← positivityProof? q($term ≠ 0) then return some proof
        -- the route is asked for a sign that one evaluation at the point does not exclude
        have atProbe : Q(ℝ) := term.replaceFVar t probe
        unless (← holdsByEvaluation q(0 < $atProbe) precision degree) == some false do
          let above ← mkFreshExprMVar q(0 < $term)
          if ← prove above.mvarId! then
            return some (← mkAppM ``LT.lt.ne' #[← instantiateMVars above])
        unless (← holdsByEvaluation q($atProbe < 0) precision degree) == some false do
          let below ← mkFreshExprMVar q($term < 0)
          if ← prove below.mvarId! then
            return some (← mkAppM ``LT.lt.ne #[← instantiateMVars below])
        return none
      let some rule ← derivativeProof t nonzero (difference.replaceFVar x t) | return none
      let (derivative, rule) ← cleanDerivative rule
      have derivative : Q(ℝ) := derivative
      let sign : Q(Prop) := match anchor.lower, increasing with
        | true, false => q(0 ≤ $derivative)
        | true, true => q(0 < $derivative)
        | false, false => q($derivative ≤ 0)
        | false, true => q($derivative < 0)
      let inside ← match far with
        | some (_, w, _) => mkArrow (anchor.before true t w) sign
        | none => pure sign
      let statement ← mkForallFVars #[t] (← mkArrow (anchor.beyond true t) inside)
      return some (← mkLambdaFVars binders rule, ← mkLambdaFVars #[t] derivative, statement)
  let some (rules, f', statement) := closed? | return false
  let signGoal ← withLCtx {} #[] <| mkFreshExprMVar statement
  unless ← prove signGoal.mvarId! do return false
  let signs ← instantiateMVars signGoal
  -- the two families of hypotheses of the theorem: on the closed range between the end and
  -- `x`, and strictly inside
  let family (strict : Bool) (proofs : Lean.Expr) : TacticM Lean.Expr :=
    withLocalDeclD `t q(ℝ) fun (t : Q(ℝ)) =>
    withLocalDeclD `near (anchor.beyond strict t) fun near =>
    withLocalDeclD `within (anchor.before strict t x) fun within => do
      let body ← match far with
        | some (farProof, _, farStrict) =>
          pure (mkAppN proofs #[t, near, ← anchor.chain strict within farStrict farProof])
        | none => pure (mkAppN proofs #[t, near])
      mkLambdaFVars #[t, near, within] body
  let derivatives ← family false rules
  let interior ← family true signs
  have f : Q(ℝ → ℝ) := ← mkLambdaFVars #[x] difference
  let theorems := if anchor.lower then (``le_of_deriv_nonneg, ``lt_of_deriv_pos)
    else (``le_of_deriv_nonpos, ``lt_of_deriv_neg)
  let beyond ← if anchor.strict && !increasing then mkAppM ``le_of_lt #[anchor.proof]
    else pure anchor.proof
  let grows ← mkAppOptM (if increasing then theorems.2 else theorems.1)
    #[some f, some f', some a, some x, some beyond, some derivatives, some interior]
  -- the sign of the difference at `x`, against the comparison
  let refuted : Q(False) ← if increasing then do
      have value : Q(0 ≤ $atEnd) := value
      have grows : Q($atEnd < $p - $q) := grows
      have target : Q($p ≤ $q) := c.proof
      pure q(absurd $target (not_le.mpr (sub_pos.mp (lt_of_le_of_lt $value $grows))))
    else do
      have grows : Q($atEnd ≤ $p - $q) := grows
      if positive then
        have value : Q(0 < $atEnd) := value
        if c.strict then
          have target : Q($p < $q) := c.proof
          pure q(absurd $target
            (not_lt.mpr (sub_nonneg.mp (le_of_lt (lt_of_lt_of_le $value $grows)))))
        else
          have target : Q($p ≤ $q) := c.proof
          pure q(absurd $target (not_le.mpr (sub_pos.mp (lt_of_lt_of_le $value $grows))))
      else
        have value : Q(0 ≤ $atEnd) := value
        have target : Q($p < $q) := c.proof
        pure q(absurd $target (not_lt.mpr (sub_nonneg.mp (le_trans $value $grows))))
  goal.assign refuted
  trace[interval.constraints] "the difference of the two sides has a sign at {x} = {a}, and \
    its derivative {f'.beta #[x]} has one beyond"
  return true

/--
Close the main goal `False` from one end of the range of the variable. The step proves the
sign of the difference `f` of the two sides at the end `a`, by `norm_num` or by `prove`, and
then looks at the sign of the derivative of `f` at four points of the range, by one evaluation
each: the points at `1 / 64`, `1 / 8`, `1 / 2` and `7 / 8` of the way to the other bound, or
at the distances `1 / 64`, `1`, `8` and `64` from the end when there is no other bound. Where
all four have the sign that is needed, the whole range is tried (`onRange`). Where that fails,
or the sign is wrong from some point on, and `split` allows it, the range is cut at one of the
points with the right sign: the part at the end is tried in the same way, and the rest is left
to `prove`, where the two sides do not meet.
-/
def fromEnd (prove : MVarId → TacticM Bool) (precision degree : Nat) (split : Bool)
    (c : Comparison) (anchor : Anchor) (far : Option (Lean.Expr × Q(ℝ) × Bool)) :
    TacticM Bool := do
  have p : Q(ℝ) := c.p
  have q : Q(ℝ) := c.q
  have x : Q(ℝ) := c.x
  have a : Q(ℝ) := anchor.point
  have difference : Q(ℝ) := q($p - $q)
  have atEnd : Q(ℝ) := difference.replaceFVar x a
  -- the sign of the value at the end
  let valueProof (statement : Q(Prop)) : TacticM (Option Lean.Expr) := do
    if let some proof ← normNumProof? statement then return some proof
    -- the route is not asked for what one evaluation does not show
    if (← holdsByEvaluation statement precision degree) == some false then return none
    let goal ← mkFreshExprMVar statement
    if ← prove goal.mvarId! then return some (← instantiateMVars goal) else return none
  let positive? ← valueProof q(0 < $atEnd)
  let value? ← if positive?.isSome then pure positive? else normNumProof? q(0 ≤ $atEnd)
  let some value := value? | return false
  -- the derivative as a term of the variable, for its sign at the points
  let derivative? ← withLCtx {} #[] <| withLocalDeclD `t q(ℝ) fun (t : Q(ℝ)) => do
    let assumed (term : Lean.Expr) : TacticM (Option Lean.Expr) := do
      have term : Q(ℝ) := term
      return some (← mkFreshExprMVar q($term ≠ 0))
    let some rule ← derivativeProof t assumed (difference.replaceFVar x t) | return none
    return some (← mkLambdaFVars #[t] (← cleanDerivative rule).1)
  let some f' := derivative? | return false
  let mut points : Array Q(ℝ) := #[]
  match far with
  | some (_, w, _) =>
    for fraction in [(1 : ℚ) / 64, 1 / 8, 1 / 2, 7 / 8] do
      let fraction ← ratTerm fraction
      points := points.push q($a + ($w - $a) * $fraction)
  | none =>
    for distance in [(1 : ℚ) / 64, 1, 8, 64] do
      let distance ← ratTerm distance
      points := points.push (if anchor.lower then q($a + $distance) else q($a - $distance))
  let mut good := 0
  for point in points do
    have slope : Q(ℝ) := f'.beta #[point]
    let wrong : Q(Prop) := if anchor.lower then q($slope < 0) else q(0 < $slope)
    if (← holdsByEvaluation wrong precision degree) == some true then break
    good := good + 1
  if good == 0 then return false
  let goal ← getMainGoal
  let some (probe : Q(ℝ)) := points[0]? | return false
  if good == points.size then
    if ← onRange prove precision degree goal c anchor far probe value positive?.isSome then
      replaceMainGoal []
      return true
  unless split do return false
  -- the part at the end, up to a point where the derivative still has its sign, and the rest
  let some (cut : Q(ℝ)) := points[min (good - 1) (if far.isSome then 2 else 1)]? | return false
  let saved ← saveState
  let rest : Q(Prop) := if anchor.lower then q($cut < $x) else q($x < $cut)
  let nearGoal ← mkFreshExprMVar (← mkArrow (anchor.before false x cut) q(False))
  let restGoal ← mkFreshExprMVar (← mkArrow rest q(False))
  let (within, nearBody) ← nearGoal.mvarId!.intro1P
  unless ← onRange prove precision degree nearBody c anchor (some (.fvar within, cut, false))
      probe value positive?.isSome do
    saved.restore
    return false
  unless ← prove restGoal.mvarId! do
    saved.restore
    return false
  let cases : Lean.Expr := if anchor.lower then q(le_or_gt $x $cut) else q(le_or_gt $cut $x)
  goal.assign (← mkAppM ``Or.elim #[cases, ← instantiateMVars nearGoal,
    ← instantiateMVars restGoal])
  replaceMainGoal []
  trace[interval.constraints] "the range of {x} was cut at {cut}: the derivative decides the \
    part at {a}"
  return true

/--
Close the main goal `False` by the sign of a derivative, when the hypotheses are one comparison
between two terms in one real variable `x` and bounds of `x` by terms without variables. From
the lower bound, and then from the upper bound, `fromEnd` proves the sign of the difference of
the two sides at the end and the sign of its derivative beyond. A comparison `p < |a|` or
`p ≤ |a|` is refuted as the two comparisons of `p` with `a` and with `-a`. `prove` closes a
goal by the route: it is given the sign of the derivative, the sign at the end where `norm_num`
does not decide it, the terms that must not vanish, and the part of a range that was cut off.
The result says whether the goal was closed.
-/
partial def byDerivative (prove : MVarId → TacticM Bool) (precision degree : Nat)
    (split : Bool) : TacticM Bool := withMainContext do
  -- the comparisons of the hypotheses: bounds of a variable by a closed term, and the others
  let mut lowers : Array (Lean.Expr × Q(ℝ) × Q(ℝ) × Bool) := #[]
  let mut uppers : Array (Lean.Expr × Q(ℝ) × Q(ℝ) × Bool) := #[]
  let mut targets : Array (Lean.Expr × Q(ℝ) × Q(ℝ) × Bool) := #[]
  let mut others : Array Lean.Expr := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    let type ← instantiateMVars decl.type
    match ← realComparison? type with
    | some (a, b, strict) =>
      if b.isFVar && !a.hasFVar then lowers := lowers.push (decl.toExpr, b, a, strict)
      else if a.isFVar && !b.hasFVar then uppers := uppers.push (decl.toExpr, a, b, strict)
      else targets := targets.push (decl.toExpr, a, b, strict)
    | none => others := others.push type
  let #[(proof, p, q, strict)] := targets | return false
  if p.hasMVar || q.hasMVar then return false
  -- a comparison with an absolute value as its larger side is one with each sign of the
  -- argument, and the step refutes the two one after the other
  if q.isAppOfArity ``abs 4 && proof.isFVar then
    have a : Q(ℝ) := q.appArg!
    let cases : Lean.Expr := if strict then
        have proof : Q($p < |$a|) := proof
        q(lt_abs.mp $proof)
      else
        have proof : Q($p ≤ |$a|) := proof
        q(le_abs.mp $proof)
    let goal ← getMainGoal
    let later := (← getGoals).drop 1
    let saved ← saveState
    let mut refuted : Array Lean.Expr := #[]
    for side in [a, q(-$a)] do
      let branch ← mkFreshExprMVar
        (← mkArrow (if strict then q($p < $side) else q($p ≤ $side)) q(False))
      let (_, body) ← branch.mvarId!.intro1P
      setGoals [← body.tryClear proof.fvarId!]
      unless ← byDerivative prove precision degree split do
        saved.restore
        return false
      refuted := refuted.push (← instantiateMVars branch)
    let #[first, second] := refuted | return false
    goal.assign (← mkAppM ``Or.elim #[cases, first, second])
    setGoals later
    return true
  -- one variable, which the other hypotheses do not mention
  let #[index] := (collectFVars (collectFVars {} p) q).fvarIds | return false
  have x : Q(ℝ) := .fvar index
  unless ← isDefEq (← inferType x) q(ℝ) do return false
  if others.any (·.containsFVar index) then return false
  let c : Comparison := { proof, p, q, strict, x }
  -- the last bound on each side is the one that a cut of the range has added
  let bound (bounds : Array (Lean.Expr × Q(ℝ) × Q(ℝ) × Bool)) :
      Option (Lean.Expr × Q(ℝ) × Bool) :=
    (bounds.reverse.find? (·.2.1 == x)).map fun (proof, _, point, strict) =>
      (proof, point, strict)
  for lower in [true, false] do
    let (near, far) := if lower then (bound lowers, bound uppers) else (bound uppers, bound lowers)
    let some (proof, point, strict) := near | continue
    if ← fromEnd prove precision degree split c { lower, point, proof, strict } far then
      return true
  return false

end FloatLib.Numerics.Interval.Tactic.Constraints
