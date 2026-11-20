/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Elementary.Slopes
public meta import FloatLib.Tactic.Interval.Constraints.Forms

/-!
# Introducing bounded slopes into interval constraints

The elementary slope theorems express sine, cosine, hyperbolic tangent and arctangent
as polynomials with bounded auxiliary variables. `introduceSlopes` supplies these
witnesses when interval search stops at a zero margin, retaining the original
comparisons. The additional comparisons forget the witnesses' dependence on their
arguments and are therefore weaker.

`rangeFacts` and `signedFacts` supply range, tangent and sign facts for arithmetic.
`generalizeValues` names bounded function values whose arguments have no box.
`openAbsoluteValues` splits by sign and replaces absolute values in each case.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- The values of the given real function among the subterms of some terms, each once. The
function has `arity` arguments, of which the last is its real argument. -/
def valuesOf (function : Name) (terms : Array Lean.Expr) (arity : Nat := 1) :
    Array Lean.Expr := Id.run do
  let mut found := #[]
  let mut todo := terms
  while !todo.isEmpty do
    let e := todo.back!
    todo := todo.pop
    if e.isAppOfArity function arity && !e.hasLooseBVars && !found.contains e then
      found := found.push e
    match e with
    | .app f a => todo := (todo.push f).push a
    | .lam _ d b _ | .forallE _ d b _ => todo := (todo.push d).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return found

/-- The lemmas about the values of a function that hold for every argument, with the number of
arguments of the function: its range, for the exponential also its tangent at zero, and for the
absolute value its comparisons with its argument. -/
def rangeLemmas : List (Name × Nat × List Name) :=
  [ (``Real.sin, 1, [``Real.neg_one_le_sin, ``Real.sin_le_one])
  , (``Real.cos, 1, [``Real.neg_one_le_cos, ``Real.cos_le_one])
  , (``Real.tanh, 1, [``Real.neg_one_lt_tanh, ``Real.tanh_lt_one])
  , (``Real.arctan, 1, [``Real.neg_pi_div_two_lt_arctan, ``Real.arctan_lt_pi_div_two])
  , (``Real.exp, 1, [``Real.exp_pos, ``Real.add_one_le_exp])
  , (``Real.cosh, 1, [``Real.one_le_cosh])
  , (``Real.sqrt, 1, [``Real.sqrt_nonneg])
  , (``abs, 4, [``abs_nonneg, ``le_abs_self, ``neg_abs_le]) ]

/--
The facts of `rangeLemmas` about the function values in some terms, as proofs: `-1 ≤ Real.sin t`
and `Real.sin t ≤ 1`, the same for the cosine, the strict bounds of the hyperbolic tangent, the
bounds of the arctangent by `π / 2`, `0 < Real.exp t` and `t + 1 ≤ Real.exp t`,
`1 ≤ Real.cosh t`, `0 ≤ √t`, and `0 ≤ |t|`, `t ≤ |t|` and `-|t| ≤ t`.
-/
def rangeFacts (terms : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let mut facts := #[]
  for (function, arity, lemmas) in rangeLemmas do
    for value in valuesOf function terms arity do
      for name in lemmas do
        facts := facts.push (← mkAppM name #[value.appArg!])
  return facts

/--
The cases of the absolute values in the comparisons that hold outright: one goal for each choice
of signs, in which every `|t|` is replaced by `t` under the hypothesis `0 ≤ t`, or by `-t` under
`t < 0`. In a case the comparisons have no absolute value, so they have forms where they hold
with zero margin. At most `limit` values are opened. The result is the goals, or `none` when the
comparisons have no absolute value.
-/
def openAbsoluteValues (literals : Array Literal) (limit : Nat := 3) :
    TacticM (Option (List MVarId)) := do
  let sides := sidesOf literals
  let values := (valuesOf ``abs sides 4).extract 0 limit
  if values.isEmpty then return none
  let mut goals := [← getMainGoal]
  for value in values do
    have t : Q(ℝ) := value.appArg!
    let mut next : List MVarId := []
    for goal in goals do
      let (fvar, start) ← (← goal.assert `sign
        q((|$t| = $t ∧ 0 ≤ $t) ∨ (|$t| = -$t ∧ $t < 0)) q(abs_cases $t)).intro1P
      for (subgoal, replacement) in (← start.cases fvar).toList.zip [t, q(-$t)] do
        let some both := subgoal.fields[0]? | throwError "interval: a case has no hypothesis"
        let #[inner] ← subgoal.mvarId.cases both.fvarId!
          | throwError "interval: a case of an absolute value did not leave one goal"
        let some equation := inner.fields[0]? | throwError "interval: a case has no equation"
        let (rewritten, _) ← rewriteHypotheses inner.mvarId value replacement equation
          fun decl => pure (decl.toExpr == equation)
        next := next ++ [← rewritten.tryClear equation.fvarId!]
    goals := next
  return some goals

/--
The facts about function values that need the sign of the argument, for the values in some
terms: `√t ^ 2 = t` where `0 ≤ t`, `Real.exp t ≤ 1` where `t ≤ 0`, and
`Real.log t ≤ t - 1` where `0 < t`. The sign is proved by `positivity`, or by `linarith` from
the given facts; a value whose argument has no such sign gets no fact. `failed` remembers the
signs that `linarith` did not prove, with the statements of the facts it had, so that a later
round with the same facts does not ask again.
-/
def signedFacts (terms : Array Lean.Expr) (facts : Array Lean.Expr)
    (failed : Option (IO.Ref (Std.HashSet UInt64)) := none) : TacticM (Array Lean.Expr) := do
  -- what `linarith` reads: a sign that it did not prove from these facts is not asked again
  let reading ← facts.foldlM (init := (7 : UInt64)) fun code proof =>
    return mixHash code (← instantiateMVars (← inferType proof)).hash
  let prove (statement : Q(Prop)) : TacticM (Option Lean.Expr) := do
    if let some proof ← positivityProof? statement then return some proof
    let key := mixHash statement.hash reading
    if let some failed := failed then
      if (← failed.get).contains key then return none
    let proof? ← linarithProof? statement facts
    if let (none, some failed) := (proof?, failed) then failed.modify (·.insert key)
    return proof?.map fun proof => (proof : Lean.Expr)
  let mut found := #[]
  for value in valuesOf ``Real.sqrt terms do
    have t : Q(ℝ) := value.appArg!
    if let some h ← prove q(0 ≤ $t) then
      found := found.push (mkApp2 (mkConst ``Real.sq_sqrt) t h)
  for value in valuesOf ``Real.exp terms do
    have t : Q(ℝ) := value.appArg!
    if let some (h : Q($t ≤ 0)) ← prove q($t ≤ 0) then
      found := found.push q(Real.exp_le_one_iff.mpr $h)
  for value in valuesOf ``Real.log terms do
    have t : Q(ℝ) := value.appArg!
    if let some h ← prove q(0 < $t) then
      found := found.push (mkApp2 (mkConst ``Real.log_le_sub_one_of_pos) t h)
  return found

/--
Give a name to each value of the sine, the cosine, the hyperbolic tangent or the arctangent whose
argument contains one of the given atoms, which have no bounds. Such a value has no enclosure on
a box, but it lies in the range of its function whatever the argument is: the range becomes two
hypotheses and the value a new variable in every hypothesis, so the constraints keep the range
and forget the argument. Only the outermost such values are named. The result says whether a
hypothesis changed.
-/
def generalizeValues (unbounded : Array Lean.Expr) : TacticM Bool := withMainContext do
  let mut types := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then types := types.push (← instantiateMVars decl.type)
  let mut values : Array (Name × Lean.Expr) := #[]
  for function in [``Real.sin, ``Real.cos, ``Real.tanh, ``Real.arctan] do
    for value in valuesOf function types do
      if unbounded.any fun atom => (value.appArg!.find? (· == atom)).isSome then
        values := values.push (function, value)
  let outer := values.filter fun (_, value) => !values.any fun (_, other) =>
    other != value && (other.appArg!.find? (· == value)).isSome
  let mut goal ← getMainGoal
  let mut changed := false
  for (function, value) in outer, k in [0:outer.size] do
    -- the hypotheses that contain the value
    let fvars ← goal.withContext do
      let mut fvars := #[]
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        if ((← instantiateMVars decl.type).find? (· == value)).isSome then
          fvars := fvars.push decl.fvarId
      return fvars
    if fvars.isEmpty then continue
    let lemmas := ((rangeLemmas.find? (·.1 == function)).map (·.2.2)).getD []
    let facts ← lemmas.toArray.mapM fun name => do
      let proof := mkApp (mkConst name) value.appArg!
      return ({ userName := `range, type := ← inferType proof, value := proof } : Hypothesis)
    let (ranges, next) ← goal.assertHypotheses facts
    let (_, _, next) ← next.withContext <| next.generalizeHyp
      #[{ expr := value, xName? := some (Name.mkSimple s!"v{k + 1}") }] (fvars ++ ranges)
    trace[interval.constraints] "{value} has an argument without bounds: it becomes a variable \
      with the range of its function"
    goal := next
    changed := true
  replaceMainGoal [goal]
  return changed

/--
Introduce slopes into the main goal. Each value of the sine, the cosine, the hyperbolic tangent
or the arctangent in a comparison that holds outright gets a new variable with the equation and
the bounds of its slope, and each such comparison gets a copy in which the slope forms replace
the values. At most `limit` values get one. The result is the new variables.
-/
def introduceSlopes (literals : Array Literal) (limit : Nat := 8) :
    TacticM (Array Lean.Expr) := do
  let sides := sidesOf literals
  let table : List (Name × Name) :=
    [ (``Real.sin, ``exists_sin_eq_sub), (``Real.cos, ``exists_cos_eq_sub)
    , (``Real.tanh, ``exists_tanh_eq_sub), (``Real.arctan, ``exists_arctan_eq_sub) ]
  let mut goal ← getMainGoal
  -- each value with the proof that it equals its slope form
  let mut slopes : Array Lean.Expr := #[]
  let mut equations : Array (Lean.Expr × Lean.Expr) := #[]
  for (function, slope) in table do
    for value in valuesOf function sides do
      if equations.size ≥ limit then break
      let fact := mkApp (mkConst slope) value.appArg!
      let (fvar, next) ← (← goal.assert `slope (← inferType fact) fact).intro1P
      let name := Name.mkSimple s!"s{equations.size + 1}"
      let #[subgoal] ← next.cases fvar #[{ varNames := [name, `slope] }]
        | throwError "interval: a slope did not leave one goal"
      goal := subgoal.mvarId
      let some bounds := subgoal.fields[1]? | throwError "interval: a slope has no equation"
      slopes := slopes.push (subgoal.fields.getD 0 bounds)
      equations := equations.push (value, ← goal.withContext (mkAppM ``And.left #[bounds]))
  if equations.isEmpty then return #[]
  -- the copies of the comparisons
  let copies ← goal.withContext do
    let mut copies : Array Hypothesis := #[]
    for literal in literals do
      have a : Q(ℝ) := literal.lhs
      have b : Q(ℝ) := literal.rhs
      let mut statement : Lean.Expr := if literal.strict then q($a < $b) else q($a ≤ $b)
      let mut proof := literal.proof
      let mut changed := false
      for (value, equation) in equations do
        let abstracted ← kabstract statement value
        unless abstracted.hasLooseBVars do continue
        let motive := Lean.Expr.lam `t q(ℝ) abstracted .default
        proof ← mkEqMP (← mkCongrArg motive equation) proof
        let some (_, _, replacement) := (← inferType equation).eq? | continue
        statement := abstracted.instantiate1 replacement
        changed := true
      if changed then
        copies := copies.push { userName := `sloped, type := statement, value := proof }
    return copies
  let (_, final) ← goal.assertHypotheses copies
  replaceMainGoal [final]
  return slopes

end FloatLib.Numerics.Interval.Tactic.Constraints
