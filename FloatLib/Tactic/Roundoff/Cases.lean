/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Meta.Tactic.Split
public import FloatLib.Tactic.Roundoff.Apply

/-!
# A `match` in `roundoff`

A `match` whose discriminants compute is the alternative it selects (`reduceControl?`). One whose
discriminants stay open, such as a size, a case of an inductive type or an optional input, is
analyzed alternative by alternative. Each alternative is analyzed for its own pattern variables,
under its own hypotheses:

* the equations between the discriminants and its patterns, those that the `match` names with
  `h :` and those it does not;
* and each hypothesis of the context about a discriminant that is a variable, restated at the
  pattern.

`Cases.proveBySplit` then proves a statement about the `match` from the statements about its
alternatives, by the splitter of the matcher (`Lean.Meta.Split.splitMatch`), so the kernel checks
the case distinction like any other proof. The forward analysis states the reference, the budgets
and the conditions of a `match` as the `match` of those of its alternatives (`Cases.forward`). The
backward and closed commands state the `match` of the statements of the alternatives.

The pattern variables of an alternative are parts of its discriminants, so they are inputs only
when the discriminants are index data or stored inputs (`indexClosed`). A `match` that takes a
value computed from numerical values apart is refused, since its reference would keep the parts.
One that binds no variable at all, such as a `match` on a computed comparison, keeps its
discriminant as the program computes it, as a branch keeps its condition.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Cases

/-- A complete application of a matcher, with no further argument. -/
def matcher? (value : Lean.Expr) : MetaM (Option MatcherApp) := do
  let some app ← matchMatcherApp? value | return none
  if app.remaining.isEmpty then return some app else return none

/-- The patterns of each alternative of `app`: for alternative `i`, a function of the parameters
of the alternative whose body applies a placeholder to the patterns of the discriminants, in
order. They are read off the type of the matcher at a variable motive, where the type of an
alternative is the motive at its patterns. -/
def patterns (app : MatcherApp) : MetaM (Array Lean.Expr) := do
  let matcher := mkAppN (mkConst app.matcherName app.matcherLevels.toList) app.params
  let .forallE _ motiveType rest _ ← whnfD (← inferType matcher) |
    throwError "roundoff: unexpected type of the matcher `{app.matcherName}`"
  withLocalDeclD `motive motiveType fun motive => do
    let mut type ← instantiateForall (rest.instantiate1 motive) app.discrs
    let mut result := #[]
    for count in app.altNumParams, alternative in app.alts do
      let .forallE _ expected body _ ← whnfD type |
        throwError "roundoff: unexpected type of the matcher `{app.matcherName}`"
      result := result.push (← forallBoundedTelescope expected (some count)
        fun parameters conclusion =>
          mkLambdaFVars parameters (mkAppN (.sort .zero) conclusion.getAppArgs))
      type := body.instantiate1 alternative
    return result

/-- The hypotheses of an alternative of `app` whose patterns are `matched`, each with its name: an
equation `discriminant = pattern` for each discriminant that is no proof, that the `match` does
not name and whose pattern has its type, and each hypothesis of the context `outer` that mentions
a discriminant that is a variable, restated at the patterns where that is type correct. -/
def armHypotheses (app : MatcherApp) (matched : Array Lean.Expr) (outer : LocalContext) :
    MetaM (Array (Name × Lean.Expr)) := do
  let mut replaced := #[]
  let mut values := #[]
  let mut hypotheses : Array (Name × Lean.Expr) := #[]
  for discriminant in app.discrs, pattern in matched, info in app.discrInfos do
    if info.hName?.isSome || (← isProof discriminant) then continue
    if discriminant.isFVar then
      replaced := replaced.push discriminant
      values := values.push pattern
    if ← withNewMCtxDepth (isDefEq (← inferType discriminant) (← inferType pattern)) then
      hypotheses := hypotheses.push (`matched, ← mkEq discriminant pattern)
  if replaced.isEmpty then return hypotheses
  for declaration in outer do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    unless replaced.any (type.containsFVar ·.fvarId!) do continue
    unless ← isProp type do continue
    let copy := type.replaceFVars replaced values
    if ← isTypeCorrect copy then hypotheses := hypotheses.push (declaration.userName, copy)
  return hypotheses

/-- Run `action` in the context of alternative `index` of `app`, with the parameters of the
alternative, the hypotheses of the alternative (`armHypotheses`), its patterns and its body. The
parameters are those that the matcher binds: the pattern variables, a unit for an alternative
without variables, and the equations of the discriminants that the `match` names. `patterns` are
those of `Cases.patterns`. -/
def withArm {n : Type → Type} [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]
    [MonadError n] {α : Type} (app : MatcherApp) (patterns : Array Lean.Expr) (index : Nat)
    (action : Array Lean.Expr → Array Lean.Expr → Array Lean.Expr → Lean.Expr → n α) : n α := do
  let count := app.altNumParams[index]!
  let outer ← liftMetaM getLCtx
  lambdaBoundedTelescope app.alts[index]! count fun parameters body => do
    unless parameters.size == count do
      throwError "roundoff: an alternative of `{app.toExpr}` is not written as a function of its \
        pattern variables"
    let matched := (patterns[index]!.beta parameters).getAppArgs
    let hypotheses ← liftMetaM (armHypotheses app matched outer)
    let under : Array Lean.Expr → n α := hypotheses.foldr
      (fun (name, type) rest facts => withLocalDeclD name type fun fact => rest (facts.push fact))
      (fun facts => action parameters facts matched body.headBeta)
    under #[]

/-- Check that the pattern variables of the alternatives of `app` are inputs: every discriminant
is a proof, a stored input (`isStoredInput`) or index data (`indexClosed`), and one whose type is
a numerical carrier is matched by a variable in every alternative, so that no pattern looks into
a number. A `match` whose alternatives bind no variable only chooses, as a branch does, and
passes. The error says which discriminant the `match` may not take apart. -/
def checkDiscriminants (app : MatcherApp) (patterns : Array Lean.Expr) : AnalyzeM Unit := do
  let cache := (← read).carriers
  if app.altInfos.all (·.numFields == 0) then return
  for discriminant in app.discrs, position in [0:app.discrs.size] do
    if ← isProof discriminant then continue
    let stored ← isStoredInput discriminant <||> indexClosed discriminant (cache? := some cache)
    unless stored do
      throwError "roundoff: no numerical rule for the `match` on `{discriminant}`: it binds \
        parts of a value computed from numerical values, so the reference would keep them; \
        match on index data or on a stored input"
    if ← carrierHead (← inferType discriminant) (some cache) then
      for pattern in patterns, count in app.altNumParams do
        let whole ← lambdaBoundedTelescope pattern count fun _ body =>
          return body.getAppArgs[position]?.any (·.isFVar)
        unless whole do
          throwError "roundoff: no numerical rule for the `match` that takes the numerical \
            value `{discriminant}` apart: the reference would keep its parts"

/-- Whether the alternatives of `app` can be analyzed one by one (`checkDiscriminants` passes). -/
def analyzable (app : MatcherApp) : AnalyzeM Bool := do
  try
    checkDiscriminants app (← patterns app)
    return true
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return false

/-- The matcher of `app` at the constant motive `type`, applied to the discriminants of `app` and
to `alternatives`: the `match` of the same patterns whose alternative `i` is `alternatives[i]`,
a function of the parameters of that alternative. -/
def combine (app : MatcherApp) (type : Lean.Expr) (alternatives : Array Lean.Expr) :
    MetaM Lean.Expr := do
  let some position := app.uElimPos? |
    throwError "roundoff: the matcher `{app.matcherName}` eliminates into propositions only"
  let motive ← forallTelescopeReducing (← inferType app.motive) fun binders _ =>
    mkLambdaFVars binders type
  let levels := app.matcherLevels.set! position (← getLevel type)
  let combined := mkAppN (mkConst app.matcherName levels.toList)
    (app.params ++ #[motive] ++ app.discrs ++ alternatives)
  check combined
  return combined

/-- The term that all of `alternatives` return, when they return the same term and it does not
depend on their parameters: the `match` of these alternatives is that term in every case. -/
def shared? (app : MatcherApp) (alternatives : Array Lean.Expr) : MetaM (Option Lean.Expr) := do
  let mut found? : Option Lean.Expr := none
  for alternative in alternatives, count in app.altNumParams do
    let body? ← lambdaBoundedTelescope alternative count fun parameters body => do
      let body ← instantiateMVars body
      if parameters.size != count || mentions body (fun id => parameters.any (·.fvarId! == id))
      then return none
      return some body
    let some body := body? | return none
    match found? with
    | some found => unless found == body do return none
    | none => found? := some body
  return found?

/-- Fill the argument `argument`, a metavariable of the proof of one case, from the context of
`goal`: a unit, a hypothesis or variable of its type, the most recent first, or reflexivity. -/
def fill (goal : MVarId) (argument : Lean.Expr) (arms : Array Name) : MetaM Bool :=
  goal.withContext do
    let argument ← instantiateMVars argument
    unless argument.isMVar do return true
    let type ← whnfR (← instantiateMVars (← inferType argument))
    if type.isConstOf ``PUnit then
      argument.mvarId!.assign (mkConst ``PUnit.unit type.constLevels!)
      return true
    let declarations := (← getLCtx).foldl (init := #[]) fun found declaration =>
      if declaration.isImplementationDetail || arms.contains declaration.userName then found
      else found.push declaration
    for declaration in declarations.reverse do
      if ← isDefEq declaration.type type then
        if ← isDefEq argument declaration.toExpr then return true
    if let some (_, left, right) := type.eq? then
      if ← isDefEq left right then
        if ← isDefEq argument (← mkEqRefl left) then return true
    if let some (_, left, _, right) := type.heq? then
      if ← isDefEq left right then
        if ← isDefEq argument (← mkHEqRefl left) then return true
    return false

/-- Prove `statement`, which contains the `match` application `split`, from the proofs `arms` of
its cases. `arms[i]` proves, for the parameters of alternative `i` (`parameters[i]` of them),
then with `conditional` for the condition of the case, then for `hypotheses[i]` hypotheses of the
case, the statement with every application of that matcher to those discriminants replaced by
its alternative `i`. With `conditional` the statement is an implication from the `match` of the
conditions. The matcher's splitter makes the case distinction, each case is closed by the arm
whose conclusion it is (the arm at the position of the case first), and the arguments of that arm
are found in the context of the case. -/
def proveBySplit (statement split : Lean.Expr) (arms : Array Lean.Expr) (conditional : Bool)
    (parameters hypotheses : Array Nat) : MetaM Lean.Expr := do
  let statement ← instantiateMVars statement
  let types ← arms.mapM fun arm => do instantiateMVars (← inferType arm)
  if statement.hasExprMVar || types.any (·.hasExprMVar) then
    throwError "roundoff: a case of `{split}` leaves a value undetermined"
  let names ← (Array.range arms.size).mapM fun index =>
    mkFreshUserName ((`arm).appendIndexAfter index)
  let goalType ← withLocalDeclsDND (names.zip types) fun binders =>
    mkForallFVars binders statement
  let goal ← mkFreshExprSyntheticOpaqueMVar goalType
  let (_, main) ← goal.mvarId!.introNP arms.size
  let cases ← try main.withContext (Split.splitMatch main split) catch error =>
    throwError "roundoff: could not distinguish the cases of `{split}`: {error.toMessageData}"
  for (case, position) in cases.zipIdx do
    let (_, case) ← if conditional then case.intro1P else pure (default, case)
    let closed ← case.withContext do
      let target ← instantiateMVars (← case.getType)
      -- The splitter lists its cases in the order of the alternatives, so the arm at the position
      -- of the case is tried first and as stated; any other arm only up to reducible unfolding,
      -- which keeps a failed comparison of two computations from unfolding their arithmetic.
      let others := (Array.range arms.size).filter (· != position)
      let mut closed := false
      for index in (if position < arms.size then #[position] else #[]) ++ others do
        if closed then break
        let some declaration := (← getLCtx).findFromUserName? names[index]! | continue
        let arity := parameters[index]! + (if conditional then 1 else 0) + hypotheses[index]!
        let saved ← saveState
        let (arguments, _, conclusion) ← forallMetaBoundedTelescope
          (← instantiateMVars declaration.type) arity
        -- Hypotheses first: they determine the pattern variables that the conclusion leaves open.
        let facts ← arguments.filterM fun argument => do isProp (← inferType argument)
        let ordered := facts ++ arguments.filter (!facts.contains ·)
        let unifies ← if index == position then isDefEq conclusion target
          else withReducible (isDefEq conclusion target)
        if arguments.size == arity && unifies && (← ordered.allM (fill case · names)) then
          case.assign (mkAppN declaration.toExpr arguments)
          closed := true
        else saved.restore
      pure closed
    unless closed do
      throwError "roundoff: a case of `{split}` is not that of an alternative:{indentD
        (MessageData.ofGoal case)}"
  let proof ← instantiateMVars goal
  if proof.hasExprMVar then
    throwError "roundoff: the case distinction of `{split}` is incomplete"
  return mkAppN proof arms

/-- One alternative of a `match` in the forward analysis. -/
structure Arm where
  /-- The reference and the budgets, each a function of the parameters of the alternative. -/
  terms : Array Lean.Expr
  /-- The condition, a function of the parameters: `True`, or the open premises of the
  alternative under the hypotheses of the case they use. -/
  condition : Lean.Expr
  /-- A proof of the bound of the alternative for its parameters, its condition and the
  hypotheses of the case, in this order. -/
  proof : Lean.Expr
  /-- A proof that the value of the alternative is finite, for the same arguments. -/
  finite? : Option Lean.Expr
  /-- The number of parameters and of hypotheses. -/
  counts : Nat × Nat
  deriving Inhabited

/-- The estimate of the observation `observe` of `split`, the `match` application `app`: each
alternative is analyzed for its own pattern variables and hypotheses (`withArm`), and the
reference, the budgets and the open premises are the `match` of those of the alternatives. The
value is finite when the value of each alternative is. No cached result or premise of one
alternative reaches another. -/
def forward (r : Recursor) (observe split : Lean.Expr) (app : MatcherApp) (fuel : Nat) :
    AnalyzeM Estimate := do
  let session ← read
  let patterns ← patterns app
  checkDiscriminants app patterns
  let initial ← get
  let actual : Q(ℝ) := (mkApp observe split).headBeta
  let mut arms : Array Arm := #[]
  let mut mixed? : Option Bool := none
  for index in [0:app.alts.size] do
    let (arm, isMixed) ← withArm app patterns index fun parameters facts _ body => do
      let observed : Q(ℝ) := (mkApp observe body).headBeta
      -- An absolute budget that the identities of zero and one reduce to zero is stated as zero
      -- (`Session.zeroBudget`), so that exact alternatives share one budget.
      let estimate ← session.zeroBudget (← r.analyze observed fuel)
      -- In mixed analysis each alternative also proves its decoded value finite, as a branch. The
      -- finiteness its estimate derived may be stated on another form of the value, such as the
      -- producer of a read unfolded at its coordinate. The case distinction compares each case
      -- with its alternative as written, so the finiteness is proved for that value.
      let finite? ← match decodedValue? observed with
        | some decoded =>
            if session.mixed && observed.isAppOf ``ExecFloat.Binary.toReal then
              let wanted ← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[decoded])
                (mkConst ``Bool.true)
              let stated ← match estimate.finite? with
                | some finite => pure ((← instantiateMVars (← inferType finite)) == wanted)
                | none => pure false
              if stated then pure estimate.finite? else
                let goal ← mkFreshExprMVar wanted
                if ← r.proveFinite goal.mvarId! fuel then pure (some (← instantiateMVars goal))
                else pure none
            else pure estimate.finite?
        | none => pure estimate.finite?
      let localGoals := (← get).pending.extract initial.pending.size (← get).pending.size
      withConditions localGoals session.comparisons fun condition evidence => do
        let inner := facts.push evidence
        let budgets := match estimate.bound with
          | .absolute error => #[(error : Lean.Expr)]
          | .mixed relative absolute => #[relative, absolute]
        let terms ← (#[(estimate.reference : Lean.Expr)] ++ budgets).mapM fun term => do
          let term ← instantiateMVars term
          if mentions term fun id => inner.any (·.fvarId! == id) then
            throwError "roundoff: the reference or a budget of a case of `{split}` depends on a \
              hypothesis of the case"
          mkLambdaFVars parameters term
        let used := facts.filter fun fact => condition.containsFVar fact.fvarId!
        let stated ← mkForallFVars used condition
        withLocalDeclD `given stated fun given => do
          let close (proof statement : Lean.Expr) : MetaM Lean.Expr := do
            let proof ← mkExpectedTypeHint (← instantiateMVars proof) statement
            let conditional ← mkLambdaFVars #[evidence] proof
            mkLambdaFVars (parameters ++ #[given] ++ facts) (mkApp conditional (mkAppN given used))
          let proof ← close estimate.proof (estimate.bound.statement observed estimate.reference)
          let finite? ← finite?.mapM fun finite => do close finite (← inferType finite)
          let arm : Arm := {
            terms, proof, finite?, condition := ← mkLambdaFVars parameters stated
            counts := (parameters.size, facts.size) }
          pure (arm, estimate.bound matches .mixed ..)
    set initial
    if mixed?.any (· != isMixed) then
      throwError "roundoff: the cases of `{split}` were analyzed in different modes"
    mixed? := some isMixed
    arms := arms.push arm
  -- A term that every alternative states alike, such as a zero budget, is stated once.
  let real (position : Nat) : MetaM Q(ℝ) := do
    let terms := arms.map (·.terms[position]!)
    match ← shared? app terms with
    | some term => pure term
    | none => combine app q(ℝ) terms
  let reference ← real 0
  let bound ← if mixed? == some true then pure (Bound.mixed (← real 1) (← real 2))
    else pure (Bound.absolute (← real 1))
  -- The premises of the alternatives are one premise, unless no alternative has any.
  let conditional := arms.any fun arm => !arm.condition.getLambdaBody.isConstOf ``True
  let (parameters, hypotheses) := (arms.map (·.counts.1), arms.map (·.counts.2))
  let unconditional (proof : Lean.Expr) (arm : Arm) : MetaM Lean.Expr := do
    if conditional then return proof
    forallBoundedTelescope (← inferType proof) (some (arm.counts.1 + 1)) fun binders _ => do
      let trivial := mkConst ``True.intro
      mkLambdaFVars binders.pop (mkAppN proof (binders.pop.push trivial))
  let premise? ← if conditional then
      pure (some (← mkFreshExprMVar (← combine app (.sort .zero) (arms.map (·.condition)))))
    else pure none
  let prove (statement : Lean.Expr) (proofs : Array Lean.Expr) : MetaM Lean.Expr := do
    let proofs ← (proofs.zip arms).mapM fun (proof, arm) => unconditional proof arm
    match premise? with
    | some premise =>
        let stated ← mkArrow (← inferType premise) statement
        return mkApp (← proveBySplit stated split proofs true parameters hypotheses) premise
    | none => proveBySplit statement split proofs false parameters hypotheses
  let proof ← prove (bound.statement actual reference) (arms.map (·.proof))
  let finite? ← match decodedValue? actual, arms.mapM (·.finite?) with
    | some value, some proofs =>
        some <$> prove (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value])
          (mkConst ``Bool.true)) proofs
    | _, _ => pure none
  if let some premise := premise? then
    modify fun state => { state with pending := state.pending.push premise.mvarId! }
  return ⟨reference, bound, proof, finite?⟩

/-- Move the function of `value` through its first argument that is a `match`:
`f (match d with | p => a) = match d with | p => f a`, when each `f a` has the type of `value`.
The equality is proved by the case distinction of the `match`. -/
def liftArgument? (value : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let arguments := value.getAppArgs
  let type ← inferType value
  for h : index in [:arguments.size] do
    let some app ← matcher? arguments[index] | continue
    let lifted? ← observing? do
      let alternatives ← (app.alts.zip app.altNumParams).mapM fun (alternative, count) =>
        lambdaBoundedTelescope alternative count fun parameters body => do
          unless parameters.size == count do throwError "roundoff: an alternative is not written"
          let applied := mkAppN value.getAppFn (arguments.set! index body.headBeta)
          check applied
          unless ← isDefEq (← inferType applied) type do throwError "roundoff: dependent match"
          mkLambdaFVars parameters applied
      let lifted ← combine app type alternatives
      let cases ← (app.alts.zip app.altNumParams).mapM fun (alternative, count) =>
        lambdaBoundedTelescope alternative count fun parameters body => do
          let applied := mkAppN value.getAppFn (arguments.set! index body.headBeta)
          mkLambdaFVars parameters (← mkEqRefl applied)
      let proof ← proveBySplit (← mkEq value lifted) arguments[index] cases false
        app.altNumParams (app.alts.map fun _ => 0)
      return (lifted, proof)
    if lifted?.isSome then return lifted?
  return none

end Cases

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
