/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Tuple

/-!
# Loops read through a registered step relation

Some loops keep a relation that their components do not keep one at a time, such as Kahan's sum
minus its compensation, which stays close to the exact sum while each component alone drifts. A
library registers such a relation with the lemma that one step preserves it, lemmas that start it
and lemmas that read a bound off it (`StepRelation`).

An observation that a reader concludes about is matched against the computation. The reader's
state must be a registered loop with a relation law, the loop's step must unfold to the relation's
step, and its initial value must be one that an initial lemma states. That law then lifts the
relation through the traversal under the condition of the preservation lemma at every visited
state, which becomes a premise of the bound.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Analyze

/-- The functions of a step relation, read off its preservation lemma at fresh parameters. -/
structure Preserved where
  /-- The step, a function of the state and the entry. -/
  step : Lean.Expr
  /-- The reference step, a function of the shadow state and the entry. -/
  reference : Lean.Expr
  /-- The budget step, a function of the state, the shadow state, the budgets and the entry. -/
  budget : Lean.Expr
  /-- The relation, a function of the state, the shadow state and the budgets. -/
  relation : Lean.Expr
  /-- The condition of one step, a function of the state, the shadow state, the budgets and the
  entry. -/
  condition : Lean.Expr
  /-- The condition as a function of the state and the entry, when it reads nothing else. -/
  actualCondition? : Option Lean.Expr
  /-- The types of the shadow state and of the budgets. -/
  shadowType : Lean.Expr
  budgetType : Lean.Expr
  /-- The preservation lemma at its parameters, which are metavariables. -/
  proof : Lean.Expr
  parameters : Array Lean.Expr
  binders : Array BinderInfo

/-- The functions of the preservation lemma `name`, whose last six binders are the state, the
shadow state, the budgets, the entry, the condition and the relation before the step. -/
def preserved (name : Name) : MetaM Preserved := do
  let rule ← mkConstWithFreshMVarLevels name
  let type ← inferType rule
  let arity ← forallTelescopeReducing type fun binders _ => pure binders.size
  let (parameters, binders, body) ← forallMetaBoundedTelescope type (arity - 6)
  forallBoundedTelescope body (some 6) fun locals conclusion => do
    let #[state, shadow, budgets, value, hcondition, hrelation] := locals |
      throwError "roundoff: `{name}` does not state that a step preserves a relation"
    let relationType ← inferType hrelation
    let conditionType ← inferType hcondition
    if mentions relationType (#[value, hcondition].contains <| .fvar ·) then
      throwError "roundoff: the relation of `{name}` reads the entry"
    let relation ← mkLambdaFVars #[state, shadow, budgets] relationType
    let next ← mkFreshExprMVar (← inferType state)
    let reference ← mkFreshExprMVar (← inferType shadow)
    let budget ← mkFreshExprMVar (← inferType budgets)
    unless ← isDefEq (relation.beta #[next, reference, budget]) conclusion do
      throwError "roundoff: `{name}` does not conclude its relation after the step"
    let reference ← instantiateMVars reference
    if mentions reference (#[state, budgets, hcondition, hrelation].contains <| .fvar ·) then
      throwError "roundoff: the reference of `{name}` reads the rounded state or the budgets"
    let actualCondition? ← if mentions conditionType (#[shadow, budgets].contains <| .fvar ·)
      then pure none
      else pure (some (← mkLambdaFVars #[state, value] conditionType))
    return {
      step := ← mkLambdaFVars #[state, value] (← instantiateMVars next)
      reference := ← mkLambdaFVars #[shadow, value] reference
      budget := ← mkLambdaFVars #[state, shadow, budgets, value] (← instantiateMVars budget)
      relation := relation
      condition := ← mkLambdaFVars #[state, shadow, budgets, value] conditionType
      actualCondition? := actualCondition?
      shadowType := ← inferType shadow
      budgetType := ← inferType budgets
      proof := mkAppN rule parameters
      parameters := parameters
      binders := binders }

/-- The unassigned parameters among `parameters`: a proposition is discharged or becomes a
premise, an instance is synthesized, and data that no unification determined rejects the match. -/
def settleParameters (parameters : Array Lean.Expr) (binders : Array BinderInfo) :
    AnalyzeM Bool := do
  synthesizeInstances parameters binders
  for parameter in parameters do
    let parameter ← instantiateMVars parameter
    unless parameter.isMVar do continue
    let goal := parameter.mvarId!
    unless ← isProp (← goal.getType) do return false
    let remaining ← require (← read) goal
    modify fun state => { state with pending := state.pending ++ remaining }
  return true

/-- The estimate of `actual` that `reader` reads off `relation` at the loop it observes, or
`none` when the reader, the loop's step or its initial value do not match. -/
def stepRelationBound? (relation : StepRelation) (reader : Name) (actual : Q(ℝ)) :
    AnalyzeM (Option Estimate) := do
  let rule ← mkConstWithFreshMVarLevels reader
  let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
  let (finiteType?, statement) := if conclusion.isAppOfArity ``And 2 then
      (some conclusion.appFn!.appArg!, conclusion.appArg!)
    else (none, conclusion)
  let some (observed, _, _) ← boundConclusion? statement | return none
  let observedMatch? ← attempt? 10000 do
    return if ← withReducible (isDefEq observed actual) then some () else none
  if observedMatch?.isNone then return none
  -- The loop whose state the reader reads.
  let mut fold? := none
  for argument in arguments do
    let argument ← instantiateMVars argument
    if let some loop ← loopOf? argument then
      if loop.relation.isSome then fold? := some (loop, argument)
  let some (loop, fold) := fold? | return none
  let some (_, _, law) := loop.relation | return none
  let loopArguments := fold.getAppArgs
  let step := loopArguments[loop.step]!
  let initial := loopArguments[loop.initial]!
  let input := loopArguments[loop.input]!
  let preserved ← preserved relation.preservation
  let stepMatch? ← attempt? 10000 do
    return if ← isDefEq preserved.step step then some () else none
  if stepMatch?.isNone then
    trace[roundoff] "the step of {fold} is not the step of {relation.preservation}"
    return none
  unless ← settleParameters preserved.parameters preserved.binders do return none
  let preserved := { preserved with
    reference := ← instantiateMVars preserved.reference
    budget := ← instantiateMVars preserved.budget
    relation := ← instantiateMVars preserved.relation
    condition := ← instantiateMVars preserved.condition
    shadowType := ← instantiateMVars preserved.shadowType
    budgetType := ← instantiateMVars preserved.budgetType }
  checkEntries loop input preserved.reference
  -- The initial relation.
  let mut start? := none
  for name in relation.initial do
    let starting ← mkConstWithFreshMVarLevels name
    let (parameters, binders, type) ← forallMetaTelescopeReducing (← ruleType starting)
    let shadow ← mkFreshExprMVar preserved.shadowType
    let budgets ← mkFreshExprMVar preserved.budgetType
    let matched? ← attempt? 10000 do
      let expected := (preserved.relation.beta #[initial, shadow, budgets]).headBeta
      return if ← isDefEq type expected then some () else none
    if matched?.isNone then continue
    unless ← settleParameters parameters binders do continue
    start? := some (mkAppN starting parameters, ← instantiateMVars shadow,
      ← instantiateMVars budgets)
    break
  let some (hinit, shadow, budgets) := start? | do
    trace[roundoff] "no initial lemma of {relation.preservation} states {initial}"
    return none
  let lifted ← mkAppM law #[step, preserved.reference, preserved.budget, preserved.relation,
    preserved.condition, initial, shadow, budgets, input, hinit, preserved.proof]
  let .forallE _ validType _ _ ← whnf (← inferType lifted) |
    throwError "roundoff: unexpected relation law {law}"
  let validType ← instantiateMVars validType
  let valid ← mkFreshExprMVar validType
  -- A condition on the state and the entry alone is a condition on the loop's own states.
  if let some actualCondition := preserved.actualCondition? then
    let augmentedType ← inferType (validType.getArg! 4)
    let first ← withLocalDeclD `state augmentedType fun state =>
      mkLambdaFVars #[state] (.proj ``Prod 0 state)
    let goals ← valid.mvarId!.apply (← mkAppM loop.allStepsOfMap
      #[validType.getArg! 2, validType.getArg! 3, validType.getArg! 4, input, first, step,
        actualCondition])
    for goal in goals do
      unless ← discharge (← read) goal do
        if let some condition ← (← read).tidy goal then
          modify fun state => { state with pending := state.pending.push condition }
  else
    modify fun state => { state with pending := state.pending.push valid.mvarId! }
  let proof := mkApp lifted valid
  let holds := (← instantiateMVars (← inferType proof)).headBeta
  -- The reader's hypothesis is the lifted relation.
  let mut supplied := false
  for argument in arguments do
    let argument ← instantiateMVars argument
    unless argument.isMVar do continue
    let type ← instantiateMVars (← argument.mvarId!.getType)
    unless ← isProp type do continue
    let matched? ← attempt? 10000 do
      return if ← isDefEq type holds then some () else none
    if matched?.isSome then
      argument.mvarId!.assign proof
      supplied := true
      break
  unless supplied do return none
  unless ← settleParameters arguments binders do return none
  let reading ← instantiateMVars (mkAppN rule arguments)
  let statement ← instantiateMVars statement
  let some (_, reference, bound) ← boundConclusion? statement | return none
  let reference : Q(ℝ) := reference
  let (boundProof, finite?) ← match finiteType? with
    | some _ =>
      let finite? ← if actual.isAppOf ``ExecFloat.Binary.toReal then
          pure (some (← mkExpectedTypeHint (← mkAppM ``And.left #[reading])
            (← Tuple.finiteness actual.appArg!)))
        else pure none
      pure (← mkAppM ``And.right #[reading], finite?)
    | none => pure (reading, none)
  let estimate : Estimate := {
    reference := reference
    bound := bound
    proof := ← mkExpectedTypeHint boundProof (bound.statement actual reference)
    finite? := finite? }
  let session ← read
  if session.mixed then return some (← session.simplify (← estimate.inMode true))
  -- Absolute analysis reads a mixed bound as the absolute bound it implies.
  unless bound matches .mixed .. do return some estimate
  let mixed ← session.simplify estimate
  let .mixed relative absolute := mixed.bound | return some estimate
  let error : Q(ℝ) := q($relative * |$(mixed.reference)| + $absolute)
  let context ← Simp.mkContext { implicitDefEqProofs := false } #[session.budget]
  let tidied ← session.tidyTerm error context
  let proof ← mkAppM ``MixedError.bound #[mixed.proof]
  let proof ← if tidied.expr == error then pure proof else do
    let motive ← withLocalDeclD `error q(ℝ) fun bound =>
      mkLambdaFVars #[bound] ((Bound.absolute bound).statement actual mixed.reference)
    mkEqMP (← mkCongrArg motive (← tidied.getProof' error)) proof
  return some { mixed with
    bound := .absolute tidied.expr
    proof := ← mkExpectedTypeHint proof
      ((Bound.absolute tidied.expr).statement actual mixed.reference) }

/-- The estimate of `actual` read off a registered step relation of a loop it observes. The
observation must contain a registered loop with a relation law, or a reduction that the registered
conversions write as one. The first reader that matches and whose relation the loop's step and
initial value admit gives the estimate. Readers come before the registered rules, so a reader of a
sum such as `s.1 + s.2` takes precedence over the rules for its operations. -/
def relationBound? (actual : Q(ℝ)) : AnalyzeM (Option Estimate) := do
  let extension ← extension
  if extension.stepRelations.isEmpty then return none
  let observesLoop (term : Lean.Expr) := (term.find? fun term => extension.loops.any fun loop =>
    loop.relation.isSome && term.isAppOfArity loop.fold loop.arity).isSome
  let readAt (observation : Q(ℝ)) : AnalyzeM (Option Estimate) := do
    for relation in extension.stepRelations do
      for reader in relation.readers do
        let reading ← speculate? (stepRelationBound? relation reader observation)
        if let some (some estimate) := reading then
          trace[roundoff] "read {observation} through {reader}"
          return some estimate
    return none
  if observesLoop actual then return ← readAt actual
  -- A loop written another way, such as over an array, is read as its registered loop.
  if extension.conversions.isEmpty then return none
  unless (actual.find? fun term => extension.reductions.any term.isAppOf).isSome do return none
  let context ← conversionSimpContext
  let (normalized, _) ← simp actual context
  unless normalized.expr != actual && observesLoop normalized.expr do return none
  let some estimate ← readAt normalized.expr | return none
  let decoded := actual.isAppOf ``ExecFloat.Binary.toReal
  let source := if decoded then actual.appArg! else actual
  return some (← rewriteSimp estimate actual source decoded normalized context #[])

end Analyze

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
