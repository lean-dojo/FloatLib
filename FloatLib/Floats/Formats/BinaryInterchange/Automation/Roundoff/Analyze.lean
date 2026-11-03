/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Tuple
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Relation

/-!
# The `roundoff` analysis

`analyze` derives an estimate of a real observation of a computation: registered rules first,
then control flow, container reads, loops, decoding and the expansion of definitions, sharing the
analysis of repeated subexpressions. `Analyze.recursor` ties the parts of the analysis together.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Whether `container` is `Option.get o h` of an input option `o`, also in the matcher form that
coordinate normalization unfolds it to: a matcher application on two discriminants is accepted only
when the whole expression, motive and alternatives included, is definitionally equal to the genuine
getter on them. An entry read from it is exact, that is, equal to the decoded stored entry, and no
proof of its finiteness is supplied. A computed option, such as an `Option.map`, is not accepted. -/
def isInputOptionGet (container : Lean.Expr) : MetaM Bool := do
  let arguments := container.getAppArgs
  let mut candidate : Option (Lean.Expr × Lean.Expr) := none
  if container.isAppOfArity ``Option.get 3 then
    candidate := some (arguments[1]!, arguments[2]!)
  else if let some name := container.getAppFn.constName? then
    if let some info ← getMatcherInfo? name then
      if info.numDiscrs == 2 && container.getAppNumArgs == info.arity then
        candidate := some (arguments[info.getFirstDiscrPos]!,
          arguments[info.getFirstDiscrPos + 1]!)
  let some (option, proof) := candidate | return false
  unless ← isInputValue option do return false
  try
    let getter ← mkAppM ``Option.get #[option, proof]
    withoutModifyingState <| withNewMCtxDepth <| withDefault <| isDefEq container getter
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return false

/-- The terms of an estimate: its reference, budgets, proof and finiteness. -/
def Estimate.terms (estimate : Estimate) : Array Lean.Expr :=
  let reference : Lean.Expr := estimate.reference
  let budgets : Array Lean.Expr := match estimate.bound with
    | .absolute error => #[error]
    | .mixed relative absolute => #[relative, absolute]
  (#[reference] ++ budgets).push estimate.proof ++ estimate.finite?.toArray

/-- The estimate whose terms (`Estimate.terms`) are `terms`, with the bound of `estimate`. -/
def Estimate.withTerms (estimate : Estimate) (terms : Array Lean.Expr) : Estimate :=
  let bound := match estimate.bound with
    | .absolute _ => Bound.absolute terms[1]!
    | .mixed .. => .mixed terms[1]! terms[2]!
  let next := if bound matches .absolute _ then 2 else 3
  { reference := terms[0]!, bound, proof := terms[next]!, finite? := terms[next + 1]? }

/-- Apply `transform` to the terms of `estimates` at once, so that the parts they share are
transformed once. -/
def transformTerms (estimates : Array Estimate) (transform : Lean.Expr → MetaM Lean.Expr) :
    MetaM (Array Estimate) := do
  let terms := estimates.map (·.terms)
  let packed ← transform (mkAppN (.sort .zero) (terms.foldl (· ++ ·) #[]))
  let arguments := packed.getAppArgs
  let mut offset := 0
  let mut result := #[]
  for estimate in estimates, part in terms do
    result := result.push (estimate.withTerms (arguments.extract offset (offset + part.size)))
    offset := offset + part.size
  return result

namespace Analyze

/-- The least cost, in heartbeats, of an analysis whose estimate `keep` keeps for other scopes. -/
def keptCost : Nat := 2000000

/-- Keep the estimate of `actual`, which needs `fuel`, for other scopes (`Session.derivations`),
with the estimates its analysis cached since `added` and the obligations it left since `pending`.
Nothing is kept when a metavariable its proofs leave open is not a pending obligation. -/
def keep (actual : Q(ℝ)) (estimate : Estimate) (fuel pending added : Nat) : AnalyzeM Unit := do
  let session ← read
  let state ← get
  let parts := (state.added.extract added state.added.size).filterMap fun (mixed, term) =>
    ((if mixed then state.mixedCache else state.cache).get? term).map (mixed, term, ·)
  let estimates ← transformTerms (#[estimate] ++ parts.map (·.2.2)) instantiateMVars
  let terms := estimates.foldl (fun terms estimate => terms ++ estimate.terms) #[]
  if actual.hasMVar || terms.any (·.hasLevelMVar) then return
  let unassigned := (terms.foldl (fun state (term : Lean.Expr) => term.collectMVars state)
    ({} : CollectMVars.State)).result
  -- The obligations its analysis left, and the earlier pending ones its proofs use.
  let earlier := (state.pending.extract 0 pending).filter unassigned.contains
  let mut obligations := #[]
  for goal in earlier ++ state.pending.extract pending state.pending.size do
    if ← goal.isAssigned then continue
    if ← goal.isDelayedAssigned then return
    let type ← instantiateMVars (← goal.getType)
    if type.hasMVar then return
    obligations := obligations.push (goal, (← goal.getDecl).userName, type)
  unless unassigned.all fun goal => obligations.any (·.1 == goal) do return
  -- Most kept derivations are never reused, and collecting the local variables of their proofs
  -- is costly, so a reuse collects them when it first checks them.
  let locals := Thunk.mk fun _ => ((terms ++ obligations.map (·.2.2)).foldl
    (fun state term => collectFVars state term) (collectFVars {} actual)).fvarIds
  let some main := estimates[0]? | return
  let derivation : Derivation := {
    estimate := main, obligations, fuel, locals
    parts := (parts.zip (estimates.extract 1 estimates.size)).map fun ((mixed, term, _), part) =>
      (mixed, term, part)
    facts := (← session.scopeFacts actual) }
  session.derivations.modify fun derivations =>
    let key := (session.mode, actual)
    derivations.insert key ((derivations.getD key #[]).push derivation)

/-- An estimate of `actual` kept by `keep`, when its local variables and auxiliary constants
exist, the facts of the scopes about `actual` are those it was derived under, and it needs no
more fuel than there is. Its obligations that are no longer pending become pending again as
fresh goals, and the estimates of its parts are cached in this scope. -/
def reuse? (actual : Q(ℝ)) (fuel : Nat) : AnalyzeM (Option Estimate) := do
  let session ← read
  let some derivations := (← session.derivations.get).get? (session.mode, actual) | return none
  let context ← getLCtx
  let environment ← getEnv
  let mut facts? := none
  for derivation in derivations do
    unless derivation.fuel ≤ fuel && derivation.locals.get.all context.contains do continue
    let facts ← match facts? with
      | some facts => pure facts
      | none => session.scopeFacts actual
    facts? := some facts
    unless facts == derivation.facts do continue
    let estimates := #[derivation.estimate] ++ derivation.parts.map (·.2.2)
    -- An auxiliary lemma of a rolled-back attempt no longer exists. Each distinct subterm is
    -- visited once.
    let missing (term : Lean.Expr) := (term.find? fun child => match child with
      | .const name _ => name.isInternal && !environment.contains name
      | _ => false).isSome
    if estimates.any (·.terms.any missing) then continue
    -- An obligation still pending here, such as one of an enclosing scope, is shared, as a new
    -- analysis would share it; the others become pending again as fresh goals.
    let pending : Std.HashSet MVarId := .ofArray (← get).pending
    let mut goals : Std.HashMap MVarId Lean.Expr := {}
    for (goal, name, type) in derivation.obligations do
      if pending.contains goal then continue
      let fresh ← mkFreshExprMVar type (userName := name)
      goals := goals.insert goal fresh
      modify fun state => { state with pending := state.pending.push fresh.mvarId! }
    let renewed ← transformTerms estimates fun term => pure <| term.replace fun child =>
      if !child.hasMVar then some child
      else match child with
        | .mvar goal => goals.get? goal
        | _ => none
    for (mixed, term, _) in derivation.parts, part in renewed.extract 1 renewed.size do
      modify fun state =>
        let cache := if mixed then state.mixedCache else state.cache
        if cache.contains term then state
        else
          let state := { state with added := state.added.push (mixed, term) }
          if mixed then { state with mixedCache := cache.insert term part }
          else { state with cache := cache.insert term part }
    -- Its analyses count as below this one.
    session.leastFuel.modify (min · (fuel + 1 - derivation.fuel))
    return renewed[0]?
  return none

/-- Whether a failure with `failedFuel`, inside a loop's step when `failedNested`, can be reused for
an analysis with `fuel`, inside a step when `nested`: a failure inside a step may come from what a
step refuses, such as an agreement premise, so it is reused only inside a step. -/
def isFailureReusable (failedFuel : Nat) (failedNested : Bool) (fuel : Nat) (nested : Bool) : Bool :=
  fuel ≤ failedFuel && (!failedNested || nested)

/-- The error of an analysis of `actual` in this mode that failed with at least `fuel`, under the
facts of the scopes about `actual` that hold here (`Session.scopeFacts`), and outside a loop's step
unless this analysis is inside one. -/
def failedAnalysis? (actual : Q(ℝ)) (fuel : Nat) : AnalyzeM (Option Exception) := do
  let session ← read
  let some failed := (← session.analysisFailures.get).get? (session.mode, actual) |
    return none
  let facts ← session.scopeFacts actual
  return failed.findSome? fun (scope, failedFuel, failedNested, error) =>
    if isFailureReusable failedFuel failedNested fuel session.nested && scope == facts then some error
    else none

/-- Record that the analysis of `actual` in this mode failed with `fuel` and `error`, under the
facts of the scopes about `actual` that hold here, inside a loop's step or not. -/
def recordFailure (actual : Q(ℝ)) (fuel : Nat) (error : Exception) : AnalyzeM Unit := do
  let session ← read
  let facts ← session.scopeFacts actual
  let nested := session.nested
  session.analysisFailures.modify fun failures =>
    let key := (session.mode, actual)
    let failed := failures.getD key #[]
    if failed.any fun (scope, failedFuel, failedNested, _) =>
        scope == facts && isFailureReusable failedFuel failedNested fuel nested then failures
    else
      let kept := failed.filter fun (scope, failedFuel, failedNested, _) =>
        !(scope == facts && isFailureReusable fuel nested failedFuel failedNested)
      failures.insert key (kept.push (facts, fuel, nested, error))

/-- Analyze the real value `actual`: the shared result of the same computation in the same
scope, an estimate kept from another scope (`reuse?`), or a new one by `build`, kept when it was
costly. A computation whose analysis failed under the same facts of the scopes about it fails
again at once with no more fuel, and a failure inside a loop's step does so only inside a step. -/
def analyze (r : Recursor) (actual : Q(ℝ)) (fuel : Nat) : AnalyzeM Estimate := do
  let actual : Q(ℝ) ← instantiateMVars actual
  let actual : Q(ℝ) := stripHeadMetadata actual
  if actual.headBeta != actual then return ← r.analyze actual.headBeta fuel
  trace[roundoff] "analyze {actual.getAppFn.constName?.getD .anonymous}"
  (← read).leastFuel.modify (min · fuel)
  if fuel == 0 then throwError "roundoff: source expansion exceeded its traversal limit"
  let mixed := (← read).mixed
  let state ← get
  let cache := if mixed then state.mixedCache else state.cache
  if let some estimate := cache.get? actual then return estimate
  -- An analysis that failed under these facts fails again with no more fuel. Speculative
  -- attempts that need the same computation then stop at once instead of repeating it, also in
  -- a sibling scope that introduced other variables.
  if let some error ← failedAnalysis? actual fuel then throw error
  let reused? ← reuse? actual fuel
  let start ← IO.getNumHeartbeats
  let pending := (← get).pending.size
  let added := (← get).added.size
  -- The least fuel of the analyses below gives the fuel that the derivation needs.
  let outer ← (← read).leastFuel.swap fuel
  let depths ← depthsCaught
  let estimate ← match reused? with
    | some estimate => pure estimate
    | none => try r.build actual (fuel - 1) catch error => do
        (← read).leastFuel.modify (min outer)
        -- A failure after a caught recursion depth may not recur at a shallower depth.
        if (← depthsCaught) == depths then recordFailure actual fuel error
        throw error
  let least ← (← read).leastFuel.modifyGet fun least => (least, min outer least)
  if reused?.isNone && (← IO.getNumHeartbeats) - start ≥ keptCost then
    -- When an analysis below ran out of fuel, the derivation needs all of it again.
    keep actual estimate (if least == 0 then fuel else fuel + 1 - least) pending added
  modify fun state =>
    let state := { state with added := state.added.push (mixed, actual) }
    if mixed then { state with mixedCache := state.mixedCache.insert actual estimate }
    else { state with cache := state.cache.insert actual estimate }
  return estimate

/-- One analysis step for `actual`, below the shared caches: registered rules, control flow,
reads, loops, decoding, and the expansion of definitions. A hypothesis stated like a generated
theorem, the contract of a function the program takes, bounds the call against its model at the
computed argument. Its reference becomes the model at the exact argument when the analysis of that
reference propagates the argument's error through the model; it stays the model at the decoded
computed argument when the argument is exact data or the analysis has no rule for the model. -/
def build (r : Recursor) (actual : Q(ℝ)) (fuel : Nat) : AnalyzeM Estimate := do
  let mixed := (← read).mixed
  if let some (bound, final) ← givenBound? actual (r.analyze · fuel) (r.prove · fuel) then
    -- A contract, such as that of a function the program takes, bounds the call against its
    -- model at the computed argument. When the analysis reads that model, the argument's own
    -- error is propagated through it, so that the reference is the model at the exact argument.
    -- A model without a rule, such as a real function the program takes, keeps the computed
    -- argument: the bound holds, but the argument's own rounding is not part of it.
    if final || bound.reference == actual then return bound
    let some input ← speculate? (r.analyze bound.reference fuel) | do
      trace[roundoff] "contract reference kept at the computed argument: {bound.reference}"
      return bound
    if input.bound.isExact then return bound
    return ← (← read).simplify (← compose (← bound.inMode mixed) input)
  -- A loop that keeps a registered step relation, such as Kahan's, is read through it before its
  -- operations are taken apart.
  if let some estimate ← relationBound? actual then return estimate
  -- A cast count that computes to a numeral, such as the number of slices of a vector, is
  -- analyzed as that numeral, where exact rules apply.
  if mixed && actual.isAppOf ``ExecFloat.Binary.toReal then
    let cast := actual.getAppArgs.back!
    if cast.isAppOfArity ``Nat.cast 3 && cast.appArg!.nat?.isNone then
      let numeral? ← attempt? 1000 do
        let count ← withDefault (whnf cast.appArg!)
        return count.rawNatLit? <|> count.nat?
      if let some numeral := numeral? then
        let next : Q(ℝ) := mkAppN actual.getAppFn
          (actual.getAppArgs.pop.push (mkApp cast.appFn! (mkNatLit numeral)))
        return ← r.analyze next fuel
  let name := actual.getAppFn.constName?.getD .anonymous
  if mixed && realOperations.contains name then
    -- Each candidate rule needs the operands' estimates; derive them once, outside its trial.
    for argument in actual.getAppArgs do
      if (← withReducible (whnf (← inferType argument))).isConstOf ``Real &&
          argument.nat?.isNone then
        discard <| speculate? (r.analyze argument fuel)
  -- So do the exact and rounding rules of a configured operation, for its decoded operands,
  -- also behind a matcher or a projection such as that of a destructured pair.
  if mixed && name == ``ExecFloat.Binary.toReal then
    let source ← whnfCore actual.getAppArgs.back!
    if floatOperations.contains (source.getAppFn.constName?.getD .anonymous) then
      let observe := mkAppN actual.getAppFn actual.getAppArgs.pop
      let type ← inferType source
      for argument in source.getAppArgs do
        if ← withReducible (isDefEq (← inferType argument) type) then
          unless ← assumedFinite argument do
            discard <| speculate? (r.analyze (mkApp observe argument) fuel)
  let selected? ← registeredBound? actual (r.analyze · fuel) (r.prove · fuel)
  let selected? ← if selected?.isSome then pure selected? else
    splitBound? actual (r.analyze · fuel) (r.prove · fuel)
  let selected? ← if selected?.isSome then pure selected? else
    pure ((← primitiveBound? actual (r.analyze · fuel) (r.prove · fuel)).map fun bound =>
      (bound, false))
  let selected? ← if selected?.isSome then pure selected? else
    pure ((← intervalBound? actual).map fun bound => (bound, false))
  if let some (estimate, propagatesInputs) := selected? then
    let estimate ← estimate.inMode mixed
    if propagatesInputs || estimate.reference == actual then
      return ← (← read).simplify estimate
    let inputEstimate ← r.analyze estimate.reference fuel
    return ← (← read).simplify (← compose estimate inputEstimate)
  -- An observation of an input or a literal is exact as a real value. The rounding when that
  -- literal was encoded is not silently identified with its unrounded source spelling.
  let observed ← if (← read).observations.contains name then
      isScalarObservation (← read).containerFree actual
    else pure false
  let source ← instantiateMVars (if observed then actual.getAppArgs.back! else actual)
  let source := stripHeadMetadata source
  if source.headBeta != source then
    let next : Q(ℝ) := if observed then
        mkAppN actual.getAppFn (actual.getAppArgs.pop.push source.headBeta)
      else source.headBeta
    return ← r.analyze next fuel
  if source.isAppOfArity ``Option.get 3 then
    let (context, procedures) ← coordinateSimpContext (← read)
    let (normalized, _) ← simp actual context procedures
    if normalized.expr != actual then
      let estimate ← r.analyze normalized.expr fuel
      return ← rewriteSimp estimate actual source (mixed && observed) normalized context
        procedures
  let optionalValue? ← optionGet? source
  if source.isAppOfArity ``Option.get 3 && optionalValue?.isNone then
    throwError "roundoff: no numerical rule for optional producer {source.getAppArgs[1]!}; \
      expose its computation or supply an explicit bound"
  if let some (value, equality) := optionalValue? then
    let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
      else q(fun value : ℝ => value)
    let equality ← mkAppM ``congrArg #[observe, equality]
    let next : Q(ℝ) := (mkApp observe value).headBeta
    let estimate ← r.analyze next fuel
    return ← rewriteActual estimate equality
  if let some reduced ← reduceControl? (← read).containerProducers source then
    unless reduced == source do
      let next : Q(ℝ) := if observed then
          mkAppN actual.getAppFn (actual.getAppArgs.pop.push reduced)
        else reduced
      return ← r.analyze next fuel
  if let some (_, equality) ← optionMatch? source then
    let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
      else q(fun value : ℝ => value)
    let equality ← mkAppM ``congrArg #[observe, equality]
    let some (_, _, next) := (← inferType equality).eq? |
      throwError "roundoff: Option observation did not produce an equality"
    let estimate ← r.analyze next fuel
    return ← rewriteActual estimate equality
  if source.isAppOf ``cond ||
      ((source.isAppOf ``ite || source.isAppOf ``dite) && source.getAppNumArgs > 5) then
    let mut branches : SimpTheorems := {}
    for name in #[``Bool.cond_eq_ite, ``ite_apply, ``dite_apply] do
      branches ← branches.addConst name
    let context ← Simp.mkContext { implicitDefEqProofs := false } #[branches]
    let (normalized, _) ← simp actual context
    if normalized.expr != actual then
      let estimate ← r.analyze normalized.expr fuel
      return ← rewriteActual estimate (← normalized.getProof' actual)
  if name == ``FloatLib.Floats.Formats.BinaryInterchange.Model.toReal &&
      source.isAppOf ``FloatLib.Floats.ExecFloat.Binary.toModel then
    return ← r.analyze (← mkAppM ``FloatLib.Floats.ExecFloat.Binary.toReal
      #[source.getAppArgs.back!]) fuel
  if (← isReduction source) || (← extension).loops.any (source.isAppOf ·.fold) ||
      (mixed && (← isExactSum source)) then
    let (context, procedures) ← foldSimpContext (← read)
    let normalized ← (← read).normalize `fold actual context procedures
    if normalized.expr != actual then
      let estimate ← r.analyze normalized.expr fuel
      return ← rewriteSimp estimate actual source (mixed && observed) normalized context
        procedures
    if let some loop ← loopOf? source then
      let args := source.getAppArgs
      let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
        else q(fun value : ℝ => value)
      let step := args[loop.step]!
      let initial := args[loop.initial]!
      let input := args[loop.input]!
      let element := args[loop.element]!
      let state := args[loop.state]!
      -- A computed container must expose its producer at each coordinate. Otherwise its
      -- already-rounded entries would silently become the inputs of the real reference.
      -- Mixed analysis also reads stored inputs by coordinate, so facts about their entries,
      -- such as signs, apply to each visited value.
      if let some (coordinates, traversalLaw) := loop.coordinates then
        unless input.isAppOf coordinates || (!mixed && (← isInputValue input)) do
          let traversal ← mkAppM traversalLaw #[step, initial, input]
          let equality ← mkAppM ``congrArg #[observe, traversal]
          let some (_, _, next) := (← inferType equality).eq? |
            throwError "roundoff: coordinate traversal did not produce an observation equality"
          let estimate ← r.analyze next fuel
          return ← if mixed then rewriteValue estimate observe traversal
            else rewriteActual estimate equality
      -- Otherwise the step is analyzed at a fresh entry, which is exact data, so a container that
      -- does not store inputs is first fused into the step by the loop's laws. The loop analysis
      -- rejects a step whose reference still reads such a container's entries.
      unless loop.fusions.isEmpty || (← storedEntries loop input (← read).carriers) do
        let context ← fusionSimpContext loop
        let (normalized, _) ← simp actual context
        -- A change only up to reducible unfolding, such as the spelling of a numeral that the fold
        -- normalizer writes the other way, fuses nothing and would repeat without end.
        let fused ← pure (normalized.expr != actual) <&&>
          withNewMCtxDepth (return !(← withReducible (isDefEq normalized.expr actual)))
        if fused then
          let estimate ← r.analyze normalized.expr fuel
          return ← rewriteSimp estimate actual source (mixed && observed) normalized context #[]
        -- A producer whose definition is such an operation, such as a map, is unfolded first,
        -- when the fused loop then traverses stored or index entries. A library producer such as
        -- `List.zip` would otherwise unfold and fuse back without end.
        if let some producer ← unfoldDefinition? input then
          let unfolded := mkAppN source.getAppFn (args.set! loop.input producer.headBeta)
          let next : Q(ℝ) := if observed then
              mkAppN actual.getAppFn (actual.getAppArgs.pop.push unfolded)
            else unfolded
          let fused := (← simp next context).1.expr
          let fusedLoop := if observed then fused.getAppArgs.back?.getD fused else fused
          if fused != next && fusedLoop.isAppOfArity loop.fold loop.arity then
            if ← storedEntries loop fusedLoop.getAppArgs[loop.input]! (← read).carriers then
              return ← r.analyze next fuel
      if mixed then
        if let some estimate ← speculate? (r.singleFold loop observe step initial input element
            state fuel) then
          return estimate
        -- Both strategies analyze the step at one element variable, so that the costly parts that
        -- do not depend on the accumulator are derived once (`reuse?`).
        let carried? ← withLocalDeclD `value element fun value => do
          if let some estimate ← speculate? (r.constantFold loop observe step initial value state
              source fuel) then
            return some estimate
          speculate? (r.mixedFold loop observe step initial input value state fuel)
        if let some estimate := carried? then return estimate
        -- Without a relational invariant the loop keeps its absolute analysis.
        let estimate ← withReader ({ · with mixed := false }) (r.analyze actual fuel)
        return ← estimate.inMode true
      return ← r.absoluteFold loop observe step initial input element state fuel
    -- A loop written another way, such as over an array, is analyzed as its registered loop.
    unless (← extension).conversions.isEmpty do
      let context ← conversionSimpContext
      let (normalized, _) ← simp actual context
      if normalized.expr != actual then
        let estimate ← r.analyze normalized.expr fuel
        return ← rewriteSimp estimate actual source (mixed && observed) normalized context #[]
  if source.isAppOfArity ``ite 5 || source.isAppOfArity ``dite 5 then
    let args := source.getAppArgs
    let condition : Q(Prop) := args[1]!
    let observe ← if observed then
        pure (mkAppN actual.getAppFn actual.getAppArgs.pop)
      else pure q(fun value : ℝ => value)
    -- Evidence for the guard or its negation makes the other branch unreachable. Keep the
    -- source's decision procedure and, for dependent branches, its actual proof argument.
    let select (positive : Bool) (evidence : Lean.Expr) : AnalyzeM Estimate := do
      let rule := if source.isAppOfArity ``dite 5 then
          if positive then ``dite_eq_left else ``dite_eq_right
        else if positive then ``ite_eq_left else ``ite_eq_right
      let equality ← mkAppOptM rule #[some args[1]!, some args[2]!,
        some evidence, some args[0]!, some args[3]!, some args[4]!]
      check equality .default
      let some (_, _, next) := (← inferType equality).eq? |
        throwError "roundoff: conditional reduction did not produce an equality"
      -- The selected case's finiteness is the branch's.
      let estimate ← r.analyze (mkApp observe next).headBeta fuel
      rewriteValue estimate observe equality
    if let some (positive, evidence) ← guardEvidence? (← read) condition then
      return ← select positive evidence
    if let some evidence ← refutedGuard? condition then
      return ← select false evidence
    let branch (guard value : Lean.Expr) : MetaM Lean.Expr := do
      if source.isAppOfArity ``dite 5 then return value
      withLocalDeclD `branch guard fun evidence => mkLambdaFVars #[evidence] value
    let yes ← branch condition args[3]!
    let no ← branch q(¬$condition) args[4]!
    -- In mixed analysis each case also proves its decoded value finite, so that the branch
    -- is finite when both cases are.
    let analyzeCase (value : Lean.Expr) : AnalyzeM Estimate := do
      let observed : Q(ℝ) := (mkApp observe value).headBeta
      let estimate ← r.analyze observed fuel
      unless mixed && estimate.finite?.isNone && observed.isAppOf ``ExecFloat.Binary.toReal do
        return estimate
      let some decoded := decodedValue? observed | return estimate
      let goal ← mkFreshExprMVar (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[decoded])
        (mkConst ``Bool.true))
      unless ← r.proveFinite goal.mvarId! fuel do return estimate
      return { estimate with finite? := some (← instantiateMVars goal) }
    let yesBranch ← inBranch condition fun guard => analyzeCase (mkApp yes guard).headBeta
    let noBranch ← inBranch q(¬$condition) fun guard => analyzeCase (mkApp no guard).headBeta
    let proof ← match yesBranch.bound, noBranch.bound with
      | .absolute yesError, .absolute noError =>
          mkAppOptM ``dite_error #[none, some observe, some condition, some args[2]!,
            some yes, some no, some yesBranch.reference, some yesError, some noBranch.reference,
            some noError, some yesBranch.proof, some noBranch.proof]
      | .mixed yesRelative yesAbsolute, .mixed noRelative noAbsolute =>
          mkAppOptM ``mixedError_dite #[none, some observe, some condition, some args[2]!,
            some yes, some no, some yesBranch.reference, some yesRelative, some yesAbsolute,
            some noBranch.reference, some noRelative, some noAbsolute, some yesBranch.proof,
            some noBranch.proof]
      | _, _ => throwError "roundoff: branches were analyzed in different modes"
    let type : Q(Prop) ← instantiateMVars (← inferType proof)
    let some (_, reference, bound) ← boundConclusion? type |
      throwError "roundoff: unexpected branch proof type {type}"
    -- A branch is finite when both of its cases are.
    let finite? ← match yesBranch.finite?, noBranch.finite?, decodedValue? actual with
      | some yesFinite, some noFinite, some value => do
          let motive ← withLocalDeclD `value (← inferType value) fun other => do
            mkLambdaFVars #[other] (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[other])
              (mkConst ``Bool.true))
          let combined? ← attempt? 1000 do
            let proof ← mkAppOptM ``dite_of_forall #[none, some motive, some condition,
              some args[2]!, some yes, some no, some yesFinite, some noFinite]
            return if ← isDefEq (← inferType proof) (mkApp motive value).headBeta then
              some proof else none
          pure combined?
      | _, _, _ => pure none
    -- A budget that both cases share, independent of their guard, is left undivided.
    return ← (← read).simplify (← (← read).zeroBudget ⟨reference, bound, proof, finite?⟩)
  if let .letE _ _ value body _ := source then
    let source := body.instantiate1 value
    let next : Q(ℝ) := if observed then
        mkAppN actual.getAppFn (actual.getAppArgs.pop.push source)
      else source
    return ← r.analyze next fuel
  if source.isFVar then
    if let some value := (← source.fvarId!.getDecl).value? then
      -- Canonical real literals need no source expansion. Floating-point conversions are
      -- analyzed below, including when their result has a local name.
      if ← literalInput? actual value then
        return ← exactEstimate mixed actual
      let next : Q(ℝ) := if observed then
          mkAppN actual.getAppFn (actual.getAppArgs.pop.push value)
        else value
      return ← r.analyze next fuel
    return ← exactEstimate mixed actual
  -- An entry of a stored function, such as a vector on `Fin n` or a matrix, is exact data when it
  -- is read at index data.
  if ← isAppliedInput source then
    unless ← source.getAppArgs.allM (indexClosed · (cache? := (← read).carriers)) do
      throwError "roundoff: {source} reads a stored input at an index computed from numerical \
        values, so the reference would keep them"
    return ← exactEstimate mixed actual
  let sourceName := source.getAppFn.constName?.getD .anonymous
  -- A generated callback may use the flat getter. Recover its coordinate observation before
  -- generic source expansion can expose the selected storage's raw read method.
  for (getter, arity, law) in (← extension).readRecoveries do
    unless source.isAppOfArity' getter arity do continue
    let some (value, equality) ← readObservation? law source |
        throwError "roundoff: could not recover the original tensor observation in {source}"
      let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
        else q(fun value : ℝ => value)
      let equality ← mkAppM ``congrArg #[observe, equality]
      let next : Q(ℝ) := (mkApp observe value).headBeta
      let estimate ← r.analyze next fuel
      return ← rewriteActual estimate equality
  if let some entry := (← extension).reads.find? fun read =>
      source.isAppOf read.head && read.selects source then
    let position := source.getAppNumArgs - entry.fromEnd
    let container := source.getAppArgs[position]!
    let containerType ← withDefault (whnf (← inferType container))
    -- Normalize the receiver's type so ordinary aliases are accepted without evaluating
    -- its stored values. General function coercions follow source analysis below.
    if entry.types.any containerType.isAppOf then
      let (context, procedures) ← coordinateSimpContext (← read)
      let normalized ← (← read).normalize `coordinate actual context procedures
      if normalized.expr != actual then
        let estimate ← r.analyze normalized.expr fuel
        return ← rewriteSimp estimate actual source (mixed && observed) normalized context
          procedures
      -- Its index is not checked, as a tensor read at an index chosen by comparing stored values,
      -- such as the pivot of a log-softmax, needs; an index computed from rounded values would
      -- keep that choice in the reference. The value of an input option is an input container.
      if (← isInputValue container) || (← isInputOptionGet container) then
        return ← exactEstimate mixed actual
      -- Producers are analyzed through reads whose container is followed by the index only.
      unless position + 2 == source.getAppNumArgs do
        throwError "roundoff: no numerical rule for tensor producer {container}; expose its \
          computation or supply an explicit bound"
      -- A loop that computes a container is analyzed on the read coordinate of its accumulator,
      -- which its steps may read and update there only. A step choosing its update by an
      -- Option match is split like a scalar match.
      let readAt ← withLocalDeclD `tensor (← inferType container) fun value => do
        let read := mkAppN source.getAppFn (source.getAppArgs.set! position value)
        mkLambdaFVars #[value] (if observed then
          mkAppN actual.getAppFn (actual.getAppArgs.pop.push read) else read)
      let splitOption : AnalyzeM (Option Estimate) := do
        let some (_, equality) ← optionMatch? container | return none
        let equality ← mkCongrArg readAt equality
        let some (_, _, next) := (← inferType equality).eq? |
          throwError "roundoff: Option observation did not produce an equality"
        return some (← rewriteActual (← r.analyze next.headBeta fuel) equality)
      if (← read).containerLoop then
        if let some estimate ← splitOption then return estimate
      if (← loopOf? container).isSome || container.isAppOf ``List.foldl ||
          container.isAppOf ``Fin.foldl then
        return ← r.containerFold readAt container fuel
      -- A producer kept folded on a shape that is not literal is read by its registered read.
      let producer := containerProducer container
      for (_, rule) in (← read).reads.filter (·.1 == producer) do
        if let some (value, equality) ← readObservation? rule source then
          if ← rereads producer container value then continue
          let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
            else q(fun value : ℝ => value)
          let estimate ← r.analyze (mkApp observe value).headBeta fuel
          if observed then return ← rewriteValue estimate observe equality
          return ← rewriteActual estimate (← mkAppM ``congrArg #[observe, equality])
      -- Expose the producer while retaining its container read. A stalled producer must not
      -- unfold into storage access and hide the computation that created its entries.
      if let some producer ← unfoldDefinition? container then
        unless producer == container do
          let arguments := source.getAppArgs.set! position producer
          let source := mkAppN source.getAppFn arguments
          let next : Q(ℝ) := if observed then
              mkAppN actual.getAppFn (actual.getAppArgs.pop.push source)
            else source
          return ← r.analyze next fuel
      for fallback in (← extension).readFallbacks do
        if let some (value, equality) ← readObservation? fallback source then
          let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
            else q(fun value : ℝ => value)
          let equality ← mkAppM ``congrArg #[observe, equality]
          let next : Q(ℝ) := (mkApp observe value).headBeta
          let estimate ← r.analyze next fuel
          return ← rewriteActual estimate equality
      -- A registered restatement may still expose the producer, such as one whose definition is
      -- stuck on a length and reduces at `k - 1 + 1`, where the read coordinate shows `0 < k`.
      if observed then
        if let some (next, observe, equality) ← restate? actual then
          return ← rewriteValue (← r.analyze next fuel) observe equality
      -- Elsewhere a producer choosing by an Option match whose discriminant does not compute, such
      -- as an optional mask, is read in each case.
      if let some estimate ← splitOption then return estimate
      throwError "roundoff: no numerical rule for tensor producer {container}; expose its \
        computation or supply an explicit bound"
  -- The value a checked loop computes beside its flags is the loop of that value alone.
  if let some (next, equality) ← projectLoop? source then
    let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
      else q(fun value : ℝ => value)
    let estimate ← r.analyze (mkApp observe next).headBeta fuel
    if observed then return ← rewriteValue estimate observe equality
    return ← rewriteActual estimate (← mkAppM ``congrArg #[observe, equality])
  -- A value read from a loop whose state is a tuple is a conjunct of the loop's relation. A loop
  -- written another way, such as over an array, is first written as its registered loop.
  if observed then
    if let some (base, path) ← Tuple.projection? source then
      let base ← instantiateMVars base
      if let some loop ← loopOf? base then
        if loop.relation.isSome then
          unless loop.fusions.isEmpty ||
              (← storedEntries loop base.getAppArgs[loop.input]! (← read).carriers) do
            let context ← fusionSimpContext loop
            let (normalized, _) ← simp actual context
            let fused ← pure (normalized.expr != actual) <&&>
              withNewMCtxDepth (return !(← withReducible (isDefEq normalized.expr actual)))
            if fused then
              let estimate ← r.analyze normalized.expr fuel
              return ← rewriteSimp estimate actual source mixed normalized context #[]
          return ← tupleFold r loop (mkAppN actual.getAppFn actual.getAppArgs.pop) base path
            actual fuel
      else if (← isReduction base) && !(← extension).conversions.isEmpty then
        let context ← conversionSimpContext
        let (normalized, _) ← simp actual context
        if normalized.expr != actual then
          let estimate ← r.analyze normalized.expr fuel
          return ← rewriteSimp estimate actual source mixed normalized context #[]
  if let .proj .. := source.getAppFn then
    if ← isInputValue source then
      return ← exactEstimate mixed actual
    -- Helpers returning a record or tuple retain their original control flow. Reuse the
    -- proved source normalizer when that helper appears after earlier scalar unfolding.
    let (context, procedures) ← coordinateSimpContext (← read)
    let normalized ← (← read).normalize `coordinate actual context procedures
    if normalized.expr != actual then
      let estimate ← r.analyze normalized.expr fuel
      return ← rewriteSimp estimate actual source (mixed && observed) normalized context
        procedures
    if let some implementation ← withReducibleAndInstances (reduceProj? source.getAppFn) then
      let source := (mkAppN implementation source.getAppArgs).headBeta
      let next : Q(ℝ) := if observed then
          mkAppN actual.getAppFn (actual.getAppArgs.pop.push source)
        else source
      return ← r.analyze next fuel
  -- Casts may observe a complete loop or container computation, handled above. Otherwise only
  -- canonical real literals and exact discrete-to-real casts remain data.
  if ← exactRealData? actual (← read).carriers then
    return ← exactEstimate mixed actual
  if ← literalInput? actual source then
    return ← exactEstimate mixed actual
  -- The cast of an integer computed from numerical values, such as the numerator of a rounded
  -- value or a count of tests of rounded values, would keep them in the reference.
  if let some integer ← castInteger? actual then
    unless ← indexClosed integer (cache? := (← read).carriers) do
      throwError "roundoff: {actual} casts an integer computed from real or floating-point \
        values, so the reference would keep them; compute it from index data"
  if name == ``FloatLib.Floats.ExecFloat.Binary.toReal ||
      name == ``Rat.cast || name == ``RatCast.ratCast then
    let (context, procedures) ← decodingSimpContext (← read)
    let normalized ← (← read).normalize `decoding actual context procedures
    trace[roundoff] "decoded observation: {normalized.expr}"
    -- Merely unfolding the observer makes no progress if the operation was not decoded.
    let decoded := normalized.expr.getAppArgs.back?.all fun value =>
      !value.isAppOf ``FloatLib.Floats.ExecFloat.Binary.toModel
    if decoded && normalized.expr != actual then
      let estimate ← r.analyze normalized.expr fuel
      return ← rewriteActual estimate (← normalized.getProof' actual)
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Neg.neg].contains sourceName then
    -- An operation fails for the reason the analysis of one of its operands did.
    let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
      else q(fun value : ℝ => value)
    for operand in source.getAppArgs do
      if let some error ← failedAnalysis? (mkApp observe operand).headBeta 0 then throw error
    throwError "roundoff: no proved arithmetic rule matches the selected implementation in \
      `{sourceName}`"
  -- A scalar method can select an implementation through several nested dictionaries.
  -- Expose that selected field, including FloatLib interfaces, before interpreting its code.
  if (← getProjectionFnInfo? sourceName).isSome then
    let implementation? ← unfoldProjInst? source
    let implementation? ← if implementation?.isSome then pure implementation?
      else unfoldDefinition? source
    if let some implementation := implementation? then
      unless implementation == source do
        let next : Q(ℝ) := if observed then
            mkAppN actual.getAppFn (actual.getAppArgs.pop.push implementation)
          else implementation
        return ← r.analyze next fuel
  -- A scalar producer with a registered observation is read through it, as it is inside a
  -- container read, before its definition is expanded. The value keeps its finiteness.
  if (← read).boundaries.contains sourceName then
    let (context, procedures) ← coordinateSimpContext (← read)
    if observed then
      let value ← (← read).normalize `coordinate source context procedures
      if value.expr != source then
        let observe := mkAppN actual.getAppFn actual.getAppArgs.pop
        let estimate ← r.analyze (mkApp observe value.expr) fuel
        return ← rewriteValue estimate observe (← value.getProof' source)
    else
      let normalized ← (← read).normalize `coordinate actual context procedures
      if normalized.expr != actual then
        return ← rewriteActual (← r.analyze normalized.expr fuel) (← normalized.getProof' actual)
  -- Expanding a user definition preserves its exact arithmetic. Unsupported library primitives
  -- are rejected before exposing their implementation or dispatch dictionaries. The definition
  -- of a real primitive, through complex numbers or orders, has no numerical rule either.
  let primitive := [``Real.exp, ``Real.log, ``Real.sqrt].contains sourceName
  unless (`FloatLib).isPrefixOf sourceName || primitive do
    if let some unfolded ← unfoldDefinition? source then
      let unfolded := headZeta unfolded
      unless unfolded == source do
        let next : Q(ℝ) := if observed then
            mkAppN actual.getAppFn (actual.getAppArgs.pop.push unfolded)
          else unfolded
        return ← r.analyze next fuel
  -- A function the analysis cannot expose, applied to a branch, is analyzed in each case.
  if let some (next, equality) ← branchArgument? source then
    let observe := if observed then mkAppN actual.getAppFn actual.getAppArgs.pop
      else q(fun value : ℝ => value)
    let equality ← mkAppM ``congrArg #[observe, equality]
    let estimate ← r.analyze (mkApp observe next).headBeta fuel
    return ← rewriteActual estimate equality
  -- A real primitive with no rule here fails for the reason the analysis of its operand did.
  if primitive then
    for operand in source.getAppArgs do
      if let some error ← failedAnalysis? operand 0 then throw error
  throwError "roundoff: no numerical rule for {source}; expose its arithmetic or supply an \
    explicit bound in the context"

/-- The analysis, each function reaching the others through the record. -/
partial def recursor (_ : Unit) : Recursor where
  build a0 a1 := build (recursor ()) a0 a1
  prove a0 a1 := prove (recursor ()) a0 a1
  proveNormalized a0 a1 := proveNormalized (recursor ()) a0 a1
  proveForall a0 a1 := proveForall (recursor ()) a0 a1
  proveNonzero a0 a1 := proveNonzero (recursor ()) a0 a1
  enclosedNonzero a0 a1 := enclosedNonzero (recursor ()) a0 a1
  proveRange a0 a1 := proveRange (recursor ()) a0 a1
  rangeByBounds a0 a1 := rangeByBounds (recursor ()) a0 a1
  proveFinite a0 a1 := proveFinite (recursor ()) a0 a1
  deriveFinite a0 a1 := deriveFinite (recursor ()) a0 a1
  exactAnalysis a0 a1 := exactAnalysis (recursor ()) a0 a1
  proveSelection a0 a1 := proveSelection (recursor ()) a0 a1
  proveSign a0 a1 a2 := proveSign (recursor ()) a0 a1 a2
  proveSignCore a0 a1 a2 := proveSignCore (recursor ()) a0 a1 a2
  branchSign a0 a1 a2 a3 := branchSign (recursor ()) a0 a1 a2 a3
  foldSign a0 a1 a2 a3 := foldSign (recursor ()) a0 a1 a2 a3
  relativeSign a0 a1 a2 a3 := relativeSign (recursor ()) a0 a1 a2 a3
  primitiveSign a0 a1 a2 a3 := primitiveSign (recursor ()) a0 a1 a2 a3
  roundingSign a0 a1 a2 a3 a4 := roundingSign (recursor ()) a0 a1 a2 a3 a4
  absoluteFold a0 a1 a2 a3 a4 a5 a6 a7 := absoluteFold (recursor ()) a0 a1 a2 a3 a4 a5 a6 a7
  containerFold a0 a1 a2 := containerFold (recursor ()) a0 a1 a2
  mixedFold a0 a1 a2 a3 a4 a5 a6 a7 := mixedFold (recursor ()) a0 a1 a2 a3 a4 a5 a6 a7
  singleFold a0 a1 a2 a3 a4 a5 a6 a7 := singleFold (recursor ()) a0 a1 a2 a3 a4 a5 a6 a7
  singleFoldAt a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :=
    singleFoldAt (recursor ()) a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  constantFold a0 a1 a2 a3 a4 a5 a6 a7 := constantFold (recursor ()) a0 a1 a2 a3 a4 a5 a6 a7
  exactStart a0 a1 a2 a3 a4 a5 := exactStart (recursor ()) a0 a1 a2 a3 a4 a5
  exactStepCase a0 a1 a2 a3 a4 a5 a6 a7 a8 := exactStepCase (recursor ()) a0 a1 a2 a3 a4 a5 a6 a7 a8
  liftLoopObligations a0 a1 a2 a3 := liftLoopObligations a0 a1 a2 a3
  analyze a0 a1 := analyze (recursor ()) a0 a1

end Analyze

/-- The analysis of `Analyze`, its parts tied together. -/
def analysis : Recursor := Analyze.recursor ()

/-- Analyze the real value `actual`, with at most `fuel` nested source expansions. -/
def analyze (actual : Q(ℝ)) (fuel : Nat := 256) : AnalyzeM Estimate :=
  analysis.analyze actual fuel

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
