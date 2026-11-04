/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Analyze

/-!
# The `roundoff` tactic

`roundoff` decodes an exact equality, derives an absolute or mixed error bound, or proves a
finiteness, decoded-value or sign property of a computed result. Container reads are normalized
first, loops are written as their registered traversals, and the obligations the analysis leaves
become goals. A mixed or property target keeps one goal per proposition (`deduplicate`), while an
absolute-error target lists its obligations as they arose, possibly with repeats. A generated
theorem states each condition once.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Exact decoding uses FloatLib's existing operation equalities, the registered decoding lemmas and
the laws of complete sums of configured values. A higher-order fold rule transports arbitrary
scalar steps, so reductions need no per-layer decoding specifications. -/
def decode : TacticM Unit := do
  let environment ← getEnv
  let sums := (← extension).sums.filter fun sum => !sum.exact && !sum.entries
  let laws := sums.flatMap (·.laws) |>.filter (environment.contains ·.1)
  let names := sums.filterMap (fun sum => if sum.laws.isEmpty then some sum.head else none) ++
    #[``MathFunctions.exp, ``MathFunctions.log, ``MathFunctions.abs,
    ``FloatLib.Floats.ExecFloat.Binary.toRat?,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_hAdd,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_hSub,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_hMul,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_hDiv,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_neg,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_abs,
    ``FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded.toModel_exp,
    ``FloatLib.Floats.ExecFloat.Binary.CorrectlyRounded.toModel_log,
    ``FloatLib.Floats.ExecFloat.Binary.toModel_ofModel] ++ (← extension).decodeLemmas
  let lemmas ← (names.filter environment.contains).mapM fun name =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident)
  let lemmas := lemmas ++ (← laws.mapM fun (name, inverse) =>
    if inverse then `(Lean.Parser.Tactic.simpLemma| ← $(mkIdent name):ident)
    else `(Lean.Parser.Tactic.simpLemma| $(mkIdent name):ident))
  evalTactic (← `(tactic| simp (config := {
        implicitDefEqProofs := false, failIfUnchanged := false }) only
          [$lemmas,*, apply_ite FloatLib.Floats.ExecFloat.Binary.toModel]))

/-- The targets mixed analysis proves about a computed value. -/
inductive Property where
  /-- `MixedError actual reference relative absolute`, possibly preceded by the finiteness of the
  value that `actual` decodes: `isFinite value = true ∧ MixedError (toReal value) …`. -/
  | mixed
  /-- `isFinite value = true`. -/
  | finite
  /-- `toRat? value = some q`. -/
  | decoded
  /-- `0 ≤ x` or `x ≤ 0`. -/
  | sign
  /-- `0 < x`. -/
  | positive
  /-- `x < 0`. -/
  | negative
  /-- `x ≠ 0`. -/
  | nonzero

/-- Classify a target of mixed analysis. -/
def property? (target : Lean.Expr) : MetaM (Option Property) := do
  let target := target.consumeMData
  if target.isAppOfArity ``MixedError 4 then return some .mixed
  if let some (finite, bound) := finiteMixed? target then
    if decodedValue? bound.getAppArgs[0]! == some finite.getAppArgs[1]!.getAppArgs.back! then
      return some .mixed
  if isFiniteness target then return some .finite
  if target.isAppOfArity ``Eq 3 && target.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.toRat? &&
      target.getAppArgs[2]!.isAppOfArity ``Option.some 2 then return some .decoded
  -- An absolute-error target keeps its own analysis, including a zero budget.
  if (← errorConclusion? target).isSome then return none
  let proposition : Q(Prop) ← pure target
  match proposition with
  | ~q(0 ≤ ($_x : ℝ)) => return some .sign
  | ~q(($_x : ℝ) ≤ 0) => return some .sign
  | ~q(0 < ($_x : ℝ)) => return some .positive
  | ~q(($_x : ℝ) < 0) => return some .negative
  | ~q(($_x : ℝ) ≠ 0) => return some .nonzero
  | _ => return none

/-- The value whose sign `target` states: `x` in `0 ≤ x`, `x ≤ 0`, `0 < x`, `x < 0` or `x ≠ 0`. -/
def signedValue? (target : Lean.Expr) : Option Lean.Expr :=
  if target.isAppOfArity ``Ne 3 then some target.getAppArgs[1]!
  else if target.isAppOfArity ``LE.le 4 || target.isAppOfArity ``LT.lt 4 then
    let (left, right) := (target.getAppArgs[2]!, target.getAppArgs[3]!)
    if left.nat? == some 0 then some right
    else if right.nat? == some 0 then some left else none
  else none

/-- Keep one goal per proposition and local context. Later duplicates are closed by the first. -/
def deduplicate (goals : List MVarId) : MetaM (List MVarId) := do
  let mut kept : Array (MVarId × Lean.Expr) := #[]
  for goal in goals do
    if ← goal.isAssigned then continue
    let type ← instantiateMVars (← goal.getType)
    let context := (← goal.getDecl).lctx
    if let some (earlier, _) := ← kept.findM? fun (earlier, earlierType) => do
        return earlierType == type && (← earlier.getDecl).lctx.getFVarIds == context.getFVarIds
    then
      goal.assign (mkMVar earlier)
    else kept := kept.push (goal, type)
  return (kept.map (·.1)).toList

/-- The obligations among `goals` that the proof of `goal` uses. Speculative analysis of an
operand can leave obligations that the chosen proof does not need, such as the range conditions of
a factor whose product with an exact zero is exact. -/
def usedObligations (goal : MVarId) (goals : List MVarId) : MetaM (List MVarId) := do
  let used ← getMVars (mkMVar goal)
  return goals.filter used.contains

/-- A proof of the sign `target` of a value from its analysis with correctly rounded calls kept as
computed values, whose contracts may give the sign of the reference. An exact value has the sign
of its reference, and a purely relative error below one keeps a strict sign. Only a proof that
leaves no obligation is returned. -/
def signByCalls? (session : Session) (target : Lean.Expr) :
    TacticM (Option Lean.Expr) := do
  let some actual := signedValue? target | return none
  let session := { session with computedCalls := true }
  let run {α : Type} (action : AnalyzeM α) (state : Analysis) : TacticM (α × Analysis) :=
    (action.run session).run state
  let (estimate, state) ← run (analyze actual) {}
  let .mixed relative absolute := estimate.bound | return none
  let strict := !target.isAppOfArity ``LE.le 4
  unless state.pending.isEmpty && (estimate.bound.isExact || strict && absolute.nat? == some 0) do
    return none
  let motive := Lean.mkLambda `value .default q(ℝ) (← kabstract target actual)
  let sign ← mkFreshExprMVar (motive.bindingBody!.instantiate1 estimate.reference)
  -- The local equalities may give the value of an input of the reference.
  let mut state := state
  if let some tidied ← session.tidy sign.mvarId! (hypotheses := true) then
    let (proved, next) ← run (analysis.proveSign tidied 256 signDepth) state
    unless proved do return none
    state := next
  if estimate.bound.isExact then
    unless state.pending.isEmpty do return none
    return some (← mkEqMPR (← mkCongrArg motive (← exactEquality estimate.proof))
      (← instantiateMVars sign))
  let below ← mkFreshExprMVar q($relative < 1)
  let (proved, next) ← run (analysis.proveSign below.mvarId! 256 signDepth) state
  unless proved && next.pending.isEmpty do return none
  let conclude := if target.isAppOfArity ``Ne 3 then ``MixedError.ne_zero_of_ne_zero
    else if (target.getAppArgs[2]!).nat? == some 0 then ``MixedError.pos_of_pos
    else ``MixedError.lt_zero_of_lt_zero
  return some (← mkAppM conclude #[estimate.proof, ← instantiateMVars below,
    ← instantiateMVars sign])

/-- Prove a property target by mixed analysis, returning the obligations it leaves. Finiteness
and range conditions concern the inputs. A mixed bound's budget comparison and a strict sign's
margin stay goals when they are not proved. -/
def proveProperty (session : Session) (property : Property) (goal : MVarId) :
    TacticM (List MVarId) := goal.withContext do
  let session ← session.index (mixed := true)
  let target : Q(Prop) ← instantiateMVars (← goal.getType)
  let runWith {α : Type} (session : Session) (action : AnalyzeM α) (state : Analysis := {}) :
      TacticM (α × Analysis) :=
    (action.run session).run state
  let run {α : Type} (action : AnalyzeM α) (state : Analysis := {}) : TacticM (α × Analysis) :=
    runWith session action state
  let close (condition : MVarId) : TacticM (List MVarId) := do
    let some condition ← session.tidy condition | return []
    if ← discharge session condition then return []
    -- Concrete formats evaluate their unit roundoff and underflow allowance.
    let evaluated? ← attempt? 2000 do
      let remaining ← Lean.Elab.Tactic.run condition do
        evalTactic (← `(tactic| norm_num [Model.unitRoundoffAt_eq, Model.underflowErrorAt_eq,
          FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent,
          FloatFormat.Encoding.defaultBias, FloatFormat.ieeeBias]))
      return if remaining.isEmpty then some () else none
    return if evaluated?.isSome then [] else [condition]
  match property with
  | .finite =>
      -- The value's own analysis establishes its finiteness, including through loops. Its
      -- loops are first normalized as a floating-point value, so the finiteness transfers back.
      -- With correctly rounded calls kept as computed values, the exact operations may show it
      -- finite under no condition; otherwise their roundings are analyzed.
      let observed := target.getAppArgs[1]!
      if observed.isAppOf ``ExecFloat.Binary.isFinite then
        let value := observed.getAppArgs.back!
        let (context, procedures) ← foldSimpContext session
        let (normalized, _) ← simp value context procedures
        let decoded ← mkAppM ``ExecFloat.Binary.toReal #[normalized.expr]
        for computedCalls in [true, false] do
          let saved ← saveState
          let (estimate?, state) ← runWith { session with computedCalls }
            (speculate? (analyze decoded))
          if let some estimate := estimate? then
            let normalizedGoal ← mkFreshExprMVar (← mkEq (mkAppN observed.getAppFn
              (observed.getAppArgs.pop.push normalized.expr)) (mkConst ``Bool.true))
            if (← estimate.closeFinite normalizedGoal.mvarId!) &&
                (!computedCalls || state.pending.isEmpty) then
              let transport ← mkCongrArg (← withLocalDeclD `value (← inferType value)
                fun other => do
                  mkLambdaFVars #[other] (← mkEq (mkAppN observed.getAppFn
                    (observed.getAppArgs.pop.push other)) (mkConst ``Bool.true)))
                (← normalized.getProof' value)
              goal.assign (← mkEqMPR transport (← instantiateMVars normalizedGoal))
              return state.pending.toList
          saved.restore
      let (proved, state) ← run (analysis.proveFinite goal 256)
      return (if proved then [] else [goal]) ++ state.pending.toList
  | .sign =>
      let saved ← saveState
      let (proved, state) ← run (analysis.proveSign goal 256 signDepth)
      if proved then return state.pending.toList
      saved.restore
      let some proof ← transaction? (signByCalls? session target) |
        throwError "roundoff: could not determine the sign in {target}"
      goal.assign proof
      return []
  | .mixed =>
      let (finite?, bound) := match finiteMixed? target with
        | some (finite, bound) => (some finite, bound)
        | none => (none, target)
      let arguments := bound.getAppArgs
      let actual : Q(ℝ) := arguments[0]!
      let reference : Q(ℝ) := arguments[1]!
      let relative : Q(ℝ) := arguments[2]!
      let absolute : Q(ℝ) := arguments[3]!
      let (estimate, state) ← run (analyze actual)
      let .mixed derivedRelative derivedAbsolute := estimate.bound |
        throwError "roundoff: expected a mixed estimate"
      -- The same analysis proves the finiteness of the decoded value.
      let derived? ← match finite? with
        | some finite => do
            let goal ← mkFreshExprMVar finite
            if ← estimate.closeFinite goal.mvarId! then pure (some (← instantiateMVars goal))
            else pure none
        | none => pure none
      let (finite, state) ← match finite?, derived? with
        | none, _ => pure (none, state)
        | some _, some proof => pure (some proof, state)
        | some finite, none => do
            let goal ← mkFreshExprMVar finite
            let (proved, state) ← run (analysis.proveFinite goal.mvarId! 256) state
            pure (some (← instantiateMVars goal),
              if proved then state else { state with pending := state.pending.push goal.mvarId! })
      let conclude (proof : Lean.Expr) : MetaM Lean.Expr := do
        let some finite := finite | return proof
        mkAppM ``And.intro #[finite, proof]
      -- Inference: an unassigned reference and budgets take the derived ones.
      if reference.isMVar && relative.isMVar && absolute.isMVar then
        unless ← isDefEq reference estimate.reference <&&> isDefEq relative derivedRelative <&&>
            isDefEq absolute derivedAbsolute do
          throwError "roundoff: could not infer the mixed bound"
        goal.assign (← conclude estimate.proof)
        return state.pending.toList
      let same ← mkFreshExprMVar (← mkEq estimate.reference reference)
      -- Mixed analysis traverses stored containers by coordinate; so may the stated reference.
      let traversals := (← extension).loops.filterMap (·.coordinates.map (·.2))
      let traversed (goal : MVarId) : TacticM Bool := do
        let remaining? ← attempt? 10000 do
          if traversals.isEmpty then return none
          let laws ← traversals.mapM fun law => `(Lean.Parser.Tactic.rwRule| $(mkIdent law):ident)
          let remaining ← Lean.Elab.Tactic.run goal do
            evalTactic (← `(tactic| conv => rhs; rw [$laws,*]))
          for next in remaining do
            unless ← referenceEquality session next do return none
          return some ()
        return remaining?.isSome
      unless ← referenceEquality session same.mvarId! <||> traversed same.mvarId! do
        throwError "roundoff derived the reference {estimate.reference}, but the goal uses \
          {reference}; establish their equality before applying the numerical bound"
      let estimate ← rewriteReference estimate (← instantiateMVars same)
      let relativeGoal ← mkFreshExprMVar q($derivedRelative ≤ $relative)
      let absoluteGoal ← mkFreshExprMVar q($derivedAbsolute ≤ $absolute)
      goal.assign (← conclude
        (← mkAppM ``MixedError.mono #[estimate.proof, relativeGoal, absoluteGoal]))
      return state.pending.toList ++ (← close relativeGoal.mvarId!) ++
        (← close absoluteGoal.mvarId!)
  | .decoded =>
      let value := target.getAppArgs[1]!.getAppArgs.back!
      let rational := target.getAppArgs[2]!.appArg!
      let observed ← mkAppM ``ExecFloat.Binary.toReal #[value]
      let (estimate, state) ← run (analyze observed)
      unless estimate.bound.isExact do
        throwError "roundoff: the computation of {value} is not exact"
      let exact ← exactEquality estimate.proof
      let decodedValue ← mkFreshExprMVar
        (← mkEq estimate.reference (← mkAppOptM ``Rat.cast #[q(ℝ), none, rational]))
      let finite ← mkFreshExprMVar (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value])
        (mkConst ``Bool.true))
      let (proved, state) ← run (analysis.proveFinite finite.mvarId! 256) state
      goal.assign (← mkAppM ``ExecFloat.Binary.toRat?_eq_some_of_toReal_eq
        #[finite, ← mkEqTrans exact decodedValue])
      return state.pending.toList ++ (if proved then [] else [finite.mvarId!]) ++
        (← close decodedValue.mvarId!)
  | .positive | .negative | .nonzero =>
      let actual : Q(ℝ) ← match target with
        | ~q(0 < ($x : ℝ)) => pure x
        | ~q(($x : ℝ) < 0) => pure x
        | ~q(($x : ℝ) ≠ 0) => pure x
        | _ => throwError "roundoff: unsupported sign target {target}"
      -- The signs of the computed operands first, then the sign of an exact value; the margin of
      -- the whole error otherwise.
      let saved ← saveState
      let (proved, state) ← run (analysis.proveSign goal 256 signDepth)
      if proved then return state.pending.toList
      saved.restore
      if let some proof ← transaction? (signByCalls? session target) then
        goal.assign proof
        return []
      let (estimate, state) ← run (analyze actual)
      let .mixed relative absolute := estimate.bound |
        throwError "roundoff: expected a mixed estimate"
      let reference := estimate.reference
      let signGoal : Q(Prop) := match property with
        | .positive => q(0 < $reference)
        | .negative => q($reference < 0)
        | _ => q($reference ≠ 0)
      -- A purely relative error below one keeps the reference's sign; otherwise the error must
      -- stay below the reference's magnitude.
      let (proof, conditions) ← if absolute.nat? == some 0 then do
          let below ← mkFreshExprMVar q($relative < 1)
          let sign ← mkFreshExprMVar signGoal
          let conclude := match property with
            | .positive => ``MixedError.pos_of_pos
            | .negative => ``MixedError.lt_zero_of_lt_zero
            | _ => ``MixedError.ne_zero_of_ne_zero
          pure (← mkAppM conclude #[estimate.proof, below, sign], #[below, sign])
        else do
          let margin ← mkFreshExprMVar <| match property with
            | .positive => q($relative * |$reference| + $absolute < $reference)
            | .negative => q($relative * |$reference| + $absolute < -$reference)
            | _ => q($relative * |$reference| + $absolute < |$reference|)
          let conclude := match property with
            | .positive => ``MixedError.pos
            | .negative => ``MixedError.lt_zero
            | _ => ``MixedError.ne_zero
          pure (← mkAppM conclude #[estimate.proof, margin], #[margin])
      goal.assign proof
      let mut state := state
      let mut unproved := []
      for condition in conditions do
        let some condition ← session.tidy condition.mvarId! | continue
        if ← discharge session condition then continue
        let (proved, next) ← run (analysis.proveSign condition 256 signDepth) state
        state := next
        unless proved do unproved := unproved ++ (← close condition)
      return state.pending.toList ++ unproved

/-- Close `error ≤ budget` for an error that takes the smaller `min a b` of two bounds, such as a
square root's `sqrtError e a x`, through `min a b ≤ a` and `sqrtError e a x ≤ √e`: a tolerance
stated with the first bound holds. -/
def relaxMinimum (session : Session) (goal : MVarId) : TacticM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  unless target.isAppOfArity ``LE.le 4 do return false
  let error := target.getArg! 2
  let smaller (term : Lean.Expr) : Bool :=
    term.isAppOfArity ``Min.min 4 || term.isAppOfArity ``sqrtError 3
  unless (error.find? smaller).isSome do return false
  let relaxed := error.replace fun term =>
    if term.isAppOfArity ``Min.min 4 then some (term.getArg! 2)
    else if term.isAppOfArity ``sqrtError 3 then some (mkApp (mkConst ``Real.sqrt) (term.getArg! 0))
    else none
  let closed? ← attempt? 10000 do
    let weaker ← mkFreshExprMVar (← mkAppM ``LE.le #[relaxed, target.getArg! 3])
    unless ← discharge session weaker.mvarId! do return none
    let smaller ← mkFreshExprMVar (← mkAppM ``LE.le #[error, relaxed])
    let remaining ← Lean.Elab.Tactic.run smaller.mvarId! do
      evalTactic (← `(tactic| gcongr <;>
        first | exact min_le_left _ _ | exact sqrtError_le_sqrt _ _ _ | positivity))
    unless remaining.isEmpty do return none
    goal.assign (← mkAppM ``le_trans #[smaller, weaker])
    return some ()
  return closed?.isSome

/-- The `roundoff` tactic. Conjunctions are split and each conjunct gets its own proof. -/
partial def roundoffTactic : TacticM Unit := do
  -- A goal that `have` leaves wraps its statement in metadata, which the classification of the
  -- target would not see through.
  let stripMetadata : TacticM Unit := do
    let target ← instantiateMVars (← getMainTarget)
    unless target.consumeMData == target do
      replaceMainGoal [← (← getMainGoal).change target.consumeMData]
  stripMetadata
  -- Keep named inputs and their local assumptions available to numerical rule matching. A `let`
  -- of the statement is inlined, so that later hypotheses mention the computation itself.
  while (← getMainTarget).isForall || (← getMainTarget).isLet do
    if let .letE _ _ value body _ := ← getMainTarget then
      replaceMainGoal [← (← getMainGoal).change (body.instantiate1 value)]
    else
      let (_, goal) ← (← getMainGoal).intro1
      replaceMainGoal [goal]
    stripMetadata
  let target ← getMainTarget
  if target.isAppOfArity ``And 2 && (finiteMixed? target).isNone then
    let goals ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels ``And.intro)
    let mut remaining := []
    for goal in goals do
      setGoals [goal]
      roundoffTactic
      remaining := remaining ++ (← getGoals)
    setGoals (← deduplicate remaining)
    return
  let property ← withMainContext (property? target)
  -- Exact model equalities expose the executed schedule before any real-error analysis.
  -- No assumption about the accuracy of a transcendental approximation is introduced here.
  if target.isAppOf ``Eq && !(← hasObservation target) &&
      !(property matches some .finite | some .decoded) then
    decode
    return
  let session ← Session.prepare
  let extension ← extension
  let sums := extension.sums.filter fun sum => !sum.entries && !sum.exact
  let loopNames := extension.reductions ++ sums.map (·.head) ++ extension.loopHeads ++
    extension.loops.map (·.fold) ++ extension.loops.map (·.allSteps) ++
    extension.loops.map (·.foldError)
  if (!target.isAppOf ``Eq || property matches some .finite | some .decoded) &&
      (target.find? fun term =>
        loopNames.contains (term.getAppFn.constName?.getD .anonymous)).isSome then
    withMainContext do
      let (context, procedures) ← foldSimpContext session
      discard <| simpLocation context procedures none .wildcard
  if (← getGoals).isEmpty then return
  trace[roundoff] "prepare tensor coordinates"
  -- Coordinate rules expose the existing container arithmetic, without flattening containers or
  -- unfolding their storage. The same equalities normalize the finiteness assumptions.
  let target ← getMainTarget
  -- Mixed analysis reads stored containers by coordinate, so facts about their entries are
  -- normalized like the program even when the target itself reads no container.
  let observedFacts ← withMainContext do
    return property.isSome && (← (← getLCtx).anyM fun declaration => do
      return !declaration.isImplementationDetail && (← hasObservation declaration.type))
  if (← hasObservation target) || observedFacts then
    withMainContext do
      let (context, procedures) ← coordinateSimpContext session
      discard <| simpLocation context procedures none .wildcard
  if (← getGoals).isEmpty then return
  if let some property ← withMainContext do property? (← getMainTarget) then
    let goal ← getMainGoal
    match property with
    | .decoded | .positive | .nonzero =>
        -- The established forms keep their decoding and absolute proofs when mixed analysis
        -- does not prove the target outright. A closed computation keeps them directly.
        if (← getMainTarget).hasFVar then
          let saved ← saveState
          let remaining? ← try
              let goals ← proveProperty session property goal
              some <$> deduplicate (← usedObligations goal goals)
            catch error => do
              trace[roundoff] "mixed analysis failed: {error.toMessageData}"
              pure none
          if remaining?.any (·.isEmpty) then
            replaceMainGoal []
            return
          saved.restore
    | _ =>
        replaceMainGoal
          (← deduplicate (← usedObligations goal (← proveProperty session property goal)))
        return
  -- An exact equality is decoded once its container reads are normalized.
  if (← getMainTarget).isAppOf ``Eq then
    decode
    return
  withMainContext do
    let goal ← getMainGoal
    let target : Q(Prop) ← instantiateMVars (← goal.getType)
    let actual : Q(ℝ) ← match target with
      | ~q(|($actual : ℝ) - $_reference| ≤ $_budget) => pure actual
      | ~q(($actual : ℝ) ≠ 0) => pure actual
      | ~q(0 < ($actual : ℝ)) => pure actual
      | _ => throwError "roundoff expects an absolute-error bound, a mixed bound, or a \
          property of a computed value"
    let session ← session.index
    let (estimate, state) ← ((analyze actual).run session).run {}
    let .absolute error := estimate.bound | throwError "roundoff: expected an absolute estimate"
    let (proof, remaining) ← match target with
      | ~q(|($_actual : ℝ) - $reference| ≤ $budget) => do
          let same ← mkFreshExprMVar (← mkEq estimate.reference reference)
          unless ← referenceEquality session same.mvarId! do
            throwError "roundoff derived the reference {estimate.reference}, but the goal uses \
              {reference}; establish their equality before applying the numerical bound"
          let statement ← mkAppM ``congrArg
            #[q(fun value : ℝ => |$actual - value| ≤ $error), same]
          let numerical ← mkAppM ``Eq.mp #[statement, estimate.proof]
          let remaining ← mkFreshExprMVar q($error ≤ $budget)
          pure (← mkAppM ``le_trans #[numerical, remaining], remaining)
      | ~q(($_actual : ℝ) ≠ 0) => do
          let reference := estimate.reference
          let remaining ← mkFreshExprMVar q($error < |$reference|)
          pure (← mkAppM ``nonzero_of_error_lt #[estimate.proof, remaining], remaining)
      | ~q(0 < ($_actual : ℝ)) => do
          let reference := estimate.reference
          let remaining ← mkFreshExprMVar q($error < $reference)
          pure (← mkAppM ``positive_of_error_lt #[estimate.proof, remaining], remaining)
      | _ => throwError "roundoff: unsupported target"
    goal.assign proof
    let mut pending := state.pending.toList
    unless ← discharge session remaining.mvarId! <||> relaxMinimum session remaining.mvarId! do
      pending := pending ++ [remaining.mvarId!]
    replaceMainGoal pending

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
