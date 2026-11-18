/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.Roundoff.Cases

/-!
# Premises of the `roundoff` analysis

The analysis proves the premises of a mixed rule itself:

* finiteness through range theorems and the finiteness of exact operations,
* a fact about every value of a variable for a fresh one,
* a nonzero divisor from a sign or from a margin of its enclosure,
* the domain of a square root from the sign of its operand,
* and range conditions from the enclosure `(1 + r) * |x₀| + a` of an exact value.

A premise that cannot be proved stays open as a condition on the inputs, with two exceptions. A
premise that selects a rule, such as a sign or a zero test, rejects the rule instead. A finiteness
whose derivation is in progress rejects a rule that needs it, because a derivation is not nested
inside itself, nor more than `finiteDepth` deep.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Analyze

/-- Prove a premise of a mixed rule: finiteness through a range theorem, a fact about every
value of a variable for a fresh one, otherwise a selection premise through the exact analysis or
the sign rules. On `false` the premise is left unassigned, for the caller to keep or reject, and
`true` may rest on obligations recorded as pending. -/
def prove (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := do
  let type ← instantiateMVars (← goal.getType)
  -- A premise that reads a container through a surface getter is normalized like the analyzed
  -- program, which reads its coordinates. Without metavariables, and when it was stated in this
  -- local context, it shares the program's normalization there (`Session.normalize`). Normalizing
  -- assigns the premise, so a normal form left unproved undoes it.
  let surfaces := (← extension).surfaces
  if (type.find? fun term => surfaces.any term.isAppOf).isSome then
    let session ← read
    let (context, procedures) ← coordinateSimpContext session
    let saved ← Tactic.saveState
    let initial ← get
    let normalized? ← attempt? 10000 do
      if type.hasMVar || (← goal.getDecl).lctx.getFVarIds != (← getLCtx).getFVarIds then
        let (next, _) ← simpTarget goal context procedures
        return some next
      goal.withContext do
        goal.checkNotAssigned `simp
        return some (← applySimpResult? goal type
          (← session.normalize `coordinate type context procedures))
    if let some next := normalized? then
      let some next := next | return true
      if next != goal then
        if ← r.proveNormalized next fuel then return true
        saved.restore
        set initial
        return false
  r.proveNormalized goal fuel

/-- The domain condition of square root follows from the sign `0 ≤ toReal value`, and the
finiteness of the value is proved or kept open. -/
def proveDomain (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  let some value := domainValue? (← instantiateMVars (← goal.getType)) | return false
  let proved? ← speculate? do
    let decoded : Q(ℝ) ← mkAppM ``ExecFloat.Binary.toReal #[value]
    let sign ← mkFreshExprMVar q(0 ≤ $decoded)
    unless ← r.proveSign sign.mvarId! fuel signDepth do
      throwError "roundoff: unproved sign of a square-root operand"
    let finite ← mkFreshExprMVar (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value])
      (mkConst ``Bool.true))
    unless ← r.proveFinite finite.mvarId! fuel do
      modify fun state => { state with pending := state.pending.push finite.mvarId! }
    goal.assign (← mkAppM ``ExecFloat.Binary.isZero_or_signBit_eq_false_of_toReal_nonneg
      #[← instantiateMVars finite, ← instantiateMVars sign])
  return proved?.isSome

/-- `prove` for a premise whose container reads are normalized. -/
def proveNormalized (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := do
  let type ← instantiateMVars (← goal.getType)
  if (domainValue? type).isSome then proveDomain r goal fuel
  else if isFiniteness type then r.proveFinite goal fuel
  else if type.isForall then r.proveForall goal fuel
  else if isRange type then r.proveRange goal fuel
  else if isNonzeroTest type then r.proveNonzero goal fuel
  else r.proveSelection goal fuel

/-- A premise about every value of a variable, such as the finiteness of every entry of a
computed container, is proved for a fresh one. The conditions left are required of every value,
and no cached result mentioning the variable escapes. An implication is not such a premise. -/
def proveForall (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  let .forallE name domain body info ← whnfR (← instantiateMVars (← goal.getType)) |
    return false
  if ← isProp domain then return false
  let initial ← get
  let outerContext ← getLCtx
  let outerInstances ← getLocalInstances
  let proved? ← withLocalDecl name info domain fun point => do
    let inner ← mkFreshExprMVar (body.instantiate1 point)
    unless ← r.prove inner.mvarId! fuel do return none
    let localGoals := (← get).pending.extract initial.pending.size (← get).pending.size
    if localGoals.isEmpty then
      return some (← mkLambdaFVars #[point] (← instantiateMVars inner), #[])
    withConditions localGoals (← read).comparisons fun condition evidence => do
      let closed ← withLCtx outerContext outerInstances
        (mkFreshExprMVar (← mkForallFVars #[point] condition))
      let proof ← mkLambdaFVars #[evidence] (← instantiateMVars inner)
      return some (← mkLambdaFVars #[point] (mkApp proof (mkApp closed point)),
        #[closed.mvarId!])
  let some (proof, pending) := proved? | do
    set initial
    return false
  set { initial with pending := initial.pending ++ pending }
  goal.assign proof
  return true

/-- A finite value with a real value of a strict sign, or whose exact value's enclosure excludes
zero, is not an executable zero, as a divisor must be. -/
def proveNonzero (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  let value := type.getAppArgs[1]!.getAppArgs.back!
  let decoded : Q(ℝ) ← mkAppM ``ExecFloat.Binary.toReal #[value]
  let proved? ← speculate? do
    let finite ← mkFreshExprMVar (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value])
      (mkConst ``Bool.true))
    unless ← r.proveFinite finite.mvarId! fuel do
      throwError "roundoff: the divisor need not be finite"
    let mut nonzero? := none
    for positive in [true, false] do
      if nonzero?.isSome then continue
      let sign ← mkFreshExprMVar (if positive then q(0 < $decoded) else q($decoded < 0))
      if ← r.proveSign sign.mvarId! fuel signDepth then
        nonzero? := some (← mkAppM (if positive then ``ne_of_gt else ``ne_of_lt)
          #[← instantiateMVars sign])
    let nonzero ← match nonzero? with
      | some nonzero => pure nonzero
      | none => r.enclosedNonzero decoded fuel
    let zero ← mkAppM ``ExecFloat.Binary.isZero_eq_true_iff_toReal_eq_zero
      #[← instantiateMVars finite]
    let notZero ← withLocalDeclD `zero (← mkEq (← mkAppM ``ExecFloat.Binary.isZero #[value])
        (mkConst ``Bool.true)) fun hzero => do
      mkLambdaFVars #[hzero] (mkApp nonzero (← mkAppM ``Iff.mp #[zero, hzero]))
    let test ← mkAppM ``ExecFloat.Binary.isZero #[value]
    goal.assign (← mkAppM ``Iff.mpr #[← mkAppOptM ``Bool.eq_false_iff #[some test], notZero])
  return proved?.isSome

/-- A computed value is nonzero when the enclosure of its exact value excludes zero: its error is
below the magnitude of its reference. That condition on the inputs is proved or kept open. -/
def enclosedNonzero (r : Recursor) (decoded : Q(ℝ)) (fuel : Nat) : AnalyzeM Lean.Expr := do
  let estimate ← r.analyze decoded fuel
  let .mixed relative absolute := estimate.bound |
    throwError "roundoff: expected a mixed estimate"
  let reference := estimate.reference
  let margin ← mkFreshExprMVar q($relative * |$reference| + $absolute < |$reference|)
  if let some condition ← (← read).tidy margin.mvarId! then
    -- The margin of an exact value is the sign of its reference, which the sign rules may settle.
    let settled ← if estimate.bound.isExact then r.proveSign condition fuel signDepth
      else pure false
    unless settled do modify fun state => { state with pending := state.pending.push condition }
  mkAppM ``MixedError.ne_zero #[estimate.proof, ← instantiateMVars margin]

/-- A range condition `y < c`, `|y| < c`, `y ≤ c` or `|y| ≤ c` on a real computed from
configured values follows from the same bound on the enclosure `(1 + r) * |x₀| + a` of its
exact value. That condition on the inputs is proved or kept open. -/
def proveRange (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  let session ← read
  let type ← instantiateMVars (← goal.getType)
  let strict := type.isAppOfArity ``LT.lt 4
  unless strict || type.isAppOfArity ``LE.le 4 do return false
  let bounded := type.getAppArgs[2]!
  let limit : Q(ℝ) := type.getAppArgs[3]!
  -- A rule's bound on the enclosure of its input, such as the range of an integer type, is
  -- proved or kept as it is.
  if isEnclosure bounded then
    if let some condition ← session.tidy goal then
      unless ← discharge session condition do
        modify fun state => { state with pending := state.pending.push condition }
    return true
  let magnitude := bounded.isAppOf ``abs
  let value : Q(ℝ) := if magnitude then bounded.appArg! else bounded
  -- A condition on the format alone is proved, or kept as it is when it depends on a variable
  -- such as a symbolic format or length. A closed one, for a given format and length, must be
  -- proved; one that fails rules out the rule it belongs to.
  -- A value of the descriptor model is computed too, when it is not a constant of the format.
  let computed (term : Lean.Expr) : Bool :=
    term.isAppOf ``ExecFloat.Binary.toReal ||
      (term.isAppOf ``Model.toReal && term.hasFVar && !term.appArg!.isAppOf ``Model.posMaxFinite)
  unless (value.find? computed).isSome do
    if type.hasExprMVar || (type.find? (·.isAppOf ``ExecFloat.Binary.toReal)).isSome then
      return false
    unless type.hasFVar do return ← discharge session goal
    if let some condition ← session.tidy goal then
      unless ← discharge session condition do
        modify fun state => { state with pending := state.pending.push condition }
    return true
  let some estimate ← speculate? (r.analyze value fuel) | return false
  let .mixed relative absolute := estimate.bound | return false
  let reference := estimate.reference
  let enclosure : Q(ℝ) := q((1 + $relative) * |$reference| + $absolute)
  let condition ← mkFreshExprMVar
    (if strict then q($enclosure < $limit) else q($enclosure ≤ $limit))
  let enclosed ← mkAppM ``MixedError.abs_le #[estimate.proof]
  let enclosed ← if magnitude then pure enclosed
    else mkAppM ``le_trans #[← mkAppM ``le_abs_self #[value], enclosed]
  goal.assign (← mkAppM (if strict then ``lt_of_le_of_lt else ``le_trans) #[enclosed, condition])
  if let some condition ← session.tidy condition.mvarId! then
    unless ← discharge session condition <||> r.rangeByBounds condition fuel do
      modify fun state => { state with pending := state.pending.push condition }
  return true

/-- With correctly rounded calls kept as computed values, close a range condition on such
values by linear arithmetic from their signs, the hypotheses and `1 ≤ posMax`, such as
`|exp y - 1| ≤ posMax` for a computed `exp y` in `[0, 1)`. -/
def rangeByBounds (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  unless (← read).computedCalls do return false
  let type ← instantiateMVars (← goal.getType)
  unless type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4 do return false
  -- The decoded computed values, and the formats whose largest finite value is the bound.
  let leaves ← IO.mkRef (#[] : Array Q(ℝ))
  let formats ← IO.mkRef (#[] : Array Q(FloatFormat))
  type.forEach' fun term => do
    if term.isAppOfArity ``Model.posMaxFinite 1 then formats.modify (·.push term.appArg!)
    unless term.isAppOf ``ExecFloat.Binary.toReal do return true
    -- A value bound inside the condition, such as a loop's state, is not a leaf.
    let bound := term.hasLooseBVars
    unless bound || (← isInputValue term.appArg!) || (← leaves.get).contains term do
      leaves.modify (·.push term)
    return false
  if (← leaves.get).isEmpty then return false
  let mut facts := #[]
  for leaf in ← leaves.get do
    for nonneg in [true, false] do
      let sign? ← speculate? do
        let sign ← mkFreshExprMVar (if nonneg then q(0 ≤ $leaf) else q($leaf ≤ 0))
        let before := (← get).pending.size
        unless (← r.proveSign sign.mvarId! fuel signDepth) && (← get).pending.size == before do
          throwError "roundoff: no sign of {leaf}"
        instantiateMVars sign
      if let some sign := sign? then
        facts := facts.push sign
        break
  for format in ← formats.get do
    facts := facts.push (← mkAppM ``Model.one_le_toReal_posMaxFinite #[format])
  let closed? ← attempt? 2000 do
    let hypotheses ← facts.mapM fun fact => do
      return ({ userName := `fact, type := ← inferType fact, value := fact } : Hypothesis)
    let (_, next) ← goal.assertHypotheses hypotheses
    let remaining ← Lean.Elab.Tactic.run next do
      evalTactic (← `(tactic| first
        | linarith
        | (rw [abs_le]; constructor <;> linarith)
        | (rw [abs_lt]; constructor <;> linarith)))
    return if remaining.isEmpty then some () else none
  return closed?.isSome

/-- Finiteness, proved once per scope: an earlier proof whose local variables are in the current
context is reused. A finiteness whose derivation is in progress is not derived again inside it
(`Session.deriving`), and the search fails there instead of repeating. -/
def proveFinite (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  let derive : AnalyzeM Bool := do
    if ← (← read).deriving type then return false
    withReader (fun session => { session with finiteGoals := session.finiteGoals.push type })
      (r.deriveFinite goal fuel)
  if type.hasExprMVar then return ← derive
  let context ← getLCtx
  for (proved, used) in (← get).finite.getD type #[] do
    if used.all context.contains && (← proved.isAssigned) then
      goal.assign (mkMVar proved)
      return true
  unless ← derive do return false
  let used := (collectFVars {} (← instantiateMVars (mkMVar goal))).fvarIds
  modify fun state => { state with
    finite := state.finite.insert type ((state.finite.getD type #[]).push (goal, used)) }
  return true

/-- Finiteness from the context, from an analyzed node, or from a registered finiteness
theorem. Its enclosure premises come from the analysis. A range condition it cannot prove stays
an obligation on the inputs, and so does the finiteness of an input. -/
def deriveFinite (r : Recursor) (goal : MVarId) (fuel : Nat) : AnalyzeM Bool := goal.withContext do
  let session ← read
  let type ← instantiateMVars (← goal.getType)
  -- A finiteness is an equality `test value = true`. No other proposition is derived here, such
  -- as the invariant `True` of a loop whose state decodes no value.
  let some (_, observed, _) := type.eq? | return false
  -- The decoded finiteness of a configured value is its finiteness, by definition.
  if observed.isAppOfArity ``Model.isFinite 2 &&
      observed.appArg!.isAppOf ``ExecFloat.Binary.toModel then
    let finite ← mkFreshExprMVar (← mkEq
      (← mkAppM ``ExecFloat.Binary.isFinite #[observed.appArg!.appArg!]) (mkConst ``Bool.true))
    unless ← r.proveFinite finite.mvarId! fuel do
      -- An entry of a function the program takes is a premise, stated on the configured value.
      unless ← isAppliedInput observed.appArg!.appArg! do return false
      modify fun state => { state with pending := state.pending.push finite.mvarId! }
    goal.assign (← instantiateMVars finite)
    return true
  let some value := observed.getAppArgs.back? | return false
  -- A cast count that computes to a numeral is that numeral, as in the analysis.
  if value.isAppOfArity ``Nat.cast 3 && value.appArg!.nat?.isNone then
    let numeral? ← attempt? 1000 do
      let count ← withDefault (whnf value.appArg!)
      return count.rawNatLit? <|> count.nat?
    if let some numeral := numeral? then
      let next ← mkFreshExprMVar (← mkEq (mkAppN observed.getAppFn
        (observed.getAppArgs.pop.push (mkApp value.appFn! (mkNatLit numeral)))) type.appArg!)
      if ← r.proveFinite next.mvarId! fuel then
        goal.assign (← instantiateMVars next)
        return true
  -- A value already analyzed has its finiteness at hand.
  for (actual, estimate) in (← get).mixedCache.toList do
    unless decodedValue? actual == some value do continue
    if ← estimate.closeFinite goal then return true
  if ← discharge session goal then return true
  -- The finiteness of an input is otherwise a condition on the input.
  if ← isStoredInput value then
    modify fun state => { state with pending := state.pending.push goal }
    return true
  -- A branch decided by a hypothesis, by simplification or by a refutation of its guard is finite
  -- when its selected value is.
  if value.isAppOfArity ``ite 5 || value.isAppOfArity ``dite 5 then
    let arguments := value.getAppArgs
    let condition := arguments[1]!
    let hypothesis? ← (← getLCtx).findDeclM? fun declaration => do
      if declaration.isImplementationDetail then return none
      let hypothesis ← instantiateMVars declaration.type
      if ← withReducible (isDefEq hypothesis condition) then
        return some (true, declaration.toExpr)
      if ← withReducible (isDefEq hypothesis (mkNot condition)) then
        return some (false, declaration.toExpr)
      return none
    let evidence? ← if hypothesis?.isSome then pure hypothesis? else
      match ← guardEvidence? session condition with
      | some evidence => pure (some evidence)
      | none => pure ((← refutedGuard? condition).map (false, ·))
    if let some (positive, evidence) := evidence? then
      let rule := if value.isAppOfArity ``dite 5 then
          if positive then ``dite_eq_left else ``dite_eq_right
        else if positive then ``ite_eq_left else ``ite_eq_right
      let equality ← mkAppOptM rule #[some arguments[1]!, some arguments[2]!,
        some evidence, some arguments[0]!, some arguments[3]!, some arguments[4]!]
      let some (_, _, selected) := (← inferType equality).eq? | return false
      let selected := selected.headBeta
      let next ← mkFreshExprMVar
        (← mkEq (mkAppN observed.getAppFn (observed.getAppArgs.pop.push selected)) type.appArg!)
      unless ← r.proveFinite next.mvarId! fuel do return false
      let transport ← mkCongrArg (← withLocalDeclD `value (← inferType value) fun other => do
        mkLambdaFVars #[other] (← mkEq (mkAppN observed.getAppFn
          (observed.getAppArgs.pop.push other)) type.appArg!)) equality
      goal.assign (← mkEqMPR transport next)
      return true
    -- Otherwise both cases must be finite, each under its guard, as the analysis of the branch
    -- proves them.
    if session.mixed && observed.isAppOf ``ExecFloat.Binary.isFinite then
      let proved? ← speculate? do
        let estimate ← r.analyze (← mkAppM ``ExecFloat.Binary.toReal #[value]) fuel
        unless ← estimate.closeFinite goal do
          throwError "roundoff: a case of the branch is not finite"
      if proved?.isSome then return true
  -- A `match` is finite when each of its alternatives is, as its analysis proves them.
  if session.mixed && observed.isAppOf ``ExecFloat.Binary.isFinite &&
      (← Cases.matcher? value).isSome then
    let proved? ← speculate? do
      let estimate ← r.analyze (← mkAppM ``ExecFloat.Binary.toReal #[value]) fuel
      unless ← estimate.closeFinite goal do
        throwError "roundoff: a case of the match is not finite"
    if proved?.isSome then return true
  -- A container read is finite when the scalar computation it observes is.
  if (← readPosition? value (strict := false)).isSome then
    let (context, procedures) ← coordinateSimpContext session
    let normalized ← session.normalize `coordinate value context procedures
    if normalized.expr != value then
      let next ← mkFreshExprMVar (← mkEq (mkAppN observed.getAppFn
        (observed.getAppArgs.pop.push normalized.expr)) type.appArg!)
      if ← r.proveFinite next.mvarId! fuel then
        let motive ← withLocalDeclD `value (← inferType value) fun other => do
          mkLambdaFVars #[other] (← mkEq (mkAppN observed.getAppFn
            (observed.getAppArgs.pop.push other)) type.appArg!)
        goal.assign (← mkEqMPR (← mkCongrArg motive (← normalized.getProof' value))
          (← instantiateMVars next))
        return true
  -- A reduction is analyzed as its fold, written by the fold laws or else by the conversions, and
  -- so is a loop, such as an exposed sum. A loop that they leave unchanged, or change only up to
  -- reducible unfolding, such as the spelling of a numeral, is finite only by its own analysis;
  -- its finiteness is not sought again, which would repeat without end.
  let loop := (← loopOf? value).isSome
  if loop || (← isReduction value) || (← extension).loopHeads.any value.isAppOf then
    let (context, procedures) ← foldSimpContext session
    let normalized ← session.normalize `fold value context procedures
    let normalized ← if normalized.expr != value then pure normalized
      else pure (← simp value (← conversionSimpContext)).1
    let changed ← pure (normalized.expr != value) <&&>
      withNewMCtxDepth (return !(← withReducible (isDefEq normalized.expr value)))
    if changed || loop then
      if let some estimate ← speculate? (r.analyze (← mkAppM ``ExecFloat.Binary.toReal
          #[normalized.expr]) fuel) then
        let next ← mkFreshExprMVar (← mkEq (mkAppN observed.getAppFn
          (observed.getAppArgs.pop.push normalized.expr)) (mkConst ``Bool.true))
        if ← estimate.closeFinite next.mvarId! <||>
            (pure changed <&&> r.proveFinite next.mvarId! fuel) then
          let motive ← withLocalDeclD `value (← inferType value) fun other => do
            mkLambdaFVars #[other] (← mkEq (mkAppN observed.getAppFn
              (observed.getAppArgs.pop.push other)) (mkConst ``Bool.true))
          goal.assign (← mkEqMPR (← mkCongrArg motive (← normalized.getProof' value))
            (← instantiateMVars next))
          return true
  let mut candidates ← withCanUnfoldPred (programCanUnfold session.boundaries false)
    (do rulesFor session.finiteness observed (← session.indexKey observed))
  -- A hypothesis stated like a generated theorem, such as a function's contract, is a
  -- finiteness rule too.
  for declaration in ← getLCtx do
    if ← isGeneratedForm declaration value then
      let finite ← projectConclusion declaration.toExpr ``And.left
      candidates := candidates.push
        { name := declaration.userName, exact := false, prepared := ← abstractMVars finite }
  for rule in candidates.qsort (·.order < ·.order) do
    let applied? ← speculate? do
      let law ← rule.instantiate
      let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
      unless ← isDefEq conclusion type do throwError "roundoff: {rule.name} does not apply"
      -- A registered rule stated like a generated theorem: the orders that select its bound
      -- select its finiteness too, and are not left as conditions.
      let generated ← do
        let some info := (← getEnv).find? rule.name | pure false
        forallTelescopeReducing info.type fun _ stated => pure (finiteMixed? stated).isSome
      synthesizeInstances arguments binders
      -- A cast's policy selects its finiteness law just as it selects its error law.
      -- An IEEE-only law must not leave an impossible condition on an FP8 or MX cast.
      if value.isAppOf ``Model.cast then
        for argument in arguments do
          let argument ← instantiateMVars argument
          unless argument.isMVar do continue
          let premise ← instantiateMVars (← inferType argument)
          if isEncodingPolicy premise then
            unless ← r.prove argument.mvarId! fuel do
              throwError "roundoff: {rule.name} needs the encoding policy {premise}"
      -- The enclosure of the exact operation comes first; its analysis covers the operands.
      for argument in arguments do
        let argument ← instantiateMVars argument
        unless argument.isMVar do continue
        let premise ← instantiateMVars (← inferType argument)
        let some (bounded, _, _, _) ← mixedConclusion? premise | continue
        let estimate ← r.analyze bounded fuel
        unless ← isDefEq premise (← inferType estimate.proof) do
          throwError "roundoff: the enclosure does not match {rule.name}"
        argument.mvarId!.assign estimate.proof
      for argument in arguments do
        let argument ← instantiateMVars argument
        unless argument.isMVar do continue
        let premise ← instantiateMVars (← inferType argument)
        unless ← isProp premise do throwError "roundoff: unresolved data in {rule.name}"
        if isFiniteness premise then
          -- A rule that needs a finiteness being derived, such as its own conclusion, does not
          -- apply: it would leave that finiteness as its own condition. Nor does one whose
          -- premise search was cut off there, which did not settle the premise.
          if ← session.deriving premise then
            throwError "roundoff: {rule.name} needs the finiteness {premise} it is deriving"
          let cuts ← session.finiteCuts.get
          unless ← r.proveFinite argument.mvarId! fuel do
            if (← session.finiteCuts.get) > cuts then
              throwError "roundoff: the search for the finiteness {premise} that {rule.name} \
                needs was cut off"
            modify fun state => { state with pending := state.pending.push argument.mvarId! }
        else if isNonzeroTest premise then
          unless ← r.proveNonzero argument.mvarId! fuel do
            modify fun state => { state with pending := state.pending.push argument.mvarId! }
        else if premise.isForall then
          -- A fact about every entry, such as their finiteness, follows from one entry's.
          unless ← r.proveForall argument.mvarId! fuel do
            if let some condition ← session.tidy argument.mvarId! then
              unless ← discharge session condition do
                modify fun state => { state with pending := state.pending.push condition }
        else
          -- A sign or order that is not a range condition, or the domain of a square root,
          -- follows from the sign rules where they apply.
          if (!isRange premise && (← isRealOrder premise)) || (domainValue? premise).isSome then
            if ← r.prove argument.mvarId! fuel then continue
            if generated && (← isSelection premise) then
              throwError "roundoff: {rule.name} is selected by {premise}"
          if let some condition ← session.tidy argument.mvarId! then
            unless ← discharge session condition do
              -- Local equalities, such as a loop accumulator's exact value, may decide it.
              let decided? ← attempt? 2000 do
                let some next ← session.tidy condition (hypotheses := true) | return some ()
                return if ← discharge session next then some () else none
              unless decided?.isSome || (← r.rangeByBounds condition fuel) do
                modify fun state => { state with pending := state.pending.push condition }
      goal.assign (mkAppN law arguments)
    if applied?.isSome then return true
  -- Negation keeps finiteness.
  if value.isAppOfArity ``Neg.neg 3 then
    let operand ← mkFreshExprMVar (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite
      #[value.appArg!]) (mkConst ``Bool.true))
    if ← r.proveFinite operand.mvarId! fuel then
      let negated ← attempt? 1000 do
        let proof ← mkEqTrans (← mkAppM ``ExecFloat.Binary.isFinite_neg #[value.appArg!])
          (← instantiateMVars operand)
        return if ← isDefEq (← inferType proof) type then some proof else none
      if let some proof := negated then
        goal.assign proof
        return true
  -- A correctly rounded primitive call is finite under the premises of its contract: a sign
  -- of the input or a zero input, or else the domain and range conditions. Its implementation
  -- is not unfolded.
  for contract in ← primitiveContracts do
    unless contract.observes value do continue
    for (name, withoutRange) in contract.finiteWithoutRange.map (·, true) ++
        contract.roundings.map (·.2, false) do
      let applied? ← speculate? do
        let some (proof, premises) ← instantiatePrimitive contract name value |
          throwError "roundoff: {name} does not apply"
        unless ← isDefEq (← inferType proof) type do
          throwError "roundoff: {name} does not apply"
        -- The input's sign or zero test, which selects the theorem, before its finiteness.
        let finiteness ← premises.filterM fun premise => do
          return isFiniteness (← instantiateMVars (← premise.getType))
        let selections := premises.filter (!finiteness.contains ·)
        for premise in selections ++ finiteness do
          if ← r.prove premise fuel then continue
          if withoutRange then throwError "roundoff: unproved premise of {name}"
          let remaining ← require session premise
          modify fun state => { state with pending := state.pending ++ remaining }
        goal.assign proof
      if applied?.isSome then return true
  -- The import of a computed value is finite when the analysis of its real value proves it.
  -- The import itself is not unfolded.
  if let some entry ← import? value then
    unless session.mixed && observed.isAppOf ``ExecFloat.Binary.isFinite do return false
    -- The computation of the imported value is exposed under the import, as the analysis
    -- exposes it: an applied function, a local definition or a definition of the program.
    let inner := stripHeadMetadata (← instantiateMVars (value.getArg! entry.value))
    let exposed? ← do
      if inner.headBeta != inner then pure (some inner.headBeta)
      else if let .letE _ _ bound body _ := inner then pure (some (body.instantiate1 bound))
      else if inner.isFVar then inner.fvarId!.getValue?
      else
        let head := inner.getAppFn.constName?.getD .anonymous
        if (`FloatLib).isPrefixOf head || (← coreConstant head) then pure none
        else unfoldDefinition? inner
    if let some exposed := exposed? then
      let converted := mkAppN value.getAppFn (value.getAppArgs.set! entry.value exposed.headBeta)
      let next ← mkFreshExprMVar (← mkEq (mkAppN observed.getAppFn
        (observed.getAppArgs.pop.push converted)) (mkConst ``Bool.true))
      if ← r.proveFinite next.mvarId! fuel then
        goal.assign (← instantiateMVars next)
        return true
    let proved? ← speculate? do
      let estimate ← r.analyze (← mkAppM ``ExecFloat.Binary.toReal #[value]) fuel
      unless ← estimate.closeFinite goal do
        throwError "roundoff: the imported value need not be finite"
    return proved?.isSome
  -- A definition computing the value is unfolded, as the analysis does. Arithmetic and
  -- branches have their own rules, and a container read is not unfolded into its storage.
  let kept := [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Neg.neg, ``ite, ``dite]
  let head := value.getAppFn.constName?.getD .anonymous
  unless kept.contains head || (← extension).storage.any (·.isPrefixOf head) do
    if let some unfolded ← unfoldDefinition? value then
      let next ← mkFreshExprMVar (← mkEq (mkAppN observed.getAppFn
        (observed.getAppArgs.pop.push unfolded.headBeta)) (mkConst ``Bool.true))
      if ← r.proveFinite next.mvarId! fuel then
        goal.assign (← instantiateMVars next)
        return true
  return false

/-- The analysis of `observed` for a zero or unit test, which only an exact estimate passes.
It runs without the registered reads: a read bounds the entries of a producer at a shape that
is not literal but does not show them exact. -/
def exactAnalysis (r : Recursor) (observed : Q(ℝ)) (fuel : Nat) : AnalyzeM Estimate :=
  withReader ({ · with reads := #[] }) (r.analyze observed fuel)

/-- The order facts on reals that the hypothesis `proof` of type `type` states: itself when it
is an order or an equality of reals, the parts of a conjunction, and the two bounds of a
membership in a closed interval. -/
partial def orderFacts (proof type : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let type ← instantiateMVars type
  if let some (left, right) := type.and? then
    return (← orderFacts (← mkAppM ``And.left #[proof]) left) ++
      (← orderFacts (← mkAppM ``And.right #[proof]) right)
  if type.isAppOfArity ``Membership.mem 5 && (type.getArg! 3).isAppOfArity ``Set.Icc 4 then
    -- Membership in a closed interval is, by definition, the conjunction of its two bounds.
    let interval := type.getArg! 3
    let value := type.getArg! 4
    let bounds := mkAnd (← mkAppM ``LE.le #[interval.getArg! 2, value])
      (← mkAppM ``LE.le #[value, interval.getArg! 3])
    return ← orderFacts (← mkExpectedTypeHint proof bounds) bounds
  -- Any other hypothesis states no order, also one that is no application, such as `True`.
  unless type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4 ||
      type.isAppOfArity ``Eq 3 do return #[]
  unless (← whnfR type.getAppArgs[0]!).isConstOf ``Real do return #[]
  return #[proof]

/-- A real order between values that the order hypotheses of the context give by linear
arithmetic: interval facts about inputs, such as `1 ≤ toReal x` and `toReal x ≤ 2`, or the two
bounds `toReal y / 2 ≤ toReal x` and `toReal x ≤ 2 * toReal y` of an exact subtraction. The goal
may be a linear order, the sign of a product of two terms of one known sign, or an order
between multiples of two magnitudes of known sign. It is tried only when a hypothesis shares a
variable with the goal, and once for an order under the facts of its scope
(`Session.scopeFacts`). The forms that rewrite a magnitude are tried only on a goal that has
one. -/
def orderByHypotheses (session : Session) (goal : MVarId) : TacticM Bool := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  if type.hasMVar || !type.hasFVar then return false
  let wanted := (collectFVars {} type).fvarSet
  -- The facts inside conjunctions and interval memberships; an order hypothesis is in the
  -- context of the arithmetic already.
  let mut facts := #[]
  let mut relevant := false
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let fact ← instantiateMVars declaration.type
    if fact.isForall || !fact.hasFVar then continue
    unless (collectFVars {} fact).fvarIds.any wanted.contains do continue
    let found ← try orderFacts declaration.toExpr fact catch _ => pure #[]
    if found.isEmpty then continue
    relevant := true
    unless found.size == 1 && found[0]! == declaration.toExpr do facts := facts ++ found
  unless relevant do return false
  -- The search fails alike wherever the scopes state the same facts about the goal.
  let scope ← session.scopeFacts type
  if ((← session.orderFailures.get).getD type #[]).contains scope then return false
  let depths ← depthsCaught
  let closed? ← attempt? 4000 do
    let hypotheses ← facts.mapM fun fact => do
      return ({ userName := `fact, type := ← inferType fact, value := fact } : Hypothesis)
    let (_, next) ← goal.assertHypotheses hypotheses
    let linear ← `(tactic| first
      | linarith
      | (apply mul_nonneg <;> linarith)
      | (apply mul_nonneg_of_nonpos_of_nonpos <;> linarith))
    let magnitude ← `(tactic| first
      | (rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith)
      | (rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith)
      | (rw [abs_le]; constructor <;> linarith)
      | (rw [abs_lt]; constructor <;> linarith))
    let tactic ← if (type.find? (·.isAppOf ``abs)).isSome then
        `(tactic| first | $linear:tactic | $magnitude:tactic)
      else pure linear
    let remaining ← Lean.Elab.Tactic.run next (evalTactic tactic)
    return if remaining.isEmpty then some () else none
  -- A search that a caught recursion depth may have cut off is not kept as failed.
  if closed?.isNone && (← depthsCaught) == depths then
    session.orderFailures.modify fun failures =>
      failures.insert type ((failures.getD type #[]).push scope)
  return closed?.isSome

/-- A selection premise: an executable zero, a unit magnitude, a real sign or order,
a descriptor encoding policy, or a precision/exponent comparison. Integer arithmetic derives
widening
from a stronger product-precision hypothesis. -/
def proveSelection (r : Recursor) (goal : MVarId) (fuel : Nat) :
    AnalyzeM Bool := goal.withContext do
  let session ← read
  let type ← instantiateMVars (← goal.getType)
  if (type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4) &&
      (← whnfR type.getAppArgs[0]!).isConstOf ``Real then
    if ← r.proveSign goal fuel signDepth then return true
    -- An order that the hypotheses give by linear arithmetic, such as the factor-of-two
    -- condition of an exact subtraction from interval facts about the inputs.
    if ← orderByHypotheses session goal then return true
    -- A closed order, such as the range in which a converted numeral is exact, is decided by
    -- arithmetic.
    if type.hasFVar || type.hasMVar then return false
    return ← closeByArithmetic goal
  if ← discharge session goal then return true
  if type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4 then
    let domain ← whnfR type.getAppArgs[0]!
    if domain.isConstOf ``Nat || domain.isConstOf ``Int then
      let closed? ← attempt? 1000 do
        let remaining ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| omega)))
        return if remaining.isEmpty then some () else none
      return closed?.isSome
  if type.isAppOfArity ``Eq 3 && type.getAppArgs[1]!.isAppOf ``abs then
    -- A unit magnitude `|toReal value| = 1` from the exact analysis of `value`.
    let magnitude := type.getAppArgs[1]!.appFn!
    let observed := type.getAppArgs[1]!.appArg!
    let some estimate ← speculate? (r.exactAnalysis observed fuel) | return false
    unless estimate.bound.isExact do return false
    -- Only a constant, or a value that a local equality rewrites, can be shown to be a unit;
    -- an input or a variable need not be one.
    if estimate.reference.hasFVar then
      let rewritten ← (← getLCtx).anyM fun declaration => do
        if declaration.isImplementationDetail then return false
        let some (_, left, _) := (← instantiateMVars declaration.type).eq? | return false
        return (estimate.reference.find? (· == left)).isSome
      unless rewritten do return false
    let exact ← exactEquality estimate.proof
    let unit ← mkFreshExprMVar (← mkEq (mkApp magnitude estimate.reference)
      type.getAppArgs[2]!)
    -- The local equalities may give the value of an input of the reference.
    if let some tidied ← session.tidy unit.mvarId! (hypotheses := true) then
      let closed? ← attempt? 2000 do
        let remaining ← Lean.Elab.Tactic.run tidied do
          evalTactic (← `(tactic| norm_num))
        return if remaining.isEmpty then some () else none
      unless closed?.isSome do return false
    goal.assign (← mkEqTrans (← mkCongrArg magnitude exact) unit)
    return true
  if type.isAppOfArity ``Eq 3 && type.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.isZero then
    -- A finite value whose exact analysis gives the real value zero.
    let value := type.getAppArgs[1]!.getAppArgs.back!
    let observed ← mkAppM ``ExecFloat.Binary.toReal #[value]
    let some estimate ← speculate? (r.exactAnalysis observed fuel) | return false
    unless estimate.bound.isExact do return false
    let zero ← mkFreshExprMVar (← mkEq estimate.reference q((0 : ℝ)))
    -- The exact value must tidy to zero, also with the local equalities, such as a loop
    -- accumulator's known value; no further search decides a zero test.
    if (← session.tidy zero.mvarId! (hypotheses := true)).isSome then return false
    let finite ← mkFreshExprMVar (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value])
      (mkConst ``Bool.true))
    unless ← r.proveFinite finite.mvarId! fuel do return false
    let exact ← exactEquality estimate.proof
    goal.assign (← mkAppM ``Iff.mpr
      #[← mkAppM ``ExecFloat.Binary.isZero_eq_true_iff_toReal_eq_zero #[finite],
        ← mkEqTrans exact zero])
    return true
  r.proveSign goal fuel signDepth

end Analyze

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
