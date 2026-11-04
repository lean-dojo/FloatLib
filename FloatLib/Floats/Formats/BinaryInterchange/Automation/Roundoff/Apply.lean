/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Discharge

/-!
# Applying rules in `roundoff`

A registered rule applies when its whole statement unifies with the computation, selected
dictionaries included. Its input-error premises must be supplied by the analysis of the operands
and its selection premises proved, or the rule is rejected. Any other premise becomes a condition.
A correctly rounded call contributes the half ulp of its contract, an elementary function without
one its rational enclosure, and a hypothesis stated like a generated theorem is used as a
registered rule. The analysis of a branch keeps its guard, and the step of a loop is analyzed for
a symbolic accumulator. Local roundings compose with the propagation of input errors, and budgets
are tidied once per call.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Whether the input premise `type`, an error bound at every value of a variable, bounds `actual`
itself at some value, so that supplying it would analyze `actual` again. -/
private def boundsActual (type : Lean.Expr) (actual : Lean.Expr) : TacticM Bool := do
  let .forallE _ domain body _ := type | return false
  if ← isProp domain then return false
  let matched? ← attempt? 1000 <| withNewMCtxDepth do
    let point ← mkFreshExprMVar domain
    let some (value, _, _) ← boundConclusion? (body.instantiate1 point) | return none
    return if ← withReducible (isDefEq (← instantiateMVars value) actual) then some () else none
  return matched?.isSome

/-- Apply the bound built by `prepare` with its original instances. Input-error premises determine
the reference before ordinary domain conditions are discharged or retained as obligations.
In mixed analysis, every rule hands its finiteness premises, and exact operations and mixed rules
their selection premises, to `prove`, which may analyze the operands. A selection premise it cannot
prove rejects the rule. The estimate of a generated rule carries its output's finiteness under
the premises of its bound. -/
def applyRule? (actual : Q(ℝ)) (label : Name) (prepare : MetaM Lean.Expr) (exact : Bool)
    (deriveInput : Q(ℝ) → AnalyzeM Estimate) (prove : MVarId → AnalyzeM Bool) :
    AnalyzeM (Option (Estimate × Bool)) := do
  let session ← read
  let initial ← get
  let boundaries := session.boundaries
  let result? ← transaction? do
    let rule ← prepare
    let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
    let some (candidate, _, _) ← numericalConclusion? conclusion | return none
    let mixedRule := (← mixedConclusion? conclusion).isSome
    let reference : Q(ℝ) ← mkFreshExprMVar q(ℝ)
    let bound : Bound ← if exact then pure (.absolute q(0))
      else if mixedRule then pure (.mixed (← mkFreshExprMVar q(ℝ)) (← mkFreshExprMVar q(ℝ)))
      else pure (.absolute (← mkFreshExprMVar q(ℝ)))
    let target : Q(Prop) := if exact then q($actual = $reference)
      else bound.statement actual reference
    let proof ← mkFreshExprMVar target
    let matched? ← attempt? 10000 do
      let matched ← withCanUnfoldPred (fun config info =>
        if boundaries.contains info.name then pure false else canUnfoldDefault config info) do
          -- Match the computation before its dependent representation parameters.
          if let some source := actual.getAppArgs.back? then
            if let some pattern := candidate.getAppArgs.back? then
              unless ← isDefEq pattern source do return false
          isDefEq candidate actual
      unless matched do return none
      unless ← isDefEq conclusion target do return none
      return some ()
    unless matched?.isSome do return none
    proof.mvarId!.assign (mkAppN rule arguments)
    trace[roundoff] "matched {label}; checking {arguments.size} parameters"
    -- Detect input-reference parameters before solving any premise. Two inputs may share a
    -- reference, so assigning it for the first must not hide the second input's error premise.
    let needed ← getMVars (← instantiateMVars reference)
    let mut inputs := #[]
    for h : index in [:arguments.size] do
      let argument ← instantiateMVars arguments[index]
      unless argument.isMVar do continue
      let type ← instantiateMVars (← argument.mvarId!.getType)
      let some wanted ← inputReference? type | continue
      let mut feedsReference := false
      for dependency in wanted do
        if needed.contains dependency && !(← isProp (← dependency.getType)) then
          feedsReference := true
      if feedsReference then inputs := inputs.push index
    let propagatesInputs := !inputs.isEmpty
    let mut state := initial
    let mut allInputsAnalyzed := true
    for index in inputs do
      let argument ← instantiateMVars arguments[index]!
      let type ← instantiateMVars (← inferType argument)
      if type.isForall then
        -- A bound at every coordinate of the container that `actual` reads is rejected like an
        -- input equal to `actual`: supplying it would analyze the same read again.
        if ← boundsActual type actual then
          allInputsAnalyzed := false
          continue
        -- An error bound at every coordinate of a container input, from its analysis at a fresh one.
        let resolved? ← transaction? do
          let (supplied?, next) ← ((forallInput? type deriveInput).run session).run state
          let some supplied := supplied? | return none
          let matched? ← attempt? 10000 do
            unless ← isDefEq type (← inferType supplied) do return none
            if argument.isMVar then argument.mvarId!.assign supplied
            return some ()
          return matched?.map fun _ => next
        if let some next := resolved? then state := next
        else allInputsAnalyzed := false
        continue
      let some (value, _, premise) ← boundConclusion? type | do
        allInputsAnalyzed := false
        continue
      let value : Q(ℝ) ← instantiateMVars value
      if value.hasExprMVar || value == actual then
        allInputsAnalyzed := false
        continue
      let resolved? ← transaction? do
        let (bound, next) ← ((deriveInput value).run session).run state
        let supplied ← presentInput bound premise
        let matched? ← attempt? 10000 do
          unless ← isDefEq type (← inferType supplied) do return none
          if argument.isMVar then argument.mvarId!.assign supplied
          return some ()
        return matched?.map fun _ => next
      if let some next := resolved? then
        state := next
      else
        allInputsAnalyzed := false
    -- In mixed analysis an input error the analysis cannot supply rejects the rule; it never
    -- becomes an obligation.
    if session.mixed then
      for index in inputs do
        if (← instantiateMVars arguments[index]!).isMVar then return none
    -- An unchanged real reference needs no new domain assumptions. Keep the child validity
    -- obligations, including finiteness, domain and range conditions. Even a shared,
    -- already assigned premise must have its executed input analyzed before this shortcut.
    let reference : Q(ℝ) ← instantiateMVars reference
    if propagatesInputs && allInputsAnalyzed && !reference.hasExprMVar && !actual.hasExprMVar then
      let identical? ← if reference == actual then pure (some ()) else
        attempt? 1000 do
          return if ← withReducible (isDefEq reference actual) then some () else none
      if identical?.isSome then
        return some (← exactEstimate session.mixed actual, true, state)
    -- Capabilities still need their existing instance evidence; none is guessed or assumed.
    synthesizeInstances arguments binders
    -- A real parameter that neither the computation nor the inputs fix, such as the margin of
    -- `MixedError.log_one_add_of_le`, is the end of an enclosure that one of its premises bounds:
    -- of a computed value, read off its analysis, or else of the bounded exact value itself. Its
    -- other premises then become conditions rather than selecting the rule.
    let mut conditional := #[]
    if session.mixed && mixedRule then
      let budget ← match bound with
        | .mixed relative absolute =>
            pure [← instantiateMVars relative, ← instantiateMVars absolute]
        | .absolute error => pure [← instantiateMVars error]
      let computed ← inputs.filterMapM fun index => do
        let type ← instantiateMVars (← inferType arguments[index]!)
        return (← boundConclusion? type).map (·.1)
      for argument in arguments do
        let argument ← instantiateMVars argument
        unless argument.isMVar do continue
        let parameter := argument.mvarId!
        unless ← withReducible (isDefEq (← parameter.getType) q(ℝ)) do continue
        unless budget.any fun term => (term.findMVar? (· == parameter)).isSome do continue
        let mut choice? := none
        for premise in arguments do
          let premise ← instantiateMVars premise
          unless premise.isMVar do continue
          let type ← instantiateMVars (← premise.mvarId!.getType)
          if (type.findMVar? (· == parameter)).isSome then
            conditional := conditional.push premise.mvarId!
          let some (side, bounded) := parameterBound? parameter type | continue
          if bounded.hasExprMVar then continue
          let onComputed := computed.any fun value => (bounded.find? (· == value)).isSome
          if choice?.isNone || onComputed then
            choice? := some (premise.mvarId!, side, bounded, onComputed)
        let some (premise, side, bounded, onComputed) := choice? | continue
        let bounded : Q(ℝ) := bounded
        unless onComputed do
          parameter.assign (if side matches .magnitude then q(|$bounded|) else bounded)
          premise.assign (← mkAppM ``le_refl #[← instantiateMVars (mkMVar parameter)])
          continue
        let (estimate, next) ← ((deriveInput bounded).run session).run state
        state := next
        let .mixed relative absolute := estimate.bound | return none
        let center := estimate.reference
        let (value, enclosed, centered?) : Q(ℝ) × Name × Option Name := match side with
          | .upper => (q($center - ($relative * |$center| + $absolute)), ``MixedError.lower_le,
              some ``MixedError.lower_le_center)
          | .lower => (q($center + ($relative * |$center| + $absolute)), ``MixedError.le_upper,
              some ``MixedError.center_le_upper)
          | .magnitude => (q((1 + $relative) * |$center| + $absolute), ``MixedError.abs_le, none)
        parameter.assign value
        let enclosure ← mkAppM enclosed #[estimate.proof]
        unless ← isDefEq (← premise.getType) (← inferType enclosure) do return none
        premise.assign enclosure
        -- A premise bounding the parameter by the exact value of the same enclosure holds too.
        if let some centered := centered? then
          let center ← mkAppM centered #[estimate.proof]
          for other in conditional do
            if ← other.isAssigned then continue
            let matched? ← attempt? 1000 do
              return if ← isDefEq (← other.getType) (← inferType center) then some () else none
            if matched?.isSome then other.assign center
    let selective := session.mixed && (exact || mixedRule)
    let mut pending := #[]
    let mut finite := #[]
    for argument in arguments do
      let argument ← instantiateMVars argument
      unless argument.isMVar do continue
      let goal := argument.mvarId!
      let type ← instantiateMVars (← goal.getType)
      unless ← isProp type do continue
      -- The exactness of a conversion, a decoded value `toRat? x = some q` such as that of a
      -- literal, is evaluated; the rule applies only when it holds.
      if exact && type.isAppOfArity ``Eq 3 && (type.getArg! 1).isAppOf ``Model.toRat? then
        if type.hasFVar || type.hasMVar then return none
        let decided? ← attempt? 10000 do
          let remaining ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| decide +kernel)))
          return if remaining.isEmpty then some () else none
        if decided?.isNone then return none
        continue
      if conditional.contains goal then
        -- A condition the analysis does not prove, also when its search fails with an error,
        -- stays a condition.
        let proved? ← transaction? do
          let (proved, next) ← ((prove goal).run session).run state
          return if proved then some next else none
        if let some next := proved? then state := next
        else if let some condition ← session.tidy goal then
          pending := pending ++ (← require session condition)
      else if session.mixed && isFiniteness type then
        finite := finite.push goal
      else if selective && (← isSelection type) then
        let (proved, next) ← ((prove goal).run session).run state
        unless proved do return none
        state := next
      else if selective && (isNonzeroTest type || type.isForall ||
          (type.isAppOfArity ``Ne 3 && (← isRealOrder type))) then
        -- A nonzero divisor follows from its sign, and a fact about every entry from the facts
        -- about one, or each remains an obligation.
        let (proved, next) ← ((prove goal).run session).run state
        state := next
        unless proved do pending := pending ++ (← require session goal)
      else if (domainValue? type).isSome then
        -- The domain of a square root follows from the sign of its operand, or remains.
        let proved? ← transaction? do
          let (proved, next) ← ((prove goal).run session).run state
          return if proved then some next else none
        if let some next := proved? then state := next
        else if !session.mixed then pending := pending ++ (← require session goal)
        else if let some condition ← session.tidy goal then
          pending := pending ++ (← require session condition)
      else if session.mixed then
        -- A premise of an instantiated rule reads its containers as the program does.
        if let some condition ← session.tidy goal then
          pending := pending ++ (← require session condition)
      else pending := pending ++ (← require session goal)
    -- The result's own finiteness comes first: its range theorem analyzes the operands.
    let source? := decodedValue? actual
    let mut own := #[]
    let mut operands := #[]
    -- A rule's instances may be spelled differently from the program's.
    let concernsSource (type : Lean.Expr) : MetaM Bool := do
      let (some source, some value) := (source?, type.getAppArgs[1]!.getAppArgs.back?) |
        return false
      if value == source then return true
      withReducible (isDefEq value source)
    for goal in finite do
      let type ← instantiateMVars (← goal.getType)
      if ← concernsSource type then own := own.push goal
      else operands := operands.push goal
    for goal in own ++ operands do
      let (proved, next) ← ((prove goal).run session).run state
      state := next
      unless proved do pending := pending.push goal
    for argument in arguments do
      let argument ← instantiateMVars argument
      unless argument.isMVar do continue
      unless ← isProp (← argument.mvarId!.getType) do return none
    let reference : Q(ℝ) ← instantiateMVars reference
    let bound ← match bound with
      | .absolute error => pure (Bound.absolute (← instantiateMVars error))
      | .mixed relative absolute =>
          pure (.mixed (← instantiateMVars relative) (← instantiateMVars absolute))
    let unresolved := match bound with
      | .absolute error => error.hasExprMVar
      | .mixed relative absolute => relative.hasExprMVar || absolute.hasExprMVar
    if reference.hasExprMVar || unresolved then
      trace[roundoff] "unresolved reference or budget after {label}"
      return none
    let mut finite? := none
    if session.mixed then
      for argument in arguments do
        let type ← instantiateMVars (← inferType argument)
        unless isFiniteness type do continue
        if ← concernsSource type then finite? := some (← instantiateMVars argument)
      if let (true, none, some source) := (exact, finite?, source?) then
        finite? ← exactFinite? label arguments source
      -- A generated rule also concludes that its output is finite, under the conditions of its
      -- bound; that conclusion is its finiteness rule.
      if let (false, none, some source) := (exact, finite?, source?) then
        finite? ← generatedFinite? session label arguments source
    let estimate ← if exact then
        rewriteActual (← exactEstimate session.mixed reference) (← instantiateMVars proof)
      else Estimate.inMode ⟨reference, bound, ← instantiateMVars proof, none⟩ session.mixed
    return some ({ estimate with finite? }, propagatesInputs,
      { state with pending := state.pending ++ pending })
  if let some (estimate, propagatesInputs, state) := result? then
    set state
    return some (estimate, propagatesInputs)
  return none

/-- Retrieve candidate laws for this computation before checking their full statements. -/
def registeredBound? (actual : Q(ℝ)) (deriveInput : Q(ℝ) → AnalyzeM Estimate)
    (prove : MVarId → AnalyzeM Bool) : AnalyzeM (Option (Estimate × Bool)) := do
  let session ← read
  let key ← session.indexKey actual
  let candidates ← withCanUnfoldPred (programCanUnfold session.boundaries false) do
    let ordinary ← rulesFor session.bounds actual key
    unless session.mixed do return ordinary
    -- Exact operations first, then mixed rules in registration order, then absolute rules.
    let preferred ← rulesFor session.mixedBounds actual key
    return preferred.qsort (·.order < ·.order) ++ ordinary
  let incompatible ← match actual.getAppArgs.back? with
    | some source => isNonBooleanTest source
    | none => pure false
  for rule in candidates do
    if selectionRules.contains rule.name then
      unless ← readsAccumulator actual do continue
      if incompatible then continue
    if session.symbolicBounds.contains rule.name then
      let some source := actual.getAppArgs.back? | continue
      let some position ← readPosition? source | continue
      unless ← symbolic source.getAppArgs[position]! do continue
    -- Subtracting a value from itself needs identical operands; unifying different ones would
    -- evaluate their code.
    if rule.name == ``ExecFloat.Binary.toReal_sub_self then
      let some source := actual.getAppArgs.back? | continue
      unless source.getAppNumArgs ≥ 2 && source.appFn!.appArg! == source.appArg! do continue
    trace[roundoff] "trying {rule.name}"
    if let some bound ← applyRule? actual rule.name rule.instantiate rule.exact deriveInput
        prove then
      return some bound
  return none

/-- A registered rule stated at a successor length, for a read of a container whose outer extent is
not literal, applied after `splitRead?` restates the read at that form. -/
def splitBound? (actual : Q(ℝ)) (deriveInput : Q(ℝ) → AnalyzeM Estimate)
    (prove : MVarId → AnalyzeM Bool) : AnalyzeM (Option (Estimate × Bool)) := do
  let session ← read
  let key ← session.indexKey actual
  let candidates ← withCanUnfoldPred (programCanUnfold session.boundaries false) do
    let ordinary ← rulesFor session.bounds actual key
    let preferred ← if session.mixed then rulesFor session.mixedBounds actual key else pure #[]
    return ordinary.size + preferred.size
  if candidates == 0 then return none
  let some (next, observe, equality) ← restate? actual | return none
  let some (estimate, propagatesInputs) ← registeredBound? next deriveInput prove | return none
  return some (← rewriteValue estimate observe equality, propagatesInputs)

/-- The finiteness of a primitive call by its contract, under the premises already instantiated
for the call's rounding theorem. -/
def primitiveFiniteness? (contract : PrimitiveContract) (source : Lean.Expr)
    (premises : Array MVarId) : MetaM (Option Lean.Expr) := do
  let some (proof, remaining) ← instantiatePrimitive contract contract.finite source |
    return none
  for goal in remaining do
    let type ← instantiateMVars (← goal.getType)
    let some premise ← premises.findM? fun premise => do
        isDefEq (← instantiateMVars (← premise.getType)) type
      | return none
    goal.assign (← instantiateMVars (mkMVar premise))
  return some (← instantiateMVars proof)

/-- Bound a call of a correctly rounded primitive by its one rounding at the real reference: half
an ulp, or in mixed analysis the unit roundoff and the underflow allowance, together with the
call's finiteness under the same premises. An exact case of the contract whose premises `prove`
establishes, such as a zero input, comes first and gives the result without error. Mixed
analysis proves the domain and range premises with `prove` where it can, and the domain
`-1 < x` of `log1p` from the enclosure of `1 + x` that `deriveInput` gives. The others are
discharged or kept open. With `computedCalls` the call is its own exact reference instead, with
its finiteness when `prove` shows it. -/
def primitiveBound? (actual : Q(ℝ)) (deriveInput : Q(ℝ) → AnalyzeM Estimate)
    (prove : MVarId → AnalyzeM Bool) : AnalyzeM (Option Estimate) := do
  unless actual.isAppOf ``ExecFloat.Binary.toReal do return none
  let source := actual.getAppArgs.back!
  let session ← read
  for contract in ← primitiveContracts do
    for name in contract.exact do
      let exactCase? ← speculate? do
        let some (proof, premises) ← instantiatePrimitive contract name source |
          throwError "roundoff: {name} does not apply"
        for premise in premises do
          unless ← prove premise do throwError "roundoff: unproved premise of {name}"
        let some (_, _, value) := (← inferType proof).eq? |
          throwError "roundoff: {name} does not state an equality"
        rewriteActual (← exactEstimate session.mixed (← instantiateMVars value)) proof
      if exactCase?.isSome then return exactCase?
    let some (rounding, premises) ← attempt? 2000
        (instantiatePrimitive contract contract.rounding source) | continue
    if session.computedCalls then
      let finite ← mkFreshExprMVar
        (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[source]) (mkConst ``Bool.true))
      let finite? ← if ← prove finite.mvarId! then pure (some (← instantiateMVars finite))
        else pure none
      return some { ← exactEstimate true actual with finite? }
    let some (_, _, rounded) := (← inferType rounding).eq? |
      throwError "roundoff: {contract.rounding} does not state an equality"
    unless rounded.isAppOfArity ``Model.roundAt 3 do
      throwError "roundoff: {contract.rounding} does not state a nearest-even rounding"
    let format := rounded.getAppArgs[0]!
    let reference : Q(ℝ) := rounded.getAppArgs[1]!
    -- The lower end of the enclosure of `1 + x` is the margin of the error rule of the
    -- logarithm, so the domain `-1 < x` and that rule leave the same condition.
    let domainByEnclosure (premise : MVarId) : AnalyzeM Bool := do
      let type : Q(Prop) ← instantiateMVars (← premise.getType)
      let ~q((-1 : ℝ) < $argument) := type | return false
      let enclosed? ← speculate? do
        let estimate ← deriveInput q(1 + $argument)
        let .mixed relative absolute := estimate.bound |
          throwError "roundoff: expected a mixed enclosure"
        let center := estimate.reference
        let lower ← mkFreshExprMVar q(0 < $center - ($relative * |$center| + $absolute))
        premise.assign (← mkAppM ``neg_one_lt_of_mixedError_one_add #[estimate.proof, lower])
        if let some condition ← session.tidy lower.mvarId! then
          unless ← discharge session condition do
            modify fun state => { state with pending := state.pending.push condition }
      return enclosed?.isSome
    for premise in premises do
      if session.mixed then
        if ← prove premise then continue
        if ← domainByEnclosure premise then continue
      let remaining ← require session premise
      modify fun state => { state with pending := state.pending ++ remaining }
    unless session.mixed do
      let error ← mkAppM ``Model.halfUlpAt #[format, reference]
      let proof ← mkAppM ``Model.abs_roundAt_sub_le #[format, reference]
      return some (← rewriteActual ⟨reference, .absolute error, proof, none⟩ rounding)
    let proof ← mkAppM ``ExecFloat.Binary.mixedError_toReal_of_eq_roundAt #[rounding]
    let some (_, _, relative, absolute) ← mixedConclusion? (← inferType proof) |
      throwError "roundoff: expected the mixed error of {contract.rounding}"
    return some ⟨reference, .mixed relative absolute, proof,
      ← primitiveFiniteness? contract source premises⟩
  return none

/-- Existing FloatLib soundness theorems supply real enclosures independently of the selected
implementation's accuracy. The configured and model functions they bound are defined in the
optional transcendental modules, so they are named here without importing those modules. -/
def elementaryEnclosures : Array (Name × Array Name) := #[
  (``FloatLib.Numerics.Interval.containsReal_sinBounds,
    #[``MathFunctions.sin, `FloatLib.Floats.ExecFloat.Binary.sin,
      `FloatLib.Floats.Formats.BinaryInterchange.Model.sin]),
  (``FloatLib.Numerics.Interval.containsReal_cosBounds,
    #[``MathFunctions.cos, `FloatLib.Floats.ExecFloat.Binary.cos,
      `FloatLib.Floats.Formats.BinaryInterchange.Model.cos]),
  (``FloatLib.Numerics.Interval.containsReal_sinhBounds,
    #[``MathFunctions.sinh, `FloatLib.Floats.ExecFloat.Binary.sinh,
      `FloatLib.Floats.Formats.BinaryInterchange.Model.sinh]),
  (``FloatLib.Numerics.Interval.containsReal_coshBounds,
    #[``MathFunctions.cosh, `FloatLib.Floats.ExecFloat.Binary.cosh,
      `FloatLib.Floats.Formats.BinaryInterchange.Model.cosh]),
  (``FloatLib.Numerics.Interval.containsReal_tanhBounds,
    #[``MathFunctions.tanh, `FloatLib.Floats.ExecFloat.Binary.tanh,
      `FloatLib.Floats.Formats.BinaryInterchange.Model.tanh])]

/-- Compare an actual primitive result with its certified rational enclosure. The shared
composition pass propagates input error afterward, and endpoints stay symbolic during
construction. -/
def intervalBound? (actual : Q(ℝ)) : AnalyzeM (Option Estimate) := do
  let configured := actual.isAppOf ``ExecFloat.Binary.toReal
  unless configured || actual.isAppOf ``Model.toReal do return none
  let source := actual.getAppArgs.back!
  let name := source.getAppFn.constName?.getD .anonymous
  let some (soundnessName, _) := elementaryEnclosures.find? (fun entry => entry.2.contains name)
    | return none
  let argument := source.getAppArgs.back!
  let modelOf (value : Lean.Expr) : MetaM Lean.Expr :=
    if configured then mkAppM ``ExecFloat.Binary.toModel #[value] else pure value
  let input ← modelOf argument
  let candidate ← modelOf source
  let modelType ← inferType candidate
  unless modelType.isAppOfArity ``Model 1 do
    throwError "roundoff: the candidate has no binary descriptor model"
  let precision ← mkAppM ``FloatFormat.fracWidth #[modelType.getAppArgs[0]!]
  let terms ← mkAppM ``max #[mkNatLit 8, precision]
  let rational ← mkAppM ``Option.getD #[← mkAppM ``Model.toRat? #[input], q((0 : Rat))]
  let point ← mkAppM ``FloatLib.Numerics.Interval.point #[rational]
  let contained ← mkAppM soundnessName #[point, terms, ← mkAppM ``Model.containsReal_point_toRat
      #[input]]
  let finite (value model : Lean.Expr) : MetaM Lean.Expr := do
    let predicate ← if configured then mkAppM ``ExecFloat.Binary.isFinite #[value]
      else mkAppM ``Model.isFinite #[model]
    mkEq predicate (mkConst ``Bool.true)
  let inputFinite ← mkFreshExprMVar (← finite argument input)
  let outputFinite ← mkFreshExprMVar (← finite source candidate)
  let session ← read
  for premise in #[inputFinite, outputFinite] do
    let remaining ← require session premise.mvarId!
    modify fun state => { state with pending := state.pending ++ remaining }
  let proof ← mkAppM ``Model.abs_toReal_sub_le_of_containsReal
    #[input, candidate, inputFinite, outputFinite, contained]
  let type : Q(Prop) ← instantiateMVars (← inferType proof)
  match type with
  | ~q(|($observed : ℝ) - $reference| ≤ $error) =>
      unless ← isDefEq observed actual do
        throwError "roundoff: enclosure result does not observe the requested computation"
      return some ⟨reference, .absolute error, proof, none⟩
  | _ => throwError "roundoff: unexpected interval error theorem {type}"

/-- The variable or definition computing `value`: the function of a call, the producer of a container
read, through projections, written as primitive projections. -/
partial def producer (environment : Environment) (reads : Array Read) (value : Lean.Expr) :
    Lean.Expr :=
  let value := value.consumeMData
  if let some position := Read.position? reads value then
    producer environment reads value.getAppArgs[position]!
  else match value.getAppFn.consumeMData with
    | .proj owner index source => .proj owner index (producer environment reads source)
    | function@(.const name _) =>
      match environment.getProjectionFnInfo? name, environment.getProjectionStructureName? name with
      | some info, some owner =>
        if value.getAppNumArgs > info.numParams then
          .proj owner info.i (producer environment reads value.getAppArgs[info.numParams]!)
        else function
      | _, _ => function
    | function => function

/-- `fun xs => projection (proof xs)`, the conjunct `projection` of the conclusion of `proof`. -/
def projectConclusion (proof : Lean.Expr) (projection : Name) : MetaM Lean.Expr := do
  forallTelescope (← inferType proof) fun arguments _ => do
    mkLambdaFVars arguments (← mkAppM projection #[mkAppN proof arguments])

/-- Whether a hypothesis is stated like a generated theorem, concluding under its conditions the
finiteness and a mixed bound of a value with the producer of `value`, as the contract of a
function variable does. -/
def isGeneratedForm (declaration : LocalDecl) (value : Lean.Expr) : MetaM Bool := do
  if declaration.isImplementationDetail then return false
  unless declaration.type.getForallBody.consumeMData.isAppOfArity ``And 2 do return false
  forallTelescope (← instantiateMVars declaration.type) fun _ conclusion => do
    let some (finite, _) := finiteMixed? conclusion | return false
    let some candidate := finite.getAppArgs[1]!.getAppArgs.back? | return false
    let environment ← getEnv
    let reads := (← extension).reads
    return producer environment reads candidate == producer environment reads value

/-- How the hypothesis `declaration` bounds a value (`Given`), in the analysis mode of `session`.
Mixed hypotheses are read only by mixed analysis, absolute ones by both. For mixed analysis, a
bound between two decoded values is a range fact and does not count as an input error. -/
def Session.readGiven (session : Session) (declaration : LocalDecl) : MetaM Given := do
  unless ← isProp declaration.type do return { proposition := false }
  let type ← instantiateMVars declaration.type
  let producer? ← if session.mixed && !declaration.isImplementationDetail &&
      declaration.type.getForallBody.consumeMData.isAppOfArity ``And 2 then
    forallTelescope type fun arguments conclusion => do
      let some (finite, _) := finiteMixed? conclusion | return none
      let some candidate := finite.getAppArgs[1]!.getAppArgs.back? | return none
      let produced := producer (← getEnv) (← extension).reads candidate
      -- A producer bound by the hypothesis is no computation's.
      if mentions produced (fun id => arguments.any (·.fvarId! == id)) then return none
      return some produced
    else pure none
  let heads (generated : Bool) : MetaM (Option BoundHeads) := withNewMCtxDepth do
    let (_, _, type) ← forallMetaTelescope type
    let type : Q(Prop) := if generated then (finiteMixed? type).map (·.2) |>.getD type
      else type
    let value? ← match type with
      | ~q(|($value : ℝ) - $reference| ≤ $_error) =>
          if session.mixed && (reference.find? fun term =>
              term.isAppOf ``ExecFloat.Binary.toReal || term.isAppOf ``Model.toReal).isSome then
            pure none
          else pure (some value)
      | _ => if session.mixed then pure ((← mixedConclusion? type).map (·.1)) else pure none
    return value?.map boundHeads
  let generatedHeads? ← if producer?.isSome then heads true else pure none
  return { proposition := true, producer?, heads? := ← heads false, generatedHeads? }

/-- `Session.readGiven`, read once per local variable and analysis mode. -/
def Session.given (session : Session) (declaration : LocalDecl) : MetaM Given := do
  let key := (declaration.fvarId, session.mixed)
  if let some given := (← session.givens.get).get? key then return given
  let given ← session.readGiven declaration
  session.givens.modify (·.insert key given)
  return given

/-- The hypotheses of the local context that bound a value (`Session.given`), in order, read once
per local context and analysis mode. -/
def Session.hypothesisBounds (session : Session) : MetaM (Array (LocalDecl × Given)) := do
  let key := ((← getLCtx).getFVarIds, session.mixed)
  if let some bounds := (← session.givenBounds.get).get? key then return bounds
  let mut bounds := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let given ← session.given decl
    if given.proposition && (given.heads?.isSome || given.generatedHeads?.isSome) then
      bounds := bounds.push (decl, given)
  session.givenBounds.modify (·.insert key bounds)
  return bounds

/-- Reuse scalar or pointwise bounds, discharging their conditional premises in the current
branch or leaving the required evidence visible to the caller. Mixed analysis reads a hypothesis
stated like a generated theorem through its bound, and `proveFinite` uses its finiteness. The
result also says whether the bound is final. A supplied input error, or a bound that propagated
input errors, is used as it is. A hypothesis stated like a generated theorem is a contract whose
reference is its model at the computed argument, which `Analyze.build` then propagates through the
model when it can. -/
def givenBound? (actual : Q(ℝ)) (deriveInput : Q(ℝ) → AnalyzeM Estimate)
    (prove : MVarId → AnalyzeM Bool) : AnalyzeM (Option (Estimate × Bool)) := do
  let session ← read
  let heads := boundHeads actual
  let produced? := (decodedValue? actual).map (producer (← getEnv) (← extension).reads)
  for (decl, given) in ← session.hypothesisBounds do
    let generated := session.mixed && given.producer?.isSome && given.producer? == produced?
    unless (if generated then given.generatedHeads? else given.heads?) == some heads do continue
    let prepare := do
      let hypothesis ← if generated then projectConclusion decl.toExpr ``And.right
        else pure decl.toExpr
      normalizeRule session (← specializeLocalError hypothesis)
    if let some (bound, propagatesInputs) ← applyRule? actual decl.userName prepare false
        deriveInput prove then
      return some (bound, propagatesInputs || !generated)
  return none

/-- Share repeated premises and bind the remaining ones as a stated condition.
Branches, loop invariants and generated statements use the same condition handling. The outcomes
of comparisons without metavariables are kept in `comparisons` for later calls. -/
def withConditions {α : Type} (candidates : Array MVarId)
    (comparisons : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) Bool))
    (action : Q(Prop) → Lean.Expr → TacticM α) : TacticM α := do
  let mut goals := #[]
  let mut known : Lean.ExprMap MVarId := {}
  let mut indexed : Array ((Name × Name) × Lean.Expr × MVarId) := #[]
  for goal in candidates do
    if ← goal.isAssigned then continue
    let type ← instantiateMVars (← goal.getType)
    unless ← isProp type do throwError "roundoff: unresolved data parameter {type}"
    if let some earlier := known.get? type then
      goal.assign (mkMVar earlier)
    else
      -- Restrict definitional comparison to matching predicates and source heads, avoiding
      -- expansion of unrelated floating-point implementations during deduplication.
      let body := type.getForallBody
      let predicate := if body.isAppOfArity ``Eq 3 then body.getAppArgs[1]! else body
      let key := (predicate.getAppFn.constName?.getD .anonymous,
        predicate.getAppArgs.back?.bind (·.getAppFn.constName?) |>.getD .anonymous)
      let mut duplicate := false
      for (earlierKey, earlierType, earlier) in indexed do
        unless key == earlierKey do continue
        let pair := (type, earlierType)
        let memo := if type.hasMVar || earlierType.hasMVar then none else some comparisons
        let matched ← match ← memo.bindM fun memo => return (← memo.get).get? pair with
          | some matched => pure matched
          | none => do
            -- Equal premises agree at reducible transparency or after a few unfoldings; a
            -- comparison of different ones would expand their computations, so the full one
            -- gets a small budget.
            let depths ← depthsCaught
            let reducible := (← attempt? 1000 do
              return if ← withReducibleAndInstances (isDefEq type earlierType) then some ()
                else none).isSome
            let matched := reducible || (← attempt? 100 do
              return if ← isDefEq type earlierType then some () else none).isSome
            if let some memo := memo then
              if matched || (← depthsCaught) == depths then memo.modify (·.insert pair matched)
            pure matched
        if matched then
          goal.assign (mkMVar earlier)
          duplicate := true
          break
      unless duplicate do
        goals := goals.push goal
        known := known.insert type goal
        indexed := indexed.push (key, type, goal)
  let mut condition : Q(Prop) := q(True)
  for goal in goals.reverse do
    let type : Q(Prop) ← instantiateMVars (← goal.getType)
    condition := q($type ∧ $condition)
  let mut simplifications : SimpTheorems := {}
  for name in #[``and_true, ``true_and] do
    simplifications ← simplifications.addConst name
  let context ← Simp.mkContext { implicitDefEqProofs := false } #[simplifications]
  let (simplified, _) ← simp condition context
  let simplifiedCondition : Q(Prop) := simplified.expr
  withLocalDeclD `conditions simplifiedCondition fun evidence => do
    let mut remaining ← mkAppM ``Eq.mpr #[← simplified.getProof' condition, evidence]
    for goal in goals do
      goal.assign (← mkAppM ``And.left #[remaining])
      remaining ← mkAppM ``And.right #[remaining]
    action simplifiedCondition evidence

/-- Keep branch-specific side conditions under their guard. Neither a cached proof nor a
finiteness obligation from one branch may escape into the other. -/
def inBranch (condition : Q(Prop)) (action : Lean.Expr → AnalyzeM Estimate) :
    AnalyzeM Estimate := do
  let initial ← get
  let outerContext ← getLCtx
  let outerInstances ← getLocalInstances
  let (estimate, pending) ← withLocalDeclD `branch condition fun guard => do
    let estimate ← action guard
    let localGoals := (← get).pending.extract initial.pending.size (← get).pending.size
    let (numerical, finite?, pending) ← if localGoals.isEmpty then
        pure (← instantiateMVars estimate.proof, ← estimate.finite?.mapM instantiateMVars, #[])
      else withConditions localGoals (← read).comparisons fun condition evidence => do
        let type ← mkForallFVars #[guard] condition
        let closed ← withLCtx outerContext outerInstances (mkFreshExprMVar type)
        let discharged (proof : Lean.Expr) : MetaM Lean.Expr := do
          let conditional ← mkLambdaFVars #[evidence] (← instantiateMVars proof)
          return mkApp conditional (mkApp closed guard)
        let finite? ← (estimate.finite?.mapM discharged : MetaM _)
        pure (← discharged estimate.proof, finite?, #[closed.mvarId!])
    let abstract (value : Lean.Expr) : MetaM Lean.Expr := do
      mkLambdaFVars #[guard] (← instantiateMVars value)
    let bound ← match estimate.bound with
      | .absolute error => pure (Bound.absolute (← abstract error))
      | .mixed relative absolute => pure (.mixed (← abstract relative) (← abstract absolute))
    let proof ← mkLambdaFVars #[guard] numerical
    let finite? ← (finite?.mapM abstract : MetaM _)
    pure (⟨← abstract estimate.reference, bound, proof, finite?⟩, pending)
  set { initial with pending := initial.pending ++ pending }
  return estimate

/-- Analyze a scalar step once under an incoming accumulator bound. Its new premises become
one condition on visited states, and no local variables or cached proofs escape the loop. -/
def deriveStep (observe step inputType stateType : Lean.Expr)
    (analyzeBody : Q(ℝ) → AnalyzeM Estimate) : AnalyzeM StepEstimate := do
  let before ← get
  let result ← withLocalDeclD `accumulator stateType fun accumulator =>
    withLocalDeclD `reference q(ℝ) fun reference =>
    withLocalDeclD `budget q(ℝ) fun budget =>
    withLocalDeclD `value inputType fun value => do
      let observed : Q(ℝ) := (mkApp observe accumulator).headBeta
      let reference : Q(ℝ) := reference
      let budget : Q(ℝ) := budget
      withLocalDeclD `accumulator_error q(|$observed - $reference| ≤ $budget) fun incoming => do
        let actual : Q(ℝ) := (mkApp observe (mkAppN step #[accumulator, value]).headBeta).headBeta
        -- A loop that the step holds is nested in this one.
        let estimate ← withReader (fun session => { session with nested := true })
          (analyzeBody actual)
        let .absolute error := estimate.bound |
          throwError "roundoff: a loop step needs an absolute bound"
        let candidates := (← get).pending.extract before.pending.size (← get).pending.size
        withConditions candidates (← read).comparisons fun condition evidence => do
          if mentions condition (· == incoming.fvarId!) then
            throwError "roundoff: a loop condition depends on its proof argument"
          if mentions estimate.reference fun id =>
              id == accumulator.fvarId! || id == budget.fvarId! then
            throwError "roundoff: the loop's real reference depends on its rounded accumulator; \
              establish agreement of its branch conditions first"
          let referenceFunction ← mkLambdaFVars #[reference, value] estimate.reference
          let errorFunction ← mkLambdaFVars #[accumulator, reference, budget, value] error
          let conditionFunction ← mkLambdaFVars #[accumulator, reference, budget, value] condition
          let actualCondition? ← if mentions condition fun id =>
              id == reference.fvarId! || id == budget.fvarId! then pure none
            else pure (some (← mkLambdaFVars #[accumulator, value] condition))
          let proof ← mkLambdaFVars #[accumulator, reference, budget, value, evidence, incoming]
            (← instantiateMVars estimate.proof)
          pure ⟨referenceFunction, errorFunction, conditionFunction, proof, actualCondition?⟩
  set before
  return result

/-- Metadata on an application spine carries elaboration information and no computation.
Keep every argument, including the selected dictionaries, while exposing the actual head. -/
def stripHeadMetadata : Lean.Expr → Lean.Expr
  | .mdata _ expression => stripHeadMetadata expression
  | expression@(.app function argument) =>
      expression.updateApp! (stripHeadMetadata function) argument
  | expression => expression

/-- Substitute the local definitions at the head of an expression, so that the rules and the
operand pass see the operation an unfolded definition computes instead of its `let` bindings. -/
partial def headZeta : Lean.Expr → Lean.Expr
  | .letE _ _ value body _ => headZeta (body.instantiate1 value)
  | expression => expression

/-- Evidence from a hypothesis for a branch guard (`true`) or for its negation (`false`): the
guard or its negation itself, and for a guard `a = b` also `b = a`, `a ≠ b` or `b ≠ a`. -/
def guardHypothesis? (condition : Lean.Expr) : MetaM (Option (Bool × Lean.Expr)) := do
  let condition := stripHeadMetadata (← instantiateMVars condition)
  let swapped? := condition.eq?.map fun (type, left, right) =>
    mkApp3 condition.getAppFn type right left
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type := stripHeadMetadata (← instantiateMVars declaration.type)
    if type == condition then return some (true, declaration.toExpr)
    if swapped? == some type then return some (true, ← mkEqSymm declaration.toExpr)
    let negated? := match type.not?, type.ne? with
      | some negated, _ => some (stripHeadMetadata negated)
      | none, some (scalar, left, right) =>
          some (mkApp3 (mkConst ``Eq type.getAppFn.constLevels!) scalar left right)
      | none, none => none
    let some negated := negated? | continue
    if negated == condition then return some (false, declaration.toExpr)
    if swapped? == some negated then
      return some (false, ← mkAppM ``Ne.symm #[declaration.toExpr])
  return none

/-- Decide a branch guard by a hypothesis, or else by simplification as `decideGuard?` does. -/
def guardEvidence? (session : Session) (condition : Lean.Expr) :
    TacticM (Option (Bool × Lean.Expr)) := do
  if let some evidence ← guardHypothesis? condition then return some evidence
  decideGuard? session condition

/-- Evidence against a branch guard `test = true`: a registered theorem concluding `test = false`
(`Session.refutations`) whose premises the context discharges, such as the finiteness of an input
whose infinity test the guard is. A refutation whose proof would keep an unresolved obligation is
not taken, so refuting a guard assumes nothing beyond the context. -/
def refutedGuard? (condition : Lean.Expr) : AnalyzeM (Option Lean.Expr) := do
  let session ← read
  if session.refutations.isEmpty then return none
  let some (type, test, value) := (← instantiateMVars condition).consumeMData.eq? | return none
  unless type.isConstOf ``Bool && value.isConstOf ``Bool.true do return none
  for name in session.refutations do
    let result? ← transaction? do
      let rule ← mkConstWithFreshMVarLevels name
      let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
      let some (_, left, _) := conclusion.eq? | return none
      let matched? ← attempt? 10000 do
        let matched ← withCanUnfoldPred (fun config info =>
            if session.boundaries.contains info.name then pure false
            else canUnfoldDefault config info) do
          withReducible (isDefEq left test)
        return if matched then some () else none
      unless matched?.isSome do return none
      synthesizeInstances arguments binders
      for argument in arguments do
        let argument ← instantiateMVars argument
        unless argument.isMVar do continue
        let goal := argument.mvarId!
        let type ← instantiateMVars (← goal.getType)
        unless ← isProp type do return none
        unless ← discharge session goal do return none
      let proof ← instantiateMVars (mkAppN rule arguments)
      if proof.hasExprMVar then return none
      return some (← mkAppM ``ne_true_of_eq_false #[proof])
    if result?.isSome then return result?
  return none

/-- Apply one existing container-read equality after ordinary coordinate simplification stalls.
Only this fully typed observation uses default transparency and local-let expansion. The selected
storage, original producer, and scalar callback stay in its checked proof. -/
def readObservation? (name : Name) (expression : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let expression ← instantiateMVars expression
  if expression.hasExprMVar then return none
  withoutModifyingState <| withNewMCtxDepth do
    try
      let rule ← mkConstWithFreshMVarLevels name
      let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
      let some (_, left, right) := conclusion.eq? | return none
      unless ← withConfig (fun config =>
          { config with transparency := .default, zetaDelta := true })
          (isDefEq left expression) do return none
      -- An instance the read needs but its producer does not take comes from the context.
      synthesizeInstances arguments binders
      let result ← instantiateMVars right
      let proof ← instantiateMVars (mkAppN rule arguments)
      if result.hasExprMVar || proof.hasExprMVar || proof.hasLevelMVar then return none
      let expected ← mkEq expression result
      let proof := mkApp2 (mkConst ``id [0]) expected proof
      check proof
      return some (result, proof)
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      return none

/-- Whether the read `value` of a container that `producer` computes reads `producer` again at a
shape of the same skeleton (`Extension.skeleton`), such as a row read applied to a vector. Such a
read makes no progress, and applying it again would not end. -/
def rereads (producer : Name) (container value : Expr) : MetaM Bool := do
  let some original ← skeleton? container | return false
  let found ← IO.mkRef false
  value.forEach' fun term => do
    if (← found.get) then return false
    if term.hasLooseBVars || !term.isAppOf producer then return true
    if (← skeleton? term) == some original then found.set true
    return true
  found.get

/-- One step of exposing the computation behind a decoded container read or definition, as the
analysis does: the coordinate equalities, the unfolding of a container producer, or the unfolding
of the definition that computes the value. Returns the exposed observation and, unless the step
is definitional, a proof that it equals the original one. -/
def exposeObservation (session : Session) (observation : Lean.Expr) :
    MetaM (Option (Lean.Expr × Option Lean.Expr)) := do
  unless observation.isAppOf ``ExecFloat.Binary.toReal do return none
  let source := observation.getAppArgs.back!
  let observe := mkAppN observation.getAppFn observation.getAppArgs.pop
  let name := source.getAppFn.constName?.getD .anonymous
  if let some position ← readPosition? source (getters := true) (strict := false)
      (certified := true) then
    let (context, procedures) ← coordinateSimpContext session
    let normalized ← session.normalize `coordinate observation context procedures
    if normalized.expr != observation then
      return some (normalized.expr, some (← normalized.getProof' observation))
    let container := source.getAppArgs[position]!
    if let some producer ← unfoldDefinition? container then
      unless producer == container do
        let arguments := source.getAppArgs.set! position producer
        return some (mkApp observe (mkAppN source.getAppFn arguments), none)
    for fallback in (← extension).readFallbacks do
      if let some (value, equality) ← readObservation? fallback source then
        return some (mkApp observe value, some (← mkCongrArg observe equality))
    return none
  -- Arithmetic and the primitives have their own sign rules; other definitions are unfolded.
  if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Neg.neg, ``ite, ``dite].contains name
  then return none
  let some unfolded ← unfoldDefinition? source | return none
  return some (mkApp observe unfolded.headBeta, none)

/-- The sign of `x` from `rounding : x = Model.roundAt format t` and the same sign of `t`, by
monotone rounding. -/
def roundedSign (rounding sign : Lean.Expr) (nonneg : Bool) : MetaM Lean.Expr := do
  let some (_, _, rounded) := (← inferType rounding).eq? |
    throwError "roundoff: expected a rounding identity"
  let format := rounded.getAppArgs[0]!
  let signOfRounding ← mkAppM (if nonneg then ``Model.roundAt_nonneg else ``Model.roundAt_nonpos)
    #[format, sign]
  let motive : Q(ℝ → Prop) := if nonneg then q(fun value : ℝ => 0 ≤ value)
    else q(fun value : ℝ => value ≤ 0)
  mkEqMPR (← mkCongrArg motive rounding) signOfRounding

/-- The depth of a sign search. Each rule, branch and fold step it passes through uses a level. -/
def signDepth : Nat := 10

/-- Configured operations whose decoded operands mixed analysis derives before trying candidate
rules. -/
def floatOperations : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Neg.neg]

/-- Real operations whose operands mixed analysis derives before trying candidate rules. -/
def realOperations : Array Name :=
  #[``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Neg.neg, ``abs, ``Max.max, ``Min.min,
    ``Real.exp, ``Real.log, ``Real.sqrt]

/-- Compose a local bound of `actual` against an intermediate value with the bound of that
intermediate value against the final reference. An exact step contributes no budget. -/
def compose (step input : Estimate) : MetaM Estimate := do
  match step.bound, input.bound with
  | .absolute error, .absolute inputError =>
      return ⟨input.reference, .absolute q($inputError + $error),
        ← mkAppM ``compose_error #[step.proof, input.proof], step.finite?⟩
  | .mixed relative absolute, .mixed inputRelative inputAbsolute =>
      if input.bound.isExact then
        return ← rewriteReference step (← exactEquality input.proof)
      if step.bound.isExact then
        return { ← rewriteActual input (← exactEquality step.proof) with finite? := step.finite? }
      return ⟨input.reference,
        .mixed q((1 + $relative) * $inputRelative + $relative)
          q((1 + $relative) * $inputAbsolute + $absolute),
        ← mkAppM ``MixedError.trans #[step.proof, input.proof], step.finite?⟩
  | _, _ => throwError "roundoff: cannot compose an absolute and a mixed bound"

/-- Tidy the reference and budgets of a mixed estimate with identities of zero and one. Terms
without metavariables share the session's cache of tidied terms, since an assignment, or its
rollback, could change the meaning of another term. -/
def Session.simplify (session : Session) (estimate : Estimate) : MetaM Estimate := do
  let .mixed relative absolute := estimate.bound | return estimate
  let context ← Simp.mkContext { implicitDefEqProofs := false } #[session.budget]
  let tidy (term : Lean.Expr) := session.tidyTerm term context
  let reference' ← tidy estimate.reference
  let estimate ← if reference'.expr == estimate.reference then pure estimate
    else rewriteReference estimate (← reference'.getProof' estimate.reference)
  let relative' ← tidy relative
  let absolute' ← tidy absolute
  if relative'.expr == relative && absolute'.expr == absolute then return estimate
  let statement ← instantiateMVars (← inferType estimate.proof)
  let observed := mkApp2 (mkConst ``MixedError) statement.getAppArgs[0]! estimate.reference
  -- Built directly, as `transportReal` is, for both budgets at once.
  let equality := mkApp8 (mkConst ``congr [1, 1]) q(ℝ) (mkSort 0)
    (mkApp observed relative) (mkApp observed relative'.expr) absolute absolute'.expr
    (mkApp6 (mkConst ``congrArg [1, 1]) q(ℝ) q(ℝ → Prop) relative relative'.expr
      observed (← relative'.getProof' relative)) (← absolute'.getProof' absolute)
  return { estimate with
    bound := .mixed relative'.expr absolute'.expr
    proof := mkApp4 (mkConst ``Eq.mp [0]) (mkApp2 observed relative absolute)
      (mkApp2 observed relative'.expr absolute'.expr) equality estimate.proof }

/-- Restate an absolute budget that the identities of zero and one reduce to zero as the numeral
zero. Absolute budgets are otherwise kept as derived. The restatement makes a branch of exact
cases, such as a backward slice read inside or outside its range, exact. -/
def Session.zeroBudget (session : Session) (estimate : Estimate) : MetaM Estimate := do
  let .absolute error := estimate.bound | return estimate
  let context ← Simp.mkContext { implicitDefEqProofs := false } #[session.budget]
  let tidied ← session.tidyTerm error context
  unless tidied.expr.nat? == some 0 && tidied.expr != error do return estimate
  let statement ← instantiateMVars (← inferType estimate.proof)
  return { estimate with
    bound := .absolute tidied.expr
    proof := transportReal statement.appFn! error tidied.expr (← tidied.getProof' error)
      estimate.proof }

/-- Close an equality between real values by reflexivity, or by the local equalities and the
identities of zero and one. -/
def closeExactEquality (goal : MVarId) : TacticM Bool := do
  let closed? ← attempt? 2000 do
    let remaining ← Lean.Elab.Tactic.run goal do
      evalTactic (← `(tactic| first
        | rfl
        | (simp only [*, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one,
            Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat]; done)))
    return if remaining.isEmpty then some () else none
  return closed?.isSome

/-- The invariant an exact loop carries: the finiteness of a configured accumulator. -/
def loopValidity (stateType : Lean.Expr) (configured : Bool) : MetaM Lean.Expr :=
  withLocalDeclD `accumulator stateType fun accumulator => do
    if configured then
      mkLambdaFVars #[accumulator]
        (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[accumulator]) (mkConst ``Bool.true))
    else mkLambdaFVars #[accumulator] q(True)

/-- Analyze one case of a loop step under its own hypotheses: its obligations remain, its cached
results and sign facts do not. -/
def isolated {α : Type} (action : AnalyzeM α) : AnalyzeM α := do
  let saved ← get
  let result ← action
  set { saved with pending := (← get).pending }
  return result

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
