/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Sign

/-!
# Loops in the `roundoff` analysis

A registered loop is analyzed once, for a symbolic accumulator whose error against its reference is
given. Its lemmas then lift that step bound through the whole traversal. The result is
either the absolute bound of `List.fold_error` and its analogues, or a mixed bound together with a
relational invariant, the finiteness of the accumulator and a sign of its reference. Conditions
concern the states actually visited. A loop that keeps its accumulator exact, or changes it at a
single coordinate, is exact at every length.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Reject the reference step `referenceStep`, a function of the reference and the entry, of a
loop over `input` unless the entries of `input` are stored inputs or indices (`storedEntries`), or
the step ignores the entry and `input` is index data (`indexClosed`). An entry is analyzed as exact
data, so an entry of any other computed container, of whatever type, could bring an already-rounded
value into the reference. The reference also takes a step per entry, so a container whose length is
computed from a rounded value could too. -/
def checkEntries (loop : Loop) (input referenceStep : Lean.Expr) : AnalyzeM Unit := do
  if ← storedEntries loop input (← read).carriers then return
  let reads ← lambdaBoundedTelescope referenceStep 2 fun arguments body => do
    let some entry := arguments[1]? | return false
    return mentions body (· == entry.fvarId!)
  if reads then
    throwError "roundoff: the loop reads the entries of the computed container {input} as exact \
      data, so its reference would omit their rounding; write the producer into the step or \
      register a law that does (`Loop.fusions`)"
  unless ← indexClosed input (cache? := (← read).carriers) do
    throwError "roundoff: the loop takes a step for each entry of the computed container \
      {input}, whose length may be computed from numerical values, so its reference would take \
      as many steps as the rounded computation; traverse index data or a stored input"

namespace Analyze

/-- A loop in absolute analysis. The step is analyzed once for a symbolic accumulator
whose error against its reference is given, and `fold_error` lifts it through the loop. Its
side conditions concern the visited states. -/
def absoluteFold (r : Recursor) (loop : Loop)
    (observe step initial input inputType stateType : Lean.Expr) (fuel : Nat) :
    AnalyzeM Estimate := do
  let initialValue : Q(ℝ) := (mkApp observe initial).headBeta
  let initialEstimate ← r.analyze initialValue fuel
  let .absolute initialError := initialEstimate.bound |
    throwError "roundoff: a loop needs an absolute initial bound"
  let body ← deriveStep observe step inputType stateType (r.analyze · fuel)
  checkEntries loop input body.reference
  let augmented ← mkAppM loop.foldStep #[step, body.reference, body.error]
  let initialState ← mkAppM ``Prod.mk #[initial,
    ← mkAppM ``Prod.mk #[initialEstimate.reference, initialError]]
  let augmentedType ← inferType initialState
  let condition ← withLocalDeclD `state augmentedType fun state =>
    withLocalDeclD `value inputType fun value => do
      let current := Lean.Expr.proj ``Prod 0 state
      let pair := Lean.Expr.proj ``Prod 1 state
      mkLambdaFVars #[state, value] (mkAppN body.condition
        #[current, .proj ``Prod 0 pair, .proj ``Prod 1 pair, value])
  let validType ← mkAppM loop.allSteps #[augmented, condition, initialState, input]
  let valid ← mkFreshExprMVar validType
  if let some actualCondition := body.actualCondition? then
    let project ← withLocalDeclD `state augmentedType fun state =>
      mkLambdaFVars #[state] (.proj ``Prod 0 state)
    let goals ← valid.mvarId!.apply (← mkAppM loop.allStepsOfMap
      #[augmented, condition, initialState, input, project, step, actualCondition])
    for goal in goals do
      unless ← discharge (← read) goal do
        modify fun state => { state with pending := state.pending.push goal }
  else
    modify fun state => { state with pending := state.pending.push valid.mvarId! }
  let proof ← mkAppM loop.errorBound #[observe, step, body.reference, body.error, body.condition,
    initial, initialEstimate.reference, initialError, input, initialEstimate.proof,
    body.proof, valid]
  let type : Q(Prop) ← instantiateMVars (← inferType proof)
  match type with
  | ~q(|($_actual : ℝ) - $reference| ≤ $error) =>
      pure ⟨reference, .absolute error, proof, none⟩
  | _ => throwError "roundoff: unexpected loop proof type {type}"

/-- A loop whose state is a container, observed at one coordinate by `observe`. Its steps are
analyzed at that coordinate of the accumulator, which succeeds when each step reads the
accumulator only there. The bound is the absolute one of `fold_error`, which mixed analysis reads
as a mixed bound. A loop written another way is first written as a registered loop. -/
def containerFold (r : Recursor) (observe fold : Lean.Expr) (fuel : Nat) : AnalyzeM Estimate := do
  if (← read).mixed then
    let estimate ← withReader ({ · with mixed := false }) (r.containerFold observe fold fuel)
    return ← estimate.inMode true
  let some loop ← loopOf? fold | do
    -- A loop over a list of indices is first written as a fold over coordinates.
    let (context, procedures) ← foldSimpContext (← read)
    let normalized ← (← read).normalize `fold fold context procedures
    unless (← loopOf? normalized.expr).isSome do
      throwError "roundoff: no numerical rule for tensor loop {fold}"
    return ← rewriteActual (← r.containerFold observe normalized.expr fuel)
      (← mkCongrArg observe (← normalized.getProof' fold))
  let args := fold.getAppArgs
  let input := args[loop.input]!
  if let some (coordinates, traversalLaw) := loop.coordinates then
    unless input.isAppOf coordinates do
      let traversal ← mkAppM traversalLaw #[args[loop.step]!, args[loop.initial]!, input]
      let some (_, _, next) := (← inferType traversal).eq? |
        throwError "roundoff: coordinate traversal did not produce an equality"
      return ← rewriteActual (← r.containerFold observe next fuel) (← mkCongrArg observe traversal)
  withReader ({ · with containerLoop := true })
    (r.absoluteFold loop observe args[loop.step]! args[loop.initial]! input args[loop.element]!
      args[loop.state]! fuel)

/-- A loop in mixed analysis. The step is analyzed once for a symbolic accumulator whose bound
against its reference is given, at the element variable `element`, together with a relational
invariant: finiteness of the accumulator and a sign of its reference, each kept when the step
preserves it. A sign that neither the step's bound nor its finiteness proof and conditions use is
dropped without analyzing the step again. Its side conditions concern the visited states, and
`fold_mixedError` lifts it through the loop. A step that keeps zero budgets zero from zero initial
budgets makes the loop exact (`Loop.exactBudgets`). -/
def mixedFold (r : Recursor) (loop : Loop)
    (observe step initial input element stateType : Lean.Expr) (fuel : Nat) :
    AnalyzeM Estimate := do
  let inputType ← inferType element
  let initialValue : Q(ℝ) := (mkApp observe initial).headBeta
  let initialEstimate ← r.analyze initialValue fuel
  let .mixed initialRelative initialAbsolute := initialEstimate.bound |
    throwError "roundoff: expected a mixed initial bound"
  let initialReference := initialEstimate.reference
  let configured := initialValue.isAppOf ``ExecFloat.Binary.toReal
  let finiteness (accumulator : Lean.Expr) : MetaM Q(Prop) := do
    mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[accumulator]) (mkConst ``Bool.true)
  let signed (nonneg : Bool) (reference : Q(ℝ)) : Q(Prop) :=
    if nonneg then q(0 ≤ $reference) else q($reference ≤ 0)
  let initialFinite? ← if configured then do
      let goal ← mkFreshExprMVar (← finiteness initial)
      if ← r.proveFinite goal.mvarId! fuel then pure (some (← instantiateMVars goal))
      -- The finiteness of an entry of a function the program takes is a premise, as it is at
      -- each step.
      else if ← isAppliedInput initial then
        modify fun state => { state with pending := state.pending.push goal.mvarId! }
        pure (some goal)
      else pure none
    else pure none
  let mut initialSign? : Option (Bool × Lean.Expr) := none
  for nonneg in [true, false] do
    if initialSign?.isSome then continue
    let goal ← mkFreshExprMVar (signed nonneg initialReference)
    if ← r.proveSign goal.mvarId! fuel signDepth then
      initialSign? := some (nonneg, ← instantiateMVars goal)
  let attempts := [(initialFinite?.isSome, initialSign?.isSome), (initialFinite?.isSome, false),
    (false, initialSign?.isSome), (false, false)].eraseDups
  for (useFinite, useSign) in attempts do
    let carried? ← speculate? do
      let before ← get
      let (referenceFunction, relativeFunction, absoluteFunction, invariant, conditionFunction,
          stepProof, actualCondition?, keptSign) ←
        withLocalDeclD `accumulator stateType fun accumulator =>
        withLocalDeclD `reference q(ℝ) fun reference =>
        withLocalDeclD `relative q(ℝ) fun relative =>
        withLocalDeclD `absolute q(ℝ) fun absolute => do
          let value := element
          let observed : Q(ℝ) := (mkApp observe accumulator).headBeta
          let reference : Q(ℝ) := reference
          let relative : Q(ℝ) := relative
          let absolute : Q(ℝ) := absolute
          let finiteProp : Q(Prop) ← if useFinite then finiteness accumulator else pure q(True)
          let signProp : Q(Prop) := if let (true, some (nonneg, _)) := (useSign, initialSign?)
            then signed nonneg reference else q(True)
          withLocalDeclD `accumulator_error q(MixedError $observed $reference $relative $absolute)
              fun incoming =>
          withLocalDeclD `accumulator_finite finiteProp fun finite =>
          withLocalDeclD `reference_sign signProp fun sign =>
          -- A loop that the step holds is nested in this one.
          withReader (fun session => { session with nested := true }) do
            let next := (mkAppN step #[accumulator, value]).headBeta
            let actual : Q(ℝ) := (mkApp observe next).headBeta
            let estimate ← r.analyze actual fuel
            let .mixed nextRelative nextAbsolute := estimate.bound |
              throwError "roundoff: a loop step needs a mixed bound"
            let nextReference : Q(ℝ) := estimate.reference
            -- The invariant at the next state.
            let nextFinite ← if useFinite then do
                let next := (mkAppN step #[accumulator, value]).headBeta
                let goal ← mkFreshExprMVar (← finiteness next)
                unless ← estimate.closeFinite goal.mvarId! <||> r.proveFinite goal.mvarId! fuel do
                  throwError "roundoff: the accumulator need not stay finite"
                instantiateMVars goal
              else pure (mkConst ``True.intro)
            -- A sign that the next reference loses is dropped if the step's bound does not use it.
            let nextSign? ← if let (true, some (nonneg, _)) := (useSign, initialSign?) then do
                let goal ← mkFreshExprMVar (signed nonneg nextReference)
                if ← r.proveSign goal.mvarId! fuel signDepth then
                  pure (some (← instantiateMVars goal))
                else if mentions (← instantiateMVars estimate.proof) (· == sign.fvarId!) then
                  throwError "roundoff: the reference need not keep its sign"
                else pure none
              else pure (some (mkConst ``True.intro))
            let keptSign := nextSign?.isSome
            let nextSign := nextSign?.getD (mkConst ``True.intro)
            let signProp : Q(Prop) := if keptSign then signProp else q(True)
            let candidates := (← get).pending.extract before.pending.size (← get).pending.size
            withConditions candidates (← read).comparisons fun condition evidence => do
              for hypothesis in #[incoming, finite, sign] do
                if mentions condition (· == hypothesis.fvarId!) then
                  throwError "roundoff: a loop condition depends on its proof argument"
              if mentions nextReference fun id => id == accumulator.fvarId! ||
                  id == relative.fvarId! || id == absolute.fvarId! then
                throwError "roundoff: the loop's real reference depends on its rounded \
                  accumulator; establish agreement of its branch conditions first"
              let state := #[accumulator, reference, relative, absolute, value]
              let invariantBody : Q(Prop) := q($finiteProp ∧ $signProp)
              let conclusion ← mkAppM ``And.intro
                #[← instantiateMVars estimate.proof, ← mkAppM ``And.intro #[nextFinite, nextSign]]
              if mentions conclusion (· == sign.fvarId!) && !keptSign then
                throwError "roundoff: the reference need not keep its sign"
              let actualCondition? ← if mentions condition fun id => id == reference.fvarId! ||
                  id == relative.fvarId! || id == absolute.fvarId! then pure none
                else pure (some (← mkLambdaFVars #[accumulator, value] condition))
              let stepProof ← withLocalDeclD `reference_sign signProp fun unused =>
                let carried := if keptSign then sign else unused
                mkLambdaFVars (state ++ #[evidence, incoming, finite, carried]) conclusion
              return (← mkLambdaFVars #[reference, value] nextReference,
                ← mkLambdaFVars state nextRelative, ← mkLambdaFVars state nextAbsolute,
                ← mkLambdaFVars #[accumulator, reference] invariantBody,
                ← mkLambdaFVars state condition, stepProof, actualCondition?, keptSign)
      set { before with pending := before.pending }
      checkEntries loop input referenceFunction
      -- `fold_mixedError` takes the bound and the invariant as one conjunction.
      let stateType' ← inferType (← mkAppM ``Prod.mk #[initial, ← mkAppM ``Prod.mk
        #[initialReference, ← mkAppM ``Prod.mk #[initialRelative, initialAbsolute]]])
      let hstep ← withLocalDeclD `accumulator stateType fun accumulator =>
        withLocalDeclD `reference q(ℝ) fun reference =>
        withLocalDeclD `relative q(ℝ) fun relative =>
        withLocalDeclD `absolute q(ℝ) fun absolute =>
        withLocalDeclD `value inputType fun value => do
          let state := #[accumulator, reference, relative, absolute, value]
          let condition := (mkAppN conditionFunction state).headBeta
          withLocalDeclD `evidence condition fun evidence => do
            let observed : Q(ℝ) := (mkApp observe accumulator).headBeta
            let reference : Q(ℝ) := reference
            let relative : Q(ℝ) := relative
            let absolute : Q(ℝ) := absolute
            let invariantAt : Q(Prop) := (mkAppN invariant #[accumulator, reference]).headBeta
            withLocalDeclD `state q(MixedError $observed $reference $relative $absolute ∧
                $invariantAt) fun hypothesis => do
              let bound ← mkAppM ``And.left #[hypothesis]
              let carried ← mkAppM ``And.right #[hypothesis]
              let proof := mkAppN stepProof (state ++ #[evidence, bound,
                ← mkAppM ``And.left #[carried], ← mkAppM ``And.right #[carried]])
              mkLambdaFVars (state ++ #[evidence, hypothesis]) proof.headBeta
      let augmented ← mkAppM loop.mixedFoldStep
        #[step, referenceFunction, relativeFunction, absoluteFunction]
      let initialState ← mkAppM ``Prod.mk #[initial, ← mkAppM ``Prod.mk
        #[initialReference, ← mkAppM ``Prod.mk #[initialRelative, initialAbsolute]]]
      let condition ← withLocalDeclD `state stateType' fun state =>
        withLocalDeclD `value inputType fun value => do
          let rest := Lean.Expr.proj ``Prod 1 state
          let budgets := Lean.Expr.proj ``Prod 1 rest
          mkLambdaFVars #[state, value] (mkAppN conditionFunction
            #[.proj ``Prod 0 state, .proj ``Prod 0 rest, .proj ``Prod 0 budgets,
              .proj ``Prod 1 budgets, value]).headBeta
      let valid ← mkFreshExprMVar
        (← mkAppM loop.allSteps #[augmented, condition, initialState, input])
      if let some actualCondition := actualCondition? then
        let project ← withLocalDeclD `state stateType' fun state =>
          mkLambdaFVars #[state] (.proj ``Prod 0 state)
        let goals ← valid.mvarId!.apply (← mkAppM loop.allStepsOfMap
          #[augmented, condition, initialState, input, project, step, actualCondition])
        -- The condition reads the step's containers as the tidied budgets do, so both name it
        -- once.
        for goal in goals do
          unless ← discharge (← read) goal do
            if let some condition ← (← read).tidy goal then
              modify fun state => { state with pending := state.pending.push condition }
      else
        modify fun state => { state with pending := state.pending.push valid.mvarId! }
      let initialFinite := if useFinite then initialFinite?.getD (mkConst ``True.intro)
        else mkConst ``True.intro
      let initialSign := if useSign && keptSign then
          (initialSign?.map (·.2)).getD (mkConst ``True.intro)
        else mkConst ``True.intro
      let hinit ← mkAppM ``And.intro #[initialEstimate.proof,
        ← mkAppM ``And.intro #[initialFinite, initialSign]]
      let proof ← mkAppM loop.mixedBound #[observe, step, referenceFunction,
        relativeFunction, absoluteFunction, invariant, conditionFunction, initial,
        initialReference, initialRelative, initialAbsolute, input, hinit, hstep, valid]
      let bound ← mkAppM ``And.left #[proof]
      let some (_, reference, bound') ← boundConclusion? (← inferType bound) |
        throwError "roundoff: unexpected loop proof type"
      let finite? ← if useFinite then
          pure (some (← mkAppM ``And.left #[← mkAppM ``And.right #[proof]]))
        else pure none
      -- A step that keeps zero budgets zero, such as an exact maximum, makes the loop exact.
      if let (some exactBudgets, some 0, some 0) :=
          (loop.exactBudgets, initialRelative.nat?, initialAbsolute.nat?) then
        let zero (function : Lean.Expr) : AnalyzeM (Option Lean.Expr) :=
          withLocalDeclD `accumulator stateType fun accumulator =>
          withLocalDeclD `reference q(ℝ) fun reference =>
          withLocalDeclD `value inputType fun value => do
            let budget := (mkAppN function
              #[accumulator, reference, q((0 : ℝ)), q((0 : ℝ)), value]).headBeta
            let context ← Simp.mkContext { implicitDefEqProofs := false } #[(← read).budget]
            let tidied ← (← read).tidyTerm budget context
            unless tidied.expr.nat? == some 0 do return none
            return some (← mkLambdaFVars #[accumulator, reference, value]
              (← tidied.getProof' budget))
        let relativeZero? ← zero relativeFunction
        let absoluteZero? ← zero absoluteFunction
        if let (some relativeZero, some absoluteZero) := (relativeZero?, absoluteZero?) then
          let zeros ← mkAppM exactBudgets #[step, referenceFunction, relativeFunction,
            absoluteFunction, initial, initialReference, input, relativeZero, absoluteZero]
          let statement ← instantiateMVars (← inferType bound)
          let observed := mkApp2 (mkConst ``MixedError) (statement.getArg! 0) reference
          let equality ← mkCongr (← mkCongrArg observed (← mkAppM ``And.left #[zeros]))
            (← mkAppM ``And.right #[zeros])
          return ⟨reference, .mixed q(0) q(0), ← mkEqMP equality bound, finite?⟩
      return (⟨reference, bound', bound, finite?⟩ : Estimate)
    if let some estimate := carried? then return estimate
  throwError "roundoff: no relational invariant carries this loop"

/-- A fold over coordinates whose step branches on a test that holds at a single coordinate. If
every step elsewhere keeps an exact zero and then the reached value, the fold returns the value its
step at that coordinate produces from zero, for every length (`fold_eq_of_single`). -/
partial def singleFold (r : Recursor) (loop : Loop)
    (observe step initial input coordinateType stateType : Lean.Expr) (fuel : Nat) :
    AnalyzeM Estimate := do
  let session ← read
  unless loop.coordinates.any (input.isAppOf ·.1) && loop.single.isSome do
    throwError "roundoff: a single-coordinate loop traverses coordinates"
  let configured := (mkApp observe initial).headBeta.isAppOf ``ExecFloat.Binary.toReal
  let valid ← loopValidity stateType configured
  -- The tests, read from the step's coordinate reads, that hold at one coordinate and away
  -- from which the step keeps the accumulator, through a zero operand or by returning it.
  -- They are tried in order; a step with nested tests may select its coordinate by an inner
  -- one.
  let tests ← withLocalDeclD `accumulator stateType fun accumulator =>
    withLocalDeclD `coordinate coordinateType fun coordinate => do
      let body := (mkApp observe (mkAppN step #[accumulator, coordinate]).headBeta).headBeta
      let (context, procedures) ← coordinateSimpContext session
      let (normalized, _) ← simp body context procedures
      -- Coordinate traversals read through identity maps and pairs. A vector coordinate pairs
      -- its index with the unit coordinate of the scalar shape.
      let rec reduceRead (term : Lean.Expr) : Lean.Expr :=
        if term.isAppOfArity ``id 2 then reduceRead term.appArg!
        else
          let receiver? := match term with
            | .proj ``Prod 0 receiver => some receiver
            | _ => if term.isAppOfArity ``Prod.fst 3 then some term.appArg! else none
          match receiver? with
          | some receiver =>
              let receiver := reduceRead receiver
              if receiver.isAppOfArity ``Prod.mk 4 then reduceRead receiver.appFn!.appArg!
              else .proj ``Prod 0 receiver
          | none => term
      let found ← IO.mkRef #[]
      normalized.expr.forEach' fun branch => do
        unless branch.isAppOfArity ``ite 5 || branch.isAppOfArity ``dite 5 do return true
        let test := branch.getAppArgs[1]!
        unless !test.hasLooseBVars && mentions test (· == coordinate.fvarId!) &&
            !mentions test (· == accumulator.fvarId!) do return true
        let outside := branch.getAppArgs[4]!
        let outside := if branch.isAppOfArity ``dite 5 then outside.bindingBody! else outside
        unless outside.nat? == some 0 || outside.isAppOf ``Zero.zero ||
            mentions outside (· == accumulator.fvarId!) do return true
        let some (_, left, right) := test.eq? | return true
        let (read, other) := if mentions right (· == coordinate.fvarId!) then (right, left)
          else (left, right)
        if mentions other (· == coordinate.fvarId!) then return true
        let read := reduceRead read
        let index? ← if read == coordinate then pure (some other)
          else if read == .proj ``Prod 0 coordinate then
            some <$> mkAppM ``Prod.mk #[other, mkConst ``PUnit.unit [Level.one]]
          else pure none
        if let some index := index? then
          found.modify (·.push (← mkLambdaFVars #[coordinate] test, index))
        return true
      found.get
  if tests.isEmpty then throwError "roundoff: no single-coordinate test in this loop"
  for (guard, index) in tests do
    if let some estimate ← speculate? (r.singleFoldAt loop observe step initial coordinateType
        stateType configured valid guard index fuel) then
      return estimate
  throwError "roundoff: no single-coordinate test makes this loop exact"

/-- `singleFold` for the test `guard`, which holds at `index` and nowhere else. -/
def singleFoldAt (r : Recursor) (loop : Loop)
    (observe step initial coordinateType stateType : Lean.Expr) (configured : Bool)
    (valid guard index : Lean.Expr) (fuel : Nat) : AnalyzeM Estimate := do
  let session ← read
  let outerContext ← getLCtx
  let outerInstances ← getLocalInstances
  let characterized ← mkFreshExprMVar (← withLocalDeclD `coordinate coordinateType
    fun coordinate => do
      mkForallFVars #[coordinate] (← mkAppM ``Iff #[(mkApp guard coordinate).headBeta,
        ← mkEq coordinate index]))
  let proved? ← attempt? 2000 do
    let remaining ← Lean.Elab.Tactic.run characterized.mvarId! do
      evalTactic (← `(tactic| (intro coordinate; constructor <;> intro h <;>
        first | (subst_vars; rfl) | (ext <;> simp_all) | simp_all)))
    return if remaining.isEmpty then some () else none
  unless proved?.isSome do throwError "roundoff: the loop's test may hold at two coordinates"
  let before := (← get).pending.size
  let (hinit, _) ← r.exactStart observe initial valid configured (some q(0)) fuel
  -- At the test's coordinate, the test itself selects the step's branch.
  let inside ← mkAppM ``Iff.mpr #[mkApp (← instantiateMVars characterized) index,
    ← mkEqRefl index]
  let atIndex (known : Q(ℝ)) (target? : Option Q(ℝ)) : AnalyzeM (Lean.Expr × Q(ℝ)) :=
    withLocalDeclD `accumulator stateType fun accumulator => do
      withLocalDeclD `inside (mkApp guard index).headBeta fun insideProof => do
        let (proof, target) ← r.exactStepCase observe step valid configured accumulator index
          known target? fuel
        let proof ← mkLambdaFVars #[insideProof] proof
        return (← mkLambdaFVars #[accumulator] (mkApp proof inside).headBeta, target)
  -- Away from the selected coordinate the test fails, which selects the step's other branch.
  let outside (known : Q(ℝ)) : AnalyzeM Lean.Expr :=
    withLocalDeclD `accumulator stateType fun accumulator =>
    withLocalDeclD `coordinate coordinateType fun coordinate => do
      withLocalDeclD `other (mkNot (← mkEq coordinate index)) fun otherProof => do
        let fails ← withLocalDeclD `test (mkApp guard coordinate).headBeta fun test => do
          mkLambdaFVars #[test] (mkApp otherProof (← mkAppM ``Iff.mp
            #[mkApp (← instantiateMVars characterized) coordinate, test]))
        let failing := mkNot (mkApp guard coordinate).headBeta
        withLetDecl `outside failing fails fun outsideProof => do
          let (proof, _) ← r.exactStepCase observe step valid configured accumulator coordinate
            known (some known) fuel
          mkLambdaFVars #[accumulator, coordinate, otherProof]
            (← mkLetFVars #[outsideProof] proof)
  -- Each case analyzes under its own hypotheses; none of its cached results may escape.
  let (_, reached) ← isolated (atIndex q(0) none)
  let budgetContext ← Simp.mkContext { implicitDefEqProofs := false } #[session.budget]
  let (simplified, _) ← simp reached budgetContext
  let value : Q(ℝ) := simplified.expr
  let (hindex, _) ← isolated (atIndex q(0) (some value))
  let hzero ← isolated (outside q(0))
  let hrest ← isolated (outside value)
  r.liftLoopObligations before outerContext outerInstances #[hinit, hzero, hindex, hrest]
  let some single := loop.single | throwError "roundoff: no single-coordinate loop law"
  let proof ← mkAppM single #[observe, step, valid, index, value, initial,
    ← instantiateMVars hinit, hzero, hindex, hrest]
  let exact ← mkAppM ``And.right #[proof]
  let finite? ← if configured then some <$> mkAppM ``And.left #[proof] else pure none
  return ⟨value, .mixed q(0) q(0), ← mkAppM ``MixedError.of_eq #[exact], finite?⟩

/-- A fold whose every step keeps the exact value of the accumulator, such as a sum of exact
zeros, returns its initial value unchanged, for every length. `fold` is the loop itself, and its
step is analyzed at the element variable `element`, which the loop's obligations may not mention.
-/
def constantFold (r : Recursor) (loop : Loop)
    (observe step initial element stateType fold : Lean.Expr) (fuel : Nat) :
    AnalyzeM Estimate := do
  let configured := (mkApp observe initial).headBeta.isAppOf ``ExecFloat.Binary.toReal
  let valid ← loopValidity stateType configured
  let outerContext := (← getLCtx).erase element.fvarId!
  let outerInstances ← getLocalInstances
  let before := (← get).pending.size
  let (hinit, value) ← r.exactStart observe initial valid configured none fuel
  let hstep ← isolated <| withLocalDeclD `accumulator stateType fun accumulator => do
    let (proof, _) ← r.exactStepCase observe step valid configured accumulator element
      value (some value) fuel
    mkLambdaFVars #[accumulator, element] proof
  r.liftLoopObligations before outerContext outerInstances #[hinit, hstep]
  let motive ← withLocalDeclD `accumulator stateType fun accumulator => do
    mkLambdaFVars #[accumulator] (← mkAppM ``And #[(mkApp valid accumulator).headBeta,
      ← mkEq (mkApp observe accumulator).headBeta value])
  let law ← mkConstWithFreshMVarLevels loop.induction
  let (arguments, _, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
  let some predicate ← arguments.findM? fun argument => do
      return (← inferType argument).getForallBody.isProp
    | throwError "roundoff: foldl_induction has no motive"
  predicate.mvarId!.assign motive
  let expected := (mkApp motive fold).headBeta
  unless ← isDefEq conclusion expected do throwError "roundoff: the fold does not match"
  unless ← isDefEq arguments[arguments.size - 2]! (← instantiateMVars hinit) <&&>
      isDefEq arguments.back! (← instantiateMVars hstep) do
    throwError "roundoff: the loop's invariant does not match"
  let proof ← mkExpectedTypeHint (← instantiateMVars (mkAppN law arguments)) expected
  let exact ← mkAppM ``And.right #[proof]
  let finite? ← if configured then some <$> mkAppM ``And.left #[proof] else pure none
  return ⟨value, .mixed q(0) q(0), ← mkAppM ``MixedError.of_eq #[exact], finite?⟩

/-- The start of a loop at an exact value: a proof of `valid initial ∧ observe initial = value`,
for `value` the given `target?`, or else the tidied reference of the initial value. -/
def exactStart (r : Recursor) (observe initial valid : Lean.Expr) (configured : Bool)
    (target? : Option Q(ℝ))
    (fuel : Nat) : AnalyzeM (Lean.Expr × Q(ℝ)) := do
  let initialEstimate ← r.analyze (mkApp observe initial).headBeta fuel
  unless initialEstimate.bound.isExact do throwError "roundoff: the loop starts inexactly"
  let (value, reached) ← match target? with
    | some target => do
        let reached ← mkFreshExprMVar (← mkEq initialEstimate.reference target)
        unless ← closeExactEquality reached.mvarId! do
          throwError "roundoff: the loop does not start at {target}"
        pure (target, ← instantiateMVars reached)
    | none => do
        let context ← Simp.mkContext { implicitDefEqProofs := false } #[(← read).budget]
        let (tidied, _) ← simp initialEstimate.reference context
        pure (tidied.expr, ← tidied.getProof' initialEstimate.reference)
  let initialValid ← mkFreshExprMVar (mkApp valid initial).headBeta
  if configured then
    unless ← r.proveFinite initialValid.mvarId! fuel do
      throwError "roundoff: the loop's initial value need not be finite"
  else initialValid.mvarId!.assign (mkConst ``True.intro)
  let hinit ← mkAppM ``And.intro #[← instantiateMVars initialValid,
    ← mkEqTrans (← exactEquality initialEstimate.proof) reached]
  return (hinit, value)

/-- One exact step of a loop. From an accumulator that satisfies `valid` and has the exact value
`known`, the step at `coordinate` keeps `valid` and reaches `target?`, or else the value its
analysis derives. Returns a proof of `valid ∧ value → valid ∧ value` and the value reached. -/
def exactStepCase (r : Recursor) (observe step valid : Lean.Expr) (configured : Bool)
    (accumulator coordinate : Lean.Expr) (known : Q(ℝ)) (target? : Option Q(ℝ)) (fuel : Nat) :
    AnalyzeM (Lean.Expr × Q(ℝ)) := do
  let observed : Q(ℝ) := (mkApp observe accumulator).headBeta
  -- One step from the accumulator, given its exact value as `equality`.
  let exactStep (equality : Lean.Expr) : AnalyzeM (Lean.Expr × Lean.Expr × Q(ℝ)) := do
    withLocalDeclD `accumulator_error q(MixedError $observed $known 0 0) fun incoming => do
      let next := (mkAppN step #[accumulator, coordinate]).headBeta
      -- A loop that the step holds is nested in this one.
      let estimate ← withReader (fun session => { session with nested := true })
        (r.analyze (mkApp observe next).headBeta fuel)
      unless estimate.bound.isExact do
        throwError "roundoff: a loop step is not exact: {← inferType estimate.proof}"
      let nextValid ← mkFreshExprMVar (mkApp valid next).headBeta
      if configured then
        unless ← estimate.closeFinite nextValid.mvarId! <||> r.proveFinite nextValid.mvarId! fuel do
          throwError "roundoff: a loop step need not be finite"
      else nextValid.mvarId!.assign (mkConst ``True.intro)
      let exact ← exactEquality estimate.proof
      let close (value : Lean.Expr) : MetaM Lean.Expr := do
        let value ← mkLambdaFVars #[incoming] (← instantiateMVars value)
        return (mkApp value (← mkAppM ``MixedError.of_eq #[equality])).headBeta
      return (← close nextValid, ← close exact, estimate.reference)
  let stateProp : Q(Prop) := (mkApp valid accumulator).headBeta
  let premise ← mkAppM ``And #[stateProp, ← mkEq observed known]
  withLocalDeclD `state premise fun hypothesis => do
    -- A reached value is stated in terms of the accumulator, so that rewriting with it turns
    -- range conditions into facts about a finite value. A numeral stays on the right.
    let numeral := known.nat?.isSome
    let (body, target) ← withLocalDeclD `accumulator_valid stateProp fun localValid => do
      withLocalDeclD `accumulator_value
          (← if numeral then mkEq observed known else mkEq known observed) fun localValue => do
        let (nextValid, exact, next) ←
          exactStep (← if numeral then pure localValue else mkEqSymm localValue)
        let target := target?.getD next
        let agree ← mkFreshExprMVar (← mkEq next target)
        unless ← closeExactEquality agree.mvarId! do
          throwError "roundoff: a loop step leaves the reached value"
        let conclusion ← mkAppM ``And.intro
          #[nextValid, ← mkEqTrans exact (← instantiateMVars agree)]
        return (← mkLambdaFVars #[localValid, localValue] conclusion, target)
    let value ← mkAppM ``And.right #[hypothesis]
    let proof := (mkAppN body #[← mkAppM ``And.left #[hypothesis],
      ← if numeral then pure value else mkEqSymm value]).headBeta
    return (← mkLambdaFVars #[hypothesis] proof, target)

/-- Keep the obligations created since `before` that `proofs` use as conditions of the loop,
in its outer context. The speculative analysis of an operand may leave others that no proof
needs. A used obligation about the loop's local state is an error. -/
def liftLoopObligations (before : Nat) (outerContext : LocalContext)
    (outerInstances : LocalInstances) (proofs : Array Lean.Expr) : AnalyzeM Unit := do
  let mut used := #[]
  for proof in proofs do
    used := used ++ (← getMVars (← instantiateMVars proof))
  let created := (← get).pending.extract before (← get).pending.size
  let mut lifted := #[]
  for goal in created do
    unless used.contains goal do continue
    let type ← instantiateMVars (← goal.getType)
    if mentions type (!outerContext.contains ·) then
      throwError "roundoff: a loop step leaves an obligation on its local state: {type}"
    let outer ← withLCtx outerContext outerInstances (mkFreshExprMVar type)
    goal.assign outer
    lifted := lifted.push outer.mvarId!
  modify fun state => { state with pending := state.pending.extract 0 before ++ lifted }

end Analyze

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
