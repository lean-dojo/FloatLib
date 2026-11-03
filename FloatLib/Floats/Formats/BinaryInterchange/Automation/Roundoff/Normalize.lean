/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Basic

/-!
# Program normalization for `roundoff`

The analysis reads a computation as written. Normalization exposes its source code step by step:
control flow reduces only when its actual discriminant computes, branches and optional values are
split without replacing their payloads by fresh inputs, and registered producers and container
storage stay folded. Simp sets built from the environment and the registered extensions read
container entries through the producers that compute them, fuse source maps into loops, decode
real observations through the selected scalar methods, and compare configured computations by
their FloatLib meanings.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Keep registered producers available for observation equalities and numerical bounds.
Numerical rules protect their source functions without rewriting them to real arithmetic. -/
def programRules (containerFree : IO.Ref NameSet) :
    MetaM (Array (Name × Bool) × NameSet) := do
  let environment ← getEnv
  let mut rewrites := #[]
  let mut boundaries : NameSet := {}
  for name in roundoffRules.getState environment do
    let some info := environment.find? name | continue
    unless ruleKind info.type matches .numerical do continue
    let inverse := Lean.Compiler.hasCSimpAttribute environment name
    let heads? ← withNewMCtxDepth do
      let rule ← mkConstWithFreshMVarLevels name
      let (_, _, conclusion) ← forallMetaTelescopeReducing (← ruleType rule)
      do
        if let some (type, left, right) := conclusion.eq? then
          -- A polymorphic coordinate equality rewrites every scalar type. Classifying it
          -- by unifying its type with ℝ would accidentally discard its floating-point uses.
          let numerical := !inverse && (← withReducible (whnf type)).isConstOf ``Real
          let source := if inverse then right else left
          let mut heads ← containerProducerHeads containerFree source {}
          unless numerical do
            if let some head := source.getAppFn.constName? then heads := heads.insert head
          return some (heads, !numerical)
        -- A generated statement concludes the finiteness and the mixed bound of its output.
        if let some (_, bound) := finiteMixed? conclusion then
          return some (← containerProducerHeads containerFree bound.getAppArgs[0]! {}, false)
        let conclusion : Q(Prop) ← pure conclusion
        match conclusion with
        | ~q(|($actual : ℝ) - $_reference| ≤ $_error) =>
            return some (← containerProducerHeads containerFree actual {}, false)
        | _ => return none
    if let some (heads, rewrite) := heads? then
      if rewrite then
        rewrites := rewrites.push (name, inverse)
      -- The applied pattern fixes the result type, including generic transports such as Eq.mp.
      for head in heads do
        boundaries := boundaries.insert head
  return (rewrites, boundaries)

/-- Preserve FloatLib arithmetic, registered container storage, and the `intact` producers. -/
def programCanUnfold (intact : NameSet) (conditionals : Bool) (config : Meta.Config)
    (info : ConstantInfo) : CoreM Bool := do
  if intact.contains info.name ||
      (!conditionals && (info.name == ``ite || info.name == ``dite)) ||
      (`FloatLib).isPrefixOf info.name ||
      (← extension).storage.any (·.isPrefixOf info.name) then return false
  canUnfoldDefault config info

/-- Reduce control flow only when its actual discriminant computes. Selected branches retain
their numerical operations; unknown options and flags never become fresh exact inputs. -/
def reduceControl? (containerProducers : NameSet) (value : Lean.Expr) :
    MetaM (Option Lean.Expr) := do
  let some name := value.getAppFn.constName? | return none
  -- A failed control-flow reduction retains the original expression. Generic wrappers may
  -- therefore reduce while inspecting a discriminant; actual container producers stay intact.
  let reduce {α : Type} (action : MetaM α) : MetaM α :=
    withCanUnfoldPred (programCanUnfold containerProducers true) (withDefault action)
  if (name == ``ite || name == ``dite) && value.getAppNumArgs ≥ 5 then
    let arguments := value.getAppArgs
    let decision ← reduce (whnf (mkApp2 (mkConst ``decide) arguments[1]! arguments[2]!))
    unless decision.isConstOf ``Bool.true || decision.isConstOf ``Bool.false do return none
    let selected := arguments[if decision.isConstOf ``Bool.true then 3 else 4]!
    let selected := if name == ``dite then
        mkApp selected (mkApp2 (mkConst ``Decidable.reflects_decide) arguments[1]! arguments[2]!)
      else selected
    return some (mkAppN selected (arguments.extract 5 arguments.size)).headBeta
  if (← getMatcherInfo? name).isSome ||
      ((← getEnv).find? name).any (fun info => match info with
        | .recInfo _ => true | _ => false) then
    return ← reduce (reduceRecMatcher? value)
  return none

/-- Recover an unfolded dependent conditional only when its motive and complete value agree
with `dite`. The predicate and decision instance are taken from the actual discriminant. -/
def restoreBranch? (source : Expr) : MetaM (Option Expr) := do
  let source ← instantiateMVars source
  unless source.isAppOfArity ``Bool.rec 5 && !source.hasExprMVar do return none
  let arguments := source.getAppArgs
  let decision := arguments[3]!
  unless decision.isAppOfArity ``decide 2 do return none
  let predicate := decision.getAppArgs[0]!
  let selected := decision.getAppArgs[1]!
  withoutModifyingState <| withNewMCtxDepth do
    try
      let resultType ← inferType source
      let expectedMotive ← withLocalDeclD `bit q(Bool) fun bit => do
        let reflected := mkApp2 (mkConst ``Bool.Reflects) bit predicate
        mkLambdaFVars #[bit] (← mkArrow reflected resultType)
      unless ← withDefault (isDefEq arguments[0]! expectedMotive) do return none
      let restored ← withDefault <| mkAppOptM ``dite
        #[some resultType, some predicate, some selected,
          some arguments[2]!, some arguments[1]!]
      let restored ← instantiateMVars restored
      if restored.hasExprMVar then return none
      unless ← withDefault (isDefEq source restored) do return none
      return some restored
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      return none

/-- Move a function application through the actual branch, preserving its decision instance. -/
def applyBranch? (observe control : Expr) : MetaM (Option (Expr × Expr)) := do
  let dependent := control.isAppOfArity ``dite 5
  unless dependent || control.isAppOfArity ``ite 5 do return none
  let .forallE _ _ codomain _ ← withReducible (whnf (← inferType observe)) | return none
  -- Application through a branch has a fixed result type; dependent record fields need
  -- their own proved observation rather than an arbitrary transport.
  if codomain.hasLooseBVars then return none
  let arguments := control.getAppArgs
  let rule := if dependent then ``apply_dite else ``apply_ite
  let proof ← withDefault <| mkAppOptM rule #[none, none, some observe, some arguments[1]!,
    some arguments[2]!, some arguments[3]!, some arguments[4]!]
  let some (_, _, result) := (← inferType proof).eq? |
    throwError "roundoff: branch application did not produce an equality"
  return some (result.headBeta, proof)

/-- Move the function of `value` through its first argument that is a branch:
`f (if c then a else b) = if c then f a else f b`. -/
def branchArgument? (value : Expr) : MetaM (Option (Expr × Expr)) := do
  let arguments := value.getAppArgs
  for h : index in [:arguments.size] do
    let argument := arguments[index]
    unless argument.isAppOfArity ``ite 5 || argument.isAppOfArity ``dite 5 do continue
    let applied? ← observing? do
      let observe ← withLocalDeclD `branch (← inferType argument) fun branch =>
        mkLambdaFVars #[branch] (mkAppN value.getAppFn (arguments.set! index branch))
      check observe
      applyBranch? observe argument
    if let some (some result) := applied? then return some result
  return none

/-- Split one unresolved Option discriminant using matcher metadata and a constant motive.
Constructor alternatives and all other discriminants retain their actual source expressions. -/
def optionMatch? (source : Expr) : MetaM (Option (Expr × Expr)) := do
  let source ← instantiateMVars source
  if source.hasExprMVar then return none
  let some name := source.getAppFn.constName? | return none
  let arguments := source.getAppArgs
  let positions? : Option (Array Nat × Nat) ← if let some info ← getMatcherInfo? name then do
      -- Named discriminant equations can retain dependencies on the original values.
      unless info.numDiscrs > 0 && info.getNumDiscrEqs == 0 &&
          arguments.size ≥ info.arity do return none
      let positions := (Array.range info.numDiscrs).map (info.getFirstDiscrPos + ·)
      pure (some (positions, info.getMotivePos))
    else do
      let environment ← getEnv
      let recursor := match environment.find? name with
        | some (.recInfo _) => true
        | _ => isAuxRecursor environment name
      unless recursor do return none
      let info ← mkRecursorInfo name
      unless info.typeName == ``Option && info.numIndices == 0 && !info.recursive &&
          arguments.size ≥ info.numArgs do return none
      pure (some (#[info.majorPos], info.motivePos))
  let some (discriminantPositions, motivePosition) := positions? | return none
  let mut selected? : Option (Nat × Expr) := none
  for index in [:discriminantPositions.size] do
    let discriminant := arguments[discriminantPositions[index]!]!
    if discriminant.isAppOf ``Option.some || discriminant.isAppOf ``Option.none then continue
    let optionType ← withReducible (whnf (← inferType discriminant))
    unless optionType.isAppOfArity ``Option 1 do continue
    selected? := some (index, optionType)
    break
  let some (selected, optionType) := selected? | return none
  let discriminantPosition := discriminantPositions[selected]!
  let discriminant := arguments[discriminantPosition]!
  let motive := arguments[motivePosition]!
  let motiveArguments := discriminantPositions.map (arguments[·]!)
  let resultType ← inferType source
  let program? ← withoutModifyingState <| withNewMCtxDepth do
    try
      withLocalDeclD `option optionType fun option => do
        -- Trailing proof arguments may depend on the original discriminant even when the
        -- fully applied motive is constant. Check the entire replaced application.
        unless ← withReducible (isDefEq (mkAppN motive motiveArguments)
            (mkAppN motive (motiveArguments.set! selected option))) do return none
        let body := mkAppN source.getAppFn (arguments.set! discriminantPosition option)
        check body .default
        unless ← withReducible (isDefEq (← inferType body) resultType) do return none
        return some (← mkLambdaFVars #[option] body)
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      return none
  let some program := program? | return none
  -- Split producer control first, so the payload retains its original source.
  let proof ← if let some (_, proof) ← applyBranch? program discriminant then pure proof
    else mkAppM ``option_apply_eq_dite #[program, discriminant]
  let some (_, original, normalized) := (← inferType proof).eq? | return none
  unless ← withReducible (isDefEq original source) do return none
  check proof
  return some (normalized, proof)
/-- A generic producer may be a definitionally trivial wrapper around one of its data
arguments. Remove only such identity wrappers; ordinary container producers remain protected. -/
def identityProducer? (containerProducers : NameSet) (value : Lean.Expr) :
    MetaM (Option Lean.Expr) :=
  withoutModifyingState do
    let some name := value.getAppFn.constName? | return none
    if containerProducers.contains name then return none
    let resultType ← inferType value
    let arguments := value.getAppArgs
    let parameters ← getFunInfoNArgs value.getAppFn arguments.size
    for index in (List.range arguments.size).reverse do
      let some parameter := parameters.paramInfo[index]? | continue
      if parameter.isInstance || parameter.isImplicit || parameter.isStrictImplicit then continue
      let argument := arguments[index]!
      if (← isType argument) || (← isProof argument) then continue
      let sameType ← withNewMCtxDepth <| withDefault <|
        isDefEq resultType (← inferType argument)
      unless sameType do continue
      if ← withNewMCtxDepth <| withDefault <| isDefEq value argument then return some argument
    return none
/-- Expose source code before simplification visits its arguments. Definitional reduction
also works under dependent projections; observational equalities retain their explicit proofs.
A producer with a registered read (`Extension.readRules`), in `reads`, stays folded when its
shape is not literal, so that its read applies. -/
def programStep (boundaries containerProducers reads : NameSet) (containerFree : IO.Ref NameSet) :
    Simp.DSimproc := fun value => do
  if (← isType value) || (← isProof value) then return .continue
  let storage := (← extension).storage
  if let .proj structureName index receiver := value.getAppFn then
    if isClass (← getEnv) structureName then return .continue
    let some producer := receiver.getAppFn.constName? | return .continue
    if boundaries.contains producer || (`FloatLib).isPrefixOf producer ||
        storage.any (·.isPrefixOf producer) then return .continue
    -- A component of a pair whose producer has a registered read stays folded on a shape that
    -- is not literal, so that the read applies.
    if reads.contains producer then
      if ← withCanUnfoldPred (programCanUnfold boundaries false) (withDefault (symbolic receiver))
        then return .continue
    if let some restored ← restoreBranch? receiver then
      return .visit (mkAppN (.proj structureName index restored) value.getAppArgs)
    if receiver.isAppOf ``ite || receiver.isAppOf ``dite then return .continue
    if let some exposed ← withCanUnfoldPred (programCanUnfold boundaries false)
        (withDefault (unfoldDefinition? receiver)) then
      unless exposed == receiver do
        return .visit (mkAppN (.proj structureName index exposed) value.getAppArgs)
    return .continue
  let some name := value.getAppFn.constName? | return .continue
  if (`FloatLib).isPrefixOf name || storage.any (·.isPrefixOf name) then return .continue
  if boundaries.contains name then
    if let some reduced ← identityProducer? containerProducers value then return .visit reduced
    return .continue
  let reduce {α : Type} (action : MetaM α) : MetaM α :=
    withCanUnfoldPred (programCanUnfold boundaries false) (withDefault action)
  if let some reduced ← reduceControl? containerProducers value then
    if reduced != value then return .visit reduced
  if (name == ``ite || name == ``dite) && value.getAppNumArgs ≥ 5 then
    let type ← withReducible (whnf (← inferType value))
    -- Scalar branches can simplify their coordinate reads without expanding container programs
    -- in inactive branches. Their numerical analysis still runs under the original guard.
    return if ← hasContainer containerFree type.getForallBody then .done value else .continue
  if (← getMatcherInfo? name).isSome ||
      ((← getEnv).find? name).any (fun info => match info with
        | .recInfo _ => true | _ => false) then
    -- Scalar alternatives may simplify their guards. Container-producing alternatives stay
    -- intact until the actual discriminant determines which program is executed.
    let type ← withReducible (whnf (← inferType value))
    return if ← hasContainer containerFree type.getForallBody then .done value else .continue
  if let some projection ← getProjectionFnInfo? name then
    if projection.fromClass then
      -- Only data fields of the selected dictionary are metadata. Operand-taking methods
      -- retain their source computation and numerical obligations.
      if value.getAppNumArgs == projection.numParams + 1 then
        let type ← withReducible (whnf (← inferType value))
        if type.isConstOf ``Bool || type.isConstOf ``Nat then
          if let some selected ← withReducibleAndInstances (unfoldProjInst? value) then
            -- Numerals are already selected data. Revisiting a raw Nat literal would let
            -- simp re-encode it through OfNat and repeat the same projection indefinitely.
            if selected.consumeMData.rawNatLit?.isSome then return .done selected
            unless selected == value do return .visit selected
      -- Optional results retain the selected method and its operands. Revealing that
      -- producer lets exact observations follow a successful result without treating it as data.
      let resultType ← withReducible (whnf (← inferType value))
      if resultType.isAppOf ``Option then
        if let some selected ← withReducibleAndInstances (unfoldProjInst? value) then
          unless selected == value do return .visit selected
      return .continue
  let type ← withReducible (whnf (← inferType value))
  unless ← hasContainer containerFree type.getForallBody do return .continue
  if reads.contains name then
    if ← reduce (symbolic value) then return .done value
  if let some reduced ← reduce (unfoldDefinition? value) then
    if reduced != value then return .visit reduced
  return .continue

/-- Whether `term` has the heads of `pattern` in its explicit data arguments, to the given depth:
a cheap test before a law is unified with `term`. -/
partial def sameHeads (pattern term : Expr) (depth : Nat := 3) : MetaM Bool := do
  if depth == 0 then return true
  let .const name _ := pattern.getAppFn | return true
  unless term.isAppOfArity name pattern.getAppNumArgs do return false
  let info ← getFunInfoNArgs pattern.getAppFn pattern.getAppNumArgs
  for index in [:pattern.getAppNumArgs] do
    let some parameter := info.paramInfo[index]? | continue
    unless parameter.binderInfo.isExplicit && !parameter.isProp do continue
    unless ← sameHeads pattern.getAppArgs[index]! term.getAppArgs[index]! (depth - 1) do
      return false
  return true

/-- The laws reading an entry that is a sum (`Extension.sums`), the most specific first, each with
the head of the container its left side reads. -/
def sumReads : MetaM (Array (Name × Name)) := do
  let mut reads := #[]
  for sum in (← extension).sums do
    unless sum.entries do continue
    for (name, inverse) in sum.laws do
      if inverse then continue
      let some info := (← getEnv).find? name | continue
      let head? ← forallTelescopeReducing info.type fun _ conclusion => do
        let some (_, read, _) := conclusion.eq? | return none
        let some position ← readPosition? read | return none
        return read.getAppArgs[position]!.getAppFn.constName?
      if let some head := head? then reads := reads.push (name, head)
  return reads

/-- Read an entry that is a sum by the laws `reads` (`sumReads`), the first that applies. A law is
unified with the entry at default transparency, so that the proofs a producer carries, such as of
its axes or of its shape, match whatever statement they were elaborated at; instance arguments the
entry does not fix are synthesized. -/
def readSum (reads : Array (Name × Name)) : Simp.Simproc := fun entry => do
  let some position ← readPosition? entry | return .continue
  let container := entry.getAppArgs[position]!
  for (name, head) in reads do
    unless container.isAppOf head do continue
    let read? ← (commitWhenSome? do
      let law ← mkConstWithFreshMVarLevels name
      let (arguments, binders, type) ← forallMetaTelescopeReducing (← ruleType law)
      let some (_, left, right) := type.eq? | return none
      unless ← sameHeads left entry do return none
      unless ← withDefault (isDefEq left entry) do return none
      for argument in arguments, binder in binders do
        if binder.isInstImplicit && (← instantiateMVars argument).isMVar then
          let some found ← synthInstance? (← inferType argument) | return none
          unless ← isDefEq argument found do return none
      let proof ← instantiateMVars (mkAppN law arguments)
      if proof.hasExprMVar then return none
      return some (← instantiateMVars right, proof) : MetaM (Option (Expr × Expr)))
    if let some (read, proof) := read? then
      return .visit { expr := read, proof? := some proof }
  return .continue

/-- Read container and record branches through the same proved function-application rule. -/
def observeBranch : Simp.Simproc := fun expression => do
  if let .proj structureName index receiver := expression then
    if isClass (← getEnv) structureName then return .continue
    unless receiver.isAppOfArity ``ite 5 || receiver.isAppOfArity ``dite 5 do
      return .continue
    let observe ← withLocalDeclD `record (← inferType receiver) fun record =>
      mkLambdaFVars #[record] (.proj structureName index record)
    let some (result, proof) ← applyBranch? observe receiver | return .continue
    return .visit { expr := result, proof? := some proof }
  -- The container must be the read's last argument but the index, so that it can vary.
  let some position ← readPosition? expression | return .continue
  unless position + 2 == expression.getAppNumArgs do return .continue
  let arguments := expression.getAppArgs
  let container := arguments[position]!
  unless container.isAppOfArity ``ite 5 || container.isAppOfArity ``dite 5 do return .continue
  let observe ← withLocalDeclD `tensor (← inferType container) fun container =>
    mkLambdaFVars #[container] (mkAppN expression.getAppFn (arguments.set! position container))
  let some (result, proof) ← applyBranch? observe container | return .continue
  return .visit { expr := result, proof? := some proof }
/-- A successful getter agrees with a constant-motive observation of the original option. The
getter of a mapped option is the map applied to the getter of the option (`Option.get_map`). -/
def optionGet? (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  unless expression.isAppOfArity ``Option.get 3 do return none
  if expression.hasExprMVar then return none
  let arguments := expression.getAppArgs
  if arguments[1]!.isAppOfArity ``Option.map 4 then
    let mapped := arguments[1]!.getAppArgs
    let proof ← mkAppOptM ``Option.get_map
      #[none, none, some mapped[2]!, some mapped[3]!, some arguments[2]!]
    let some (_, _, result) := (← inferType proof).eq? | return none
    return some (result, proof)
  let producer ← withCanUnfoldPred (programCanUnfold {} false) <|
    withDefault (whnf arguments[1]!)
  unless producer.isAppOf ``Option.some || producer.isAppOf ``Option.none ||
      producer.isAppOfArity ``ite 5 || producer.isAppOfArity ``dite 5 do return none
  let capability ← mkAppM ``OfNat #[arguments[0]!, mkNatLit 0]
  let .some numeral ← trySynthInstance capability | return none
  let fallback ← mkAppOptM ``OfNat.ofNat
    #[some arguments[0]!, some (mkNatLit 0), some numeral]
  let proof ← mkAppOptM ``Option.get_eq_getD
    #[some arguments[0]!, some fallback, some arguments[1]!, some arguments[2]!]
  let some (_, _, result) := (← inferType proof).eq? | return none
  return some (result, proof)

/-- A paired observation also supplies its component observations. Derive these proofs directly
from the existing equality rather than requiring two wrapper lemmas for every adapter. -/
def projectedObservations (name : Name) : MetaM (Array Lean.Expr) := do
  let declaration ← getConstInfo name
  let rule := mkConst name (declaration.levelParams.map Level.param)
  forallTelescopeReducing declaration.type fun arguments conclusion => do
    let some (type, left, right) := conclusion.eq? | return #[]
    unless left.isAppOfArity ``Prod.mk 4 do return #[]
    let original := mkAppN rule arguments
    let mut proofs := #[]
    for index in [:2] do
      let projection ← withLocalDeclD `pair type fun pair =>
        mkLambdaFVars #[pair] (.proj ``Prod index pair)
      let proof ← mkAppM ``congrArg #[projection, original]
      -- Index the component observation, before reduction can expose its representation.
      let expected ← mkEq left.getAppArgs[2 + index]! (.proj ``Prod index right)
      let proof := mkApp2 (mkConst ``id [0]) expected proof
      proofs := proofs.push (← mkLambdaFVars arguments proof)
    return proofs

/-- Add the caller's equalities and range exclusions, which conditional coordinate laws can use.
An IEEE descriptor hypothesis also supplies the Boolean check of its encoding. -/
def addLocalRewrites (theorems : SimpTheorems) : MetaM SimpTheorems := do
  let mut theorems := theorems
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type := declaration.type
    -- An equality whose right side contains its left side would rewrite without end.
    let loops := match type.eq? with
      | some (_, left, right) => (right.find? (· == left)).isSome
      | none => false
    if (type.isAppOf ``Eq || type.isAppOf ``Iff || type.isAppOf ``Not || type.isAppOf ``Ne) &&
        !loops then
      theorems ← theorems.add (.fvar declaration.fvarId) #[] declaration.toExpr
    -- A disequality also rules out the equality of its sides in the other order.
    if type.isAppOf ``Ne || (type.not?.any (·.isAppOfArity ``Eq 3)) then
      theorems ← theorems.add (.fvar declaration.fvarId) #[]
        (← mkAppM ``Ne.symm #[declaration.toExpr])
    -- Derive the Boolean capability without rewriting descriptors inside scalar types.
    if let some (_, predicate, result) := type.eq? then
      if predicate.isAppOfArity ``FloatFormat.isIEEE 1 && result.isConstOf ``Bool.true then
        let descriptor : Q(FloatFormat) := predicate.getAppArgs[0]!
        let expected : Q(Prop) :=
          q((FloatFormat.encoding $descriptor == FloatFormat.Encoding.ieee) = true)
        let proof ← mkAppM ``FloatFormat.supportsInfinity_eq_true_of_isIEEE
          #[descriptor, declaration.toExpr]
        let proof := mkApp2 (mkConst ``id [0]) expected proof
        check proof
        theorems ← theorems.add (.fvar declaration.fvarId) #[] proof (post := false)
  return theorems

/-- Observational equalities remove representation plumbing. Compiler equalities recover the
source computation, including its operation order. Scalar accuracy is handled separately. -/
def addProgramRewrites (theorems : SimpTheorems) (rewrites : Array (Name × Bool)) :
    MetaM SimpTheorems := do
  let mut theorems := theorems
  -- Preserve the producer when observing a successful mapped coefficient. A rational
  -- payload can use the existing total decoder law once get is written as getD zero.
  theorems ← theorems.addConst ``Option.get_map (post := false)
  let ratGet : Q(∀ (option : Option Rat) (found : option.isSome),
      option.get found = option.getD (0 : Rat)) :=
    q(fun option found => @Option.get_eq_getD Rat 0 option found)
  theorems ← theorems.add (.decl ``Option.get_eq_getD) #[] ratGet (post := false)
  -- Simplify logical guards and identity transports before exposing their implementation.
  for name in #[``eq_self, ``not_false_eq_true, ``not_true_eq_false,
      ``Bool.and_false, ``Bool.and_true, ``Bool.false_and, ``Bool.true_and,
      ``Bool.or_false, ``Bool.or_true, ``Bool.false_or, ``Bool.true_or,
      ``Bool.not_false, ``Bool.not_true, ``bne_self_eq_false,
      ``ite_eq_left, ``ite_eq_right, ``dite_eq_left, ``dite_eq_right,
      ``ite_apply, ``dite_apply] do
    theorems ← theorems.addConst name (post := false)
  -- Registered program rewrites, such as reading a cast container one axis at a time.
  for (name, prio) in (← extension).programRewrites do
    theorems ← theorems.addConst name (post := false) (prio := prio)
  -- An entry that is a sum is read by its sum's laws, the most specific first, before any other
  -- read of it.
  for sum in (← extension).sums do
    unless sum.entries do continue
    for h : index in [:sum.laws.size] do
      let (name, inverse) := sum.laws[index]
      theorems ← theorems.addConst name (inv := inverse) (post := false)
        (prio := eval_prio high + sum.laws.size - index)
  for name in #[``Fin.cast_cast, ``Fin.cast_eq_self] do
    theorems ← theorems.addConst name (post := false)
  for (name, inverse) in rewrites do
    theorems ← theorems.addConst name (inv := inverse) (post := false)
    unless inverse do
      for proof in ← projectedObservations name do
        let declaration ← getConstInfo name
        theorems ← theorems.add (.decl name) declaration.levelParams.toArray proof (post := false)
  return theorems

/-- Container-observation laws that read coordinates without unfolding buffers or dictionaries:
the registered ones, such as the laws reading an entry through the producer that computes it. -/
def coordinateTheorems (rewrites : Array (Name × Bool)) : MetaM SimpTheorems := do
  let extension ← extension
  let mut theorems : SimpTheorems := {}
  for name in extension.coordinateUnfold do
    theorems ← theorems.addDeclToUnfold name
  -- A coordinate read through `id`, as a permutation of tensor axes writes it, is the coordinate.
  for name in extension.readRewrites ++ extension.coordinateRewrites ++
      #[``Nat.zero_mul, ``Nat.zero_add, ``Bool.cond_eq_ite, ``id_eq] do
    if (← getEnv).contains name then
      theorems ← theorems.addConst name (post := false)
  addProgramRewrites theorems rewrites

/-- Traversal equalities that fuse source maps into loops without exposing storage: the
registered ones, such as the equalities writing a reduction or a sum as its loop. -/
def foldTheorems (rewrites : Array (Name × Bool)) : MetaM SimpTheorems := do
  let extension ← extension
  let mut theorems : SimpTheorems := {}
  let (laws, unfolded) ← sumLaws
  for name in unfolded ++ extension.foldUnfold do
    theorems ← theorems.addDeclToUnfold name
  for (name, inverse) in laws do
    theorems ← theorems.addConst name (inv := inverse)
  theorems ← theorems.addConst ``Bool.cond_eq_ite
  -- A loop over an empty range is its initial value, so that it adds no obligation.
  for name in #[``List.finRange_zero, ``List.foldl_nil, ``Fin.foldl_zero] do
    theorems ← theorems.addConst name
  for (name, inverse) in extension.foldRewrites do
    theorems ← theorems.addConst name (inv := inverse)
  addProgramRewrites theorems rewrites

/-- Codec laws that decode a real observation through the selected scalar methods. -/
def decodingTheorems (rewrites : Array (Name × Bool)) : MetaM SimpTheorems := do
  let mut theorems : SimpTheorems := {}
  theorems ← theorems.addDeclToUnfold ``FloatLib.Floats.ExecFloat.Binary.toReal
  theorems ← theorems.addDeclToUnfold ``FloatLib.Floats.ExecFloat.Binary.toRat?
  for field in (getStructureInfo (← getEnv) ``MathFunctions).fieldInfo do
    theorems ← theorems.addDeclToUnfold field.projFn
  for declaration in #[``decode_unary, ``decode_binary,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_ofModel,
      ``decode_family,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_neg,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_abs,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_min,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_max,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_ofRat,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_roundToIntegral] ++
        (← extension).decodingRewrites do
    theorems ← theorems.addConst declaration
  addProgramRewrites theorems rewrites

/-- FloatLib meanings used to compare configured computations, rather than asking different
execution backends to have definitionally identical implementations. -/
def semanticTheorems (decodeClassifiers : Bool) : MetaM SimpTheorems := do
  let mut theorems : SimpTheorems := {}
  for name in #[``FloatLib.Floats.ExecFloat.Binary.toReal,
      ``FloatLib.Floats.ExecFloat.Binary.isFinite, ``FloatLib.Floats.ExecFloat.Binary.isZero,
      ``FloatLib.Floats.ExecFloat.Binary.signBit, ``Except.toOption, ``Option.getD] do
    theorems ← theorems.addDeclToUnfold name
  for field in (getStructureInfo (← getEnv) ``MathFunctions).fieldInfo do
    theorems ← theorems.addDeclToUnfold field.projFn
  if decodeClassifiers then
    -- This mode compares fresh Boolean propositions only. Other source normalization keeps
    -- the public decoder intact so an unknown producer cannot become an exact input.
    for name in #[``FloatLib.Floats.ExecFloat.Binary.toModel,
        ``FloatLib.Floats.ExecFloat.Binary.ofModel, ``Rat.cast, ``RatCast.ratCast,
        ``OfNat.ofNat, ``OfScientific.ofScientific] do
      theorems ← theorems.addDeclToUnfold name
  for name in #[``FloatLib.Floats.ExecFloat.Binary.toModel_hAdd,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_hSub,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_hMul,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_hDiv,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_neg,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_abs,
      ``FloatLib.Floats.ExecFloat.Binary.toModel_ofModel, ``decode_family, ``decode_unary,
      ``sub_self, ``abs_zero, ``zero_add, ``add_zero, ``zero_mul, ``mul_zero,
      ``zero_div, ``Real.sqrt_zero, ``Nat.cast_zero, ``Nat.cast_one,
      ``Rat.cast_natCast, ``Rat.cast_intCast, ``Rat.cast_ofScientific,
      ``Rat.cast_zero, ``Rat.cast_one] do
    theorems ← theorems.addConst name (post := !decodeClassifiers)
  if decodeClassifiers then
    theorems ← theorems.addConst ``Configured.Family.toModel_ofModel (post := false)
  theorems ← theorems.addConst ``ExecFloat.Binary.toReal_zero (post := false)
  return theorems
/-- Classify the registered rules and build every normalizer's environment lemmas. -/
def Session.prepare : MetaM Session := do
  if (caughtDepths.getState (← getEnv)).isNone then
    let count ← IO.mkRef 0
    modifyEnv (caughtDepths.setState · (some count))
  let containerFree ← IO.mkRef {}
  let (rewrites, boundaries) ← programRules containerFree
  let mut containerProducers : NameSet := {}
  for name in boundaries do
    if let some info := (← getEnv).find? name then
      if ← hasContainer containerFree info.type.getForallBody then
        containerProducers := containerProducers.insert name
  let mut reads : Array (Name × Name) := #[]
  let mut symbolicBounds : NameSet := {}
  for name in ← readRules do
    let some info := (← getEnv).find? name | continue
    let some producer ← forallTelescopeReducing info.type fun _ conclusion => do
        let some (_, read, _) := conclusion.eq? | return none
        let some position ← readPosition? read | return none
        let producer := containerProducer read.getAppArgs[position]!
        return if producer == .anonymous then none else some producer
      | do
          symbolicBounds := symbolicBounds.insert name
          continue
    reads := reads.push (producer, name)
  let readProducers := reads.foldl (fun producers (producer, _) => producers.insert producer) {}
  let mut procedures := ({} : Simp.Simprocs).addCore #[.star] ``programStep false
    (.inr (programStep boundaries containerProducers readProducers containerFree))
  procedures := procedures.addCore #[.star] ``observeBranch false (.inl observeBranch)
  let sums ← sumReads
  unless sums.isEmpty do
    procedures := procedures.addCore #[.star] ``readSum false (.inl (readSum sums))
  for (name, post, procedure) in (← extension).procedures do
    procedures := procedures.addCore #[.star] name post procedure
  let decoding ← decodingTheorems rewrites
  let mut budget : SimpTheorems := {}
  for name in #[``zero_mul, ``mul_zero, ``zero_add, ``add_zero, ``one_mul, ``mul_one,
      ``zero_div, ``div_one, ``mul_neg_one, ``neg_one_mul, ``add_sub_cancel, ``sub_self,
      ``sub_zero, ``abs_zero, ``abs_abs, ``abs_neg, ``abs_one, ``max_self, ``min_self,
      ``neg_zero, ``Real.abs_exp, ``Real.exp_zero, ``Rat.cast_zero, ``Rat.cast_one,
      ``Rat.cast_neg, ``Rat.cast_ofNat, ``Nat.cast_zero, ``Nat.cast_one, ``dite_eq_ite,
      ``ite_self, ``neg_neg, ``zero_sub, ``sub_neg_eq_add, ``neg_add_eq_sub] do
    budget ← budget.addConst name
  -- A rule instantiated at a computed container, such as a row of a matrix, reads its entries
  -- through that producer; its reference, budgets and conditions read them as the program does.
  for name in (← extension).readRewrites do
    budget ← budget.addConst name
  return {
    budget
    boundaries
    containerProducers
    reads
    symbolicBounds
    containerFree
    failures := (← IO.mkRef {})
    solved := (← IO.mkRef {})
    settledSigns := (← IO.mkRef {})
    comparisons := (← IO.mkRef {})
    inequivalent := (← IO.mkRef {})
    analysisFailures := (← IO.mkRef {})
    carriers := (← IO.mkRef {})
    finiteCuts := (← IO.mkRef 0)
    tidied := (← IO.mkRef {})
    signFailures := (← IO.mkRef {})
    derivations := (← IO.mkRef {})
    leastFuel := (← IO.mkRef 0)
    positivityFailures := (← IO.mkRef {})
    descriptions := (← IO.mkRef {})
    factsOf := (← IO.mkRef {})
    unitPairs := (← IO.mkRef {})
    contexts := (← IO.mkRef {})
    givens := (← IO.mkRef {})
    givenBounds := (← IO.mkRef {})
    hypothesisSimp := (← IO.mkRef {})
    normalized := (← IO.mkRef {})
    procedures := #[procedures]
    coordinate := (← coordinateTheorems rewrites)
    fold := (← foldTheorems rewrites)
    decoding
    guards := (← decoding.addConst ``Bool.false_eq_true)
    semantic := (← semanticTheorems false)
    classifiers := (← semanticTheorems true) }

/-- The simplification context of the normalizer `kind` in the current local context: `theorems`
with the local rewrites (`addLocalRewrites`), built once per local context. -/
def Session.localContext (session : Session) (kind : Name) (theorems : SimpTheorems)
    (config : Simp.Config) (congruences : Bool) : MetaM Simp.Context := do
  let key := (kind, (← getLCtx).getFVarIds)
  if let some context := (← session.contexts.get).get? key then return context
  let congruences ← if congruences then getSimpCongrTheorems else pure {}
  let context ← Simp.mkContext config #[← addLocalRewrites theorems] congruences
  session.contexts.modify (·.insert key context)
  return context

/-- Normalize container observations without unfolding their buffers or arithmetic dictionaries. -/
def coordinateSimpContext (session : Session) :
    MetaM (Simp.Context × Simp.SimprocsArray) := do
  let context ← session.localContext `coordinate session.coordinate
    { failIfUnchanged := false, implicitDefEqProofs := false } true
  return (context, session.procedures)

/-- Fuse source maps into loops using proved traversal equalities, without exposing storage. -/
def foldSimpContext (session : Session) :
    MetaM (Simp.Context × Simp.SimprocsArray) := do
  let context ← session.localContext `fold session.fold
    { implicitDefEqProofs := false, failIfUnchanged := false } true
  return (context, session.procedures)

/-- Write a loop of another kind, such as a loop over `Fin n` or over an array, as a registered
loop by the registered conversions. -/
def conversionSimpContext : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  for (name, inverse) in (← extension).conversions do
    theorems ← theorems.addConst name (inv := inverse)
  Simp.mkContext { implicitDefEqProofs := false } #[theorems]

/-- Write a loop over a computed container as a loop over the containers its producer reads, with
the producer in the step, by the loop's fusion laws (`Loop.fusions`). -/
def fusionSimpContext (loop : Loop) : MetaM Simp.Context := do
  let mut theorems : SimpTheorems := {}
  for name in loop.fusions do
    theorems ← theorems.addConst name
  Simp.mkContext { implicitDefEqProofs := false } #[theorems]

/-- Decode a real observation, keeping registered producers and arithmetic intact. -/
def decodingSimpContext (session : Session) :
    MetaM (Simp.Context × Simp.SimprocsArray) := do
  let context ← session.localContext `decoding session.decoding
    { implicitDefEqProofs := false } false
  return (context, session.procedures)

/-- Simplify `term` with the normalizer `kind`, given as `context` and `procedures` for the current
local context. A term without metavariables shares the normalizer's cache in this context, so
the subterms that the analysis normalizes again at each level are simplified once. -/
def Session.normalize (session : Session) (kind : Name) (term : Lean.Expr)
    (context : Simp.Context) (procedures : Simp.SimprocsArray) : MetaM Simp.Result := do
  if term.hasMVar then return (← simp term context procedures).1
  let key := (kind, (← getLCtx).getFVarIds)
  -- The cache leaves the table while simp extends it, so that the extension does not copy it.
  let cache ← session.normalized.modifyGet fun caches => (caches.getD key {}, caches.erase key)
  let (result, state) ← simpCore term context procedures (s := { cache })
  session.normalized.modify (·.insert key state.cache)
  return result

/-- Simplify `term` with the identities of zero and one in `context`. A term without metavariables
shares the session's cache of tidied terms, which no local hypothesis affects. -/
def Session.tidyTerm (session : Session) (term : Lean.Expr) (context : Simp.Context) :
    MetaM Simp.Result := do
  if term.hasMVar then return (← simp term context).1
  let cache ← session.tidied.modifyGet fun cache => (cache, {})
  let (result, state) ← simpCore term context (s := { cache })
  session.tidied.set state.cache
  return result

/-- Continue `goal` at the simplification `result` of its target `target`, as `simpTarget` does:
a target simplified to `True` closes the goal, and an unchanged one keeps it. -/
def applySimpResult? (goal : MVarId) (target : Lean.Expr) (result : Simp.Result) :
    MetaM (Option MVarId) := do
  if result.expr.isTrue then
    goal.assign (← match result.proof? with
      | some proof => mkOfEqTrue proof
      | none => pure (mkConst ``True.intro))
    return none
  if result.expr == target then return some goal
  some <$> applySimpResultToTarget goal target result

/-- Compare configured computations through their proved FloatLib meanings. -/
def semanticContext (session : Session) (decodeClassifiers : Bool := false) :
    MetaM Simp.Context := do
  let mut theorems := if decodeClassifiers then session.classifiers else session.semantic
  -- A caller may have already checked the reference and recorded its exact returned value.
  for declaration in ← getLCtx do
    unless declaration.type.isAppOfArity ``Eq 3 do continue
    unless declaration.type.getAppArgs[0]!.isAppOf ``Except do continue
    theorems ← theorems.add (.fvar declaration.fvarId) #[] declaration.toExpr (post := false)
  Simp.mkContext { implicitDefEqProofs := false, zetaDelta := false } #[theorems]

/-- Decide a branch guard with the program's Boolean and dictionary-field simplifications, giving
evidence for the guard or for its negation. A guard left undecided, including by a simplification
that fails or exceeds its budget, keeps both branches. -/
def decideGuard? (session : Session) (condition : Lean.Expr) :
    TacticM (Option (Bool × Lean.Expr)) :=
  attempt? 10000 do
    let context ← session.localContext `guards session.guards { implicitDefEqProofs := false }
      false
    let (decided, _) ← simp condition context session.procedures
    if decided.expr.isTrue then
      return some (true, ← mkAppM ``of_eq_true #[← decided.getProof' condition])
    if decided.expr.isFalse then
      return some (false, ← mkAppM ``of_eq_false #[← decided.getProof' condition])
    return none
/-- Build congruence without first comparing whole loop functions by reduction. That comparison
would expose their floating-point implementations before the decoding rules can be used. -/
def congrLoopArguments (goal : MVarId) : MetaM (Array MVarId) := do
  let target ← goal.getType
  let args := target.getAppArgs
  let left := args[1]!
  let right := args[2]!
  let loops := (← extension).loops
  let arity := if loops.any (left.isAppOf ·.allSteps) then 4
    else if loops.any (left.isAppOf ·.foldError) then 7 else 0
  if arity == 0 then throwError "roundoff: no loop congruence for this expression"
  let mut current := left.getAppArgs
  let desired := right.getAppArgs
  unless current.size == desired.size do throwError "roundoff: incompatible loop applications"
  for index in [:current.size - arity] do
    unless ← withTransparency .reducible (isDefEq current[index]! desired[index]!) do
      throwError "roundoff: loop types or storage differ"
  let mut proof ← mkEqRefl left
  let mut pending := #[]
  for index in [current.size - arity:current.size] do
    if current[index]! == desired[index]! then continue
    let equality ← mkFreshExprMVar (← mkEq current[index]! desired[index]!)
    let argumentType ← inferType current[index]!
    let replacement ← withLocalDeclD `argument argumentType fun argument =>
      mkLambdaFVars #[argument] (mkAppN left.getAppFn (current.set! index argument))
    let step ← mkAppM ``congrArg #[replacement, equality]
    proof ← mkAppM ``Eq.trans #[proof, step]
    current := current.set! index desired[index]!
    pending := pending.push equality.mvarId!
  goal.assign proof
  return pending

/-- Introduce function arguments without a reflexivity attempt on their numeric bodies. -/
partial def pointwiseGoal (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← goal.getType
  unless target.isAppOfArity ``Eq 3 do return goal
  let left := target.getAppArgs[1]!
  unless (← withTransparency .reducible (whnf (← inferType left))).isForall do return goal
  let [pointwise] ← goal.apply (← mkConstWithFreshMVarLevels ``funext)
    { synthAssignedInstances := false }
    | throwError "roundoff: unexpected function equality"
  let (_, body) ← pointwise.intro1
  pointwiseGoal body

/-- Prove equal observations of implementations with the same floating-point semantics.
Congruence stops at one application layer; scalar values are compared by exact decoding. -/
def semanticEquality (session : Session) (goal : MVarId) : TacticM Bool := do
  let target ← goal.getType
  unless target.isAppOfArity ``Eq 3 do return false
  let arguments := target.getAppArgs
  unless arguments[1]!.getAppFn == arguments[2]!.getAppFn do return false
  let succeeded? ← attempt? 10000 do
    let context ← semanticContext session
    let arguments ← congrLoopArguments goal
    let mut complete := true
    for argument in arguments do
      let pointwise ← pointwiseGoal argument
      let leaves ← Lean.Elab.Tactic.run pointwise do
        evalTactic (← `(tactic| try apply FloatLib.Floats.ExecFloat.Binary.toModel_inj.mp))
      for leaf in leaves do
        let (next, _) ← simpTarget leaf context
        if let some next := next then
          let closed ← try
            next.withContext (withTransparency .reducible next.refl)
            pure true
          catch _ => pure false
          unless closed do
            trace[roundoff] "semantic equality remains: {← next.getType}"
            complete := false
    return if complete then some () else none
  return succeeded?.isSome

/-- Transport an error proof across a proved normalization of its actual computation. The
finiteness fact still concerns the normalized value; a consumer checks that it is the value it
needs. -/
def rewriteActual (estimate : Estimate) (equality : Lean.Expr) : MetaM Estimate := do
  let reference := estimate.reference
  let statement ← match estimate.bound with
    | .absolute error => pure q(fun value : ℝ => |value - $reference| ≤ $error)
    | .mixed relative absolute =>
        pure q(fun value : ℝ => MixedError value $reference $relative $absolute)
  let proposition ← mkAppM ``congrArg #[statement, equality]
  return { estimate with proof := (← mkAppM ``Eq.mpr #[proposition, estimate.proof]) }

/-- The proof of `motive after` from a proof of `motive before` and `equality : before = after`,
for a proposition `motive` about a real number. The term is built directly: the app builder would
instantiate the metavariables of the whole proof, such as its open obligations, on each call. -/
def transportReal (motive before after equality proof : Lean.Expr) : Lean.Expr :=
  mkApp4 (mkConst ``Eq.mp [0]) (motive.beta #[before]) (motive.beta #[after])
    (mkApp6 (mkConst ``congrArg [1, 1]) q(ℝ) (mkSort 0) before after motive equality) proof

/-- Replace the reference of a mixed estimate by a proved equal one. -/
def rewriteReference (estimate : Estimate) (equality : Lean.Expr) : MetaM Estimate := do
  let .mixed relative absolute := estimate.bound | return estimate
  let some (_, previous, reference) := (← inferType equality).eq? | return estimate
  let statement ← instantiateMVars (← inferType estimate.proof)
  let actual : Q(ℝ) := statement.getAppArgs[0]!
  let motive := q(fun value : ℝ => MixedError $actual value $relative $absolute)
  let proof := transportReal motive previous reference equality estimate.proof
  return { estimate with reference, proof }

/-- Transport an estimate of `observe next` to `observe source` along `equality : source = next`
between floating-point values, together with its finiteness when that concerns `next`. -/
def rewriteValue (estimate : Estimate) (observe equality : Lean.Expr) :
    MetaM Estimate := do
  let estimate ← rewriteActual estimate (← mkCongrArg observe equality)
  let some finite := estimate.finite? | return estimate
  let some (type, _, next) := (← inferType equality).eq? | return estimate
  let motive ← withLocalDeclD `value type fun value => do
    mkLambdaFVars #[value]
      (← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value]) (mkConst ``Bool.true))
  let fact ← instantiateMVars (← inferType finite)
  unless ← withNewMCtxDepth (isDefEq fact (motive.beta #[next])) do return estimate
  return { estimate with finite? := some (← mkEqMPR (← mkCongrArg motive equality) finite) }

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
