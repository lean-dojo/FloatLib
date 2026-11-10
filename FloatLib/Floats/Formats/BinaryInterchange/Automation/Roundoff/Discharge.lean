/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Index

/-!
# Side conditions of `roundoff`

Bounded tactics try the inexpensive side conditions: hypotheses about the same relation, budget
simplification, reflexivity, decision, registered helper lemmas, the conditions of a loop that hold
at every step, and semantic comparison of configured computations. A premise that a correctly
rounded call is finite becomes that primitive's domain and range conditions. A condition that fails
is remembered with the facts of its scope, and one that cannot be proved stays open for the caller.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- Close `goal` by `dischargeSimp` with the hypotheses of its context, as
`simp only [*, ...]` does. The simplification set of a context is built once, and a target
without metavariables shares that context's cache (`Session.normalize`). -/
def simpWithHypotheses (session : Session) (goal : MVarId) :
    TacticM (Option Unit) := goal.withContext do
  let some (base, simprocs) := session.dischargeSimp | return none
  let key := (← getLCtx).getFVarIds
  let context ← match (← session.hypothesisSimp.get).get? key with
    | some context => pure context
    | none => do
      let mut theorems := base.simpTheorems
      for hypothesis in ← getPropHyps do
        unless theorems.isErased (.fvar hypothesis) do
          theorems ← theorems.addTheorem (.fvar hypothesis) (← hypothesis.getDecl).toExpr
            (config := base.indexConfig)
      let context := base.setSimpTheorems theorems
      session.hypothesisSimp.modify (·.insert key context)
      pure context
  let target ← instantiateMVars (← goal.getType)
  if target.hasMVar then
    let (remaining, _) ← simpGoal goal context simprocs
    return if remaining.isNone then some () else none
  let result ← session.normalize `hypotheses target context simprocs
  unless result.expr.isTrue do return none
  goal.assign (← match result.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro))
  return some ()

/-- The value that an absolute bound `|x - r| ≤ e` or a mixed bound concerns, read
syntactically. -/
def boundValue? (type : Lean.Expr) : Option Lean.Expr :=
  let type := type.consumeMData
  if type.isAppOfArity ``MixedError 4 then some type.getAppArgs[0]!
  else if type.isAppOfArity ``LE.le 4 then
    let left := type.getAppArgs[2]!
    if left.isAppOf ``abs && left.appArg!.isAppOfArity ``HSub.hSub 6 then
      some left.appArg!.getAppArgs[4]!
    else none
  else none

/-- Whether a bound about `fact` may unify with a bound about `target` without evaluating code:
their heads agree, and so do those of the values they decode. A metavariable, a local definition
or one of the fact's own variables `bound` agrees with every head. -/
def sameBoundValue (bound : Array Lean.Expr) (fact target : Lean.Expr) : MetaM Bool := do
  let head (value : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match value.getAppFn with
    | .const name _ => return some (.const name [])
    | .fvar id =>
        if bound.contains (.fvar id) || (← id.getDecl).value?.isSome then return none
        return some (.fvar id)
    | _ => return none
  let agree (left right : Lean.Expr) : MetaM Bool := do
    match ← head left, ← head right with
    | some left, some right => return left == right
    | _, _ => return true
  unless ← agree fact target do return false
  let decoders := #[``ExecFloat.Binary.toReal, ``Model.toReal]
  if decoders.any fact.isAppOf && decoders.any target.isAppOf then
    let (some left, some right) := (fact.getAppArgs.back?, target.getAppArgs.back?) | return true
    return ← agree left right
  return true

/-- The value of a closed natural-number or integer term, by kernel reduction. -/
private partial def kernelInt? (term : Lean.Expr) : MetaM (Option Int) := do
  let .ok value := Kernel.whnf (← getEnv) (← getLCtx) term | return none
  match value with
  | .lit (.natVal n) => return some n
  | .app (.const ``Int.ofNat _) n => return (← kernelInt? n)
  | .app (.const ``Int.negSucc _) n => return (← kernelInt? n).map (-· - 1)
  | _ => return none

/-- The formats `f` of the subterms `Model.posMaxFinite f` of `term`, each once. -/
private partial def largestFiniteFormats (term : Lean.Expr) (found : Array Lean.Expr) :
    Array Lean.Expr :=
  match term with
  | .app function argument =>
    let found := largestFiniteFormats argument (largestFiniteFormats function found)
    if term.isAppOfArity ``Model.posMaxFinite 1 && !found.contains argument then
      found.push argument
    else found
  | .lam _ type body _ | .forallE _ type body _ =>
    largestFiniteFormats body (largestFiniteFormats type found)
  | .letE _ type value body _ =>
    largestFiniteFormats body (largestFiniteFormats value (largestFiniteFormats type found))
  | .mdata _ inner | .proj _ _ inner => largestFiniteFormats inner found
  | _ => found

/-- The widest exponent and fraction fields for which closed conditions on a format are evaluated:
the closed form of its largest finite value, and the kernel evaluation of a converted literal. A
format beyond them keeps such conditions symbolic, so that no huge power is built. -/
def closedFormatLimit : Nat := 20

/-- Whether the closed format `format` has exponent and fraction fields within
`closedFormatLimit` and `2 ^ closedFormatLimit` bits, both read by the kernel before anything
larger is computed. -/
private def smallFormat (format : Lean.Expr) : MetaM Bool := do
  let some width ← kernelInt? (mkApp (mkConst ``FloatFormat.expWidth) format) | return false
  let some precision ← kernelInt? (mkApp (mkConst ``FloatFormat.fracWidth) format) | return false
  return width ≤ closedFormatLimit && precision ≤ 2 ^ closedFormatLimit

/--
Rewrite the largest finite value of every concrete format in the target of `goal` to its closed
form `significand * 2 ^ exponent`, with both parts computed by the kernel
(`Model.toReal_posMaxFinite_of_eq`). A format with a free variable, or outside `smallFormat`, is
left as it is.
-/
def unfoldLargestFinite (goal : MVarId) : MetaM MVarId := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let formats := largestFiniteFormats target #[]
  let mut goal := goal
  for format in formats do
    if format.hasFVar || format.hasMVar then continue
    unless ← smallFormat format do continue
    let fracWidth := mkApp (mkConst ``FloatFormat.fracWidth) format
    let significandTerm ← mkAppM ``HAdd.hAdd #[mkApp (mkConst ``Model.pow2) fracWidth,
      mkApp (mkConst ``FloatFormat.maxFiniteFracField) format]
    let exponentTerm ← mkAppM ``HSub.hSub #[mkApp (mkConst ``FloatFormat.maxNormalExponent) format,
      mkApp (mkConst ``Int.ofNat) fracWidth]
    let some significand ← kernelInt? significandTerm | continue
    let some exponent ← kernelInt? exponentTerm | continue
    unless significand ≥ 0 do continue
    let significand := toExpr significand.toNat
    let exponent := toExpr exponent
    -- The kernel checks both reflexivity proofs against the computed values.
    let equation := mkAppN (mkConst ``Model.toReal_posMaxFinite_of_eq)
      #[format, significand, exponent, ← mkEqRefl significand, ← mkEqRefl exponent]
    let result ← goal.rewrite (← goal.getType) equation
    goal ← goal.replaceTargetEq result.eNew result.eqProof
  return goal

/--
Close a closed goal about real numbers by arithmetic, with the largest finite value of each
concrete format in closed form. This decides the range of a literal such as `1.5` or `3e38` in
binary32, which a comparison with one does not.
-/
def closeByArithmetic (goal : MVarId) : TacticM Bool := do
  let solved? ← attempt? 2000 do
    let goal ← goal.withContext do goal.replaceTargetDefEq (← zetaReduce (← goal.getType))
    let goal ← unfoldLargestFinite goal
    let remaining ← Lean.Elab.Tactic.run goal (evalTactic (←
      `(tactic| set_option exponentiation.threshold 1048576 in norm_num)))
    return if remaining.isEmpty then some () else none
  return solved?.isSome

/-- Whether `q` is a decimal literal, such as `1e40` or `3`, of at most `2 ^ 12` digits and
exponent, so that evaluating its conversion is cheap. -/
private def smallLiteral (q : Lean.Expr) : MetaM Bool := do
  let bound : Nat := 2 ^ 12
  let small (term : Lean.Expr) : MetaM Bool := do
    let some value ← kernelInt? term | return false
    return value.natAbs < 10 ^ bound
  if q.isAppOfArity ``OfScientific.ofScientific 5 then
    let some exponent ← kernelInt? (q.getArg! 4) | return false
    return (← small (q.getArg! 2)) && exponent ≤ (bound : Int)
  if q.isAppOfArity ``OfNat.ofNat 3 then return ← small (q.getArg! 1)
  return false

/--
Whether the closed condition `condition` is known to be false. A proposition over the reals is
when arithmetic proves its negation (`closeByArithmetic`). The finiteness of a converted literal,
`Model.isFinite (Model.ofRat format q) = true`, is when the kernel evaluates it to `false`, for a
format within `smallFormat` and a decimal literal `q` of at most `2 ^ 12` digits and exponent. A
condition outside these cases is not refuted. The decision only refuses a theorem; nothing is
proved from it.
-/
def refutesClosed (condition : Lean.Expr) : TacticM Bool := withoutModifyingState do
  if condition.hasFVar || condition.hasMVar then return false
  if isFiniteness condition then
    let value := condition.getArg! 1
    let converted := value.getAppArgs.back!
    unless value.isAppOf ``Model.isFinite && converted.isAppOf ``Model.ofRat do
      return false
    unless ← smallFormat (converted.getArg! 0) do return false
    unless ← smallLiteral (converted.getArg! 1) do return false
    let .ok result := Kernel.whnf (← getEnv) (← getLCtx) value | return false
    return result.isConstOf ``Bool.false
  let negation ← mkFreshExprMVar (mkNot condition)
  closeByArithmetic negation.mvarId!

/-- Attempt inexpensive side conditions without hiding an unsolved premise. -/
def dischargeCore (session : Session) (goal : MVarId) : TacticM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let extension ← extension
  let reads := extension.reads
  let mut supplied := false
  -- In mixed analysis a fact, or a fact about every coordinate, applies only to a goal about the
  -- same operations; unifying it with another would evaluate floating-point code. A decoded
  -- finiteness is compared as the finiteness it is by definition.
  let mut unrelated := #[]
  let targetHead ← assumptionHead target
  let foldedTarget ← if session.mixed && (target.find? (·.isAppOf ``Model.isFinite)).isSome then
      foldDecodedFinite target
    else pure target
  -- In absolute analysis a bound, such as an input error left open, follows by assumption only
  -- from a bound about the same computation.
  let targetValue := if session.mixed then none else boundValue? target
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let type ← instantiateMVars declaration.type
    if type == target then
      goal.assign declaration.toExpr
      return true
    unless ← isProp type do continue
    let related ← if session.mixed then
        forallTelescopeReducing type fun _ body => do
          if sameRelation reads body target then return true
          let body ← if (body.find? (·.isAppOf ``Model.isFinite)).isSome then
              foldDecodedFinite body else pure body
          return sameRelation reads body foldedTarget
      else if let some value := targetValue then
        forallTelescopeReducing type fun bound body => do
          let some fact := boundValue? body | return true
          sameBoundValue bound fact value
      else pure true
    if !related then
      unrelated := unrelated.push declaration.fvarId
    -- Nor does a classification of a value computed by another operation.
    else if !supplied && !(session.mixed && otherClassified type.getForallBody target) then
      supplied := match ← assumptionHead type, targetHead with
        | some source, some target => source == target
        | _, _ => true
  -- Each tactic, with the hypotheses it does not see and its heartbeat budget; the inexpensive
  -- ones first. The conditions of a loop that hold at every step settle quickly when they hold,
  -- and otherwise expand the computations, so they get a smaller budget.
  let mut attempts : Array (Array FVarId × TSyntax `tactic × Nat) := #[]
  if supplied then attempts := attempts.push (unrelated, ← `(tactic| assumption), 1000)
  for helper in session.helpers do
    if ← helper.compatible target then attempts := attempts.push (#[], helper.tactic, 1000)
  if supplied then
    attempts := attempts.push (unrelated, ← `(tactic| solve_by_elim (maxDepth := 3)), 1000)
  -- In mixed analysis the local facts prove a fact about one value, such as its finiteness, a zero
  -- test or a unit magnitude, by simplification only through a fact about every coordinate of the
  -- same relation, or a local equation that rewrites part of the target. A classification of a
  -- value that no hypothesis is about cannot follow by rewriting.
  let classified := target.isAppOfArity ``Eq 3 && (target.getAppArgs[1]!.isAppOf
    ``ExecFloat.Binary.isFinite || target.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.isZero)
  let valueFact := isFiniteness target || target.isAppOfArity ``Eq 3 &&
    (target.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.isZero ||
      target.getAppArgs[1]!.isAppOf ``abs)
  let rewritable ← if session.mixed && valueFact then
      (← getLCtx).anyM fun declaration => do
        let type ← instantiateMVars declaration.type
        if type.isForall then return !unrelated.contains declaration.fvarId
        let some left := type.eq?.map (·.2.1) <|> type.iff?.map (·.1) | return false
        return (target.find? (· == left)).isSome
    else pure true
  -- The simplification with the local hypotheses (`simpWithHypotheses`) comes at this position.
  let mut simplifyAt := none
  if rewritable && !(session.mixed && classified && !supplied) then
    simplifyAt := some attempts.size
  -- Registered reflexivity applies to relations beyond equality.
  let reflexive ← withoutModifyingState <| withNewMCtxDepth do
    let target ← whnfR target
    if target.isAppOf ``Eq || target.isAppOf ``HEq then return true
    if target.getAppNumArgs < 2 then return false
    let relation := target.appFn!.appFn!
    unless relation.getAppFn.isConst do return true
    return !(← (Lean.Meta.Rfl.reflExt.getState (← getEnv)).getMatch relation).isEmpty
  -- Reflexivity would evaluate the floating-point code of a finiteness test.
  if reflexive && !isFiniteness target then attempts := attempts.push (#[], ← `(tactic| rfl), 1000)
  if target.isForall then attempts := attempts.push (#[], ← `(tactic| (intros; rfl)), 1000)
  if let some loop := extension.loops.find? (target.isAppOf ·.allSteps) then
    let ofForall := mkIdent loop.allStepsOfForall
    attempts := attempts.push (#[], ← `(tactic| (apply $ofForall; intros; trivial)), 300)
    -- In mixed analysis a condition on every visited input may follow from the inputs' facts:
    -- those about the same relation as a part of the condition.
    if session.mixed then
      let parts ← lambdaTelescope target.getAppArgs[target.getAppNumArgs - 3]! fun _ body => do
        return conjuncts (← foldDecodedFinite body)
      let mut unrelatedSteps := #[]
      for declaration in ← getLCtx do
        if declaration.isImplementationDetail || !declaration.type.isForall then continue
        let related ← forallTelescopeReducing declaration.type fun _ body => do
          let body ← foldDecodedFinite body
          return parts.any (sameRelation reads body ·)
        unless related do unrelatedSteps := unrelatedSteps.push declaration.fvarId
      attempts := attempts.push
        (unrelatedSteps, ← `(tactic| (apply $ofForall; intros; solve_by_elim)), 1000)
  -- A closed range condition, or the finiteness of a converted literal, that the cheap attempts
  -- below leave open is tried by arithmetic on the largest finite value afterwards.
  let mut arithmetic : Option Bool := none
  -- Match decide's own preprocessing: local let-values may close an otherwise symbolic type.
  let decidableTarget ← if target.hasFVar then zetaReduce target else pure target
  if !decidableTarget.hasFVar && !decidableTarget.hasMVar then
    attempts := attempts.push (#[], ← `(tactic| decide), 1000)
    -- A closed bound by the largest finite value of a format, such as the range of a literal,
    -- holds for a constant at most one, and so does the finiteness of such a rounded literal.
    let maximum := mkIdent ``Model.one_le_toReal_posMaxFinite
    if (target.find? (·.isAppOf ``Model.posMaxFinite)).isSome then
      attempts := attempts.push (#[], ← `(tactic| first
        | (refine le_trans ?_ ($maximum _); norm_num)
        | (refine lt_of_lt_of_le ?_ ($maximum _); norm_num)), 1000)
    if isFiniteness target && (target.getArg! 1).getAppArgs.back!.isAppOf ``Model.ofRat then
      let finite := mkIdent ``Model.isFinite_ofRat
      attempts := attempts.push (#[], ← `(tactic|
        (refine $finite _ (by decide) ?_; refine le_trans ?_ ($maximum _); norm_num)), 1000)
      arithmetic := some true
    else if (target.find? (·.isAppOf ``Model.posMaxFinite)).isSome then
      arithmetic := some false
  for index in [:attempts.size + 1] do
    if simplifyAt == some index then
      if (← attempt? 1000 (simpWithHypotheses session goal)).isSome then return true
    let some (cleared, attempt, budget) := attempts[index]? | continue
    let solved? ← attempt? budget do
      let remaining ← Lean.Elab.Tactic.run (← goal.tryClearMany cleared) (evalTactic attempt)
      return if remaining.isEmpty then some () else none
    if solved?.isSome then return true
  -- A literal above one, such as `1.5` or `3e38` in binary32, needs the largest finite value.
  match arithmetic with
  | some true =>
      let finite := mkIdent ``Model.isFinite_ofRat
      let ranged? ← attempt? 1000 do
        let remaining ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic|
          refine $finite _ (by decide) ?_)))
        let [range] := remaining | return none
        return if ← closeByArithmetic range then some () else none
      if ranged?.isSome then return true
  | some false => if ← closeByArithmetic goal then return true
  | none => pure ()
  -- Range evidence can describe the same operation through a different certified provider.
  -- This is an equality proof, not an assumption that similarly named backends agree.
  let target ← instantiateMVars (← goal.getType)
  let boolean? ← attempt? 1000 do
    unless target.isAppOfArity ``Eq 3 do return none
    unless ← withReducible (isDefEq target.getAppArgs[0]! q(Bool)) do return none
    return some ()
  if boolean?.isSome then
    let context ← semanticContext session (decodeClassifiers := true)
    -- In mixed analysis a FloatLib classification, such as finiteness, follows only from another
    -- one of a value of the same type, such as another spelling of the value or its decoded model;
    -- a branch guard of the program cannot state it.
    let classified (test : Lean.Expr) : MetaM (Option Lean.Expr) := do
      unless (test.getAppFn.constName?.map (`FloatLib).isPrefixOf).getD false do return none
      let some value := test.getAppArgs.back? | return none
      let value := if value.isAppOf ``ExecFloat.Binary.toModel then value.appArg! else value
      return some (← instantiateMVars (← inferType value))
    let carrier ← if session.mixed then classified target.getAppArgs[1]! else pure none
    -- The comparison depends on the local context only through the recorded results it rewrites
    -- with, so a failure is not repeated in another context with the same ones.
    let results := (← getLCtx).foldl (init := #[]) fun results declaration =>
      if declaration.type.isAppOfArity ``Eq 3 && declaration.type.getAppArgs[0]!.isAppOf ``Except
      then results.push declaration.fvarId else results
    for declaration in ← getLCtx do
      if declaration.isImplementationDetail then continue
      let source ← instantiateMVars declaration.type
      unless source.isAppOfArity ``Eq 3 && source.getAppArgs[2]! == target.getAppArgs[2]! do
        continue
      if session.mixed && otherClassified source target then continue
      if let some type := carrier then
        unless (← classified source.getAppArgs[1]!) == some type do continue
      let key := (source, target, results)
      let closed := !source.hasMVar && !target.hasMVar
      if closed && (← session.inequivalent.get).contains key then continue
      let depths ← depthsCaught
      let solved? ← attempt? 1000 do
        unless ← withReducible (isDefEq source.getAppArgs[0]! q(Bool)) do return none
        if closed then
          -- The two facts agree when their classifications have one normal form; each is
          -- normalized once in this context.
          let left ← session.normalize `classifiers source.getAppArgs[1]! context #[]
          let right ← session.normalize `classifiers target.getAppArgs[1]! context #[]
          unless left.expr == right.expr || (← withReducible (isDefEq left.expr right.expr)) do
            return none
          let same ← mkEqTrans (← left.getProof) (← mkEqSymm (← right.getProof))
          goal.assign (← mkEqTrans (← mkEqSymm same) declaration.toExpr)
          return some ()
        -- Prove equivalence without rewriting the caller's hypothesis or the numerical goal.
        let equality ← mkFreshExprMVar (← mkEq source target)
        let (remaining, _) ← simpTarget equality.mvarId! context
        if let some remaining := remaining then
          remaining.withContext (withReducible remaining.refl)
        goal.assign (← mkAppM ``Eq.mp #[← instantiateMVars equality, declaration.toExpr])
        return some ()
      if solved?.isSome then return true
      if closed && (← depthsCaught) == depths then session.inequivalent.modify (·.insert key)
  if let some loop := extension.loops.find? (target.isAppOf ·.allSteps) then
    for declaration in ← getLCtx do
      unless declaration.type.isAppOf loop.allSteps do continue
      let equality ← mkFreshExprMVar (← mkEq declaration.type target)
      if ← semanticEquality session equality.mvarId! then
        goal.assign (← mkAppM ``Eq.mp #[equality, declaration.toExpr])
        return true
  if target.isAppOfArity ``LE.le 4 then
    let args := target.getAppArgs
    let equality ← mkFreshExprMVar (← mkEq args[2]! args[3]!)
    if ← semanticEquality session equality.mvarId! then
      goal.assign (← mkAppM ``le_of_eq #[equality])
      return true
    let solved? ← attempt? 1000 do
      let (next, _) ← simpTarget goal (← semanticContext session)
      let some next := next | return some ()
      trace[roundoff] "normalized numerical budget: {← next.getType}"
      let remaining ← Lean.Elab.Tactic.run next do
        evalTactic (← `(tactic| apply le_refl))
      return if remaining.isEmpty then some () else none
    if solved?.isSome then return true
  return false

/-- Whether the declaration `declaration` is a hypothesis other than `True`, and the local
variables its type, or its value for a local definition, mentions. Descriptions are cached in
`Session.descriptions`. -/
def Session.describe (session : Session) (declaration : LocalDecl) :
    MetaM (Bool × Array FVarId) := do
  if let some description := (← session.descriptions.get).get? declaration.fvarId then
    return description
  let mentioned := collectFVars {} declaration.type
  let mentioned := match declaration.value? with
    | some value => collectFVars mentioned value
    | none => mentioned
  -- `True`, the placeholder of an invariant a loop does not carry, states no fact.
  let hypothesis := (← isProp declaration.type) && !declaration.type.isConstOf ``True
  let description := (hypothesis, mentioned.fvarIds)
  session.descriptions.modify (·.insert declaration.fvarId description)
  return description

/-- The local variables the scopes entered since the analysis began introduced, in order, each
with its description (`Session.describe`). -/
def Session.scope (session : Session) : MetaM (Array (FVarId × Bool × Array FVarId)) := do
  let mut scope := #[]
  for declaration in ← getLCtx do
    if session.base.contains declaration.fvarId || declaration.isImplementationDetail then continue
    scope := scope.push (declaration.fvarId, ← session.describe declaration)
  return scope

/-- The facts of `scope` about a term whose local variables, with those their types mention, are
`wanted`: the hypotheses that mention one of its variables the scopes introduced, directly or
through such a hypothesis, and those that mention no introduced variable and either no variable
of the goal the analysis began in (`base`) or one of the term's. A search about the term can use
no other hypothesis the scope introduced. -/
def scopeFactsOf (scope : Array (FVarId × Bool × Array FVarId)) (base : Std.HashSet FVarId)
    (wanted : Std.HashSet FVarId) : Array FVarId := Id.run do
  let introduced (uses : Array FVarId) := uses.filter (!base.contains ·)
  let mut wanted := wanted
  let mut facts : Std.HashSet FVarId := {}
  for (id, hypothesis, uses) in scope do
    if hypothesis && (introduced uses).isEmpty &&
        (uses.isEmpty || uses.any wanted.contains) then
      facts := facts.insert id
  let mut changed := true
  while changed do
    changed := false
    for (id, hypothesis, uses) in scope do
      let uses := introduced uses
      if !hypothesis || facts.contains id || !uses.any wanted.contains then continue
      facts := facts.insert id
      wanted := wanted.insertMany uses
      changed := true
  return scope.filterMap fun (id, _) => if facts.contains id then some id else none

/-- The facts that the scopes entered since the analysis began state about `term`
(`scopeFactsOf`), for its local variables and those their types mention. A search about `term`
succeeds or fails alike in every context with the same ones. -/
def Session.scopeFacts (session : Session) (term : Lean.Expr) : MetaM (Array FVarId) := do
  let context ← getLCtx
  let key := (context.getFVarIds, term)
  if !term.hasMVar then
    if let some facts := (← session.factsOf.get).get? key then return facts
  let scope ← session.scope
  if scope.isEmpty then return #[]
  let mut wanted : Std.HashSet FVarId := {}
  let mut work := (collectFVars {} term).fvarIds
  while let some id := work.back? do
    work := work.pop
    if wanted.contains id then continue
    wanted := wanted.insert id
    if let some declaration := context.find? id then
      work := work ++ (← session.describe declaration).2
  let facts := scopeFactsOf scope session.base wanted
  if !term.hasMVar then session.factsOf.modify (·.insert key facts)
  return facts

/-- Range assumptions and executed code may use different container indexing notation.
Normalize their observations by proofs before retrying the same bounded side-condition search.
A closed premise is not searched again where the facts of its scope are those under which it
already failed, or where an earlier proof of it still applies. -/
def discharge (session : Session) (goal : MVarId) : TacticM Bool := do
  let type ← instantiateMVars (← goal.getType)
  let closed := !type.hasMVar
  if closed then
    if let some proof ← (← session.solved.get).proof? type then
      goal.assign proof
      return true
  let recorded ← session.failures.get
  let failed := if closed then recorded.getD type #[] else #[]
  let facts ← if failed.isEmpty then pure none
    else some <$> goal.withContext (session.scopeFacts type)
  if facts.any failed.contains then return false
  let remember : TacticM Unit := do
    if closed then session.solved.set (← (← session.solved.get).remember type (mkMVar goal))
  let depths ← depthsCaught
  if ← dischargeCore session goal then
    remember
    return true
  if ← hasObservation type then
    -- Mixed analysis reads stored inputs by coordinate, already in the laws' normal form.
    let normal ← if session.mixed then hasOnlyInputReads type else pure false
    unless normal do
      let result? ← attempt? 1000 do
        let (context, procedures) ← coordinateSimpContext session
        let target ← instantiateMVars (← goal.getType)
        let next ← if target.hasMVar then pure (← simpTarget goal context procedures).1 else
          applySimpResult? goal target
            (← session.normalize `coordinate target context procedures)
        let some next := next | return some ()
        -- An unchanged condition would repeat the search that just failed.
        if next == goal then return none
        trace[roundoff] "normalized side condition: {← next.getType}"
        return if ← dischargeCore session next then some () else none
      if result?.isSome then
        remember
        return true
  -- A condition that a caught recursion depth may have cut off is not kept as failed.
  if closed && (← depthsCaught) == depths then
    let facts ← match facts with
      | some facts => pure facts
      | none => goal.withContext (session.scopeFacts type)
    session.failures.modify fun failures =>
      failures.insert type ((failures.getD type #[]).push facts)
  return false

/-- The observation of a primitive call that a primitive theorem concludes about: the left side
of an equality, or the decoded side of an order. -/
def primitiveObservation? (conclusion : Lean.Expr) : Option Lean.Expr :=
  if let some (_, observed, _) := conclusion.eq? then some observed
  else if conclusion.isAppOfArity ``LT.lt 4 || conclusion.isAppOfArity ``LE.le 4 then
    #[conclusion.getAppArgs[2]!, conclusion.getAppArgs[3]!].find?
      (·.isAppOf ``ExecFloat.Binary.toReal)
  else none

/-- Whether the head of `term`, read through applications, metadata and `let` bodies as
`Expr.toHeadIndex` reads it, may be the constant `name`. A `let` or a bound variable on the way
counts, since the head behind it is known only after instantiation. -/
partial def mayHaveHead (name : Name) : Lean.Expr → Bool
  | .const head _ => head == name
  | .app function _ => mayHaveHead name function
  | .mdata _ inner => mayHaveHead name inner
  | .letE .. | .bvar _ => true
  | _ => false

/-- `kabstract expression pattern` for a closed constant application `pattern`, with each distinct
subterm of `expression` visited once where `kabstract` walks it as a tree. `kabstract` compares with
`pattern` the subterms without loose bound variables that have its head and arity. When each of them
is `pattern` itself, the outermost of them are abstracted here, which is what `kabstract` does, and
otherwise `kabstract` runs. The result is the expression `kabstract` returns. -/
def abstractOccurrences (expression pattern : Lean.Expr) : MetaM Lean.Expr := do
  let expression ← instantiateMVars expression
  let some name := pattern.getAppFn.constName? | kabstract expression pattern
  if pattern.hasLooseBVars then return ← kabstract expression pattern
  let arity := pattern.getAppNumArgs
  if (expression.find? fun term => !term.hasLooseBVars && term.headNumArgs == arity &&
      mayHaveHead name term && term != pattern).isSome then
    return ← kabstract expression pattern
  let marker := mkFVar (← mkFreshFVarId)
  return (expression.replace fun term => if term == pattern then some marker else none).abstract
    #[marker]

/-- Instantiate the primitive theorem `rule`, whose conclusion observes one primitive call, at
`source`. The source is that primitive or the dictionary method of one of `contract`'s
implementation theorems, and the method must unify with that theorem's, selected instance
included. Return the proof, transported to `source`, and its open premises. -/
def instantiatePrimitive (contract : PrimitiveContract) (rule : Name)
    (source : Lean.Expr) : MetaM (Option (Lean.Expr × Array MVarId)) := do
  let law ← mkConstWithFreshMVarLevels rule
  let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
  let some observed := primitiveObservation? conclusion | return none
  let primitive := observed.getAppArgs.back!
  let mut premises := arguments
  let mut identity? := none
  if primitive.getAppFn == source.getAppFn then
    unless ← isDefEq primitive source do return none
  else
    for name in contract.implementations do
      let saved ← saveState
      let implementation ← mkConstWithFreshMVarLevels name
      let (identityArguments, _, identityType) ←
        forallMetaTelescopeReducing (← ruleType implementation)
      let some (_, method, selected) := identityType.eq? | continue
      unless method.getAppFn == source.getAppFn do continue
      unless ← isDefEq method source <&&> isDefEq selected primitive do
        saved.restore
        continue
      premises := premises ++ identityArguments
      identity? := some (mkAppN implementation identityArguments)
      break
    if identity?.isNone then return none
  synthesizeInstances arguments binders
  let mut pending := #[]
  for premise in premises do
    let premise ← instantiateMVars premise
    unless premise.isMVar do continue
    unless ← isProp (← premise.mvarId!.getType) do return none
    pending := pending.push premise.mvarId!
  let proof ← instantiateMVars (mkAppN law arguments)
  let some identity := identity? | return some (proof, pending)
  -- Restate the conclusion for the method call, which the implementation theorem equates with
  -- the primitive call.
  let primitive ← instantiateMVars primitive
  let motive := Lean.mkLambda `call .default (← inferType primitive)
    (← abstractOccurrences conclusion primitive)
  return some (← mkEqMPR (← mkCongrArg motive (← instantiateMVars identity)) proof, pending)

/-- Prove a primitive call finite by its contract, returning the contract's open premises. -/
def primitiveFinite? (goal : MVarId) : TacticM (Option (Array MVarId)) := do
  let type ← instantiateMVars (← goal.getType)
  let some (_, observed, result) := type.eq? | return none
  unless observed.isAppOf ``ExecFloat.Binary.isFinite && result.isConstOf ``Bool.true do
    return none
  let source := observed.getAppArgs.back!.consumeMData
  for contract in ← primitiveContracts do
    let premises? ← attempt? 2000 do
      let some (proof, premises) ← instantiatePrimitive contract contract.finite source |
        return none
      unless ← isDefEq (← inferType proof) type do return none
      goal.assign proof
      return some premises
    if premises?.isSome then return premises?
  return none

/-- Discharge a premise or keep it open. A premise that a correctly rounded primitive call is
finite becomes that primitive's domain and range conditions. -/
partial def require (session : Session) (goal : MVarId) : TacticM (Array MVarId) := do
  if ← discharge session goal then return #[]
  let some premises ← primitiveFinite? goal | return #[goal]
  premises.foldlM (fun remaining premise => return remaining ++ (← require session premise)) #[]

/-- Compare the generated real reference with existing container code. All normalization steps
are proved equalities, and the floating-point execution and its error budget stay unchanged. -/
def referenceEquality (session : Session) (goal : MVarId) : TacticM Bool := do
  if ← discharge session goal then return true
  let result? ← attempt? 10000 do
    let mut current := some goal
    for context in #[coordinateSimpContext session, foldSimpContext session,
        coordinateSimpContext session] do
      if let some goal := current then
        let (context, procedures) ← context
        let (next, _) ← simpTarget goal context procedures
        current := next
    if let some goal := current then
      return if ← discharge session goal then some () else none
    return some ()
  return result?.isSome

/-- The floating-point value a real observation decodes, for `toReal` of either carrier. -/
def decodedValue? (actual : Lean.Expr) : Option Lean.Expr :=
  if actual.isAppOf ``ExecFloat.Binary.toReal || actual.isAppOf ``Model.toReal then
    actual.getAppArgs.back?
  else none

/-- Transport an estimate of `normalized`, a simplification of `actual`, back to `actual`. If
`carry` holds and the same simplification of the value `source` that `actual` observes gives the
value that `normalized` decodes, that value's finiteness carries back to `source`. -/
def rewriteSimp (estimate : Estimate) (actual source : Lean.Expr) (carry : Bool)
    (normalized : Simp.Result) (context : Simp.Context) (procedures : Simp.SimprocsArray) :
    MetaM Estimate := do
  if carry && estimate.finite?.isSome then
    let (value, _) ← simp source context procedures
    if decodedValue? normalized.expr == some value.expr then
      return ← rewriteValue estimate (mkAppN actual.getAppFn actual.getAppArgs.pop)
        (← value.getProof' source)
  rewriteActual estimate (← normalized.getProof' actual)

/-- A premise that chooses between rules: a real order or equality, or an executable zero. A
mixed analysis proves it or tries the next rule, and it never becomes a caller obligation. -/
def isSelection (type : Lean.Expr) : MetaM Bool := do
  let type := type.consumeMData
  if type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4 then
    return (← whnfR type.getAppArgs[0]!).isConstOf ``Real
  unless type.isAppOfArity ``Eq 3 do return false
  if (← whnfR type.getAppArgs[0]!).isConstOf ``Real then return true
  return type.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.isZero &&
    type.getAppArgs[2]!.isConstOf ``Bool.true

/-- Whether `bound` is the enclosure `(1 + relative) * |reference| + absolute` of a mixed bound. -/
def isEnclosure (bound : Lean.Expr) : Bool :=
  bound.isAppOfArity ``HAdd.hAdd 6 && (bound.getArg! 4).isAppOfArity ``HMul.hMul 6 &&
    ((bound.getArg! 4).getArg! 4).isAppOfArity ``HAdd.hAdd 6 &&
    (((bound.getArg! 4).getArg! 4).getArg! 4).nat? == some 1 &&
    ((bound.getArg! 4).getArg! 5).isAppOf ``abs

/-- A range premise, one of

* a bound of a value by a constant of its format: the overflow threshold, the largest finite value
  or the underflow allowance,
* a condition on the format alone, relating its unit roundoff to sizes, such as
  `(1 + u) ^ (n - 1) < 2`,
* or a bound of the enclosure of a mixed bound by a constant, such as the range of an integer type
  a cast keeps.

Such a range condition is proved or becomes an obligation, and it does not select between rules.
Only a condition on the format alone with no variable, for a given format and length, must be
proved. -/
def isRange (type : Lean.Expr) : Bool :=
  (type.find? fun term => term.isAppOf ``Model.Transcendentals.Certified.overflowThreshold ||
    term.isAppOf ``Model.posMaxFinite || term.isAppOf ``Model.underflowErrorAt).isSome ||
  ((type.find? (·.isAppOf ``Model.unitRoundoffAt)).isSome &&
    (type.find? (·.isAppOf ``ExecFloat.Binary.toReal)).isNone) ||
  ((type.isAppOfArity ``LT.lt 4 || type.isAppOfArity ``LE.le 4) &&
    isEnclosure (type.getArg! 2) && !(type.getArg! 3).hasFVar)

/-- Whether a premise states that a configured value is not an executable zero. -/
def isNonzeroTest (type : Lean.Expr) : Bool :=
  type.isAppOfArity ``Eq 3 && type.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.isZero &&
    type.getAppArgs[2]!.isConstOf ``Bool.false

/-- The value of a square-root domain condition `isZero value = true ∨ signBit value = false`. -/
def domainValue? (type : Lean.Expr) : Option Lean.Expr := do
  let some (zero, sign) := type.consumeMData.app2? ``Or | none
  guard (zero.isAppOfArity ``Eq 3 && sign.isAppOfArity ``Eq 3)
  let test := zero.getAppArgs[1]!
  guard (test.isAppOf ``ExecFloat.Binary.isZero && zero.getAppArgs[2]!.isConstOf ``Bool.true)
  guard (sign.getAppArgs[1]!.isAppOf ``ExecFloat.Binary.signBit &&
    sign.getAppArgs[2]!.isConstOf ``Bool.false)
  let value ← test.getAppArgs.back?
  guard (sign.getAppArgs[1]!.getAppArgs.back? == some value)
  return value

/-- Whether a premise is a sign or order of real values: `≤`, `<` or `≠`. -/
def isRealOrder (type : Lean.Expr) : MetaM Bool := do
  unless type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4 ||
      type.isAppOfArity ``Ne 3 do return false
  return (← whnfR type.getAppArgs[0]!).isConstOf ``Real

/-- Tidy a generated condition, optionally also rewriting with the local equalities. Returns
`none` when tidying proves it. -/
def Session.tidy (session : Session) (goal : MVarId) (hypotheses : Bool := false) :
    MetaM (Option MVarId) := goal.withContext do
  let config := { implicitDefEqProofs := false, failIfUnchanged := false }
  let context ← if hypotheses then session.localContext `budget session.budget config false
    else Simp.mkContext config #[session.budget]
  let target ← instantiateMVars (← goal.getType)
  let next? ← if hypotheses || target.hasMVar then pure (← simpTarget goal context).1 else
    applySimpResult? goal target (← session.tidyTerm target context)
  let some next := next? | return none
  -- An equality whose sides already agree, up to their instances, needs no further search.
  if let some (_, left, right) := (← instantiateMVars (← next.getType)).eq? then
    if left == right || (← withReducibleAndInstances (isDefEq left right)) then
      next.assign (← mkEqRefl left)
      return none
  return some next

/-- How a premise bounds a real parameter `p` of a rule: from above (`p ≤ e`), from below
(`e ≤ p`), or in magnitude from below (`|e| ≤ p`). -/
inductive ParameterSide where
  /-- `p ≤ e`. -/
  | upper
  /-- `e ≤ p`. -/
  | lower
  /-- `|e| ≤ p`. -/
  | magnitude

/-- The side from which `type` bounds the metavariable `parameter`, and the bounded value `e`. -/
def parameterBound? (parameter : MVarId) (type : Lean.Expr) :
    Option (ParameterSide × Lean.Expr) := do
  guard (type.isAppOfArity ``LE.le 4)
  let left := type.getAppArgs[2]!
  let right := type.getAppArgs[3]!
  if left.isMVar && left.mvarId! == parameter then return (.upper, right)
  guard (right.isMVar && right.mvarId! == parameter)
  if left.isAppOfArity ``abs 3 then return (.magnitude, left.appArg!)
  return (.lower, left)

/-- Supply an input premise of either form from an estimate of either form. -/
def presentInput (estimate : Estimate) (premise : Bound) : MetaM Lean.Expr :=
  match estimate.bound, premise with
  | .mixed .., .absolute _ => mkAppM ``MixedError.bound #[estimate.proof]
  | .absolute _, .mixed .. => mkAppM ``MixedError.of_abs_sub_le #[estimate.proof]
  | _, _ => pure estimate.proof

/-- The finiteness of `value`, the result of the exact operation `rule` applied to `arguments`, by
the theorem that `exactFiniteness` pairs with `rule`. Its hypotheses are those of `rule`, taken
from `arguments` by their stated types. -/
def exactFinite? (rule : Name) (arguments : Array Lean.Expr) (value : Lean.Expr) :
    TacticM (Option Lean.Expr) := do
  let some (_, finiteness) := (← exactFiniteness).find? (·.1 == rule) | return none
  attempt? 1000 do
    let law ← mkConstWithFreshMVarLevels finiteness
    let (premises, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
    let expected ← mkEq (← mkAppM ``ExecFloat.Binary.isFinite #[value]) (mkConst ``Bool.true)
    unless ← isDefEq conclusion expected do return none
    synthesizeInstances premises binders
    for premise in premises do
      let premise ← instantiateMVars premise
      unless premise.isMVar do continue
      let type ← instantiateMVars (← premise.mvarId!.getType)
      let some argument ← arguments.findM? fun argument => do
          isDefEq (← instantiateMVars (← inferType argument)) type
        | return none
      premise.mvarId!.assign argument
    -- Stated for `value` as written, so that a consumer compares it without unfolding.
    return some (← mkExpectedTypeHint (← instantiateMVars (mkAppN law premises)) expected)

/-- The finiteness of the configured value `value`, the output of the generated rule `rule` whose
bound was applied to `arguments`, by its finiteness rule at the same arguments. The bound proved
those premises or left them as conditions. -/
def generatedFinite? (session : Session) (rule : Name) (arguments : Array Lean.Expr)
    (value : Lean.Expr) : TacticM (Option Lean.Expr) :=
  attempt? 1000 do
    let observed ← mkAppM ``ExecFloat.Binary.isFinite #[value]
    let candidates ← withCanUnfoldPred (programCanUnfold session.boundaries false)
      (do rulesFor session.finiteness observed (← session.indexKey observed))
    let some finiteness := candidates.find? (·.name == rule) | return none
    let law ← finiteness.instantiate
    let (premises, _, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
    unless premises.size == arguments.size do return none
    for premise in premises, argument in arguments do
      let argument ← instantiateMVars argument
      unless ← isDefEq (← premise.mvarId!.getType) (← inferType argument) do return none
      premise.mvarId!.assign argument
    let expected ← mkEq observed (mkConst ``Bool.true)
    unless ← isDefEq conclusion expected do return none
    return some (← mkExpectedTypeHint (← instantiateMVars (mkAppN law premises)) expected)

/-- Run an analysis step speculatively. On failure, its assignments, messages and changes to the
scope's state (`Analysis`: cached estimates and obligations) are undone, while the session's memo
tables, such as `Session.analysisFailures`, keep what it recorded. -/
def speculate? {α : Type} (action : AnalyzeM α) : AnalyzeM (Option α) := do
  let session ← read
  let state ← get
  let result? ← transaction? do
    let (value, next) ← (action.run session).run state
    return some (value, next)
  let some (value, next) := result? | return none
  set next
  return some value

/-- The metavariables of the reference that a rule premise bounds an input against. The premise is
an error bound, or an error bound for every value of a variable, such as every coordinate of a
container that the rule reduces. -/
def inputReference? (type : Lean.Expr) : MetaM (Option (Array MVarId)) := do
  let wanted (bound : Lean.Expr) : MetaM (Option (Array MVarId)) := do
    let some (_, reference, _) ← boundConclusion? bound | return none
    return some (← getMVars reference)
  let .forallE name domain body _ := type | wanted type
  if ← isProp domain then return none
  withLocalDeclD name domain fun point => wanted (body.instantiate1 point)

/-- Supply an input-error premise about every value of a variable from the analysis of the input at
a fresh one. Its conditions are required of every value, and no cached result mentioning the
variable escapes. -/
def forallInput? (type : Lean.Expr) (deriveInput : Q(ℝ) → AnalyzeM Estimate) :
    AnalyzeM (Option Lean.Expr) := do
  let .forallE name domain body info := type | return none
  if ← isProp domain then return none
  let initial ← get
  let outerContext ← getLCtx
  let outerInstances ← getLocalInstances
  let supplied? ← withLocalDecl name info domain fun point => do
    let some (value, _, premise) ← boundConclusion? (body.instantiate1 point) | return none
    let value : Q(ℝ) ← instantiateMVars value
    if value.hasExprMVar then return none
    let proof ← presentInput (← deriveInput value) premise
    let mut lifted := #[]
    for goal in (← get).pending.extract initial.pending.size (← get).pending.size do
      if ← goal.isAssigned then continue
      let condition ← instantiateMVars (← goal.getType)
      let closed ← withLCtx outerContext outerInstances
        (mkFreshExprMVar (← mkForallFVars #[point] condition))
      goal.assign (mkApp closed point)
      lifted := lifted.push closed.mvarId!
    return some (← mkLambdaFVars #[point] (← instantiateMVars proof), lifted)
  let some (proof, pending) := supplied? | do
    set initial
    return none
  set { initial with pending := initial.pending ++ pending }
  return some proof

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
