/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff.Prove

/-!
# Signs in the `roundoff` analysis

Signs and orders of real values select mixed rules and keep relative errors small. They come from
hypotheses, also a closed bound from a hypothesis with a smaller constant, `positivity`, the sign
rules of sums, differences, products, quotients, inverses and square roots, monotone rounding of
a computed value, the sign contracts of correctly rounded calls, both cases of a branch, and the
invariant of a loop. A search that failed is not repeated at the same or a smaller depth. A sign
rule is matched with instances unfolded only, so the search never compares two computed values by
evaluating their code.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean Meta Elab Tactic Qq
open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

namespace Analyze

/-- The term under absolute values and casts. -/
partial def castCore (term : Lean.Expr) : Lean.Expr :=
  let term := term.consumeMData
  if [``abs, ``Int.cast, ``Nat.cast, ``Rat.cast].any term.isAppOf then castCore term.appArg!
  else term

/-- A bound `value ≤ limit` or `value < limit` on reals by a closed `limit`, from a hypothesis
that bounds the same term, also as an integer or a natural number before its cast, by a closed
constant: the hypothesis gives the bound by that constant, and the two constants are compared by
evaluation. -/
def boundByHypothesis (goal : MVarId) : AnalyzeM Bool := goal.withContext do
  let type ← instantiateMVars (← goal.getType)
  let strict := type.isAppOfArity ``LT.lt 4
  unless strict || type.isAppOfArity ``LE.le 4 do return false
  let value := type.getArg! 2
  let limit := type.getArg! 3
  if limit.hasFVar || limit.hasMVar || value.hasMVar || !value.hasFVar then return false
  unless (← whnfR (type.getArg! 0)).isConstOf ``Real do return false
  let core := castCore value
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail then continue
    let fact ← instantiateMVars declaration.type
    let factStrict := fact.isAppOfArity ``LT.lt 4
    unless factStrict || fact.isAppOfArity ``LE.le 4 do continue
    let constant := fact.getArg! 3
    if constant.hasFVar || constant.hasMVar || castCore (fact.getArg! 2) != core then continue
    let carrier ← whnfR (fact.getArg! 0)
    let middle? : Option Lean.Expr ← if carrier.isConstOf ``Real then pure (some constant)
      else if carrier.isConstOf ``Int then
        pure (some (← mkAppOptM ``Int.cast #[mkConst ``Real, none, constant]))
      else if carrier.isConstOf ``Nat then
        pure (some (← mkAppOptM ``Nat.cast #[mkConst ``Real, none, constant]))
      else pure none
    let some middle := middle? | continue
    let proved? ← attempt? 2000 do
      let first ← mkFreshExprMVar
        (← mkAppM (if factStrict then ``LT.lt else ``LE.le) #[value, middle])
      let hypothesis ← Lean.Elab.Term.exprToSyntax declaration.toExpr
      unless (← Lean.Elab.Tactic.run first.mvarId!
          (evalTactic (← `(tactic| exact_mod_cast $hypothesis)))).isEmpty do return none
      let second ← mkFreshExprMVar
        (← mkAppM (if strict && !factStrict then ``LT.lt else ``LE.le) #[middle, limit])
      unless (← Lean.Elab.Tactic.run second.mvarId! (evalTactic (← `(tactic|
          first | (norm_num; done) | (norm_cast; decide))))).isEmpty do return none
      let law := if strict then (if factStrict then ``lt_of_lt_of_le else ``lt_of_le_of_lt)
        else ``le_trans
      let first ← if !strict && factStrict then mkAppM ``le_of_lt #[first] else pure first
      goal.assign (← mkAppM law #[first, second])
      return some ()
    if proved?.isSome then return true
  return false

/-- Signs and orders of real expressions, settled once per local context: a proof that leaves
no obligation is reused, and a search that failed is not repeated at the same or a smaller
depth, also after the attempt that made it is rolled back. -/
def proveSign (r : Recursor) (goal : MVarId) (fuel depth : Nat) :
    AnalyzeM Bool := goal.withContext do
  if depth == 0 then return false
  let type ← instantiateMVars (← goal.getType)
  if type.hasExprMVar then return ← r.proveSignCore goal fuel depth
  let key := ((← getLCtx).getFVarIds, type)
  let settled := (← read).settledSigns
  if let some proof ← (← settled.get).proof? type then
    goal.assign proof
    return true
  match (← get).signs.get? key with
  | some (some proof, _) =>
      goal.assign proof
      return true
  | some (none, failed) => if depth ≤ failed then return false
  | none => pure ()
  if let some failed := (← (← read).signFailures.get).get? key then
    if depth ≤ failed then return false
  let before := (← get).pending.size
  let depths ← depthsCaught
  let proved ← r.proveSignCore goal fuel depth
  -- A sign that a caught recursion depth may have cut off is not kept as unproved.
  let limited := (← depthsCaught) != depths
  unless proved || limited do
    (← read).signFailures.modify fun failures =>
      failures.insert key (max depth (failures.getD key 0))
  let result ← if proved then
      let proof ← instantiateMVars (mkMVar goal)
      pure (if proof.hasExprMVar || (← get).pending.size != before then none
        else some (some proof, depth))
    else pure (if limited then none else some (none, depth))
  if let some entry := result then
    modify fun state => { state with signs := state.signs.insert key entry }
    if let (some proof, _) := entry then settled.set (← (← settled.get).remember type proof)
  return proved

/-- Signs and orders of real expressions: hypotheses, `positivity`, the sign rules of sums,
differences and products, and monotone rounding for a computed value. -/
def proveSignCore (r : Recursor) (goal : MVarId) (fuel depth : Nat) :
    AnalyzeM Bool := goal.withContext do
  if ← withReducible goal.assumptionCore then return true
  -- A strict sign among the hypotheses gives the weak one.
  if (← instantiateMVars (← goal.getType)).isAppOfArity ``LE.le 4 then
    let strict? ← attempt? 200 do
      let [next] ← goal.apply (← mkConstWithFreshMVarLevels ``le_of_lt) | return none
      return if ← withReducible next.assumptionCore then some () else none
    if strict?.isSome then return true
  let reads := (← extension).reads
  -- Facts about every entry of a container, such as `∀ i, 0 ≤ toReal (x i)`. Both sides of the
  -- relation must have the same heads; unifying different ones would evaluate scalar code.
  let type : Q(Prop) ← instantiateMVars (← goal.getType)
  for declaration in ← getLCtx do
    if declaration.isImplementationDetail || !declaration.type.isForall then continue
    unless sameRelation reads declaration.type.getForallBody type do continue
    let applied? ← attempt? 2000 do
      let goals ← goal.apply declaration.toExpr
      return if goals.isEmpty then some () else none
    if applied?.isSome then return true
  if ← boundByHypothesis goal then return true
  let split (rules : Array Name) : AnalyzeM Bool := do
    for rule in rules do
      let proved? ← speculate? do
        -- Instances unfolded only: a conclusion that repeats a factor, as `mul_self_nonneg`'s
        -- does, would otherwise compare two computed values by their code.
        let goals ← withTransparency .instances
          (goal.apply (← mkConstWithFreshMVarLevels rule))
        for next in goals do
          let (introduced, next) ← next.intros
          let before := (← get).pending.size
          unless ← r.proveSign next fuel (depth - 1) do
            throwError "roundoff: unproved sign"
          -- An obligation under the introduced hypotheses cannot become a premise.
          unless introduced.isEmpty || (← get).pending.size == before do
            throwError "roundoff: a case of the sign leaves obligations"
        return ()
      if proved?.isSome then return true
    return false
  let positive : AnalyzeM Bool := do
    let closed := !type.hasMVar
    let facts ← if closed then (← read).scopeFacts type else pure #[]
    if closed && ((← (← read).positivityFailures.get).getD type #[]).contains facts then
      return false
    let depths ← depthsCaught
    let proved? ← attempt? 2000 do
      let goals ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic| positivity)))
      return if goals.isEmpty then some () else none
    if closed && proved?.isNone && (← depthsCaught) == depths then
      (← read).positivityFailures.modify fun failures =>
        failures.insert type ((failures.getD type #[]).push facts)
    return proved?.isSome
  let rules : Array Name ← match type with
    | ~q(0 ≤ ($_a : ℝ) * $_b) =>
        pure #[``mul_self_nonneg, ``mul_nonneg, ``mul_nonneg_of_nonpos_of_nonpos]
    | ~q(($_a : ℝ) * $_b ≤ 0) =>
        pure #[``mul_nonpos_of_nonneg_of_nonpos, ``mul_nonpos_of_nonpos_of_nonneg]
    | ~q(0 ≤ ($_a : ℝ) + $_b) => pure #[``add_nonneg]
    | ~q(($_a : ℝ) + $_b ≤ 0) => pure #[``add_nonpos]
    | ~q(($_a : ℝ) - $_b ≤ 0) => pure #[``sub_nonpos_of_le]
    | ~q(0 ≤ ($_a : ℝ) - $_b) => pure #[``sub_nonneg_of_le]
    | ~q(-($_a : ℝ) ≤ 0) => pure #[``neg_nonpos_of_nonneg]
    | ~q(0 ≤ -($_a : ℝ)) => pure #[``neg_nonneg_of_nonpos]
    | ~q(0 < ($_a : ℝ) + $_b) => pure #[``add_pos_of_pos_of_nonneg, ``add_pos_of_nonneg_of_pos]
    | ~q(($_a : ℝ) + $_b < 0) => pure #[``add_neg_of_neg_of_nonpos, ``add_neg_of_nonpos_of_neg]
    | ~q(0 ≤ ($_a : ℝ) / $_b) => pure #[``div_nonneg, ``div_nonneg_of_nonpos]
    | ~q(($_a : ℝ) / $_b ≤ 0) =>
        pure #[``div_nonpos_of_nonpos_of_nonneg, ``div_nonpos_of_nonneg_of_nonpos]
    | ~q(0 < ($_a : ℝ) / $_b) => pure #[``div_pos, ``div_pos_of_neg_of_neg]
    | ~q(($_a : ℝ) / $_b < 0) => pure #[``div_neg_of_neg_of_pos, ``div_neg_of_pos_of_neg]
    | ~q(0 < ($_a : ℝ)⁻¹) => pure #[``inv_pos_of_pos]
    | ~q(0 ≤ ($_a : ℝ)⁻¹) => pure #[``inv_nonneg_of_nonneg]
    | ~q(0 < √($_a : ℝ)) => pure #[``Real.sqrt_pos_of_pos]
    | ~q(0 < ($_a : ℝ) * $_b) => pure #[``mul_pos]
    | ~q(($_a : ℝ) * $_b < 0) => pure #[``mul_neg_of_pos_of_neg, ``mul_neg_of_neg_of_pos]
    | ~q(0 < -($_a : ℝ)) => pure #[``neg_pos_of_neg]
    | ~q(-($_a : ℝ) < 0) => pure #[``neg_neg_of_pos]
    | ~q(($_a : ℝ) - $_b < 0) => pure #[``sub_neg_of_lt, ``sub_neg_of_nonpos_of_pos]
    | ~q(0 < ($_a : ℝ) - $_b) => pure #[``sub_pos_of_lt]
    | ~q(($_a : ℝ) ≠ 0) => pure #[``ne_of_gt, ``ne_of_lt]
    | ~q(0 < |($_a : ℝ)|) => pure #[``abs_pos_of_pos, ``abs_pos_of_neg]
    | ~q(0 ≤ Real.log $_a) => pure #[``Real.log_nonneg]
    | ~q(0 < Real.log $_a) => pure #[``Real.log_pos]
    | ~q(1 ≤ 1 + ($_a : ℝ)) => pure #[``le_add_of_nonneg_right]
    | ~q(1 < 1 + ($_a : ℝ)) => pure #[``lt_add_of_pos_right]
    | ~q(-1 < ($_a : ℝ)) => pure #[``neg_one_lt_of_nonneg]
    | _ => pure #[]
  if ← split rules then return true
  -- A sum over the coordinates of a vector is positive when each of its terms is.
  if type.isAppOfArity ``LT.lt 4 && type.getAppArgs[2]!.nat? == some 0 then
    if let some loop := (← extension).loops.find? (type.getAppArgs[3]!.isAppOf ·.fold) then
      if let some law := loop.positiveSum then
        if ← split #[law] then return true
  -- A branch has a sign that both of its cases have.
  if type.isAppOfArity ``LE.le 4 then
    let zeroLeft := type.getAppArgs[2]!.nat? == some 0
    let side := if zeroLeft then type.getAppArgs[3]! else type.getAppArgs[2]!
    let rules := if side.isAppOfArity ``ite 5 then
        if zeroLeft then #[``ite_nonneg] else #[``ite_nonpos]
      else if side.isAppOfArity ``dite 5 then
        if zeroLeft then #[``dite_nonneg] else #[``dite_nonpos]
      else #[]
    if ← split rules then return true
    if let some proved ← r.branchSign goal side fuel depth then return proved
    if let some proved ← r.foldSign goal side fuel depth then return proved
  let signed? : Option Q(ℝ) ← match type with
    | ~q(0 < ($value : ℝ)) => pure (some value)
    | ~q(($value : ℝ) < 0) => pure (some value)
    | ~q(0 ≤ ($value : ℝ)) => pure (some value)
    | ~q(($value : ℝ) ≤ 0) => pure (some value)
    | _ => pure none
  if let some value := signed? then
    if ← r.primitiveSign goal value fuel depth then return true
    if ← r.relativeSign goal value fuel depth then return true
    -- A decoded literal has the value its decoding theorem gives.
    let literal := value.getAppArgs.back?.any fun decoded =>
      decoded.isAppOf ``OfNat.ofNat || decoded.isAppOf ``Zero.zero
    if value.isAppOf ``ExecFloat.Binary.toReal && literal then
      if ← discharge (← read) goal then return true
  -- Facts of the format, such as `unitRoundoffAt format < 1`.
  for helper in (← read).helpers do
    unless ← helper.compatible type do continue
    let solved? ← attempt? 1000 do
      let remaining ← Lean.Elab.Tactic.run goal (evalTactic helper.tactic)
      return if remaining.isEmpty then some () else none
    if solved?.isSome then return true
  if type.isAppOfArity ``LE.le 4 || type.isAppOfArity ``LT.lt 4 then
    for rule in (← read).orders, shape in (← read).orderShapes do
      unless sameRelation reads shape type do continue
      let proved? ← speculate? do
        let fact ← rule.instantiate
        let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType fact)
        unless sameRelation reads conclusion type do throwError "roundoff: {rule.name} does not
            apply"
        -- A fact that applies matches at reducible transparency or after a few unfoldings; a
        -- comparison with a different value would expand its computation.
        let reducible := (← attempt? 2000 do
          return if ← withReducibleAndInstances (isDefEq conclusion type) then some ()
            else none).isSome
        let matched := reducible || (← attempt? 200 do
          return if ← isDefEq conclusion type then some () else none).isSome
        unless matched do throwError "roundoff: {rule.name} does not apply"
        synthesizeInstances arguments binders
        for argument in arguments do
          let argument ← instantiateMVars argument
          unless argument.isMVar do continue
          let premise ← instantiateMVars (← inferType argument)
          unless ← isProp premise do throwError "roundoff: unresolved data in {rule.name}"
          let proved ← if isFiniteness premise then r.proveFinite argument.mvarId! fuel
            else if premise.isAppOfArity ``LE.le 4 || premise.isAppOfArity ``LT.lt 4 then
              r.proveSign argument.mvarId! fuel (depth - 1)
            else discharge (← read) argument.mvarId!
          unless proved do throwError "roundoff: unproved premise of {rule.name}"
        goal.assign (mkAppN fact arguments)
      if proved?.isSome then return true
  -- The computation behind a container read or a definition, exposed one step.
  if let some value := signed? then
    if let some (exposed, equality?) ← exposeObservation (← read) value then
      let motive := Lean.mkLambda `value .default q(ℝ) (← kabstract type value)
      let next ← mkFreshExprMVar (motive.bindingBody!.instantiate1 exposed)
      if ← r.proveSign next.mvarId! fuel (depth - 1) then
        match equality? with
        | some equality => goal.assign (← mkEqMPR (← mkCongrArg motive equality) next)
        | none => goal.assign next
        return true
  -- Monotone rounding may leave the finiteness of the rounded result as an obligation.
  let computed? : Option (Q(ℝ) × Bool) ← match type with
    | ~q(0 ≤ ($value : ℝ)) => pure (some (value, true))
    | ~q(($value : ℝ) ≤ 0) => pure (some (value, false))
    | _ => pure none
  if let some (value, nonneg) := computed? then
    if ← r.roundingSign goal value nonneg fuel depth then return true
  positive

/-- The sign of a decoded branch is the sign of its selected case when a hypothesis, simplification
or a refutation decides its guard, and otherwise the sign of the branch of decoded values. -/
def branchSign (r : Recursor) (goal : MVarId) (side : Lean.Expr) (fuel depth : Nat) : AnalyzeM
    (Option Bool) := do
  unless side.isAppOf ``ExecFloat.Binary.toReal do return none
  let branch := side.getAppArgs.back!
  let dependent := branch.isAppOfArity ``dite 5
  unless dependent || branch.isAppOfArity ``ite 5 do return none
  let arguments := branch.getAppArgs
  let decode := mkAppN side.getAppFn side.getAppArgs.pop
  -- A guard decided by a hypothesis, by simplification or by a refutation selects its case.
  let condition := arguments[1]!
  let evidence? ← match ← guardEvidence? (← read) condition with
    | some evidence => pure (some evidence)
    | none => pure ((← refutedGuard? condition).map (false, ·))
  if let some (positive, evidence) := evidence? then
    let rule := if dependent then (if positive then ``dite_eq_left else ``dite_eq_right)
      else if positive then ``ite_eq_left else ``ite_eq_right
    let equality ← mkAppOptM rule #[some arguments[1]!, some arguments[2]!, some evidence,
      some arguments[0]!, some arguments[3]!, some arguments[4]!]
    let some (_, _, selected) := (← inferType equality).eq? | return none
    let decoded ← mkCongrArg decode equality
    let type ← instantiateMVars (← goal.getType)
    let next ← mkFreshExprMVar ((← kabstract type side).instantiate1 (mkApp decode selected))
    unless ← r.proveSign next.mvarId! fuel (depth - 1) do return some false
    let motive := Lean.mkLambda `value .default q(ℝ) (← kabstract type side)
    goal.assign (← mkEqMPR (← mkCongrArg motive decoded) next)
    return some true
  let pushed ← mkAppOptM (if dependent then ``apply_dite else ``apply_ite)
    #[none, none, decode, arguments[1]!, arguments[2]!, arguments[3]!, arguments[4]!]
  let some (_, _, rewritten) := (← inferType pushed).eq? | return none
  let type ← instantiateMVars (← goal.getType)
  let next ← mkFreshExprMVar ((← kabstract type side).instantiate1 rewritten)
  unless ← r.proveSign next.mvarId! fuel (depth - 1) do return some false
  let motive := Lean.mkLambda `value .default q(ℝ) (← kabstract type side)
  goal.assign (← mkEqMPR (← mkCongrArg motive pushed) next)
  return some true

/-- A sign of the accumulator that every step of a fold keeps holds of its result. A reduction is
first exposed as its fold, a loop written another way, such as over `Fin n`, as its registered
loop, and a fold over a computed container as the fold over its coordinates, so that each step
reads the entry its producer computes. -/
def foldSign (r : Recursor) (goal : MVarId) (side : Lean.Expr) (fuel depth : Nat) : AnalyzeM
    (Option Bool) := do
  let fold := if side.isAppOf ``ExecFloat.Binary.toReal then side.getAppArgs.back! else side
  -- The sign of `side` written by the fold laws, or else as a registered loop by the conversions,
  -- if they change it.
  let exposed : AnalyzeM (Option Bool) := do
    let (context, procedures) ← foldSimpContext (← read)
    let (normalized, _) ← simp side context procedures
    let normalized ← if normalized.expr != side then pure normalized
      else pure (← simp side (← conversionSimpContext)).1
    if normalized.expr == side then return none
    let type ← instantiateMVars (← goal.getType)
    let motive := Lean.mkLambda `value .default (← inferType side) (← kabstract type side)
    let next ← mkFreshExprMVar (motive.bindingBody!.instantiate1 normalized.expr)
    let some proved ← r.foldSign next.mvarId! normalized.expr fuel depth | return none
    if proved then
      goal.assign (← mkEqMPR (← mkCongrArg motive (← normalized.getProof' side)) next)
    return some proved
  let some loop ← loopOf? fold | do
    unless ← isReduction fold do return none
    exposed
  if let some (coordinates, _) := loop.coordinates then
    let input := fold.getAppArgs[loop.input]!
    unless input.isAppOf coordinates || (← isInputValue input) do
      if let some true ← exposed then return some true
  let arguments := fold.getAppArgs
  let type ← instantiateMVars (← goal.getType)
  let motive ← withLocalDeclD `accumulator (← inferType arguments[loop.initial]!)
      fun accumulator => do
    let observed := if side.isAppOf ``ExecFloat.Binary.toReal then
        mkApp (mkAppN side.getAppFn side.getAppArgs.pop) accumulator
      else accumulator
    mkLambdaFVars #[accumulator] ((← kabstract type side).instantiate1 observed)
  let proved? ← speculate? do
    let law ← mkConstWithFreshMVarLevels loop.induction
    let (arguments, _, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
    let some predicate ← arguments.findM? fun argument => do
        return (← inferType argument).getForallBody.isProp
      | throwError "roundoff: foldl_induction has no motive"
    predicate.mvarId!.assign motive
    unless ← isDefEq conclusion type do throwError "roundoff: the fold does not match"
    let before := (← get).pending.size
    for argument in arguments do
      let argument ← instantiateMVars argument
      unless argument.isMVar do continue
      let (_, next) ← argument.mvarId!.intros
      unless ← r.proveSign next fuel (depth - 1) do throwError "roundoff: unproved fold sign"
    -- The step is proved for an arbitrary accumulator, so it may leave no obligation.
    unless (← get).pending.size == before do
      throwError "roundoff: a step of the fold leaves obligations"
    goal.assign (mkAppN law arguments)
  return some proved?.isSome

/-- The strict sign of a computed sum, difference or integer conversion, or of a registered
rounding, is that of the exact value it rounds: its rounding has relative error below one and no
absolute error. The finiteness of the result is proved or kept open. -/
def relativeSign (r : Recursor) (goal : MVarId) (value : Q(ℝ)) (fuel depth : Nat) :
    AnalyzeM Bool := do
  let type : Q(Prop) ← instantiateMVars (← goal.getType)
  let positive ← match type with
    | ~q(0 < ($_x : ℝ)) => pure true
    | ~q(($_x : ℝ) < 0) => pure false
    | _ => return false
  unless value.isAppOf ``ExecFloat.Binary.toReal do return false
  let source := value.getAppArgs.back!
  let roundings := #[(``HAdd.hAdd, ``ExecFloat.Binary.add_rounding),
    (``HSub.hSub, ``ExecFloat.Binary.sub_rounding)] ++ (← extension).roundings
  -- A conversion is matched by the cast it converts, so that the integer rule never unifies a
  -- natural number by unfolding the casts.
  let cast := source.getAppArgs.findSome? fun argument =>
    [``Int.cast, ``Nat.cast].find? argument.isAppOf
  let rounding := if source.isAppOf ``ExecFloat.Binary.ofRat then
      if cast == some ``Int.cast then ``ExecFloat.Binary.ofRat_intCast_rounding
      else if cast == some ``Nat.cast then ``ExecFloat.Binary.ofRat_natCast_rounding
      else .anonymous
    else ((roundings.find? (source.isAppOf ·.1)).map (·.2)).getD .anonymous
  if rounding.isAnonymous then return false
  let proved? ← speculate? do
    let law ← mkConstWithFreshMVarLevels rounding
    let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType law)
    let some (actual, reference, _, _) ← mixedConclusion? conclusion |
      throwError "roundoff: {rounding} is not a mixed bound"
    unless ← isDefEq actual value do throwError "roundoff: {rounding} does not apply"
    synthesizeInstances arguments binders
    for argument in arguments do
      let argument ← instantiateMVars argument
      unless argument.isMVar do continue
      unless ← isProp (← argument.mvarId!.getType) do
        throwError "roundoff: unresolved data in {rounding}"
      unless ← r.prove argument.mvarId! fuel do
        let remaining ← require (← read) argument.mvarId!
        modify fun state => { state with pending := state.pending ++ remaining }
    let reference : Q(ℝ) ← instantiateMVars reference
    let sign ← mkFreshExprMVar (if positive then q(0 < $reference) else q($reference < 0))
    unless ← r.proveSign sign.mvarId! fuel (depth - 1) do
      throwError "roundoff: unproved sign of the exact operation"
    let proof := mkAppN law arguments
    let some (_, _, relative, _) ← mixedConclusion? (← inferType proof) |
      throwError "roundoff: {rounding} is not a mixed bound"
    let relative : Q(ℝ) := relative
    let small ← mkFreshExprMVar q($relative < 1)
    unless ← r.proveSign small.mvarId! fuel (depth - 1) do
      throwError "roundoff: the relative error need not be below one"
    goal.assign (← mkAppM
      (if positive then ``MixedError.pos_of_pos else ``MixedError.lt_zero_of_lt_zero)
      #[proof, small, sign])
  return proved?.isSome

/-- The sign of a correctly rounded primitive call, by its contract's sign theorems.
Their finiteness and range premises are proved or kept open, and the others select the theorem. -/
def primitiveSign (r : Recursor) (goal : MVarId) (value : Q(ℝ)) (fuel depth : Nat) :
    AnalyzeM Bool := do
  let session ← read
  unless value.isAppOf ``ExecFloat.Binary.toReal do return false
  let source := value.getAppArgs.back!
  let type ← instantiateMVars (← goal.getType)
  for contract in ← primitiveContracts do
    for name in contract.signs do
      let proved? ← speculate? do
        let some (proof, premises) ← instantiatePrimitive contract name source |
          throwError "roundoff: {name} does not apply"
        unless ← isDefEq (← inferType proof) type do throwError "roundoff: {name} does not apply"
        for premise in premises do
          let premiseType ← instantiateMVars (← premise.getType)
          if isFiniteness premiseType || isRange premiseType then
            unless ← r.prove premise fuel do
              modify fun state => { state with pending := state.pending ++ #[premise] }
          else unless ← r.proveSign premise fuel (depth - 1) <||> discharge session premise do
            throwError "roundoff: unproved premise of {name}"
        goal.assign proof
      if proved?.isSome then return true
  return false

/-- The sign of a computed value from the sign of the exact operation it rounds, including the
real function a correctly rounded primitive rounds. A NaN or an infinity has real value zero, so
a rounding's premise that its result is finite is assumed rather than proved
(`ExecFloat.Binary.toReal_nonneg_of_isFinite_imp`). -/
def roundingSign (r : Recursor) (goal : MVarId) (value : Q(ℝ)) (nonneg : Bool) (fuel depth : Nat) :
    AnalyzeM Bool := do
  let session ← read
  unless value.isAppOf ``ExecFloat.Binary.toReal do return false
  let source := value.getAppArgs.back!
  for contract in ← primitiveContracts do
    let proved? ← speculate? do
      let some (rounding, premises) ← instantiatePrimitive contract contract.rounding source |
        throwError "roundoff: {contract.rounding} does not apply"
      for premise in premises do
        unless ← r.prove premise fuel do
          modify fun state => { state with pending := state.pending ++ #[premise] }
      let some (_, _, rounded) := (← inferType rounding).eq? |
        throwError "roundoff: {contract.rounding} is not a rounding identity"
      let exact : Q(ℝ) := (← instantiateMVars rounded).getAppArgs[1]!
      let sign ← mkFreshExprMVar (if nonneg then q(0 ≤ $exact) else q($exact ≤ 0))
      unless ← r.proveSign sign.mvarId! fuel (depth - 1) do
        throwError "roundoff: unproved sign of the exact function"
      goal.assign (← roundedSign rounding sign nonneg)
    if proved?.isSome then return true
  for name in roundings do
    let proved? ← speculate? do
      let rounding ← mkConstWithFreshMVarLevels name
      let (arguments, binders, conclusion) ← forallMetaTelescopeReducing (← ruleType rounding)
      let some (_, observed, rounded) := conclusion.eq? |
        throwError "roundoff: {name} is not a rounding identity"
      -- Compare the operations first; unifying different ones would evaluate their code.
      unless (observed.getAppArgs.back?.bind (·.getAppFn.constName?)) ==
          (value.getAppArgs.back?.bind (·.getAppFn.constName?)) do
        throwError "roundoff: {name} rounds a different operation"
      unless ← isDefEq observed value do throwError "roundoff: {name} does not apply"
      synthesizeInstances arguments binders
      let mut assumed? := none
      for argument in arguments do
        let argument ← instantiateMVars argument
        unless argument.isMVar do continue
        let premise ← instantiateMVars (← inferType argument)
        unless ← isProp premise do throwError "roundoff: unresolved data in {name}"
        if isFiniteness premise then
          -- A rule's instances may be spelled differently from the program's.
          let result ← match premise.getAppArgs[1]!.getAppArgs.back? with
            | some subject => pure (subject == source) <||> withReducible (isDefEq subject source)
            | none => pure false
          if assumed?.isNone && result then
            assumed? := some argument.mvarId!
            continue
          unless ← r.proveFinite argument.mvarId! fuel do
            modify fun state => { state with pending := state.pending.push argument.mvarId! }
        else if (domainValue? premise).isSome then
          unless ← r.prove argument.mvarId! fuel do
            modify fun state => { state with pending := state.pending.push argument.mvarId! }
        else unless ← discharge session argument.mvarId! do
          modify fun state => { state with pending := state.pending.push argument.mvarId! }
      let exact : Q(ℝ) := (← instantiateMVars rounded).getAppArgs[1]!
      let sign ← mkFreshExprMVar (if nonneg then q(0 ≤ $exact) else q($exact ≤ 0))
      unless ← r.proveSign sign.mvarId! fuel (depth - 1) do
        throwError "roundoff: unproved sign of the exact operation"
      let proof ← roundedSign (mkAppN rounding arguments) sign nonneg
      match assumed? with
      | none => goal.assign proof
      | some finite =>
          -- The proof for a finite result, abstracted over that finiteness.
          let type ← instantiateMVars (← finite.getType)
          let body ← kabstract (← instantiateMVars proof) (mkMVar finite)
          let law := if nonneg then ``ExecFloat.Binary.toReal_nonneg_of_isFinite_imp
            else ``ExecFloat.Binary.toReal_nonpos_of_isFinite_imp
          goal.assign (← mkAppM law #[.lam `finite type body .default])
    if proved?.isSome then return true
  return false

end Analyze

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
