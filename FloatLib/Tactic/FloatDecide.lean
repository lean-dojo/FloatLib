/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.Closure
public meta import Lean.Meta.KAbstract
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.Util.ForEachExpr
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop

/-!
# `float_decide`

`float_decide` proves a closed statement about floating-point values by evaluation in Lean's
kernel. It rewrites the public operations in the goal to their kernel operations with the rules
tagged `@[kernel_optimize]`, then runs `decide +kernel`. When several tagged rules match one
term, the rule with the lowest declared cost is used, so a cheaper kernel implementation tagged
in any imported module is picked up with no change here. Registration checks that the tagged
rules use only Lean's three standard axioms. A proof using an additional lemma supplied by the
caller inherits that lemma's assumptions.

`float_decide [f, g, h]` also unfolds the definitions `f` and `g` and rewrites with the
equation `h` before deciding, which is how the operations inside your own definitions become
visible to the rewrite.

A loop of a thousand steps has its length as a literal in the goal. The tactic proves the
rewrite for loops of every length (it replaces the literal lengths of `List.range` loops and of
`Nat.rec` recursions by variables, and leaves other occurrences of the same literal, such as the
index of a type, in place) and then applies it to the literal lengths, so that Lean's
kernel checks the rewrite proof without running the loop: with the literal in place the kernel
compares two forms of the loop by unfolding both, step by step.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Tactic Meta

/--
`float_decide` closes a goal that Lean's kernel can decide, after rewriting floating-point
operations to their kernel operations (the rules tagged `@[kernel_optimize]`, cheapest first).

* `float_decide [f, h]` also unfolds the definition `f` and rewrites with the equation `h`.
* A definition that names one stored value, such as `def tenth : Binary32 := 0.1`, is unfolded
  without being listed.
* A goal `∀ a b : Fin n, P a b` with a literal `n`, in which `a` and `b` occur only as their
  values, is checked by one loop over the `n * n` pairs (`forall_fin_pairs`).
* An operation that has no kernel operation stays as it is, and the kernel then evaluates its
  reference definition, which is correct and slow.
* The tactic fails, says why, and shows the statement when the kernel evaluates it to false or
  cannot evaluate it, when it has no `Decidable` instance, and when it is not closed (it
  mentions local variables or hypotheses).
-/
syntax (name := floatDecide) "float_decide" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- Whether `e` is a natural-number literal: `OfNat.ofNat n` at type `Nat` or a raw literal. -/
def isNatLiteral (e : Expr) : Bool :=
  e.isRawNatLit ||
    (e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appFn!.appArg!.isConstOf ``Nat &&
      e.appFn!.appArg!.isRawNatLit)

/--
The literal loop lengths in `e`: the arguments of `List.range`, the lengths of `List.range'` and
the major premises of `Nat.rec` that are natural-number literals.
-/
def loopLengths (e : Expr) : MetaM (Array Expr) := do
  let found ← IO.mkRef (#[] : Array Expr)
  e.forEach' fun sub => do
    let candidate? :=
      if sub.isAppOfArity ``List.range 1 || sub.isAppOfArity ``Nat.rec 4 then some sub.appArg!
      else if sub.isAppOfArity ``List.range' 3 then some (sub.getArg! 1)
      else none
    if let some length := candidate? then
      if isNatLiteral length then
        found.modify fun lengths => if lengths.contains length then lengths else lengths.push length
    return true
  found.get

/--
`e` with `var` in place of the literal `length` where it is a loop length: the argument of
`List.range`, the length of `List.range'` and the major premise of `Nat.rec`. Other occurrences
of the same literal stay, so a statement whose loop length is also the index of a type, such as
a loop of 32 steps over data indexed by `Fin 32`, keeps its types.
-/
partial def abstractLength (length var : Expr) (e : Expr) : Expr :=
  e.replace fun sub =>
    if (sub.isAppOfArity ``List.range 1 || sub.isAppOfArity ``Nat.rec 4) &&
        sub.appArg! == length then
      some (mkApp (abstractLength length var sub.appFn!) var)
    else if sub.isAppOfArity ``List.range' 3 && sub.getArg! 1 == length then
      let arguments := sub.getAppArgs
      some (mkAppN sub.getAppFn
        #[abstractLength length var arguments[0]!, var, abstractLength length var arguments[2]!])
    else none

/-- Whether `type` is the type of the stored values of a format: an `ExecFloat F`. -/
def isStoredValueType (type : Expr) : MetaM Bool := do
  let type ← whnfR type
  return type.isAppOfArity ``Subtype 2 &&
    ((type.getArg! 1).find? fun sub => sub.isConstOf `FloatLib.Floats.ExecFloatTag).isSome

/--
The definitions in `e` that name one stored value: constants without parameters whose type is an
`ExecFloat F`, such as `def tenth : Binary32 := 0.1`.
-/
def storedValueConstants (e : Expr) : MetaM (Array Name) := do
  let environment ← getEnv
  let mut names := #[]
  for name in e.getUsedConstants do
    if let some (.defnInfo info) := environment.find? name then
      if info.levelParams.isEmpty && !info.type.isForall then
        if ← isStoredValueType info.type then
          names := names.push name
  return names

/--
A goal `∀ a b : Fin n, P a.val b.val` with a literal `n` becomes the loop of
`forall_fin_pairs` over the `n * n` pairs: the result is the goal that the loop counts no
failure. Other goals, and statements that use `a` or `b` other than through their values, give
`none`.
-/
def pairsLoop? (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  let .forallE nameA typeA bodyA _ := target | return none
  unless typeA.isAppOfArity ``Fin 1 do return none
  let size := typeA.appArg!
  let some bound := size.nat? | return none
  let .forallE nameB typeB _ _ := bodyA | return none
  unless typeB == typeA do return none
  let natType := mkConst ``Nat
  let relation? ← withLocalDeclD nameA typeA fun a => withLocalDeclD nameB typeA fun b => do
    let statement := ((bodyA.instantiate1 a).bindingBody!).instantiate1 b
    withLocalDeclD `x natType fun x => withLocalDeclD `y natType fun y => do
      let abstracted := (← kabstract statement (mkApp2 (mkConst ``Fin.val) size a)).instantiate1 x
      let abstracted := (← kabstract abstracted (mkApp2 (mkConst ``Fin.val) size b)).instantiate1 y
      if abstracted.containsFVar a.fvarId! || abstracted.containsFVar b.fvarId! then
        return none
      return some (← mkLambdaFVars #[x, y] abstracted)
  let some relation := relation? | return none
  let count := mkRawNatLit (bound * bound)
  let partialProof ← mkAppOptM ``forall_fin_pairs
    #[some size, some relation, none, some count, some (← mkEqRefl count)]
  -- The loop is stated as the kernel infers it, by substitution without beta reduction: the
  -- kernel compares the type of the decided loop with the premise of `forall_fin_pairs`, and
  -- two loops that differ are evaluated to be compared.
  let mut premise := (← getConstInfo ``forall_fin_pairs).type
  for argument in partialProof.getAppArgs do
    premise := premise.bindingBody!.instantiate1 argument
  let loopGoal ← mkFreshExprSyntheticOpaqueMVar premise.bindingDomain!
  let proof := mkApp partialProof loopGoal
  unless ← isDefEq (← inferType proof) target do return none
  goal.assign proof
  return some loopGoal.mvarId!

elab_rules : tactic
  | `(tactic| float_decide $[[$lemmas,*]]?) => withMainContext do
  let extra : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," :=
    lemmas.getD (Syntax.TSepArray.mk #[])
  let target ← instantiateMVars (← (← getMainGoal).getType)
  -- Unfold the user's definitions first, so that their loops are visible.
  unless extra.getElems.isEmpty do
    evalTactic (← `(tactic| simp (failIfUnchanged := false) only [$extra,*]))
  if (← getUnsolvedGoals).isEmpty then
    return
  -- Unfold the definitions that name one stored value, so that a literal behind a name is
  -- computed on the kernel path too. A few rounds reach names defined from other names.
  for _ in [0:8] do
    let goal ← getMainGoal
    let statement ← instantiateMVars (← goal.getType)
    let names ← storedValueConstants statement
    if names.isEmpty then
      break
    let unfolded ← deltaExpand statement names.contains
    replaceMainGoal [← goal.replaceTargetDefEq unfolded]
  -- Keep literal loop lengths as variables while rewriting: the goal `P lengths` becomes
  -- `step lengths final` with `step : ∀ n, ?Q n → P n`, which the rewrite proves by reducing
  -- `P n` to its kernel form `?Q n`, and `final : ?Q lengths`, which the kernel decides.
  let rewrite : TacticM Unit := do
    -- The premise of a rewrite rule names the family's reference operation up to unfolding,
    -- which instance arguments are compared with only when transparency is not restricted.
    evalTactic (← `(tactic|
      set_option backward.isDefEq.respectTransparency false in
      simp (failIfUnchanged := false) only [kernel_optimize, $extra,*]))
  let goal ← getMainGoal
  let statement ← instantiateMVars (← goal.getType)
  let lengths ← loopLengths statement
  if lengths.isEmpty then
    rewrite
  else
    let natType := mkConst ``Nat
    let motiveType := lengths.foldr (fun _ type => mkForall `n .default natType type)
      (mkSort Level.zero)
    let motive ← mkFreshExprMVar motiveType
    let names ← lengths.mapM fun _ => mkFreshUserName `n
    let stepType ← withLocalDeclsD (names.map fun name => (name, fun _ => pure natType))
      fun vars => do
        let mut body := statement
        for (length, var) in lengths.zip vars do
          body := abstractLength length var body
        mkForallFVars vars (← mkArrow (mkAppN motive vars) body)
    let step ← mkFreshExprSyntheticOpaqueMVar stepType
    let (introduced, stepGoal) ← step.mvarId!.introNP (lengths.size + 1)
    replaceMainGoal [stepGoal]
    rewrite
    match ← getUnsolvedGoals with
    | [] =>
        -- The rewrite proved the statement for every length.
        let trivialMotive := lengths.foldr (fun _ body => mkLambda `n .default natType body)
          (mkConst ``True)
        motive.mvarId!.assign trivialMotive
    | remaining :: _ =>
        let hypothesis := mkFVar introduced[lengths.size]!
        let closed ← remaining.withContext do
          isDefEq (← remaining.getType) (← inferType hypothesis)
        unless closed do
          throwError "float_decide: could not put the loop lengths back in{indentExpr target}"
        remaining.assign hypothesis
    -- The rewrite for every length is a lemma of its own: applied to the literal lengths it
    -- stays an application, and the kernel does not see the lengths inside its proof. The
    -- lemma is closed, so no local definition needs expanding, and with `zetaDelta` the
    -- elaborator does not check the rewrite proof again before the kernel does, which took
    -- seconds on a statement about a ternary value.
    let rewriteLemma ← mkAuxTheorem (← instantiateMVars stepType) (← instantiateMVars step)
      (zetaDelta := true)
    let finalType := (← instantiateMVars (mkAppN motive lengths)).headBeta
    let final ← mkFreshExprSyntheticOpaqueMVar finalType
    goal.assign (mkApp (mkAppN rewriteLemma lengths) final)
    replaceMainGoal [final.mvarId!]
    if finalType.isConstOf ``True then
      final.mvarId!.assign (mkConst ``True.intro)
      replaceMainGoal []
  if (← getUnsolvedGoals).isEmpty then
    return
  -- A statement about all pairs of indices of a small type becomes one loop over the pairs.
  if let some loopGoal ← pairsLoop? (← getMainGoal) then
    replaceMainGoal [loopGoal]
  -- Decide a closed statement with one lemma whose statement and proof share equal subterms as
  -- one object. The kernel looks up the format constants of every step in its cache, and a hit
  -- on a key that is equal but a different object compares the two descriptors structurally,
  -- which costs a fifth of the time of a loop. Any failure goes on to `decide +kernel` below,
  -- which reports it.
  let goal ← getMainGoal
  let statement ← instantiateMVars (← goal.getType)
  let decidedDirectly ← goal.withContext do
    if statement.hasFVar || statement.hasMVar || statement.hasLevelParam then
      return false
    let .some decision ← trySynthInstance (mkApp (mkConst ``Decidable) statement) | return false
    let proof := mkApp3 (mkConst ``of_decide_eq_true) statement decision
      (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
    let (sharedStatement, sharedProof) := ShareCommon.shareCommon' (statement, proof)
    try
      let lemmaName ← withOptions (Elab.async.set · false) do
        mkAuxLemma [] sharedStatement sharedProof
      goal.assign (mkConst lemmaName)
      return true
    catch _ =>
      return false
  if decidedDirectly then
    replaceMainGoal []
    return
  -- The kernel may not terminate on a term that is stuck on a variable.
  if statement.hasMVar then
    throwError "float_decide: the statement is not fully elaborated:{indentExpr target}"
  if statement.hasFVar then
    throwError "float_decide: the statement mentions local variables or hypotheses, so it is \
      not closed:{indentExpr target}"
  try
    evalTactic (← `(tactic| decide +kernel))
  catch error =>
    let goal ← getMainGoal
    let reason ← goal.withContext do
      let statement ← instantiateMVars (← goal.getType)
      match ← trySynthInstance (mkApp (mkConst ``Decidable) statement) with
      | .some decision =>
          let decided := mkApp2 (mkConst ``Decidable.decide) statement decision
          match Kernel.whnf (← getEnv) (← getLCtx) decided with
          | .ok value =>
              if value.isConstOf ``Bool.false then
                throwError "float_decide: the statement is false:{indentExpr target}"
              else
                pure m!"Lean's kernel could not evaluate the statement"
          | .error _ => pure m!"Lean's kernel could not evaluate the statement"
      | _ => pure m!"the statement has no `Decidable` instance"
    throwError "float_decide: {reason}:{indentExpr target}\n{error.toMessageData}"

end FloatLib.Floats.ExecFloat.KernelPath
