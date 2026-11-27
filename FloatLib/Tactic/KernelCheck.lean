/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelOptimize
public meta import Lean.Elab.Tactic.Decide
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Meta.Check
public meta import Lean.Meta.Closure
public meta import Lean.Meta.KAbstract
public meta import Lean.Meta.Tactic.Delta
public meta import Lean.Util.ForEachExpr
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop

/-!
# Closed statements checked by Lean's kernel

`KernelCheck.prove` proves a closed decidable statement by evaluation in Lean's kernel. It first
rewrites the public operations in the statement to their kernel operations with the rules tagged
`@[kernel_optimize]`, cheapest first, and then has the kernel decide what's left. `float_decide`
is `prove` on the main goal, and `interval` checks its closed Boolean conditions with it, so a
cheaper kernel rule tagged in any imported module speeds up both tactics with no change here.

The statement doesn't have to be a goal. Say `countUp n` builds `n` one successor at a time, and
`countUp_eq : countUp n = n` is tagged `@[kernel_optimize]`. Handed
`countUp 1000000 + 1 = 1000001`, `prove` rewrites `countUp 1000000` to `1000000` with that rule,
so the kernel adds two literals instead of unfolding `countUp` a million times.

## Main definitions

* `prove`: the proof of a closed decidable statement, with optional extra rules, a heartbeat
  budget for the kernel and the name of the tactic for the messages.
* `withBudget`: run an action with the same kernel budget for every declaration it adds.
* `mentionsStoredValue`: whether a statement is about the stored values of a format, read from
  its constants and their signatures alone.

## Implementation notes

Before the rules apply, the definitions that name one stored value, such as
`def tenth : Binary32 := 0.1`, are unfolded, so that a literal behind a name is computed on the
kernel path too.

A loop of a thousand steps has its length as a literal in the statement, and with the literal in
place the kernel would check the rewrite by unfolding both forms of the loop, step by step. So
`prove` replaces the literal lengths of `List.range` loops and of `Nat.rec` recursions by
variables, proves the rewrite for loops of every length, and applies that lemma to the literal
lengths. Other occurrences of the same literal, such as the index of a type, stay in place. If a
dependent type needs the literal length, `prove` rewrites the original statement instead. A
statement `∀ a b : Fin n, P a b` with a literal `n`, in which `a` and `b` occur only as their
values, becomes one loop over the `n * n` pairs (`forall_fin_pairs`).

The kernel decides the result as one auxiliary lemma whose statement and proof share equal
subterms. A statement that no rule rewrites is decided as written, raw literals included, and its
proof is that lemma. A budget of `n` gives each declaration the kernel checks `n` thousand
heartbeats, whatever the surrounding setting, and a kernel failure comes back as the kernel's
own error.

A rule only sees the statement handed to `prove`: the rewrite changes that statement, not the
terms that the kernel meets later when it unfolds the definitions in it. So a rule for the checks
of `interval` has to match a term of the decided statement, such as `Expr.checkZero`,
`Constraint.refutes` or the constant of a backend, and a rule for an operation that only their
bodies call doesn't apply. The rules for core Lean's operations on integers and rationals
(`FloatLib.Floats.ExecFloat.Backends.Kernel.Exact`) apply to the integers and rationals written in
the statement, and each such rewrite adds to the stored proof. A rational written as `Kernel.Q.mk`
of raw literals, as `FloatLib.Numerics.Interval.Tactic.Constraints.quoteRat` writes it, is in
kernel form already, and no rule rewrites it.
-/

public meta section

namespace FloatLib.Tactic.KernelCheck

open Lean Meta Elab

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
Whether the constant `name` is about the stored values of a format. A type former is when,
applied to its parameters, it is an `ExecFloat F`, as `Binary32` and `ExecFloat.Binary` are. Any
other constant is when its type takes or gives an `ExecFloat F`: an operation of a format family,
such as `ExecFloat.Binary.add`, or a stored value, such as `def tenth : Binary32 := 0.1`. Only
the signature is read, and only its binder types and its conclusion are reduced, with reducible
transparency.
-/
def isStoredValueConstant (name : Name) : MetaM Bool := do
  let some info := (← getEnv).find? name | return false
  forallTelescope info.type fun parameters conclusion => do
    if conclusion.isSort then
      return ← isStoredValueType
        (mkAppN (mkConst name (info.levelParams.map Level.param)) parameters)
    if ← isStoredValueType conclusion then
      return true
    parameters.anyM fun parameter => do isStoredValueType (← inferType parameter)

/--
Whether `e` is about the stored values of a format: one of its constants is a type of stored
values, an operation of a format family or a stored value, as `isStoredValueConstant` reads them.
A subterm of such a type brings one of these along in an elaborated statement, as the type
argument of a polymorphic operation, as the type of a binder or as the operation that gives the
subterm. Only `e` and the signatures of its constants are read, and no unfolding of `e` takes
place, so the test is cheap on a large statement. It is false on statements built from natural
numbers, integers, rationals and definitions over them, such as a certificate on packed rows.
-/
def mentionsStoredValue (e : Expr) : MetaM Bool :=
  e.getUsedConstants.anyM isStoredValueConstant

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
  let partialProof ← mkAppOptM ``FloatLib.Floats.ExecFloat.KernelPath.forall_fin_pairs
    #[some size, some relation, none, some count, some (← mkEqRefl count)]
  -- The loop is stated as the kernel infers it, by substitution without beta reduction: the
  -- kernel compares the type of the decided loop with the premise of `forall_fin_pairs`, and
  -- two loops that differ are evaluated to be compared.
  let mut premise := (← getConstInfo ``FloatLib.Floats.ExecFloat.KernelPath.forall_fin_pairs).type
  for argument in partialProof.getAppArgs do
    premise := premise.bindingBody!.instantiate1 argument
  let loopGoal ← mkFreshExprSyntheticOpaqueMVar premise.bindingDomain!
  let proof := mkApp partialProof loopGoal
  unless ← isDefEq (← inferType proof) target do return none
  goal.assign proof
  return some loopGoal.mvarId!

/--
Run `action` with a budget of `heartbeats` for each declaration that Lean's kernel checks in it,
in the unit of the option `maxHeartbeats` (thousands of heartbeats) and whatever the surrounding
setting. The elaborator keeps the surrounding limit and counts from zero again. Declarations are
added synchronously, so that a kernel failure is an error of `action`. A budget of `0` means no
limit, as for `maxHeartbeats`.
-/
def withBudget {m : Type → Type} [Monad m] [MonadWithOptions m] [MonadControlT CoreM m]
    {α : Type} (heartbeats : Nat) (action : m α) : m α :=
  withOptions (fun options => Elab.async.set (Lean.maxHeartbeats.set options heartbeats) false) do
    withCurrHeartbeats action

/--
`goal` after one rewrite with `theorems` and `simprocs`, or `none` if the rewrite proves it. When
no theorem, simproc or unfolding applies, `goal` stays as it is: simp would still write raw
literals as numerals and reduce `let`, beta and projection redexes, which the kernel reduces just
as well.
-/
private def simplify (goal : MVarId) (theorems : SimpTheoremsArray)
    (simprocs : Simp.SimprocsArray) : MetaM (Option MVarId) := goal.withContext do
  let context ← Simp.mkContext (config := { failIfUnchanged := false })
    (simpTheorems := theorems) (congrTheorems := ← getSimpCongrTheorems)
  let target ← instantiateMVars (← goal.getType)
  let (result, stats) ← Lean.Meta.simp target context simprocs
  if result.expr.isTrue then
    goal.assign <| ← match result.proof? with
      | some proof => mkOfEqTrue proof
      | none => pure (mkConst ``True.intro)
    return none
  if stats.usedTheorems.size == 0 then
    return some goal
  applySimpResultToTarget goal target result

/--
`goal` rewritten with `theorems`, the kernel rules among them, or `none` if the rewrite proves
it. The literal loop lengths become variables while rewriting: the goal `P lengths` becomes
`step lengths final` with `step : ∀ n, ?Q n → P n`, which the rewrite proves by reducing `P n` to
its kernel form `?Q n`, and `final : ?Q lengths`, the goal that is returned.
-/
private def rewrite (goal : MVarId) (theorems : SimpTheoremsArray)
    (simprocs : Simp.SimprocsArray) (tactic : Name) (target : Expr) :
    MetaM (Option MVarId) := goal.withContext do
  -- The premise of a rewrite rule names the family's reference operation up to unfolding,
  -- which instance arguments are compared with only when transparency is not restricted.
  let rewriteOnce (goal : MVarId) : MetaM (Option MVarId) :=
    withOptions (·.setBool `backward.isDefEq.respectTransparency false) do
      simplify goal theorems simprocs
  let statement ← instantiateMVars (← goal.getType)
  let lengths ← loopLengths statement
  if lengths.isEmpty then
    return ← rewriteOnce goal
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
  unless ← withoutModifyingState (isTypeCorrect stepType) do
    return ← rewriteOnce goal
  let step ← mkFreshExprSyntheticOpaqueMVar stepType
  let (introduced, stepGoal) ← step.mvarId!.introNP (lengths.size + 1)
  match ← rewriteOnce stepGoal with
  | none =>
      -- The rewrite proved the statement for every length.
      let trivialMotive := lengths.foldr (fun _ body => mkLambda `n .default natType body)
        (mkConst ``True)
      motive.mvarId!.assign trivialMotive
  | some remaining =>
      -- Nothing applied: the statement stays as written, with no lemma for its loops.
      if remaining == stepGoal then
        return some goal
      let hypothesis := mkFVar introduced[lengths.size]!
      let closed ← remaining.withContext do
        isDefEq (← remaining.getType) (← inferType hypothesis)
      unless closed do
        throwError "{tactic}: could not put the loop lengths back in{indentExpr target}"
      remaining.assign hypothesis
  -- The rewrite for every length is a lemma of its own: applied to the literal lengths it
  -- stays an application, and the kernel does not see the lengths inside its proof. The
  -- lemma is closed, so no local definition needs expanding, and with `zetaDelta` the
  -- elaborator does not check the rewrite proof again before the kernel does, which took
  -- seconds on a statement about a ternary value.
  let rewriteLemma ← mkAuxTheorem (← instantiateMVars stepType) (← instantiateMVars step)
    (zetaDelta := true) (cache := false)
  let finalType := (← instantiateMVars (mkAppN motive lengths)).headBeta
  let final ← mkFreshExprSyntheticOpaqueMVar finalType
  goal.assign (mkApp (mkAppN rewriteLemma lengths) final)
  if finalType.isConstOf ``True then
    final.mvarId!.assign (mkConst ``True.intro)
    return none
  return some final.mvarId!

/--
Close `goal`, whose closed statement has the instance `decision`, with one lemma whose statement
and proof share equal subterms as one object. The kernel looks up the format constants of every
step in its cache, and a hit on a key that is equal but a different object compares the two
descriptors structurally, which costs a fifth of the time of a loop.
-/
private def decideShared (goal : MVarId) (statement decision : Expr) : MetaM Unit := do
  let proof := mkApp3 (mkConst ``of_decide_eq_true) statement decision
    (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
  let (sharedStatement, sharedProof) := ShareCommon.shareCommon' (statement, proof)
  let levels := (collectLevelParams (collectLevelParams {} statement) proof).params.toList
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma levels sharedStatement sharedProof (cache := false)
  goal.assign (mkConst name (levels.map Level.param))

/--
Fail as `float_decide` does when the kernel has not decided the closed statement of `goal`: Lean's
`decide +kernel` runs on it, its explanation follows the reason, and the kernel's evaluation of
the decision says whether the statement is false. If `decide +kernel` proves the statement after
all, `goal` is closed. It runs with an empty auxiliary-lemma cache so that this check, too,
must evaluate the decision.
-/
private def explainFailure (goal : MVarId) (tactic : Name) (target : Expr) : MetaM Unit := do
  try
    let cache := auxLemmasExt.getState (← getEnv)
    modifyEnv fun env => auxLemmasExt.setState env {}
    try
      discard <| Term.TermElabM.run' <| Tactic.run goal <|
        Tactic.evalDecideCore `decide { kernel := true }
    finally
      modifyEnv fun env => auxLemmasExt.setState env cache
  catch error =>
    let reason ← goal.withContext do
      let statement ← instantiateMVars (← goal.getType)
      match ← trySynthInstance (mkApp (mkConst ``Decidable) statement) with
      | .some decision =>
          let decided := mkApp2 (mkConst ``Decidable.decide) statement decision
          match Kernel.whnf (← getEnv) (← getLCtx) decided with
          | .ok value =>
              if value.isConstOf ``Bool.false then
                throwError "{tactic}: the statement is false:{indentExpr target}"
              else
                pure m!"Lean's kernel could not evaluate the statement"
          | .error _ => pure m!"Lean's kernel could not evaluate the statement"
      | _ => pure m!"the statement has no `Decidable` instance"
    throwError "{tactic}: {reason}:{indentExpr target}\n{error.toMessageData}"

/--
Close `goal`, whose statement is `target`, as `prove` describes. Without `explain`, a rewrite
that fails is skipped and a kernel failure is the kernel's own error.
-/
private def decideGoal (goal : MVarId) (target : Expr) (extra : SimpTheoremsArray)
    (simprocs : Simp.SimprocsArray) (explain : Bool) (tactic : Name) : MetaM Unit := do
  let attempt (rewritten : MetaM (Option MVarId)) (goal : MVarId) : MetaM (Option MVarId) := do
    if explain then
      return ← rewritten
    let saved ← saveState
    try rewritten
    catch _ =>
      saved.restore
      return some goal
  let mut goal := goal
  -- Unfold the caller's definitions first, so that their loops are visible.
  unless extra.isEmpty do
    let some next ← attempt (simplify goal extra simprocs) goal | return
    goal := next
  -- Unfold the definitions that name one stored value, so that a literal behind a name is
  -- computed on the kernel path too. A few rounds reach names defined from other names.
  for _ in [0:8] do
    let statement ← instantiateMVars (← goal.getType)
    let names ← storedValueConstants statement
    if names.isEmpty then
      break
    goal ← goal.replaceTargetDefEq (← deltaExpand statement names.contains)
  -- The order of `simp only [kernel_optimize, …]`: the set of the caller's theorems, which also
  -- holds the two that `simp only` adds, then the kernel rules, then the sets the caller named.
  let first ← match extra[0]? with
    | some first => pure first
    | none => Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  let theorems := #[first, ← Floats.ExecFloat.Backend.Tag.kernelOptimizeExt.getTheorems] ++
    extra.extract 1 extra.size
  let some next ← attempt (rewrite goal theorems simprocs tactic target) goal | return
  goal := next
  -- A statement about all pairs of indices of a small type becomes one loop over the pairs.
  if let some loopGoal ← pairsLoop? goal then
    goal := loopGoal
  let statement ← instantiateMVars (← goal.getType)
  -- The kernel may not terminate on a term that is stuck on a variable.
  if statement.hasMVar then
    throwError "{tactic}: the statement is not fully elaborated:{indentExpr target}"
  if statement.hasFVar then
    throwError "{tactic}: the statement mentions local variables or hypotheses, so it is \
      not closed:{indentExpr target}"
  let decision? ← goal.withContext do
    return (← trySynthInstance (mkApp (mkConst ``Decidable) statement)).toOption
  let some decision := decision? |
    if explain then
      explainFailure goal tactic target
    else
      throwError "{tactic}: the statement has no `Decidable` instance:{indentExpr target}"
  unless explain do
    return ← decideShared goal statement decision
  try
    decideShared goal statement decision
  catch _ =>
    explainFailure goal tactic target

/--
Prove the decidable statement `statement` by evaluation in Lean's kernel, after rewriting it with
the rules tagged `@[kernel_optimize]`: the proof that `float_decide` gives for a goal
`statement`, valid in the local context.

* `extra` and `simprocs` add rules as `Lean.Elab.Tactic.mkSimpContext` elaborates the list of
  `simp only [r₁, …]`. They rewrite the statement first, and then again together with the kernel
  rules, so that the operations inside the caller's definitions become visible to the rules.
  `float_decide [f, h]` passes its list here.
* With `maxHeartbeats := some n`, every declaration that the kernel checks gets `n` thousand
  heartbeats, whatever the surrounding setting. A rewrite that fails is skipped; the kernel decides
  the statement as it is. A failed kernel check rethrows the kernel's own error, such as
  `(kernel) deterministic timeout`, so that a caller can tell a resource limit apart, and nothing
  is evaluated twice.
* Without a budget, the surrounding heartbeat setting applies, and a failure says why and shows
  the statement, as `float_decide` reports it: the kernel evaluated it to false or could not
  evaluate it (with the explanation of Lean's `decide +kernel`), it has no `Decidable` instance,
  or it mentions local variables or hypotheses, so it is not closed.

`tactic` names the tactic in the messages. A statement that the kernel decides was checked
before the proof is returned: the decision is a fresh auxiliary lemma, not a previously stored
proof of the same statement. The rewrite in front of it is checked with the declaration that uses
the proof, or at once by `mkAuxLemma`, as `interval` does.
-/
def prove (statement : Expr) (extra : SimpTheoremsArray := #[])
    (simprocs : Simp.SimprocsArray := #[]) (maxHeartbeats : Option Nat := none)
    (tactic : Name := `float_decide) : MetaM Expr := do
  let target ← instantiateMVars statement
  let check : MetaM Expr := do
    let proof ← mkFreshExprSyntheticOpaqueMVar target
    decideGoal proof.mvarId! target extra simprocs maxHeartbeats.isNone tactic
    instantiateMVars proof
  match maxHeartbeats with
  | none => check
  | some heartbeats => withBudget heartbeats check

end FloatLib.Tactic.KernelCheck
