/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval.Bounds
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public meta import FloatLib.Numerics.Automation.Interval.Diagnostics
public meta import FloatLib.Numerics.Automation.Interval.Reify
public meta import Lean.Elab.Tactic.Decide

/-!
# Interval proofs from rational bounds

`interval` proves real inequalities by evaluating certified interval expressions. It reads rational
bounds from the local context and first tries algebraic expressions with exact rational endpoints.
The binary-grid backend then handles remaining goals and subdivides the widest input interval
when its first enclosure is inconclusive.

Finite sums, dot products, matrix products, and supported norms expand using Mathlib equalities.
Pointwise hypotheses supply the bounds of their entries. Real and nonnegative-real inequalities
use the same checker.

The options `precision`, `degree`, and `depth` control fractional endpoint bits, elementary-function
approximation degree, and subdivision depth. A closed Boolean check is verified by Lean's kernel;
the expression equality and the input bounds are also proved. No sampled values enter the proof.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

/-- Bound kernel verification independently of the surrounding declaration's heartbeat setting. -/
private def withCheckBudget {α : Type} (heartbeats : Nat) (action : TacticM α) : TacticM α := do
  if heartbeats == 0 then
    throwError "interval maxHeartbeats must be positive"
  withOptions (fun opts => Elab.async.set (Lean.maxHeartbeats.set opts heartbeats) false) do
    withCurrHeartbeats action

/-- Cache a closed decision proof only after the kernel has checked it within the budget. -/
private def verifyClosedCheck (proposition : Q(Prop)) (heartbeats : Nat) : TacticM Lean.Expr :=
  withCheckBudget heartbeats do
    let proof ← withTransparency .all (mkDecideProof proposition)
    let name ← mkAuxLemma [] proposition proof
    return mkConst name

/-- Verify a real or nonnegative-real inequality with exact rational or binary-grid bounds. -/
def close (precision degree depth : Nat)
    (maxHeartbeats : Nat := 20000) : TacticM Unit := withMainContext do
  let target : Q(Prop) ← instantiateMVars (← getMainTarget)
  let (lhs, rhs, strict) ← match target with
    | ~q(($a : ℝ) ≤ $b) => pure (a, b, false)
    | ~q(($a : ℝ) < $b) => pure (a, b, true)
    | ~q(($a : NNReal) ≤ $b) => pure (q(($a : ℝ)), q(($b : ℝ)), false)
    | ~q(($a : NNReal) < $b) => pure (q(($a : ℝ)), q(($b : ℝ)), true)
    | _ => throwError "interval expects a real or nonnegative-real inequality a ≤ b or a < b"
  let difference : Q(ℝ) := q($lhs - $rhs)
  let normalized ← normalizeAggregates difference
  let scalar : Q(ℝ) ← pure normalized.expr
  let (expression, cache) ← (reify scalar).run {}
  let atoms := cache.atoms
  let mut bounds := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then
      bounds := bounds ++ (← boundsOfProofFor atoms decl.toExpr)
  let data ← reifyBox bounds atoms.toList
  let box : Q(Box) ← pure data.box
  let reals : Q(List ℝ) ← pure data.reals
  let membership : Q(Box.ContainsReal $box (fun i => $reals[i]?.getD 0)) ←
    pure data.membership
  let values : Q(Nat → ℝ) ← pure q(fun i => $reals[i]?.getD 0)
  let precision : Q(Nat) ← pure (mkNatLit precision)
  let degree : Q(Nat) ← pure (mkNatLit degree)
  let depth : Q(Nat) ← pure (mkNatLit depth)
  let config : Q(Backend.Config) ← pure q(⟨$precision, $degree⟩)
  let mut extensions : Q(List Extension) := q([])
  let mut functionTable : Q(List (List ℝ → ℝ)) := q([])
  let mut extensionProof : Lean.Expr := q(extensionsSound_nil)
  for name in cache.extensions.reverse do
    let (E, function, _, sound) ← extensionCertificate name
    let quotedFunction : Q(RealFunction (Extension.arity $E)) ← pure function
    let proof : Q(Extension.Sound $E $quotedFunction) ← pure sound
    let currentProof : Q(ExtensionsSound $extensions $functionTable) ← pure extensionProof
    let newExtensions : Q(List Extension) := q($E :: $extensions)
    let newFunctions : Q(List (List ℝ → ℝ)) :=
      q(RealFunction.apply $quotedFunction :: $functionTable)
    let newProof : Q(ExtensionsSound $newExtensions $newFunctions) :=
      q(ExtensionsSound.cons $currentProof $proof)
    extensions := newExtensions
    functionTable := newFunctions
    extensionProof := newProof
  let extensionTable : Q(List Extension) ← pure extensions
  let realFunctionTable : Q(List (List ℝ → ℝ)) ← pure functionTable
  let certifiedExtensions : Q(ExtensionsSound $extensionTable $realFunctionTable) ←
    pure extensionProof
  let functions : Q(Nat → List ℝ → ℝ) := q(extensionValues $realFunctionTable)
  let backend : Q(Backend Int) :=
    q(Backend.withExtensions (Backend.binaryGrid $config) $config $extensionTable)
  let backendProof : Q(Backend.Sound $backend $functions) :=
    q(Backend.withExtensions_sound (extensions := $extensionTable) (functions := $realFunctionTable)
      (Backend.binaryGrid_sound $config) $config $certifiedExtensions)
  let relation : Q(Relation) ← pure (if strict then q(.negative) else q(.nonpositive))
  let expanded : Q($difference = $scalar) ← normalized.getProof
  let interpreted : Q($scalar = Interval.Expr.eval $expression $values $functions) ←
    evalEquality scalar expression values cache functions
  let equality : Q($difference = Interval.Expr.eval $expression $values $functions) :=
    q(Eq.trans $expanded $interpreted)
  -- Without registered calls, every reified operation is algebraic. Exact rational endpoints
  -- retain equality at non-dyadic bounds, such as the upper bound 1/3.
  if cache.extensions.isEmpty then
    let exactBackend : Q(Backend ℚ) :=
      q(Backend.withExtensions (Backend.rational $config) $config $extensionTable)
    let exactBackendProof : Q(Backend.Sound $exactBackend $functions) :=
      q(Backend.withExtensions_sound (extensions := $extensionTable)
        (functions := $realFunctionTable)
        (Backend.rational_sound $config) $config $certifiedExtensions)
    let exactProof? ← try
      let checked ← verifyClosedCheck
        q(Interval.Expr.check $expression $exactBackend $relation $box 0 = true)
        maxHeartbeats
      pure (some checked)
    catch error =>
      if error.isInterrupt then throw error
      pure none
    if let some checked := exactProof? then
      let sound := mkAppN (mkConst ``Interval.Expr.check_sound [Level.zero])
        #[functions, q(ℚ), expression, exactBackend, exactBackendProof,
          relation, box, q(0), checked, values, membership]
      let proof ← if strict then do
        let h : Q(Interval.Expr.eval $expression $values $functions < 0) := sound
        let h : Q($lhs - $rhs < 0) := q((Eq.symm $equality) ▸ $h)
        pure q(sub_neg.mp $h)
      else do
        let h : Q(Interval.Expr.eval $expression $values $functions ≤ 0) := sound
        let h : Q($lhs - $rhs ≤ 0) := q((Eq.symm $equality) ▸ $h)
        pure q(sub_nonpos.mp $h)
      closeMainGoal `interval proof
      return
  let checked : Q(Interval.Expr.check $expression $backend $relation $box $depth = true) ←
    try
      let preflight ← if cache.extensions.isEmpty then try
        withCheckBudget maxHeartbeats do
          preflightCheck expression box config relation depth
      catch error =>
        if error.isInterrupt then throw error
        pure none
      else pure none
      if preflight == some false then
        throwError "interval checker returned false"
      verifyClosedCheck q(Interval.Expr.check $expression $backend $relation $box $depth = true)
        maxHeartbeats
    catch error =>
      if error.isInterrupt then throw error
      let diagnostic ← try
        withCheckBudget maxHeartbeats do
          if cache.extensions.isEmpty then
            diagnoseFailure expression box config relation depth atoms
          else
            diagnoseRegisteredFailure expression backend box config relation depth atoms
      catch diagnosticError =>
        if diagnosticError.isInterrupt then throw diagnosticError
        pure m!"interval could not certify: bounded diagnostics could not complete."
      throwError "{diagnostic}\nKernel verification failed within the interval budget of \
        {maxHeartbeats} heartbeats; a larger `(maxHeartbeats := ...)` may be needed."
  -- All arguments are known; assembling the application avoids re-elaborating the closed check.
  let sound := mkAppN (mkConst ``Interval.Expr.check_sound [Level.zero])
    #[functions, q(Int), expression, backend, backendProof,
      relation, box, depth, checked, values, membership]
  let proof ← if strict then do
    let h : Q(Interval.Expr.eval $expression $values $functions < 0) := sound
    let h : Q($lhs - $rhs < 0) := q((Eq.symm $equality) ▸ $h)
    pure q(sub_neg.mp $h)
  else do
    let h : Q(Interval.Expr.eval $expression $values $functions ≤ 0) := sound
    let h : Q($lhs - $rhs ≤ 0) := q((Eq.symm $equality) ▸ $h)
    pure q(sub_nonpos.mp $h)
  closeMainGoal `interval proof

end FloatLib.Numerics.Interval.Tactic

/--
Prove a real or nonnegative-real inequality from rational bounds in the local context.

For example, `interval (precision := 64) (degree := 16) (depth := 8)` chooses a binary
endpoint grid with 64 fractional bits, degree-16 elementary enclosures, and at most eight
midpoint subdivisions along any branch. These are also the defaults. Each verification attempt and
failure diagnostics have separate budgets of 20,000 heartbeats, even when the surrounding
declaration disables heartbeat limits. Use `(maxHeartbeats := 40000)` for a larger finite budget.

Algebraic goals first use exact rational endpoints without subdivision, preserving equality at
non-dyadic hypothesis bounds. For arithmetic without registered calls, an advisory executable check
rejects failing binary-grid leaves before kernel reduction. Registered calls use bounded kernel
reduction directly; every successful proof requires kernel verification.

Concrete finite sums and matrix expressions are expanded automatically, including pointwise
bounds such as `∀ i, x i ∈ Set.Icc 0 1`. Norms use the instances selected in the goal.

Division requires a denominator interval away from zero; logarithm requires positive inputs,
and square root requires nonnegative inputs. Inverse sine and cosine require inputs in `[-1, 1]`;
tangent requires a cosine enclosure excluding zero. Failure reports the obstructing range or
insufficient bound and restores the original proof state.
-/
syntax (name := interval) "interval" (ppSpace "(" ident " := " num ")")* : tactic

elab_rules : tactic
  | `(tactic| interval $[($option:ident := $value:num)]*) => do
    let mut precision := 64
    let mut degree := 16
    let mut depth := 8
    let mut maxHeartbeats := 20000
    let mut seen : Array Name := #[]
    for option in option, value in value do
      let key := option.getId.eraseMacroScopes
      if seen.contains key then
        throwErrorAt option "duplicate interval option {key}"
      seen := seen.push key
      match key with
      | `precision => precision := value.getNat
      | `degree => degree := value.getNat
      | `depth => depth := value.getNat
      | `maxHeartbeats =>
        maxHeartbeats := value.getNat
        if maxHeartbeats == 0 then
          throwErrorAt value.raw "interval maxHeartbeats must be positive"
      | _ => throwErrorAt option "expected precision, degree, depth, or maxHeartbeats"
    let saved ← saveState
    discard <| tryFinally'
      (FloatLib.Numerics.Interval.Tactic.close precision degree depth maxHeartbeats)
      (fun result => unless result.isSome do saved.restore)
