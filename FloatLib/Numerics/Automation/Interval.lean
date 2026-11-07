/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Interval.Bounds
public import FloatLib.Numerics.Coeff.Bound
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public meta import FloatLib.Numerics.Automation.Interval.Coeff
public meta import FloatLib.Numerics.Automation.Interval.Diagnostics
public meta import FloatLib.Numerics.Automation.Interval.Reify
public meta import Lean.Elab.Tactic.Decide

/-!
# Interval proofs from rational bounds

`interval` proves real inequalities by evaluating certified interval expressions. It reads rational
bounds from the local context and first tries algebraic expressions with exact rational endpoints. A
binary-grid backend then handles the goals that remain, and it subdivides the widest input interval
when its first enclosure is inconclusive.

Finite sums, dot products, matrix products, and supported norms expand through Mathlib equalities,
and pointwise hypotheses supply the bounds of their entries. Real and nonnegative-real inequalities
use the same checker, with nonnegative-real inputs supplying their zero lower bound automatically.

Three options tune the search. `precision` sets the fractional endpoint bits, `degree` the
elementary-function approximation degree, and `depth` the subdivision depth. Lean's kernel verifies
a closed Boolean check, and the expression equality and the input bounds are proved as well. No
sampled values enter the proof.

A bound over a whole domain, `∀ u : ℝ, …` for a trigonometric polynomial, `∀ x ∈ Set.Icc lo hi, …`
for a power or Chebyshev series, or `∀ z : ℂ, ‖z‖ = 1 → …` for a polynomial in `z`, goes to the
coefficient route of `FloatLib.Numerics.Automation.Interval.Coeff` first, where splitting would
never end. The coefficients alone settle many of these goals, and the options `lower` and `upper`
take sum-of-squares certificates for sharp bounds. On an interval the boxes still get their turn if
the coefficients fail.
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

/-- A resource limit that stopped a verification attempt. -/
private inductive ResourceLimit where
  /-- The heartbeat budget, which `(maxHeartbeats := ...)` sets. -/
  | heartbeats
  /-- The recursion depth, which `set_option maxRecDepth` sets. -/
  | recursion

/--
The kernel limit that stopped a failed verification attempt, if one did.

The kernel reports its limits as ordinary errors whose text `Kernel.Exception.toMessageData` fixes,
so they are recognized by that text, and only these are classified. An elaboration limit is a
runtime exception, which `try ... catch` in `TacticM` rethrows before any handler runs, so it ends
the tactic with Lean's own heartbeat or recursion error instead. Any other failure, such as a
checker that returns `false`, isn't a resource failure, even when the executable preflight passed.
-/
private def resourceLimit? (error : Exception) : MetaM (Option ResourceLimit) := do
  let text ← error.toMessageData.toString
  if text.startsWith "(kernel) deterministic timeout" then return some .heartbeats
  if text.startsWith "(kernel) deep recursion" then return some .recursion
  return none

/--
The advice that follows a failure message when `limit` stopped the kernel verification of
`attempt`, or nothing when no limit did.
-/
private def resourceAdvice (attempt : String) (maxHeartbeats : Nat) :
    Option ResourceLimit → MessageData
  | some .heartbeats =>
      m!"\nKernel verification of {attempt} ran out of the interval budget of {maxHeartbeats} \
        heartbeats; a larger `(maxHeartbeats := ...)` may be needed."
  | some .recursion =>
      m!"\nKernel verification of {attempt} exceeded the maximum recursion depth; a larger \
        `set_option maxRecDepth` may be needed."
  | none => m!""

/-- Name the registered calls of an expression, in call-index order, for failure diagnostics. -/
private def registeredCalls (registrations : Array Name) : MetaM (Array RegisteredCall) :=
  registrations.mapM fun registration => do
    let (_, function, _, _) ← extensionCertificate registration
    pure { function := function.constName!
           acceptedDomain? := Interval.acceptedDomain? registration }

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
  -- retain equality at non-dyadic bounds, such as the upper bound 1/3. A kernel limit that stops
  -- this attempt is reported if the binary-grid attempt fails too.
  let mut exactLimit : Option ResourceLimit := none
  if cache.extensions.isEmpty then
    let exactBackend : Q(Backend ℚ) :=
      q(Backend.withExtensions (Backend.rational $config) $config $extensionTable)
    let exactBackendProof : Q(Backend.Sound $exactBackend $functions) :=
      q(Backend.withExtensions_sound (extensions := $extensionTable)
        (functions := $realFunctionTable)
        (Backend.rational_sound $config) $config $certifiedExtensions)
    let (exactProof?, limit) ← try
      let checked ← verifyClosedCheck
        q(Interval.Expr.check $expression $exactBackend $relation $box 0 = true)
        maxHeartbeats
      pure (some checked, (none : Option ResourceLimit))
    catch error =>
      if error.isInterrupt then throw error
      pure (none, ← resourceLimit? error)
    exactLimit := limit
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
      let limit ← resourceLimit? error
      let diagnostic ← try
        withCheckBudget maxHeartbeats do
          if cache.extensions.isEmpty then
            diagnoseFailure expression box config relation depth atoms
          else
            diagnoseRegisteredFailure expression backend box config relation depth atoms
              (← registeredCalls cache.extensions)
      catch diagnosticError =>
        if diagnosticError.isInterrupt then throw diagnosticError
        pure m!"interval could not certify: bounded diagnostics could not complete."
      let exactAdvice := resourceAdvice "the exact-rational attempt" maxHeartbeats exactLimit
      let gridAdvice := resourceAdvice "the binary-grid attempt" maxHeartbeats limit
      throwError "{diagnostic}{exactAdvice}{gridAdvice}"
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

/-- `∀ x, x ∈ Set.Icc lo hi → P x` with the two binders introduced, for the boxes. -/
private def introInterval? (goal : MVarId) : MetaM (Option MVarId) := do
  let .forallE _ dom body _ ← whnfR (← goal.getType) | return none
  unless ← isDefEq dom q(ℝ) do return none
  let .forallE _ mem _ _ := body | return none
  let_expr Membership.mem _ _ _ s _ := mem | return none
  unless s.isAppOf ``Set.Icc do return none
  let (_, goal) ← goal.intro1P
  let (_, goal) ← goal.intro1P
  return some goal

/-- Run `interval` on the main goal: the coefficient route for a bound over a whole domain, then
the boxes, and for a trigonometric polynomial in a free variable the coefficient route again once
the boxes fail for want of bounds on that variable. -/
def run (precision degree depth maxHeartbeats : Nat) (certs : Coeff.Certs) : TacticM Unit := do
  let goal ← getMainGoal
  let verify (p : Lean.Expr) : TacticM Lean.Expr := do
    try verifyClosedCheck p maxHeartbeats
    catch error =>
      if error.isInterrupt then throw error
      let advice := resourceAdvice "the coefficient check" maxHeartbeats (← resourceLimit? error)
      throwError "interval: the kernel refused the coefficient check: {error.toMessageData}{advice}"
  let attempt (route : TacticM Coeff.Outcome) : TacticM (Except Exception Coeff.Outcome) := do
    let saved ← saveState
    try return .ok (← route)
    catch error =>
      if error.isInterrupt then throw error
      saved.restore
      return .error error
  match ← attempt (Coeff.run goal certs verify) with
  | .ok .proved => replaceMainGoal []; return
  | .ok .notMine =>
      if certs.isEmpty then
        if let some boxGoal ← introInterval? goal then
          setGoals [boxGoal]
          close precision degree depth maxHeartbeats
          return
  | .error error =>
      -- a bound on a whole interval may still follow from boxes
      if certs.isEmpty then
        if let some boxGoal ← introInterval? goal then
          let saved ← saveState
          setGoals [boxGoal]
          try close precision degree depth maxHeartbeats; return
          catch boxError =>
            if boxError.isInterrupt then throw boxError
            saved.restore
            throwError "{error.toMessageData}\nThe boxes did not prove it either: \
              {boxError.toMessageData}"
      throw error
  unless certs.isEmpty do
    match ← attempt (Coeff.runFree goal certs verify) with
    | .ok .proved => replaceMainGoal []; return
    | .ok .notMine => throwError "interval: `lower` and `upper` are certificates for a bound on \
        a polynomial or series over its whole domain, and this goal is not one"
    | .error error => throw error
  try close precision degree depth maxHeartbeats
  catch boxError =>
    if boxError.isInterrupt then throw boxError
    match ← attempt (Coeff.runFree goal certs verify) with
    | .ok .proved => replaceMainGoal []
    | .ok .notMine => throw boxError
    | .error error => throwError "{boxError.toMessageData}\nThe coefficient route did not prove \
        it either: {error.toMessageData}"

end FloatLib.Numerics.Interval.Tactic

/--
Prove a real or nonnegative-real inequality from rational bounds in the local context.

`interval (precision := 64) (degree := 16) (depth := 8)` uses a binary endpoint grid with 64
fractional bits, degree-16 elementary enclosures, and at most eight midpoint subdivisions along any
branch, and these are also the defaults. Each verification attempt and the failure diagnostics have
budgets of 20,000 heartbeats apiece, even when the surrounding declaration disables heartbeat
limits. Use `(maxHeartbeats := 40000)` for a larger finite budget.

Algebraic goals first use exact rational endpoints without subdivision, which keeps equality at
non-dyadic hypothesis bounds. For arithmetic without registered calls, an advisory executable check
rejects failing binary-grid leaves before kernel reduction. Registered calls go straight to bounded
kernel reduction, and every successful proof requires kernel verification. Concrete finite sums and
matrix expressions are expanded automatically, pointwise bounds such as `∀ i, x i ∈ Set.Icc 0 1`
included, and norms use the instances selected in the goal.

Each enclosure has an accepted domain, which is a condition on the computed enclosure and not on the
real function:

* division needs a denominator enclosure that excludes zero,
* the logarithm needs an argument enclosure with a positive lower endpoint, and the square root one
  with a nonnegative lower endpoint,
* inverse sine and cosine need an argument enclosure inside `[-1, 1]`, and tangent a cosine
  enclosure that excludes zero.

A failure restores the original proof state and names the operation whose enclosure was rejected or
the bound that wasn't small enough. It suggests a larger `maxHeartbeats`, naming the attempt, only
when kernel verification of that attempt ran out of its heartbeat budget.

A bound over a whole domain is proved from coefficients first, where boxes would never finish:

* `∀ u : ℝ, lo ≤ S u`, `S u ≤ hi`, `|S u| ≤ c` and the strict versions, for a trigonometric
  polynomial `S` with cosine and sine terms,
* the same under `∀ x ∈ Set.Icc lo hi` for a polynomial in `x` or a Chebyshev series at a point of
  `[-1, 1]`,
* `∀ z : ℂ, ‖z‖ = 1 → ‖p z‖ ≤ c` or `c ≤ ‖p z‖` for a polynomial with Gaussian rational
  coefficients.

Without options the coefficients alone give the bound, the constant term plus or minus the sum of
the absolute values of the others. `(lower := h)` and `(upper := h)` take a sum-of-squares
certificate for that side: a list of integers, a file of integers next to the source, or a pair
`(p, q)` for a factor `p + i q`. `scripts/coeff_cert.py` writes them. On an interval the boxes run
when the coefficients fail, and a trigonometric polynomial in a free variable goes to the
coefficients when the boxes find no bounds for it.
-/
syntax (name := interval) "interval" (ppSpace "(" ident " := " term ")")* : tactic

elab_rules : tactic
  | `(tactic| interval $[($option:ident := $value:term)]*) => do
    let mut precision := 64
    let mut degree := 16
    let mut depth := 8
    let mut maxHeartbeats := 20000
    let mut certs : FloatLib.Numerics.Interval.Tactic.Coeff.Certs := {}
    let mut seen : Array Name := #[]
    for option in option, value in value do
      let key := option.getId.eraseMacroScopes
      if seen.contains key then
        throwErrorAt option "duplicate interval option {key}"
      seen := seen.push key
      let term : Term := ⟨value⟩
      let number : Option Nat := value.isNatLit?
      match key, number with
      | `precision, some v => precision := v
      | `degree, some v => degree := v
      | `depth, some v => depth := v
      | `maxHeartbeats, some v =>
        maxHeartbeats := v
        if maxHeartbeats == 0 then
          throwErrorAt value "interval maxHeartbeats must be positive"
      | `precision, none | `degree, none | `depth, none | `maxHeartbeats, none =>
        throwErrorAt value "interval {key} must be a natural number literal"
      | `lower, _ => certs := { certs with lower := some term }
      | `upper, _ => certs := { certs with upper := some term }
      | _, _ =>
        throwErrorAt option "expected precision, degree, depth, maxHeartbeats, lower, or upper"
    let saved ← saveState
    discard <| tryFinally'
      (FloatLib.Numerics.Interval.Tactic.run precision degree depth maxHeartbeats certs)
      (fun result => unless result.isSome do saved.restore)
