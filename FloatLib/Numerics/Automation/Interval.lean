/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.IntervalReify
public import FloatLib.Numerics.Enclosure.Expression.BackendsProof
public import FloatLib.Numerics.Enclosure.Expression.CheckProof
public meta import FloatLib.Numerics.Automation.IntervalDiagnostics
public meta import FloatLib.Numerics.Automation.IntervalEquality
public meta import Lean.Elab.Tactic.Decide

/-!
# Interval proofs from rational bounds

`interval` proves real inequalities by evaluating certified interval expressions. It reads rational
bounds from the local context, uses integer endpoints on a binary grid, and subdivides the widest
input interval when the first enclosure is inconclusive.

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

/-- A bounded real atom, with explicit proofs of its rational endpoints. -/
structure Coordinate where
  /-- Real subexpression represented by this coordinate. -/
  term : Q(ℝ)
  /-- Quoted rational lower endpoint. -/
  lo : Q(ℚ)
  /-- Quoted rational upper endpoint. -/
  hi : Q(ℚ)
  /-- Proof that the lower endpoint is below the real term. -/
  lower : Q(($lo : ℝ) ≤ $term)
  /-- Proof that the real term is below the upper endpoint. -/
  upper : Q($term ≤ ($hi : ℝ))

/-- Select the strongest rational lower and upper bounds available for one atom. -/
def coordinate (atom : Q(ℝ)) (bounds : Array Bound) : MetaM Coordinate := do
  let mut lower : Option Bound := none
  let mut upper : Option Bound := none
  for bound in bounds do
    unless ← withReducible (isDefEq atom bound.term) do continue
    if bound.lower then
      if lower.all (·.value < bound.value) then lower := some bound
    else
      if upper.all (bound.value < ·.value) then upper := some bound
  let some lowerBound := lower
    | throwError "interval needs a rational lower bound for {atom}"
  let some upperBound := upper
    | throwError "interval needs a rational upper bound for {atom}"
  return ⟨atom, lowerBound.rational, upperBound.rational, lowerBound.proof, upperBound.proof⟩

/-- A rational box and the proof that its ordered real coordinates belong to it. -/
structure ReifiedBox where
  /-- Rational intervals in variable-index order. -/
  box : Q(Box)
  /-- Real terms in the same order as the box coordinates. -/
  reals : Q(List ℝ)
  /-- Proof that each real term belongs to its corresponding interval. -/
  membership : Q(Box.ContainsReal $box (fun i => $reals[i]?.getD 0))

/-- Assemble box membership directly from the selected hypotheses. -/
def reifyBox : List Coordinate → MetaM ReifiedBox
  | [] => do
    let box : Q(Box) := q([])
    let reals : Q(List ℝ) := q([])
    let membership : Lean.Expr := q(Box.containsReal_nil (fun i => ([] : List ℝ)[i]?.getD 0))
    return ⟨box, reals, membership⟩
  | head :: tail => do
    let tail ← reifyBox tail
    let term : Q(ℝ) ← pure head.term
    let lo : Q(ℚ) ← pure head.lo
    let hi : Q(ℚ) ← pure head.hi
    let lower : Q(($lo : ℝ) ≤ $term) ← pure head.lower
    let upper : Q($term ≤ ($hi : ℝ)) ← pure head.upper
    let rest : Q(Box) ← pure tail.box
    let restReals : Q(List ℝ) ← pure tail.reals
    let restProof : Q(Box.ContainsReal $rest (fun i => $restReals[i]?.getD 0)) ←
      pure tail.membership
    let box : Q(Box) := q(⟨$lo, $hi⟩ :: $rest)
    let reals : Q(List ℝ) := q($term :: $restReals)
    let headProof : Q(($lo : ℝ) ≤ $term ∧ $term ≤ ($hi : ℝ)) ←
      pure q(And.intro $lower $upper)
    let membership : Lean.Expr :=
      q(Box.containsReal_cons
        (I := ⟨$lo, $hi⟩) (box := $rest)
        (values := fun i => ($term :: $restReals)[i]?.getD 0) $headProof $restProof)
    return ⟨box, reals, membership⟩

/-- Produce a complete proof with a tactic, without replacing the caller's goals. -/
def prove (proposition : Q(Prop)) (tactic : Syntax) : TacticM Lean.Expr := do
  let original ← getGoals
  let proof ← mkFreshExprMVar proposition
  try
    setGoals [proof.mvarId!]
    evalTactic tactic
    unless (← getUnsolvedGoals).isEmpty do
      throwError "interval could not close its verification obligation"
    instantiateMVars proof
  finally
    setGoals original

/-- Verify a real or nonnegative-real inequality with the binary-grid backend. -/
def close (precision degree depth : Nat) : TacticM Unit := withMainContext do
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
  let ((expression, cache), atoms) ← (reifyScalarWithCache scalar).run #[]
  let mut bounds := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isProp decl.type then
      bounds := bounds ++ (← boundsOfProofFor atoms decl.toExpr)
  let coordinates ← atoms.toList.mapM (fun atom => coordinate atom bounds)
  let data ← reifyBox coordinates
  let box : Q(Box) ← pure data.box
  let reals : Q(List ℝ) ← pure data.reals
  let membership : Q(Box.ContainsReal $box (fun i => $reals[i]?.getD 0)) ←
    pure data.membership
  let values : Q(Nat → ℝ) ← pure q(fun i => $reals[i]?.getD 0)
  let precision : Q(Nat) ← pure (mkNatLit precision)
  let degree : Q(Nat) ← pure (mkNatLit degree)
  let depth : Q(Nat) ← pure (mkNatLit depth)
  let config : Q(Backend.Config) ← pure q(⟨$precision, $degree⟩)
  let backend : Q(Backend Int) ← pure q(Backend.binaryGrid $config)
  let relation : Q(Relation) ← pure (if strict then q(.negative) else q(.nonpositive))
  let expanded : Q($difference = $scalar) ← normalized.getProof
  let interpreted : Q($scalar = Interval.Expr.eval $expression $values) ←
    evalEquality scalar expression values cache
  let equality : Q($difference = Interval.Expr.eval $expression $values) :=
    q(Eq.trans $expanded $interpreted)
  let checked : Q(Interval.Expr.check $expression $backend $relation $box $depth = true) ←
    try
      prove q(Interval.Expr.check $expression $backend $relation $box $depth = true)
        (← `(tactic| decide +kernel))
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      throwError (← diagnoseFailure expression box config relation depth atoms)
  -- All arguments are known; assembling the application avoids re-elaborating the closed check.
  let sound := mkAppN (mkConst ``Interval.Expr.check_sound [Level.zero])
    #[q(Int), expression, backend, q(Backend.binaryGrid_sound $config),
      relation, box, depth, checked, values, membership]
  let proof ← if strict then do
    let h : Q(Interval.Expr.eval $expression $values < 0) := sound
    let h : Q($lhs - $rhs < 0) := q((Eq.symm $equality) ▸ $h)
    pure q(sub_neg.mp $h)
  else do
    let h : Q(Interval.Expr.eval $expression $values ≤ 0) := sound
    let h : Q($lhs - $rhs ≤ 0) := q((Eq.symm $equality) ▸ $h)
    pure q(sub_nonpos.mp $h)
  closeMainGoal `interval proof

end FloatLib.Numerics.Interval.Tactic

/--
Prove a real or nonnegative-real inequality from rational bounds in the local context.

For example, `interval (precision := 64) (degree := 16) (depth := 8)` chooses a binary
endpoint grid with 64 fractional bits, degree-16 elementary enclosures, and at most eight
midpoint subdivisions along any branch. These are also the defaults.

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
      | _ => throwErrorAt option "expected precision, degree, or depth"
    let saved ← saveState
    discard <| tryFinally'
      (FloatLib.Numerics.Interval.Tactic.close precision degree depth)
      (fun result => unless result.isSome do saved.restore)
