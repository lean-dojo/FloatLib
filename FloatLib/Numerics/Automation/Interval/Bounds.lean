/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Numerics.Automation.Interval.Reify

/-!
# Hypothesis bounds and certified input boxes

Direct and pointwise hypotheses supply rational endpoints for the real atoms discovered by the
reifier. The strongest endpoints form the input box, with a proof of each coordinate's membership.
Strict hypotheses are conservatively weakened; unresolved indices or guards supply no bounds.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

/-- A rational lower or upper bound, carrying a proof of the real inequality. -/
structure Bound where
  /-- Real term bounded by this hypothesis. -/
  term : Q(ℝ)
  /-- Rational endpoint, used to select the strongest available bound. -/
  value : ℚ
  /-- Quoted syntax of that endpoint. -/
  rational : Q(ℚ)
  /-- Whether the endpoint is a lower bound rather than an upper bound. -/
  lower : Bool
  /-- Proof of `rational ≤ term` when `lower` is true, and of `term ≤ rational` otherwise. -/
  proof : Lean.Expr

/-- Convert either rational side of a weak inequality into an endpoint bound. -/
private def boundsOfLE {a b : Q(ℝ)} (h : Q($a ≤ $b)) : MetaM (Array Bound) := do
  let mut bounds := #[]
  if let some value ← rationalValue? a then
    let q := value.rational
    let he := value.equality
    let proof : Q(($q : ℝ) ≤ $b) := q($he ▸ $h)
    bounds := bounds.push ⟨b, value.value, q, true, proof⟩
  if let some value ← rationalValue? b then
    let q := value.rational
    let he := value.equality
    let proof : Q($a ≤ ($q : ℝ)) := q($he ▸ $h)
    bounds := bounds.push ⟨a, value.value, q, false, proof⟩
  return bounds

/--
Extract bounds from inequalities, equalities, conjunctions, and closed-interval membership.

Strict hypotheses supply weak endpoint bounds. The resulting closed box is sound but may be
too wide to prove a claim whose only margin comes from an open endpoint.
-/
private partial def boundsOfProof (proof : Lean.Expr) : MetaM (Array Bound) := do
  let type : Q(Prop) ← inferType proof
  go type proof
where
  /-- Inspect the proposition, unfolding interval membership and other reducible wrappers. -/
  go (type : Q(Prop)) (proof : Q($type)) : MetaM (Array Bound) := do
    match type with
    | ~q($p ∧ $q) =>
      let h : Q($p ∧ $q) := proof
      return (← boundsOfProof q(And.left $h)) ++ (← boundsOfProof q(And.right $h))
    | ~q(($a : ℝ) ≤ $b) => boundsOfLE (a := a) (b := b) proof
    | ~q(($a : ℝ) < $b) =>
      let h : Q($a < $b) := proof
      boundsOfLE q(le_of_lt $h)
    | ~q(($a : ℝ) = $b) =>
      let h : Q($a = $b) := proof
      return (← boundsOfLE q(le_of_eq $h)) ++ (← boundsOfLE q(le_of_eq (Eq.symm $h)))
    | ~q(($a : NNReal) ≤ $b) =>
      let h : Q($a ≤ $b) := proof
      boundsOfLE q(NNReal.coe_le_coe.mpr $h)
    | ~q(($a : NNReal) < $b) =>
      let h : Q($a < $b) := proof
      boundsOfLE q(le_of_lt (NNReal.coe_lt_coe.mpr $h))
    | ~q(($a : NNReal) = $b) =>
      let h : Q($a = $b) := proof
      let h : Q(($a : ℝ) = ($b : ℝ)) := q(congrArg NNReal.toReal $h)
      return (← boundsOfLE q(le_of_eq $h)) ++ (← boundsOfLE q(le_of_eq (Eq.symm $h)))
    | _ =>
      let reduced ← withTransparency .default (whnf type)
      if reduced == type then return #[]
      go reduced proof

/-- Real terms that may be bounded by a proposition, before instantiating its indices. -/
private partial def boundTerms (type : Lean.Expr) : MetaM (Array Q(ℝ)) := do
  have type : Q(Prop) := type
  match type with
  | ~q($p ∧ $q) => return (← boundTerms p) ++ (← boundTerms q)
  | ~q(($a : ℝ) ≤ $b) | ~q(($a : ℝ) < $b) | ~q(($a : ℝ) = $b) => return #[a, b]
  | ~q(($a : NNReal) ≤ $b) | ~q(($a : NNReal) < $b) | ~q(($a : NNReal) = $b) =>
    return #[q(($a : ℝ)), q(($b : ℝ))]
  | _ =>
    let reduced ← withTransparency .default (whnf type)
    if reduced == type then return #[]
    boundTerms reduced

/-- Discharge a concrete membership or inequality guarding a pointwise bound. -/
private def dischargeBoundGuard (argument : Lean.Expr) : MetaM Bool := do
  let argument ← instantiateMVars argument
  unless argument.isMVar do return !argument.hasMVar
  let type ← instantiateMVars (← inferType argument)
  if type.hasMVar || !(← isProp type) then return false
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← withReducible (isDefEq type decl.type) then
      argument.mvarId!.assign decl.toExpr
      return true
  if let some proof ← decideAggregateGuard? type then
    argument.mvarId!.assign proof
    return true
  return false

/-- Instantiate a pointwise hypothesis only at an entry occurring in the reified expression. -/
private def boundsAtAtom (atom : Q(ℝ)) (type proof : Lean.Expr) : MetaM (Array Bound) :=
  withNewMCtxDepth do
    let (arguments, _, body) ← forallMetaTelescopeReducing type
    if arguments.isEmpty then return #[]
    for term in ← boundTerms body do
      let saved ← saveState
      if ← withReducible (isDefEq atom term) then
        let mut complete := true
        for argument in arguments do
          unless ← dischargeBoundGuard argument do complete := false
        if complete then
          let instantiated ← instantiateMVars (mkAppN proof arguments)
          unless instantiated.hasMVar do
            let mut result := #[]
            for bound in ← boundsOfProof instantiated do
              if ← withReducible (isDefEq atom bound.term) then result := result.push bound
            return result
      saved.restore
    return #[]

/--
Extract direct bounds and instantiate universally quantified bounds at the supplied atoms.

For example, `∀ i, x i ∈ Set.Icc lo hi` supplies the bounds for each used `x i`. Unused entries
are not enumerated. Concrete guards such as `i ∈ Finset.range n` are proved before applying a
guarded hypothesis; an unresolved index or guard supplies no bounds.
-/
partial def boundsOfProofFor (atoms : Array Q(ℝ)) (proof : Lean.Expr) : MetaM (Array Bound) := do
  let type : Q(Prop) ← inferType proof
  match type with
  | ~q($p ∧ $q) =>
    have proof : Q($p ∧ $q) := proof
    return (← boundsOfProofFor atoms q(And.left $proof)) ++
      (← boundsOfProofFor atoms q(And.right $proof))
  | _ =>
    let direct ← boundsOfProof proof
    unless direct.isEmpty do return direct
    let mut result := #[]
    for atom in atoms do
      result := result ++ (← boundsAtAtom atom type proof)
    return result

/-- A rational box and the proof that its ordered real coordinates belong to it. -/
structure ReifiedBox where
  /-- Rational intervals in variable-index order. -/
  box : Q(Box)
  /-- Real terms in the same order as the box coordinates. -/
  reals : Q(List ℝ)
  /-- Proof that each real term belongs to its corresponding interval. -/
  membership : Q(Box.ContainsReal $box (fun i => $reals[i]?.getD 0))

/-- Select the strongest endpoints and prove membership, without an intermediate coordinate. -/
def reifyBox (bounds : Array Bound) : List Q(ℝ) → MetaM ReifiedBox
  | [] => do
    let box : Q(Box) := q([])
    let reals : Q(List ℝ) := q([])
    let membership : Lean.Expr := q(Box.containsReal_nil (fun i => ([] : List ℝ)[i]?.getD 0))
    return ⟨box, reals, membership⟩
  | term :: tail => do
    let mut lower : Option Bound := none
    let mut upper : Option Bound := none
    for bound in bounds do
      unless ← withReducible (isDefEq term bound.term) do continue
      if bound.lower then
        if lower.all (·.value < bound.value) then lower := some bound
      else
        if upper.all (bound.value < ·.value) then upper := some bound
    let some lowerBound := lower
      | throwError "interval needs a rational lower bound for {term}"
    let some upperBound := upper
      | throwError "interval needs a rational upper bound for {term}"
    let lo : Q(ℚ) ← pure lowerBound.rational
    let hi : Q(ℚ) ← pure upperBound.rational
    let lowerProof : Q(($lo : ℝ) ≤ $term) ← pure lowerBound.proof
    let upperProof : Q($term ≤ ($hi : ℝ)) ← pure upperBound.proof
    let tail ← reifyBox bounds tail
    let rest : Q(Box) ← pure tail.box
    let restReals : Q(List ℝ) ← pure tail.reals
    let restProof : Q(Box.ContainsReal $rest (fun i => $restReals[i]?.getD 0)) ←
      pure tail.membership
    let box : Q(Box) := q(⟨$lo, $hi⟩ :: $rest)
    let reals : Q(List ℝ) := q($term :: $restReals)
    let headProof : Q(($lo : ℝ) ≤ $term ∧ $term ≤ ($hi : ℝ)) ←
      pure q(And.intro $lowerProof $upperProof)
    let membership : Lean.Expr :=
      q(Box.containsReal_cons
        (I := ⟨$lo, $hi⟩) (box := $rest)
        (values := fun i => ($term :: $restReals)[i]?.getD 0) $headProof $restProof)
    return ⟨box, reals, membership⟩

end FloatLib.Numerics.Interval.Tactic
