/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.ConstraintProof
public meta import FloatLib.Tactic.Interval
public meta import FloatLib.Numerics.Enclosure.Expression.Constraint

/-!
# Reifying propositions to constraints

`reifyProp` turns a proposition into a `Constraint` that it implies, with the construction of the
proof. It reads combinations by `∧`, `∨`, `¬` and `→` of `≤`, `<`, `=` and `≠` between real
expressions, pushes negations to the comparisons, and unfolds everything else (membership in a
set, named sets) until a connective or a comparison appears. A part that gives no real constraint
is left out of a conjunction and voids a disjunction, both of which weaken the constraint, so the
implication stays true.

The expressions of all comparisons share one reification state, and with it one numbering of the
atoms. A `Piece` therefore carries the construction of its proof and not the proof: the proof
mentions the list of all atoms, which is known only when every hypothesis has been read.

## Main definitions

* `Atom`, `Tree`: the data of a reified constraint that the search and the messages read.
* `Literal`: a comparison that holds outright, with its proof.
* `Piece`, `Piece.conj`, `Piece.disj`: a reified proposition and its combinations.
* `reifyProp`: the reification.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

initialize registerTraceClass `interval.constraints

initialize registerTraceClass `interval.constraints.time

/-- Run a step of the route as a node of the trace class `interval.constraints.time`. With
`set_option trace.profiler true` the node reports the time that the step took. -/
def timed {m : Type → Type} {α : Type} [Monad m] [MonadTrace m] [MonadRef m]
    [AddMessageContext m] [MonadOptions m] [MonadAlwaysExcept Exception m] [MonadLiftT BaseIO m]
    (label : String) (step : m α) : m α :=
  withTraceNode `interval.constraints.time (fun _ => return m!"{label}") step

/-- One atom of a reified constraint, as the search and the messages read it. -/
structure Atom where
  /-- The relation whose failure is the atom. -/
  relation : Relation
  /-- The expression, the right side minus the left side of the stated comparison. -/
  expr : Interval.Expr
  /-- The comparison as a proposition, `a ≤ b` or `a < b`. -/
  source : Lean.Expr
  /-- The variables of the expression. -/
  vars : Array Nat

/-- A reified constraint with the data of its atoms. -/
inductive Tree where
  /-- A failed comparison and its reified expression. -/
  | atom (a : Atom)
  /-- A form atom, with the proposition it was derived from for the messages. -/
  | form (strict : Bool) (f : Form) (source : MessageData)
  /-- Both subconstraints hold. -/
  | and (left right : Tree)
  /-- At least one subconstraint holds. -/
  | or (left right : Tree)

/-- A comparison `lhs ≤ rhs`, or `lhs < rhs` when `strict`, that holds outright: under no case
distinction of the hypotheses. These are the sources of bounds and of quadratic forms. -/
structure Literal where
  /-- Whether the comparison is strict. -/
  strict : Bool
  /-- The smaller side. -/
  lhs : Q(ℝ)
  /-- The larger side. -/
  rhs : Q(ℝ)
  /-- The proof of the comparison. -/
  proof : Lean.Expr

/-- The two sides of each comparison, for the steps that look for subterms. -/
def sidesOf (literals : Array Literal) : Array Lean.Expr :=
  literals.foldl (fun sides literal => (sides.push literal.lhs).push literal.rhs) #[]

/-- A proof of a proposition by `positivity`, if it finds one. -/
def positivityProof? (statement : Q(Prop)) : MetaM (Option Q($statement)) := do
  let goal ← mkFreshExprMVar statement
  try
    Mathlib.Meta.Positivity.positivity goal.mvarId!
    return some (← mkExpectedTypeHint (← instantiateMVars goal) statement)
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none

/-- A proof of a proposition by `linarith` from the given facts and no others, if it finds
one. The hypotheses of the goal are left out: the steps that call this give the comparisons
they mean, and `linarith` reads every fact it is given before it starts. -/
def linarithProof? (statement : Q(Prop)) (facts : Array Lean.Expr) :
    Lean.Elab.Tactic.TacticM (Option Q($statement)) := do
  let goal ← mkFreshExprMVar statement
  let hints ← facts.mapM fun proof => Lean.Elab.Term.exprToSyntax proof
  try
    let remaining ← Lean.Elab.Tactic.run goal.mvarId!
      (Lean.Elab.Tactic.evalTactic (← `(tactic| linarith only [$hints,*])))
    unless remaining.isEmpty do return none
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none
  return some (← instantiateMVars goal)

/-- The variables of an expression, each once. -/
partial def exprVars (e : Interval.Expr) (acc : Array Nat := #[]) : Array Nat :=
  match e with
  | .const _ => acc
  | .var i => if acc.contains i then acc else acc.push i
  | .unary _ a => exprVars a acc
  | .binary _ a b => exprVars b (exprVars a acc)
  | .ternary _ a b c => exprVars c (exprVars b (exprVars a acc))
  | .call _ args => args.foldl (fun acc a => exprVars a acc) acc

/-- What the proof of a constraint needs once every atom is known. -/
structure BuildContext where
  /-- The real value of each variable. -/
  values : Q(Nat → ℝ)
  /-- The real function of each registered call. -/
  functions : Q(Nat → List ℝ → ℝ)
  /-- The reification state, with the certificates of the rational constants. -/
  cache : ReifyState

/-- The monad in which the proof of a constraint is assembled. It collects the comparisons that
hold outright. -/
abbrev BuildM := ReaderT BuildContext (StateRefT (Array Literal) MetaM)

/--
A reified proposition: its constraint, the data of its atoms, and the construction of a proof
that the constraint holds from a proof of the proposition. The Boolean passed to `prove` says
whether the proposition holds outright, that is, under no case distinction.
-/
structure Piece where
  /-- The constraint. -/
  constraint : Q(Constraint)
  /-- The data of its atoms. -/
  tree : Tree
  /-- A proof of `constraint.Holds values functions` from a proof of the source. -/
  prove : Bool → Lean.Expr → BuildM Lean.Expr

/-- Reify a piece from another source through a proof transformation. -/
def Piece.through (piece : Piece) (f : Lean.Expr → Lean.Expr) : Piece :=
  { piece with prove := fun outright h => piece.prove outright (f h) }

/-- The conjunction of two pieces whose sources follow from one proof. A side without
constraints is dropped. -/
def Piece.conj (a b : Option Piece) (left right : Lean.Expr → Lean.Expr) : Option Piece :=
  match a, b with
  | none, none => none
  | some a, none => some (a.through left)
  | none, some b => some (b.through right)
  | some a, some b =>
    have ca : Q(Constraint) := a.constraint
    have cb : Q(Constraint) := b.constraint
    some {
      constraint := q(Constraint.and $ca $cb)
      tree := .and a.tree b.tree
      prove := fun outright h => do
        let ha ← a.prove outright (left h)
        let hb ← b.prove outright (right h)
        mkAppM ``Constraint.holds_and #[ha, hb] }

/-- The disjunction of two pieces with sources `A` and `B`, from a proof of `A ∨ B`. A side
without constraints leaves no constraint. -/
def Piece.disj (a b : Option Piece) (A B : Q(Prop)) : Option Piece :=
  match a, b with
  | some a, some b =>
    have ca : Q(Constraint) := a.constraint
    have cb : Q(Constraint) := b.constraint
    some {
      constraint := q(Constraint.or $ca $cb)
      tree := .or a.tree b.tree
      prove := fun _ h => do
        let left ← withLocalDeclD `h A fun x => do
          let ha ← a.prove false x
          mkLambdaFVars #[x] (← mkAppOptM ``Constraint.holds_or_left
            #[none, none, some cb, none, some ha])
        let right ← withLocalDeclD `h B fun x => do
          let hb ← b.prove false x
          mkLambdaFVars #[x] (← mkAppOptM ``Constraint.holds_or_right
            #[none, some ca, none, none, some hb])
        mkAppM ``Or.elim #[h, left, right] }
  | _, _ => none

/-- Terms to read in place of others: an atom that has no bounds and its unfolding. -/
abbrev Rewrites := Array (Lean.Expr × Lean.Expr)

/-- Replace every occurrence of a rewritten term, also in the terms that replace others. -/
def Rewrites.apply (rewrites : Rewrites) (e : Q(ℝ)) : Q(ℝ) := Id.run do
  let mut current : Lean.Expr := e
  for _ in [0:rewrites.size] do
    let next := current.replace fun sub => (rewrites.find? (·.1 == sub)).map (·.2)
    if next == current then break
    current := next
  return current

/--
Unfold the head of a real term that is neither arithmetic nor a registered function, until it is
one of these or an application of a local variable: a definition applied to its arguments, an
entry of a vector literal, a field of a structure instance. The result is `none` when nothing
unfolds.
-/
partial def exposeAtom (e : Q(ℝ)) : MetaM (Option Q(ℝ)) :=
  loop e 64 false
where
  /-- Unfold up to `steps` times. -/
  loop (e : Lean.Expr) (steps : Nat) (changed : Bool) : MetaM (Option Lean.Expr) := do
    let reduced ← whnfCore e
    let changed := changed || reduced != e
    let done := pure (if changed then some reduced else none)
    let head := reduced.getAppFn
    if steps == 0 || !head.isConst then return ← done
    if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HPow.hPow, ``Neg.neg, ``Inv.inv,
        ``abs, ``Max.max, ``Min.min, ``OfNat.ofNat].contains head.constName! then return ← done
    if (← registeredApplication? reduced).isSome then return ← done
    match ← unfoldDefinition? reduced with
    | some unfolded => loop unfolded (steps - 1) true
    | none => done

/-- The piece of one comparison `a ≤ b` (or `a < b` when `strict`), from a proof of it. The
sides are read with the given rewrites. -/
def atomPiece (rewrites : Rewrites) (strict : Bool) (a b : Q(ℝ)) :
    StateRefT ReifyState MetaM Piece := do
  have a : Q(ℝ) := rewrites.apply a
  have b : Q(ℝ) := rewrites.apply b
  let difference : Q(ℝ) := q($b - $a)
  let normalized ← normalizeAggregates difference
  have scalar : Q(ℝ) := normalized.expr
  let expression ← reify scalar
  let value ← Diagnostics.readExpr expression true
  have source : Q(Prop) := if strict then q($a < $b) else q($a ≤ $b)
  let relation : Relation := if strict then .nonpositive else .negative
  have quoted : Q(Relation) := if strict then q(Relation.nonpositive) else q(Relation.negative)
  return {
    constraint := q(Constraint.fails $quoted $expression)
    tree := .atom { relation, expr := value, source, vars := exprVars value }
    prove := fun outright h => do
      -- The proof is recorded with the comparison as its stated type, which is what the
      -- readers of bounds and `linarith` look at.
      if outright then
        modify (·.push { strict, lhs := a, rhs := b, proof := ← mkExpectedTypeHint h source })
      let ctx ← read
      have values : Q(Nat → ℝ) := ctx.values
      have functions : Q(Nat → List ℝ → ℝ) := ctx.functions
      let expanded : Q($difference = $scalar) ← normalized.getProof
      let interpreted : Q($scalar = Interval.Expr.eval $expression $values $functions) ←
        evalEquality scalar expression values ctx.cache functions
      let equality : Q($b - $a = Interval.Expr.eval $expression $values $functions) :=
        q(Eq.trans $expanded $interpreted)
      if strict then
        have h : Q($a < $b) := h
        return q(Constraint.holds_of_lt $equality $h)
      else
        have h : Q($a ≤ $b) := h
        return q(Constraint.holds_of_le $equality $h) }

/-- The piece of a contradiction, from a proof of `False`: an atom that fails on every box. -/
def falsePiece : Piece :=
  have constraint : Q(Constraint) :=
    q(Constraint.fails Relation.nonpositive (Interval.Expr.const 0))
  { constraint
    tree := .atom { relation := .nonpositive, expr := .const 0, source := q(False), vars := #[] }
    prove := fun _ h => do
      let ctx ← read
      return mkApp4 (mkConst ``Constraint.holds_of_false) constraint ctx.values ctx.functions h }

/-- Unfold the head of a proposition until a connective or a comparison appears, and no
further. A comparison of sets or of functions is not one: it is unfolded to the comparison of
their values. -/
def exposeProp (P : Lean.Expr) : MetaM Lean.Expr :=
  whnfHeadPred P fun e => do
    if e.isForall then return false
    if [``LE.le, ``LT.lt, ``GE.ge, ``GT.gt].any e.isAppOf then
      let carrier ← whnfR (e.getArg! 0)
      return carrier.isAppOf ``Set || carrier.isForall
    return !([``And, ``Or, ``Not, ``Eq, ``True, ``False, ``Ne, ``Iff, ``Exists].any e.isAppOf)

/--
Reify a proposition, or its negation when `positive` is false, to a constraint that it implies.
The result is `none` when the proposition gives no real constraint: a part that isn't a
combination of real comparisons is left out of a conjunction and voids a disjunction.
-/
partial def reifyProp (rewrites : Rewrites) (positive : Bool) (P : Q(Prop)) :
    StateRefT ReifyState MetaM (Option Piece) :=
  withIncRecDepth do
    checkSystem "interval constraints"
    let P : Q(Prop) ← whnfR (← instantiateMVars P)
    match_expr P with
    | And p q =>
      have p : Q(Prop) := p
      have q : Q(Prop) := q
      let a ← reifyProp rewrites positive p
      let b ← reifyProp rewrites positive q
      if positive then
        return Piece.conj a b
          (fun h => have h : Q($p ∧ $q) := h; q(And.left $h))
          (fun h => have h : Q($p ∧ $q) := h; q(And.right $h))
      else
        return (Piece.disj a b q(¬ $p) q(¬ $q)).map
          (·.through fun h => have h : Q(¬ ($p ∧ $q)) := h; q(not_and_or.mp $h))
    | Or p q =>
      have p : Q(Prop) := p
      have q : Q(Prop) := q
      let a ← reifyProp rewrites positive p
      let b ← reifyProp rewrites positive q
      if positive then
        return Piece.disj a b p q
      else
        return Piece.conj a b
          (fun h => have h : Q(¬ ($p ∨ $q)) := h; q((not_or.mp $h).1))
          (fun h => have h : Q(¬ ($p ∨ $q)) := h; q((not_or.mp $h).2))
    | Not p =>
      have p : Q(Prop) := p
      let piece ← reifyProp rewrites (!positive) p
      if positive then return piece
      else return piece.map (·.through fun h => have h : Q(¬ ¬ $p) := h; q(not_not.mp $h))
    | True => if positive then return none else
      return some (falsePiece.through fun h => have h : Q(¬ True) := h; q($h trivial))
    | False => if positive then return some falsePiece else return none
    | LE.le α _ a b =>
      unless ← isDefEq α q(ℝ) do return none
      have a : Q(ℝ) := a
      have b : Q(ℝ) := b
      unless ← isDefEq P q($a ≤ $b) do return none
      if positive then return some (← atomPiece rewrites false a b)
      else return some ((← atomPiece rewrites true b a).through fun h =>
        have h : Q(¬ $a ≤ $b) := h; q(not_le.mp $h))
    | LT.lt α _ a b =>
      unless ← isDefEq α q(ℝ) do return none
      have a : Q(ℝ) := a
      have b : Q(ℝ) := b
      unless ← isDefEq P q($a < $b) do return none
      if positive then return some (← atomPiece rewrites true a b)
      else return some ((← atomPiece rewrites false b a).through fun h =>
        have h : Q(¬ $a < $b) := h; q(not_lt.mp $h))
    | Eq α a b =>
      unless ← isDefEq α q(ℝ) do return none
      have a : Q(ℝ) := a
      have b : Q(ℝ) := b
      if positive then
        return Piece.conj (some (← atomPiece rewrites false a b))
          (some (← atomPiece rewrites false b a))
          (fun h => have h : Q($a = $b) := h; q(le_of_eq $h))
          (fun h => have h : Q($a = $b) := h; q(le_of_eq (Eq.symm $h)))
      else
        return (Piece.disj (some (← atomPiece rewrites true a b))
          (some (← atomPiece rewrites true b a)) q($a < $b) q($b < $a)).map
          (·.through fun h => have h : Q(¬ $a = $b) := h; q(lt_or_gt_of_ne $h))
    | _ =>
      if let some (p, q) := P.arrow? then
        if ← isProp p then
          have p : Q(Prop) := p
          have q : Q(Prop) := q
          let a ← reifyProp rewrites (!positive) p
          let b ← reifyProp rewrites positive q
          if positive then
            return (Piece.disj a b q(¬ $p) q).map
              (·.through fun h => have h : Q($p → $q) := h; q(not_or_of_imp $h))
          else
            return Piece.conj a b
              (fun h => have h : Q(¬ ($p → $q)) := h; q((not_imp.mp $h).1))
              (fun h => have h : Q(¬ ($p → $q)) := h; q((not_imp.mp $h).2))
        return none
      let reduced ← exposeProp P
      if reduced == P then return none
      reifyProp rewrites positive reduced

/--
A proposition with the definitions at the heads of its parts unfolded, so that its combination by
`∧`, `∨`, `¬` and `→` of comparisons is visible: membership in a set that a predicate defines
becomes the predicate at the point. The result is definitionally equal to the proposition, and a
part that isn't such a combination is returned as it is.
-/
partial def exposeAll (P : Lean.Expr) : MetaM Lean.Expr := do
  let P ← instantiateMVars P
  let exposed ← exposeProp P
  match_expr exposed with
  | And p q => return mkAnd (← exposeAll p) (← exposeAll q)
  | Or p q => return mkOr (← exposeAll p) (← exposeAll q)
  | Not p => return mkNot (← exposeAll p)
  | LE.le _ _ _ _ => return exposed
  | LT.lt _ _ _ _ => return exposed
  | GE.ge _ _ _ _ => return exposed
  | GT.gt _ _ _ _ => return exposed
  | Eq _ _ _ => return exposed
  | Ne _ _ _ => return exposed
  | True => return exposed
  | False => return exposed
  | _ =>
    if exposed.isArrow then
      return ← mkArrow (← exposeAll exposed.bindingDomain!) (← exposeAll exposed.bindingBody!)
    return P

/-- Unfold the hypotheses of a goal as `exposeAll` does, so that the steps that rewrite
hypotheses find the comparisons behind definitions. -/
def exposeHypotheses (goal : MVarId) : MetaM MVarId := goal.withContext do
  let mut goal := goal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    let type ← instantiateMVars decl.type
    let exposed ← exposeAll type
    unless exposed == type do
      goal ← goal.replaceLocalDeclDefEq decl.fvarId exposed
  return goal

/--
Turn each local definition `y := v` of a real number into a variable `y` with the hypothesis
`y = v`. The variable is then an atom of the constraints with the bounds that the equation gives
it, so a comparison in `y` keeps the form that the statement gave it.
-/
partial def definitionsToEquations (goal : MVarId) : MetaM MVarId := goal.withContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail || !decl.isLet then continue
    unless (← instantiateMVars decl.type).isConstOf ``Real do continue
    let equation ← mkEq decl.toExpr decl.value
    let (_, next) ← (← goal.assert `definition equation
      (← mkExpectedTypeHint (← mkEqRefl decl.toExpr) equation)).intro1P
    return ← definitionsToEquations (← next.clearValue decl.fvarId)
  return goal

/--
Replace each hypothesis `∀ i : Fin n, P i`, for a numeral `n` of at most `limit`, by its
instances `P 0`, …, `P (n - 1)`, so that a constraint that is stated for every coordinate of a
vector is read for each of them.
-/
partial def instantiateFinite (goal : MVarId) (limit : Nat := 32) : MetaM MVarId :=
  goal.withContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      unless ← isProp type do continue
      let .forallE _ domain body _ := type | continue
      unless body.hasLooseBVars && domain.isAppOfArity ``Fin 1 do continue
      let some n := (← instantiateMVars domain.appArg!).nat? | continue
      unless 0 < n && n ≤ limit do continue
      let mut instances : Array Hypothesis := #[]
      for k in [0:n] do
        let index ← mkNumeral domain k
        instances := instances.push
          { userName := decl.userName, type := (body.instantiate1 index).headBeta,
            value := mkApp decl.toExpr index }
      let (_, next) ← goal.assertHypotheses instances
      return ← instantiateFinite (← next.tryClear decl.fvarId) limit
    return goal

/--
Bring the hypotheses of a goal to a form in which their cases are visible: an implication
between propositions becomes a disjunction, an equivalence a disjunction of two conjunctions, and
negations are pushed inward, so that the negation of a conjunction is a disjunction, that of a
disjunction a conjunction, and that of `≤` or `<` the reverse comparison. A goal that is a
conjunction is proved by refuting its negation, and the steps that split hypotheses then see its
cases.
-/
def pushNegations (goal : MVarId) : MetaM MVarId := do
  -- implications first: each becomes a disjunction, as a new hypothesis in place of the old
  let mut goal := goal
  let implications ← goal.withContext do
    let mut found : Array (FVarId × Hypothesis) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let type ← instantiateMVars decl.type
      unless type.isArrow do continue
      unless ← isProp type.bindingDomain! do continue
      unless ← isProp type do continue
      let proof ← mkAppM ``not_or_of_imp #[decl.toExpr]
      found := found.push (decl.fvarId,
        { userName := decl.userName, type := ← inferType proof, value := proof })
    return found
  unless implications.isEmpty do
    let (_, next) ← goal.assertHypotheses (implications.map (·.2))
    goal ← next.tryClearMany (implications.map (·.1))
  let rules ← [``not_and_or, ``not_or, ``not_not, ``not_le, ``not_lt, ``not_imp,
    ``iff_iff_and_or_not_and_not].foldlM
    (fun rules name => rules.addConst name) ({} : SimpTheorems)
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let count := (← goal.withContext getLCtx).foldl (fun n _ => n + 1) 0
  -- a rewritten hypothesis keeps its place, so the hypotheses are visited by position
  for position in [0:count] do
    let decl? := (← goal.withContext getLCtx).foldl (init := (0, none)) fun (k, found) decl =>
      (k + 1, if k == position then some decl else found)
    let some decl := decl?.2 | continue
    if decl.isImplementationDetail then continue
    let negated ← goal.withContext do
      unless ← isProp decl.type do return false
      return ((← instantiateMVars decl.type).find? fun e =>
        e.isAppOf ``Not || e.isAppOf ``Iff).isSome
    unless negated do continue
    let (result?, _) ← simpLocalDecl goal decl.fvarId context (mayCloseGoal := false)
    if let some (_, next) := result? then goal := next
  return goal

/--
Replace a real term by another in the hypotheses of a goal that contain it, except those that
`skip` holds back, given a proof that the two are equal. The result is the goal with the
rewritten hypotheses in place of the old ones, and whether there was one.
-/
def rewriteHypotheses (goal : MVarId) (term replacement equation : Lean.Expr)
    (skip : LocalDecl → MetaM Bool := fun _ => pure false) : MetaM (MVarId × Bool) :=
  goal.withContext do
    let mut targets : Array LocalDecl := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless ← isProp decl.type do continue
      unless ((← instantiateMVars decl.type).find? (· == term)).isSome do continue
      unless ← skip decl do targets := targets.push decl
    if targets.isEmpty then return (goal, false)
    let copies ← targets.mapM fun decl => do
      let abstracted ← kabstract (← instantiateMVars decl.type) term
      let motive := Lean.Expr.lam `t q(ℝ) abstracted .default
      let proof ← mkEqMP (← mkCongrArg motive equation) decl.toExpr
      let copy : Hypothesis :=
        { userName := decl.userName, type := abstracted.instantiate1 replacement, value := proof }
      return copy
    let (_, next) ← goal.assertHypotheses copies
    return (← next.tryClearMany (targets.map (·.fvarId)), true)

/-- Make each conjunct of a hypothesis that is a conjunction a hypothesis of its own, so that a
step that rewrites one comparison leaves the others as they are. -/
partial def splitConjunctions (goal : MVarId) : MetaM MVarId := goal.withContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← instantiateMVars decl.type
    match_expr type with
    | And p q =>
      let (_, next) ← goal.assertHypotheses #[
        { userName := decl.userName, type := p,
          value := mkApp3 (mkConst ``And.left) p q decl.toExpr },
        { userName := decl.userName, type := q,
          value := mkApp3 (mkConst ``And.right) p q decl.toExpr }]
      return ← splitConjunctions (← next.tryClear decl.fvarId)
    | _ => continue
  return goal

/-- Whether a proposition, unfolded, is a disjunction or a conjunction that contains one. -/
partial def hasCases (type : Lean.Expr) : MetaM Bool := do
  let type ← exposeProp (← instantiateMVars type)
  match_expr type with
  | Or _ _ => return true
  | And p q => return (← hasCases p) || (← hasCases q)
  | _ => return false

/--
Split a goal at the disjunctions among its hypotheses, also inside conjunctions: one goal for
each case, in which the case is a hypothesis of its own. The result is `none` when no hypothesis
has a disjunction, or when there would be more than `limit` goals.
-/
partial def splitCases (goal : MVarId) (limit : Nat := 16) : MetaM (Option (List MVarId)) := do
  let rec go (goals : List MVarId) (changed : Bool) (fuel : Nat) : MetaM (Option (List MVarId)) :=
    do
    if goals.length > limit then return none
    if fuel == 0 then return if changed then some goals else none
    -- the first goal with a hypothesis to split
    for goal in goals, index in [0:goals.length] do
      let found ← goal.withContext do
        for decl in ← getLCtx do
          if decl.isImplementationDetail then continue
          unless ← isProp decl.type do continue
          if ← hasCases decl.type then
            return some (decl.fvarId, ← exposeProp (← instantiateMVars decl.type))
        return none
      if let some (fvar, exposed) := found then
        let goal ← goal.replaceLocalDeclDefEq fvar exposed
        let subgoals ← goal.cases fvar
        let pieces := subgoals.toList.map (·.mvarId)
        return ← go (goals.take index ++ pieces ++ goals.drop (index + 1)) true (fuel - 1)
    return if changed then some goals else none
  go [goal] false 64

/-- Whether a hypothesis is an existential statement or a conjunction that contains one. -/
partial def hasExists (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR (← instantiateMVars type)
  match_expr type with
  | Exists _ _ => return true
  | And p q => return (← hasExists p) || (← hasExists q)
  | _ => return false

/-- Open the existential hypotheses of a goal, also inside conjunctions. A witness keeps the name
that its binder has in the statement. -/
partial def openExists (goal : MVarId) : MetaM MVarId := goal.withContext do
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← whnfR (← instantiateMVars decl.type)
    let names? : Option (List Name) ← match_expr type with
      | Exists _ p => pure (some [if let .lam name _ _ _ := p then name else `w, decl.userName])
      | And p q =>
        if (← hasExists p) || (← hasExists q) then pure (some [decl.userName, decl.userName])
        else pure none
      | _ => pure none
    if let some names := names? then
      let #[subgoal] ← goal.cases decl.fvarId #[{ varNames := names }]
        | throwError "interval: opening an existential hypothesis did not leave one goal"
      return ← openExists subgoal.mvarId
  return goal
end FloatLib.Numerics.Interval.Tactic.Constraints
