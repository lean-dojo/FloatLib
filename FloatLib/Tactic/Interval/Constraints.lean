/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Tactic.Interval.Constraints.Slopes
public import FloatLib.Numerics.Enclosure.Expression.ConstraintProof
public import Mathlib.Analysis.Real.Pi.Bounds
public import FloatLib.Tactic.Interval.Constraints.Ranges
public import FloatLib.Tactic.Interval.Constraints.Monotone
public meta import FloatLib.Tactic.Interval.Constraints.Derive
public meta import FloatLib.Tactic.Interval.Constraints.Monotone
public meta import FloatLib.Tactic.Interval.Constraints.Ranges
public meta import FloatLib.Tactic.Interval.Constraints.Slopes
public meta import FloatLib.Tactic.Interval.Constraints.Witness
public meta import Lean.Elab.Tactic.FalseOrByContra

/-!
# Refuting sets of real constraints with `interval`

On a goal that is not one inequality, `interval` proves that the real constraints of the goal and
of the local context have no common point. A goal `∃ x : ℝ, P x` is the exception: it is
proved by a witness among simple values and the constants of `P` (`Constraints.Witness`). An
inequality that the route of `Interval` does not prove is refuted in the same way, as the
constraint that it fails. The goal may be `False`, a
negation such as `¬ ∃ x, P x`, an implication to `False` under any binders, or any other
proposition, which is proved by refuting its negation. The constraints are the hypotheses that
are combinations by `∧`, `∨`, `¬` and `→` of `≤`, `<`, `=` and `≠` between real expressions that
the interval layer evaluates; membership in a set, inclusions of sets and other definitions are
unfolded, a local definition of a real becomes a variable with its equation, existential
hypotheses are opened, a hypothesis for every index of a `Fin n` is replaced by its instances,
implications, equivalences and negations are brought to disjunctions and conjunctions, and a
part that isn't of this form is left out.

The proof has three steps.

1. The constraints are reified to one `Constraint` over the atoms of their expressions
   (`Constraints.Reify`), and rational bounds on the atoms are read from the hypotheses as for an
   inequality goal (`Bounds`).
2. A branch and bound search, run as compiled code, evaluates the atoms on the box with three
   values and cuts an undecided box in half (`Constraints.Search`). The result is a `Refutation`:
   a tree of boxes whose leaves name the constraint that fails there.
3. Lean's kernel checks the certificate in one evaluation of `Constraint.refutes`, and
   `Constraint.refutes_sound` gives the contradiction. Nothing from the search is trusted.

## Before the box

Three steps change the hypotheses before the box is read, and the route starts again after each.
When a comparison bounds by zero a sum of terms that `positivity` proves nonnegative, each term is
zero, and so is the base of each power (`vanishingTerms`). An atom that the bounds pin to one
rational value is replaced by that value (`substitutePinned`). An atom without bounds that is a
definition applied to arguments, an entry of a vector literal or a field of a structure instance
is unfolded.

## Atoms without bounds

For an atom that still has no bounds, these steps are tried in order.

* The constraints are evaluated once on the ranges of the atoms, in which an atom has an infinite
  end where it has no bound: `Real.exp (-x)` is in `[0, 1]` for every `x ≥ 0`. When they fail
  on these ranges the goal is closed (`Constraints.closeOnRanges`).
* A comparison whose form has a constant positive definite matrix is refuted without a box.
* A comparison that is affine in the atom bounds it through the bounds of the others
  (`affineBound`), a comparison of the atom with an expression that has an enclosure bounds it by
  that enclosure (`enclosureBound`), `|t| ≤ r`, `max p q ≤ r` and `r ≤ min p q` bound the terms
  inside (`latticeBounds`), and a comparison
  that confines the atoms without bounds to a sublevel set of a quadratic bounds each of them
  (`sublevelBound`), after its nonnegative terms of higher degree are dropped (`truncated`).
* An atom that lacks a side gets it from a tail: when the constraints fail on the ranges with
  the atom beyond some `M`, the atom is on this side of `M`, and the route goes on with that
  bound (`Constraints.tailBounds`).
* A value of the sine, the cosine, the hyperbolic tangent or the arctangent at an argument
  without bounds becomes a variable with the range of the function
  (`Constraints.generalizeValues`).
* Quotients are multiplied by their denominators (`clearDenominators`).
* `linarith` and then `nlinarith` are tried on the comparisons that hold outright, with the
  ranges and tangents of function values and the comparisons of an absolute value with its
  argument (`Constraints.rangeFacts`, `Constraints.signedFacts`), and between the two `linarith`
  with the products of the slacks of the linear comparisons (`slackProducts`), which can prove
  polynomial comparisons on half-lines.
* The goal is split at the disjunctions among its hypotheses, and each case is refuted on its own
  (`Constraints.splitCases`).

Any other atom without bounds is an error that names it. The search cuts boxes, whose intervals
have two rational ends: a range with an infinite end is evaluated as a whole and is not cut.

## The search and what follows it

The search uses the binary grid first, and exact rational endpoints with a small budget when the
grid fails, which is what refutes constraints that touch at a rational point. When both stop at
a point, where no cut is left, the precision and the degree are doubled, twice at most, which
decides a comparison of constants to more digits than the default precision gives. Then
`linarith` is tried on the comparisons that hold outright: it decides a conjunction of linear
comparisons in any dimension.

Where cutting does not end, at a point where a comparison holds with zero margin, the search
stops at a small box. The comparisons that are undecided there are then written as quadratic
forms around the simplest rational point of that box (`Constraints.Forms`), and a form whose
matrix is positive definite near the point joins the constraints: the search then replaces a box
on which the matrix is definite by the point itself. The coordinates of a form are the atoms
whose intervals are not negligible; constants such as `π`, pinned atoms and slopes stay in the
matrix. When that does not help, each value of the sine, the cosine, the hyperbolic tangent or
the arctangent is written with a slope (`Real.sin y = y - y ^ 3 * r` with `r` between `0` and
`1 / 6`, `Constraints.Slopes`), which gives the comparisons a form where the function vanishes
at the point. Then the combinations `a - b + μ * (c - d)` of two comparisons with a rational
`μ > 0` are tried in the same way, which refutes two constraints that no box separates; when the
two sets touch, `μ` is the one rational that makes the form semidefinite. Where they touch at a
point that a constant such as `π` gives, the multiplier is a rational times that constant: the
comparisons are multiplied by the constant and the constant is a coordinate of the form
(`Constraints.scaledCombinations`). Then `linarith` with
the products of the linear comparisons and `nlinarith` are tried, the comparisons with quotients
are multiplied by their denominators, and the absolute
values are opened into the cases of their signs (`Constraints.openAbsoluteValues`). As a last
step the goal is split at the disjunctions among its hypotheses, since in a case the comparisons
of its disjunct can be combined with the others.

## Two sides that meet at an end of the range

No box separates the two sides of a comparison where they are equal, and the steps above decide
this only where a form or a slope does. When the route has failed and the hypotheses are one
comparison in one real variable with bounds of that variable by terms without variables, the
comparison is tried by the sign of a derivative (`Constraints.byDerivative`): the difference of
the two sides has a sign at an end of the range, and its derivative has one beyond. The
derivative is computed by the rules of the elementary functions, and its sign is a goal for the
route again, which may pass to the next derivative: `(x + 4) ^ 4 / 256 ≤ Real.exp x` for
`0 ≤ x` takes three. Where the derivative keeps its sign only near the end, the range is cut
there, once, and the rest is left to the route, where the two sides are apart. The route passes
to a derivative five times in a row at most, and on the goals of this step it leaves out the
combinations, which the next derivative replaces, and has half the heartbeats of the arithmetic
steps at each pass. Where the comparison has quotients that `field_simp` clears, the step is
tried on the cleared comparison first. A call hands at most 40 goals to the route in this way,
a goal that has failed is not tried again, and the goals have one and a half times the
heartbeats of `maxHeartbeats` together: the route stops on such a goal when they are used, and
none is started then, or with less than an eighth of the heartbeats of the declaration left.
A call with the hints `box`, `ball` or `form` does what they say, and the step is not tried
there.

A failure names the box where the search stopped, the constraints that are undecided there with
the enclosures that fail to exclude them, and the limit that stopped it. The same report comes
when the declaration is about to run out of heartbeats: the route does not start the steps that
follow a search with less than an eighth of them left, and a timeout inside a later step is
replaced by the report of the last search. The trace class `interval.constraints` reports the
steps that the route took, and with `set_option trace.profiler true` the class
`interval.constraints.time` gives the time of the searches and of the steps around them, and
the heartbeats of the call.

## Options

`precision`, `degree` and `maxHeartbeats` are those of an inequality goal. `(depth := n)` bounds
the cuts along one branch (default 40) and `(boxes := n)` the boxes that the search evaluates
(default 20000); the search has no other limit, so it does not depend on the heartbeats of the
surrounding declaration. The kernel check of a certificate has `maxHeartbeats` (default 20000)
and 200 more for each of its boxes. The steps of polynomial arithmetic that may not end have
heartbeats of their own: `nlinarith` has `maxHeartbeats`, `linarith` with the products of the
slacks a quarter of that, and in one call the two run twice at most. The other options are
hints:

* `(cut := [(x, 0), (y, 1 / 2)])` cuts the box at the given points of the given atoms before the
  search starts.
* `(ball := [(x, 0, 1 / 4), (y, 0, 1 / 4)])` names a box around a point by the center and radius
  of some atoms. It is cut out of the box first, and the comparisons are written as forms around
  its center, which are added when their matrix is positive definite on the ball.
* `(form := [[m₀₀, m₀₁], [m₁₁]])`, with `ball`, states the upper triangle of the matrix of the
  form in the coordinates of the ball. `ring` must prove that the form is the difference of the
  two sides of a comparison, and the matrix must be positive definite on the ball.
* `(box := [(x, -2, 2)])` states bounds for atoms that the hypotheses do not bound. `linarith` and
  then `nlinarith` must prove each from the comparisons, with the terms of `(facts := [...])`.
* `(facts := [sq_nonneg (x - y)])` gives terms to every step of the route that calls `linarith`
  or `nlinarith`; a term that does not elaborate to a proof where a step runs is left out there.

A hint cannot make a proof wrong: the kernel checks the certificate, the form or the bound that
it leads to.

## Main definitions

* `Constraints.refute`: the route of `interval` for these goals.
* `Constraints.vanishingTerms`, `Constraints.substitutePinned`, `Constraints.sublevelBound`,
  `Constraints.affineBound`, `Constraints.enclosureBound` (in `Constraints.Derive`) and
  `Constraints.clearDenominators`: the steps that give the constraints equations and bounds.
* `Constraints.closeOnRanges`, `Constraints.tailBounds` (in `Constraints.Ranges`): the steps on
  ranges with infinite ends.
* `Constraints.formsAt`, `Constraints.combinations`: the forms that join the constraints after a
  search has stopped.
* `Constraints.byDerivative` (in `Constraints.Monotone`): the sign of a comparison in one
  variable from the sign of a derivative.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- What a call of the route has used and where its last search stopped, for the limit of its
effort and for its report. -/
structure Ledger where
  /-- Heartbeats of the searches, which the limit of the declaration does not pay for. -/
  searched : IO.Ref Nat
  /-- Heartbeats of the steps of linear and polynomial arithmetic with a budget of their own. -/
  calculated : IO.Ref Nat
  /-- The heartbeats of the thread when the route started. -/
  start : Nat
  /-- The report of the box where the last search stopped. -/
  stuck : IO.Ref (Option MessageData)
  /-- What failed and need not be tried again on the same facts: the signs of function
  arguments that `linarith` did not prove (`signedFacts`), and the steps of
  `Ledger.unlessFailed`. -/
  failed : IO.Ref (Std.HashSet UInt64)

/-- A ledger for a call that starts now. -/
def Ledger.new : BaseIO Ledger := do
  return { searched := ← IO.mkRef 0, calculated := ← IO.mkRef 0, start := ← IO.getNumHeartbeats
           stuck := ← IO.mkRef none, failed := ← IO.mkRef {} }

/-- Run a step on some facts, unless a step of this kind has failed in this call on facts with
the same statements: a later pass that reaches the same comparisons does not repeat it. A
failure is remembered. -/
def Ledger.unlessFailed (ledger : Option Ledger) (kind : UInt64) (facts : Array Lean.Expr)
    (step : TacticM Bool) : TacticM Bool := do
  let some ledger := ledger | step
  let key ← facts.foldlM (init := kind) fun code proof =>
    return mixHash code (← instantiateMVars (← inferType proof)).hash
  if (← ledger.failed.get).contains key then return false
  let done ← step
  unless done do ledger.failed.modify (·.insert key)
  return done

/-- The heartbeats of the declaration that are used and that it may use, in thousands, or
`none` when the declaration has no limit. -/
def declarationHeartbeats : CoreM (Option (Nat × Nat)) := do
  let context ← read
  if context.maxHeartbeats == 0 then return none
  return some (((← IO.getNumHeartbeats) - context.initHeartbeats) / 1000,
    context.maxHeartbeats / 1000)

/-- What the report of a stuck box says when the route stops for the limit of the declaration:
how much of it is used, and how to raise it. -/
def limitNote (used limit : Nat) : MessageData :=
  m!"The route stopped there, with its later steps untried: it had used {used} of the {limit} \
    thousand heartbeats of the declaration; `set_option maxHeartbeats` raises the limit."

/-- What the derivative step has done in one call of the route, for its limits: the step hands
at most 40 goals to the route, none twice after it has failed, and the goals have one and a
half times the heartbeats of `maxHeartbeats` together (`Settings.left`). -/
structure Passes where
  /-- The goals that the step has handed to the route. -/
  count : Nat := 0
  /-- The goals that failed, by the hash of their statement. -/
  failed : Std.HashSet UInt64 := {}
  /-- The heartbeats of the declaration when the step started. -/
  start : Nat := 0
  /-- The heartbeats of the searches and of the arithmetic steps of the goals, which the
  declaration does not pay for. -/
  hidden : Nat := 0

/-- The settings of a refutation: the limits of its checks, the limits of its search, and the
hints. -/
structure Settings extends Limits where
  /-- Cuts along one branch. -/
  depth : Nat := 40
  /-- Boxes that the search evaluates. -/
  boxes : Nat := 20000
  /-- Points at which the box is cut first: an atom and a rational. -/
  cuts : Array (Term × Term) := #[]
  /-- A ball to decide by quadratic forms: an atom, its center and its radius. -/
  ball : Array (Term × Term × Term) := #[]
  /-- The upper triangle, by rows, of the matrix of a form in the coordinates of the ball. -/
  form : Array (Array Term) := #[]
  /-- Bounds to prove from the hypotheses first: an atom, a lower and an upper bound. -/
  bounds : Array (Term × Term × Term) := #[]
  /-- Terms that `linarith` and `nlinarith` may use, for those bounds and in the route. -/
  facts : Array Term := #[]
  /-- The ledger of the call: `Constraints.run` opens it. -/
  ledger : Option Ledger := none
  /-- How many times in a row the route may pass from a comparison to the sign of a derivative
  (`byDerivative`). -/
  derivatives : Nat := 5
  /-- Whether the derivative step may cut the range of the variable: the goals that the step
  hands to the route are not cut again. -/
  split : Bool := true
  /-- Whether the combinations of two comparisons are tried where a search stops at a zero
  margin: the goals of the derivative step leave them out, since the next derivative decides a
  zero margin there. -/
  margins : Bool := true
  /-- What the derivative step has done in this call. `Constraints.run` opens it. -/
  passes : Option (IO.Ref Passes) := none
  /-- The heartbeats of `nlinarith` in the arithmetic steps, in thousands, where they are not
  `maxHeartbeats`: the goals of the derivative step have half as many at each pass. -/
  arithmetic : Option Nat := none

/-- The heartbeats, in thousands, that the goals of the derivative step may still use in this
call: one and a half times `maxHeartbeats` for all of them together, less what they have used,
with the searches and the arithmetic steps of the goal that is running. `none` outside such a
goal. -/
def Settings.left (settings : Settings) : BaseIO (Option Nat) := do
  let some passes := settings.passes | return none
  let done ← passes.get
  let mut used := (← IO.getNumHeartbeats) - done.start + done.hidden
  if let some ledger := settings.ledger then
    used := used + (← ledger.searched.get) + (← ledger.calculated.get)
  return some ((1500 * settings.maxHeartbeats - used) / 1000)

/-- The heartbeats of `nlinarith` in an arithmetic step, in thousands: `arithmetic`, or
`maxHeartbeats`, and on a goal of the derivative step no more than such goals have left. -/
def Settings.arithmeticBudget (settings : Settings) : BaseIO Nat := do
  let budget := settings.arithmetic.getD settings.maxHeartbeats
  return match ← settings.left with
    | some left => min budget left
    | none => budget

/-- What the route has done to the goal so far: each step that starts the route again is taken
a bounded number of times. -/
structure Progress where
  /-- Rounds of bounds derived from the comparisons. -/
  derived : Nat := 0
  /-- The atoms that were unfolded, with their values. -/
  rewrites : Rewrites := #[]
  /-- Whether the slopes of function values were introduced. -/
  sloped : Bool := false
  /-- The variables that are slopes. -/
  slopes : Array Lean.Expr := #[]
  /-- Whether the goal is a case of the disjunctions among the hypotheses. -/
  split : Bool := false
  /-- Whether the denominators of the comparisons were cleared. -/
  cleared : Bool := false
  /-- Whether the terms that the comparisons force to vanish were added. -/
  vanished : Bool := false
  /-- Whether the cases of the absolute values were added. -/
  opened : Bool := false
  /-- How often the precision and the degree were doubled. -/
  sharpened : Nat := 0

/-- The goal with `False` as its target: the target is unfolded to its binders and negated,
local definitions of reals become equations, existential hypotheses are opened, the combinations
of comparisons behind definitions are unfolded, hypotheses for every index of a `Fin n` are
replaced by their instances, implications and negations are brought to disjunctions and
conjunctions, and each conjunct is a hypothesis of its own. -/
def prepare (goal : MVarId) : MetaM MVarId := do
  -- local definitions of the target are introduced, and a target behind a definition, such as
  -- an inclusion of sets, is unfolded to its binders
  let mut start := goal
  while (← instantiateMVars (← start.getType)).isLet do
    start := (← start.intro1P).2
  let target ← instantiateMVars (← start.getType)
  unless target.isForall do
    let exposed ← exposeProp target
    unless exposed == target do start ← start.replaceTargetDefEq exposed
  let some goal ← start.falseOrByContra (useClassical := some true)
    | throwError "interval: the goal closed while its negation was introduced"
  let goal ← definitionsToEquations goal
  let goal ← splitConjunctions (← exposeHypotheses (← openExists goal))
  splitConjunctions (← pushNegations (← exposeHypotheses (← instantiateFinite goal)))

/-- The widths of the intervals of a box, with `0` for one that is negligible next to the
widest: less than `2 ^ (-30)` of it, as the interval of a constant such as `π` is. -/
def significantWidths (box : Box) : Array ℚ :=
  let scale := box.foldl (fun m I => max m (I.hi - I.lo)) 0
  box.toArray.map fun I => if (I.hi - I.lo) * 2 ^ 30 < scale then 0 else I.hi - I.lo

/-- The coordinates of the forms at a box: the atoms of significant width, each with the
simplest rational point of its interval as its center. The other atoms, constants and atoms
that the bounds pin to a point, stay in the matrices of the forms. -/
def centersOf (box : Box) (widths : Array ℚ) : Array (Nat × ℚ) :=
  (box.zipIdx.filterMap fun (I, i) =>
    if widths.getD i 1 == 0 then none else some (i, simplest I.lo I.hi)).toArray

/-- The atom of the constraints that a term of the user denotes. -/
def atomIndex (atoms : Array Q(ℝ)) (stx : Term) : TacticM Nat := do
  let atom ← Term.elabTermEnsuringType stx q(ℝ)
  Term.synthesizeSyntheticMVarsNoPostponing
  let atom ← instantiateMVars atom
  let some index ← atoms.findIdxM? fun known => withReducible (isDefEq known atom)
    | throwErrorAt stx "interval: {atom} is not an atom of the constraints"
  return index

/-- The rational number that a term of the user denotes. -/
def rationalOf (stx : Term) : TacticM ℚ := do
  let term : Q(ℝ) ← Term.elabTermEnsuringType stx q(ℝ)
  Term.synthesizeSyntheticMVarsNoPostponing
  let some value ← rationalValue? (← instantiateMVars term)
    | throwErrorAt stx "interval: expected a rational number"
  return value.value

/--
Prove the bounds that the user stated for some atoms, from the comparisons that hold outright and
the given facts, by `linarith` and then `nlinarith`. The result is one hypothesis for each bound.
-/
def statedBounds (settings : Settings) (literals : Array Literal) : TacticM (Array Hypothesis) := do
  let sides := sidesOf literals
  let known ← (literals.map (·.proof) ++ (← rangeFacts sides)).mapM fun proof =>
    Term.exprToSyntax proof
  let terms := known ++ settings.facts
  let mut facts := #[]
  for (atomSyntax, lowerSyntax, upperSyntax) in settings.bounds do
    let atom : Q(ℝ) ← Term.elabTermEnsuringType atomSyntax q(ℝ)
    let lower : Q(ℝ) ← Term.elabTermEnsuringType lowerSyntax q(ℝ)
    let upper : Q(ℝ) ← Term.elabTermEnsuringType upperSyntax q(ℝ)
    Term.synthesizeSyntheticMVarsNoPostponing
    let stated : Array Q(Prop) := #[q($lower ≤ $atom), q($atom ≤ $upper)]
    for type in stated do
      let goal ← mkFreshExprMVar type
      let closed ← try
          let remaining ← Lean.Elab.Tactic.run goal.mvarId! (evalTactic (← `(tactic|
            first | linarith [$terms,*] | nlinarith [$terms,*])))
          pure remaining.isEmpty
        catch error =>
          if error.isInterrupt || error.isRuntime then throw error
          pure false
      unless closed do
        throwErrorAt atomSyntax "interval: linarith and nlinarith did not prove the stated \
          bound{indentExpr type}\nfrom the comparisons of the hypotheses; `(facts := [...])` \
          gives them further terms"
      facts := facts.push { userName := `bound, type, value := ← instantiateMVars goal }
  return facts

/--
The forms around the center of the ball that the user gave: the form with the stated matrix, for
the first comparison that it is the form of, or else the forms of the comparisons that are not
bounds. Each must be positive definite on the ball, or semidefinite for a strict comparison; a
stated matrix that is not is an error.
-/
def ballForms (settings : Settings) (atoms : Array Q(ℝ)) (literals : Array Literal)
    (ball : Array (Nat × ℚ × ℚ)) (region : Box) (widths : Array ℚ)
    (definite : Bool → Form → Box → Bool) (cache : ReifyState) :
    TacticM (Array FormPiece × ReifyState) := do
  -- the coordinates: the atoms of the ball at its center, and the other atoms of significant width
  let centers := (region.zipIdx.filterMap fun (I, i) =>
    match ball.find? (·.1 == i) with
    | some (_, center, _) => some (i, center)
    | none => if widths.getD i 1 == 0 then none else some (i, simplest I.lo I.hi)).toArray
  let mut found := #[]
  let mut cache := cache
  if settings.form.isEmpty then
    for literal in literals do
      let expansion ← Expansion.of atoms literal none centers
      if expansion.isBound then continue
      let (piece?, next) ← (formPiece atoms expansion 0).run cache
      if let some piece := piece? then
        if definite (!literal.strict) piece.form region then
          cache := next
          found := found.push piece
    return (found, cache)
  -- The stated matrix: its entries as real terms, in the coordinates of the ball.
  let mut rows : Array (Array Q(ℝ)) := #[]
  for row in settings.form do
    let mut terms := #[]
    for entry in row do
      terms := terms.push (← Term.elabTermEnsuringType entry q(ℝ))
    rows := rows.push terms
  Term.synthesizeSyntheticMVarsNoPostponing
  let coordinates := ball.map fun (i, center, _) => some (i, center, 0)
  unless rows.size == ball.size && (rows.zipIdx.all fun (row, k) => row.size == ball.size - k) do
    throwError "interval: the form of a ball with {ball.size} coordinates has {ball.size} rows, \
      row k with the entries (k, k), (k, k + 1), …"
  for literal in literals do
    let (identity?, next) ← (formIdentityOf atoms literal .trivial 0 coordinates fun k l =>
      instantiateMVars ((rows.getD k #[]).getD (l - k) q(0))).run cache
    let some identity := identity? | continue
    let piece := identity.piece literal .trivial
    unless definite (!literal.strict) piece.form region do
      throwError "interval: the stated form is not positive definite on the ball"
    return (#[piece], next)
  throwError "interval: the stated form is not the difference of the two sides of a comparison \
    that holds outright (checked by ring)"

/--
The forms of the comparisons that are undecided at a box where the search stopped: those whose
matrix is positive definite on that box, or semidefinite for a strict comparison. The form is
taken around the simplest rational point of the box, and failing that around the simplest point
of the box that the search started from, where a form that vanishes on a whole line or plane has
no linear part. With `screen`, the oracle of the enclosures that `definite` uses on the box, a
form is built only when the screening test with exact arithmetic on these enclosures accepts
its matrix: a matrix that it rejects is rejected by `definite` as well.
-/
def formsAt (atoms : Array Q(ℝ)) (literals : Array Literal) (stuck : Stuck) (root : Box)
    (widths : Array ℚ) (definite : Bool → Form → Box → Bool) (screen : Option Oracle := none) :
    StateRefT ReifyState MetaM (Array FormPiece) := do
  let undecided := stuck.work.undecided.map (·.1.source)
  let mut found := #[]
  for literal in literals do
    have a : Q(ℝ) := literal.lhs
    have b : Q(ℝ) := literal.rhs
    let source : Q(Prop) := if literal.strict then q($a < $b) else q($a ≤ $b)
    unless undecided.contains source do continue
    for centers in [centersOf stuck.box widths, centersOf root widths] do
      let expansion ← Expansion.of atoms literal none centers
      if expansion.isBound then break
      -- the screening test first: the identity of a form that fails it need not be proved
      if let some onBox := screen then
        unless (expansion.data 0).screen (← expansion.ranges onBox) (!literal.strict) do continue
      let some piece ← formPiece atoms expansion 0 | continue
      if definite (!literal.strict) piece.form stuck.box then
        found := found.push piece
        break
  return found

/-- A comparison multiplied by a positive term: `κ * a ≤ κ * b` from `a ≤ b`, and the same for
`<`. -/
def Literal.scaled (literal : Literal) (κ : Q(ℝ)) (positive : Q(0 < $κ)) : Literal :=
  have a : Q(ℝ) := literal.lhs
  have b : Q(ℝ) := literal.rhs
  { literal with
    lhs := q($κ * $a)
    rhs := q($κ * $b)
    proof := if literal.strict then
        (have h : Q($a < $b) := literal.proof; q(mul_lt_mul_of_pos_left $h $positive))
      else
        (have h : Q($a ≤ $b) := literal.proof
         q(mul_le_mul_of_nonneg_left $h (le_of_lt $positive))) }

/--
The forms of combinations whose multiplier is a rational times a constant. Two sets that touch
at a point with irrational coordinates, such as a disc of radius `π / 4` and a half-plane, have
no rational multiplier: the multiplier is a multiple of a constant of the comparisons, as `π`
is. The atoms that the box confines to a negligible interval, and that `positivity` proves
positive, are taken for such constants. With them among the coordinates, at the center zero
like every other atom, a comparison whose difference is homogeneous of degree one in the
coordinates is multiplied by a constant, which brings it to degree two, and the combination of
two comparisons of degree two with a rational multiplier has a matrix of rational numbers. Its
form vanishes where the sets touch, so it is semidefinite at most, which rational endpoints
decide exactly. At most `limit` forms are returned.
-/
def scaledCombinations (atoms : Array Q(ℝ)) (candidates : Array Literal) (box : Box)
    (onBox : Oracle) (limit : Nat) : StateRefT ReifyState MetaM (Array FormPiece) := do
  -- the constants: atoms of negligible width that are positive
  let widths := significantWidths box
  let mut positives : Array (Q(ℝ) × Lean.Expr) := #[]
  for (atom : Q(ℝ)) in atoms, i in [0:atoms.size] do
    unless widths.getD i 1 == 0 do continue
    if let some positive ← positivityProof? q(0 < $atom) then
      positives := positives.push (atom, positive)
  if positives.isEmpty then return #[]
  let centers := (Array.range atoms.size).map fun i => (i, (0 : ℚ))
  -- each comparison at degree two: as it is, or multiplied by a constant
  let mut scaled : Array (Literal × Literal × Option Q(ℝ)) := #[]
  for literal in candidates do
    let expansion ← Expansion.of atoms literal none centers
    let coordinates := expansion.generators.shifted.fold (init := #[]) fun acc _ (_, g) =>
      acc.push g
    let degrees := expansion.firstPoly.monomials.map fun (monomial, _) =>
      if monomial.all fun (g, _) => coordinates.contains g then
        some (monomial.foldl (fun degree (_, e) => degree + e) 0)
      else none
    if degrees.all (· == some 2) then scaled := scaled.push (literal, literal, none)
    else if degrees.all (· == some 1) then
      for (κ, positive) in positives do
        scaled := scaled.push (literal, literal.scaled κ positive, some κ)
  let mut found := #[]
  for (firstSource, first, firstScale) in scaled do
    for (secondSource, second, secondScale) in scaled do
      if firstSource.proof == secondSource.proof then continue
      if found.size ≥ limit then return found
      -- with no constant in either comparison the multiplier is that of `combinations`
      if firstScale.isNone && secondScale.isNone then continue
      let expansion ← Expansion.of atoms first (some second) centers
      let table := expansion.margins (← expansion.ranges onBox) (!first.strict)
      let some range := table.admits | continue
      let some μ := bestMultiplier table.at range | continue
      if !first.strict && (expansion.data μ).coordinates.isEmpty then continue
      if let some piece ← formPiece atoms expansion μ then
        trace[interval.constraints] "combination with the multiplier {μ} of\n  \
          {first.lhs} {if first.strict then "<" else "≤"} {first.rhs}\n  \
          {second.lhs} {if second.strict then "<" else "≤"} {second.rhs}"
        found := found.push piece
  return found

/--
The forms of combinations `a - b + μ * (c - d)` of two comparisons that are not bounds, for a
multiplier `μ > 0` at which the screening test finds the matrix positive definite on the whole
box, or failing that at its simplest point (`bestMultiplier`). When no rational multiplier is
found, the comparisons multiplied by constants are tried (`scaledCombinations`). At most
`limit` forms are returned.
-/
def combinations (atoms : Array Q(ℝ)) (literals : Array Literal) (box : Box)
    (widths : Array ℚ) (oracle : Box → Option Oracle) (limit : Nat := 2) :
    StateRefT ReifyState MetaM (Array FormPiece) := do
  let centers := centersOf box widths
  let point : Box := box.map fun I => ⟨simplest I.lo I.hi, simplest I.lo I.hi⟩
  let some whole := oracle box | return #[]
  let some atPoint := oracle point | return #[]
  let mut candidates : Array Literal := #[]
  for literal in literals do
    unless (← Expansion.of atoms literal none centers).isBound do
      candidates := candidates.push literal
  let mut found := #[]
  -- the expansion of a pair serves both passes
  let mut expansions : Std.HashMap (Nat × Nat) Expansion := {}
  for wholeBox in [true, false] do
    for first in candidates, i in [0:candidates.size] do
      for second in candidates, j in [0:candidates.size] do
        if first.proof == second.proof then continue
        if found.size ≥ limit then return found
        let expansion ← match expansions[(i, j)]? with
          | some known => pure known
          | none => Expansion.of atoms first (some second) centers
        expansions := expansions.insert (i, j) expansion
        let ranges ← expansion.ranges (if wholeBox then whole else atPoint)
        -- the margins at every multiplier from one table, and no search where none can pass
        let table := expansion.margins ranges (!first.strict)
        let some range := table.admits | continue
        let some μ := bestMultiplier table.at range | continue
        -- a combination that is identically zero refutes a strict comparison only
        if !first.strict && (expansion.data μ).coordinates.isEmpty then continue
        if let some piece ← formPiece atoms expansion μ then
          trace[interval.constraints] "combination with the multiplier {μ} of\n  \
            {first.lhs} {if first.strict then "<" else "≤"} {first.rhs}\n  \
            {second.lhs} {if second.strict then "<" else "≤"} {second.rhs}"
          found := found.push piece
    unless found.isEmpty do return found
  -- no rational multiplier: one that is a rational times a constant of the comparisons
  scaledCombinations atoms candidates box whole limit

/-- Close the main goal `False` by `linarith` from the given facts, the comparisons that hold
outright, or with `products` by `nlinarith`, which also multiplies them in pairs. The first
decides a conjunction of linear comparisons in any dimension, where cutting boxes does not end;
the second refutes polynomial comparisons on sets without a box when a certificate of degree two
exists. The result says whether the goal was closed. -/
def linearly (facts : Array Lean.Expr) (products : Bool := false) : TacticM Bool := do
  let terms ← facts.mapM fun proof => Term.exprToSyntax proof
  let saved ← saveState
  try
    if products then evalTactic (← `(tactic| nlinarith [$terms,*]))
    else evalTactic (← `(tactic| linarith [$terms,*]))
    return (← getUnsolvedGoals).isEmpty
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    saved.restore
    return false

/--
Products of the slacks of the linear comparisons. A comparison `a ≤ b` whose difference is
affine in the atoms, such as a bound `lo ≤ x` or `x + y ≤ 1`, has the nonnegative slack `b - a`,
and every product of slacks is nonnegative. The result is the proofs of
`0 ≤ s₁ ^ k₁ * … * sₘ ^ kₘ` for the products of total degree two up to the degree of the
comparisons (four at most), at most `limit` of them and of the first eight slacks. With these
facts `linarith` decides a polynomial comparison on a polytope or on a half-line when it is a
combination of products of the linear comparisons, as in Handelman's theorem: `x ^ 3 ≤ -8` from
`x ≤ -2`, for instance.
-/
def slackProducts (atoms : Array Q(ℝ)) (literals : Array Literal) (limit : Nat := 120) :
    MetaM (Array Lean.Expr) := do
  -- the slacks, each with the proof that it is nonnegative, and the degree of the comparisons
  let mut slacks : Array (Q(ℝ) × Lean.Expr) := #[]
  let mut degree := 2
  for literal in literals do
    let expansion ← Expansion.of atoms literal none #[]
    for (monomial, _) in expansion.firstPoly.monomials do
      degree := max degree (monomial.foldl (fun total (_, exponent) => total + exponent) 0)
    let affine := expansion.firstPoly.monomials.all fun (monomial, _) =>
      monomial.foldl (fun total (_, exponent) => total + exponent) 0 ≤ 1
    unless affine && !expansion.firstPoly.monomials.all (·.1.isEmpty) do continue
    have a : Q(ℝ) := literal.lhs
    have b : Q(ℝ) := literal.rhs
    let proof : Q(0 ≤ $b - $a) := if literal.strict then
      (have h : Q($a < $b) := literal.proof; q((sub_pos.mpr $h).le))
      else (have h : Q($a ≤ $b) := literal.proof; q(sub_nonneg.mpr $h))
    unless slacks.any (·.1 == q($b - $a)) do slacks := slacks.push (q($b - $a), proof)
  slacks := slacks.extract 0 8
  degree := min degree 4
  -- the exponent vectors of total degree two and more, by degree
  let mut vectors : Array (List Nat) := #[[]]
  for _ in slacks do
    vectors := vectors.flatMap fun vector =>
      (Array.range (degree + 1 - vector.foldl (· + ·) 0)).map fun k => vector ++ [k]
  let wanted := (vectors.filter fun vector => 2 ≤ vector.foldl (· + ·) 0).qsort fun u v =>
    u.foldl (· + ·) 0 < v.foldl (· + ·) 0
  let mut facts := #[]
  for vector in wanted.extract 0 limit do
    let mut product : Option (Q(ℝ) × Lean.Expr) := none
    for ((slack, nonneg), k) in slacks.toList.zip vector do
      if k == 0 then continue
      have s : Q(ℝ) := slack
      have hs : Q(0 ≤ $s) := nonneg
      have exponent : Q(ℕ) := mkNatLit k
      let factor : Q(ℝ) × Lean.Expr := (q($s ^ $exponent), q(pow_nonneg $hs $exponent))
      product := some (match product with
        | none => factor
        | some (previous, proof) =>
          have p : Q(ℝ) := previous
          have f : Q(ℝ) := factor.1
          have hp : Q(0 ≤ $p) := proof
          have hf : Q(0 ≤ $f) := factor.2
          (q($p * $f), q(mul_nonneg $hp $hf)))
    if let some (_, proof) := product then facts := facts.push proof
  return facts

/-- Run a step with a limit of heartbeats of its own, in thousands, which the limit of the
declaration neither bounds nor pays for. The result is that of the step, or `false` when the
step ran out of them or failed, and then the proof state is as before. With a ledger, the steps
of one call have `total` thousand heartbeats together: a step gets what is left of that, and
none runs once it is used. -/
def withinBudget (budget : Nat) (step : TacticM Bool) (ledger : Option Ledger := none)
    (total : Nat := 4 * budget) : TacticM Bool := do
  let saved ← saveState
  let before ← IO.getNumHeartbeats
  let mut allowed := budget * 1000
  if let some ledger := ledger then
    allowed := min allowed (total * 1000 - (← ledger.calculated.get))
    if allowed == 0 then
      trace[interval.constraints] "an arithmetic step is left out: the steps of this call have \
        used their {total} thousand heartbeats"
      return false
  try
    let done ← tryCatchRuntimeEx
      (withTheReader Core.Context
        (fun context => { context with maxHeartbeats := allowed, initHeartbeats := before })
        step)
      fun error => do
        if error.isInterrupt then throw error
        pure false
    unless done do saved.restore
    return done
  finally
    if let some ledger := ledger then
      ledger.calculated.modify (· + ((← IO.getNumHeartbeats) - before))
    IO.setNumHeartbeats before

/--
The steps of polynomial arithmetic on the comparisons that hold outright: `linarith` with the
products of the slacks of the linear comparisons, within a quarter of the budget of heartbeats,
then `nlinarith` within the budget. The two have twice that together in one call. The result
names the step that closed the goal. A step that has failed on the same facts in this call is
not run again.
-/
def polynomially (atoms : Array Q(ℝ)) (literals : Array Literal) (facts : Array Lean.Expr)
    (budget : Nat) (ledger : Option Ledger := none) : TacticM (Option String) := do
  -- two rounds of the two steps at most, in one call
  let total := 2 * (budget / 4 + budget)
  if ← Ledger.unlessFailed ledger 2 facts (withinBudget (budget / 4)
      (do linearly (facts ++ (← slackProducts atoms literals))) ledger total) then
    return some "linarith with products of the linear comparisons"
  if ← Ledger.unlessFailed ledger 3 facts
      (withinBudget budget (linearly facts true) ledger total) then
    return some "nlinarith"
  return none

/-- Refute each of the goals that a split of the main goal left, by the given route; a failure
says of which kind the case is. -/
def refuteCases (cases : List MVarId) (kind : String) (route : TacticM Unit) : TacticM Unit := do
  for goal in cases do
    setGoals [goal]
    try route
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      throwError "in a case of {kind}, {error.toMessageData}"

/--
Multiply the comparisons among the hypotheses by their denominators: `field_simp` rewrites each
hypothesis that contains a quotient by a term that is not a numeral, which it does where it finds
the signs of the denominators. A comparison without quotients is a polynomial comparison, for
which the route has forms and certificates that need no box. The result says whether a
hypothesis changed; the step may also close the goal.
-/
def clearDenominators : TacticM Bool := do
  let quotient (e : Lean.Expr) : Bool :=
    (e.isAppOfArity ``HDiv.hDiv 6 && e.appArg!.hasFVar) ||
      (e.isAppOfArity ``Inv.inv 3 && e.appArg!.hasFVar)
  let mut changed := false
  let mut seen : Array Name := #[]
  for k in [0:32] do
    if (← getUnsolvedGoals).isEmpty then return changed
    let goal ← getMainGoal
    -- the next hypothesis with a quotient
    let next? ← goal.withContext do
      for decl in ← getLCtx do
        if decl.isImplementationDetail || seen.contains decl.userName then continue
        unless ← isProp decl.type do continue
        if ((← instantiateMVars decl.type).find? quotient).isSome then return some decl
      return none
    let some decl := next? | return changed
    let name := Name.mkSimple s!"cleared{k}"
    seen := seen.push name
    replaceMainGoal [← goal.rename decl.fvarId name]
    let saved ← saveState
    try
      evalTactic (← `(tactic| field_simp at $(mkIdent name):ident))
      changed := true
      trace[interval.constraints] "cleared the denominators of {decl.type}"
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      saved.restore
  return changed

/--
The forms of the comparisons that are not bounds, around the simplest rational point of the box,
whose matrix the screening test finds positive definite, or semidefinite for a strict
comparison, on the whole box. Such a form decides its comparison at the first box.
-/
def rootForms (atoms : Array Q(ℝ)) (literals : Array Literal) (box : Box) (oracle : Oracle) :
    StateRefT ReifyState MetaM (Array FormPiece) := do
  let centers := centersOf box (significantWidths box)
  let mut found := #[]
  for literal in literals do
    let expansion ← Expansion.of atoms literal none centers
    if expansion.isBound then continue
    let ranges ← expansion.ranges oracle
    unless (expansion.data 0).screen ranges (!literal.strict) do continue
    if let some piece ← formPiece atoms expansion 0 then found := found.push piece
  return found

/--
One pass of the route on the real constraints of the local context: reify them, read the box,
search for a certificate and have the kernel check it, with the steps before the box, for atoms
without bounds and after a search that stops which the module docstring lists in their order.
The result is `none` when the goal is closed. A step that changes the hypotheses ends the pass
with the settings and the progress of the next one, and `progress` records the steps that are
taken once. The cases of a goal are refuted by `recurse`, the whole route. The main goal must be
`False`.
-/
def refuteOnce (recurse : Settings → Progress → TacticM Unit) (settings : Settings)
    (progress : Progress) : TacticM (Option (Settings × Progress)) := withMainContext do
  -- The constraints of the hypotheses, and the atoms of their expressions.
  let mut pieces : Array (Piece × Lean.Expr) := #[]
  let mut unread : Array MessageData := #[]
  let mut cache : ReifyState := {}
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless ← isProp decl.type do continue
    let (piece?, next) ← timed "reading a hypothesis"
      ((reifyProp progress.rewrites true decl.type).run cache)
    if let some piece := piece? then
      cache := next
      pieces := pieces.push (piece, decl.toExpr)
    else unread := unread.push m!"{decl.type}"
  -- The facts for linear arithmetic: what Mathlib proves about constants and function values.
  let general (atoms : Array Q(ℝ)) (literals : Array Literal) : TacticM (Array Lean.Expr) := do
    let sides := sidesOf literals
    let mut facts := constantFacts atoms ++ (← rangeFacts sides)
    -- the terms of the user that elaborate to proofs in this context
    for fact in settings.facts do
      let saved ← saveState
      try
        let proof ← Term.elabTerm fact none
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        if (← isProp (← inferType proof)) && !proof.hasMVar then facts := facts.push proof
        else saved.restore
      catch error =>
        if error.isInterrupt || error.isRuntime then throw error
        saved.restore
    return facts ++ (← signedFacts sides (literals.map (·.proof) ++ facts)
      (settings.ledger.map (·.failed)))
  let mut forms : Array FormPiece := #[]
  let mut combined := false
  let mut fallbacks := false
  let combinationState ← IO.mkRef (none : Option (Array FormPiece × ReifyState))
  let configValue : Backend.Config := ⟨settings.precision, settings.degree⟩
  have precision : Q(Nat) := mkNatLit settings.precision
  have degree : Q(Nat) := mkNatLit settings.degree
  have config : Q(Backend.Config) := q(⟨$precision, $degree⟩)
  for round in [0:6] do
    let atoms := cache.atoms
    have reals : Q(List ℝ) := atoms.foldr
      (fun (atom : Q(ℝ)) (rest : Q(List ℝ)) => q($atom :: $rest)) q([])
    have values : Q(Nat → ℝ) := q(fun i => $reals[i]?.getD 0)
    let tables ← extensionTables cache.extensions
    let grid := tables.gridBackend config
    have functions : Q(Nat → List ℝ → ℝ) := grid.functions
    -- The proof that the conjunction of the constraints holds, and the comparisons it uses.
    let context : BuildContext := { values, functions, cache }
    let mut whole : Option (Lean.Expr × Tree × Lean.Expr) := none
    let mut literals : Array Literal := #[]
    for (piece, h) in pieces ++ forms.map fun form => (form.piece, mkConst ``True.intro) do
      let (proof, more) ← ((piece.prove true h).run context).run literals
      literals := more
      match whole with
      | none => whole := some (piece.constraint, piece.tree, proof)
      | some (previous, tree, holds) =>
        have previous : Q(Constraint) := previous
        have next : Q(Constraint) := piece.constraint
        whole := some (q(Constraint.and $previous $next), .and tree piece.tree,
          ← mkAppM ``Constraint.holds_and #[holds, proof])
    let some (constraint, tree, holds) := whole
      | throwError "interval found no real constraint among the hypotheses: it refutes \
        combinations by ∧, ∨ and ¬ of ≤, <, = and ≠ between real expressions"
    have constraint : Q(Constraint) := constraint
    -- The comparisons that hold outright with the facts for linear arithmetic, computed once in
    -- a round and only when a step asks for them.
    let known ← IO.mkRef (none : Option (Array Lean.Expr))
    let outright : TacticM (Array Lean.Expr) := do
      if let some facts ← known.get then return facts
      let facts := literals.map (·.proof) ++ (← general atoms literals)
      known.set (some facts)
      return facts
    -- The bounds that the user stated are proved first, and the route starts again with them.
    unless settings.bounds.isEmpty do
      let (_, goal) ← (← getMainGoal).assertHypotheses (← statedBounds settings literals)
      replaceMainGoal [goal]
      return some ({ settings with bounds := #[] }, progress)
    -- The terms of a sum of nonnegative terms that is at most zero vanish: once, and the route
    -- starts again with their equations. A ball of the user is decided by its forms instead.
    if !progress.vanished && settings.ball.isEmpty then
      let mut equations : Array Hypothesis := #[]
      for literal in literals do
        equations := equations ++ (← vanishingTerms cache.atoms literal)
      unless equations.isEmpty do
        let (_, goal) ← (← getMainGoal).assertHypotheses equations
        replaceMainGoal [goal]
        return some (settings, { progress with vanished := true })
    -- The backends of the search and of the check.
    let some extensions := cache.extensions.toList.mapM compiledExtension?
      | throwError "interval: the constraint search evaluates the registered functions of \
          FloatLib.Tactic.Interval.Functions only, and the constraints call another \
          registered function"
    let gridBackend :=
      Backend.withExtensions (Backend.binaryGrid configValue) configValue extensions
    let exactBackend :=
      Backend.withExtensions (Backend.rational configValue) configValue extensions
    have quotedGrid : Q(Backend Int) := grid.backend
    have gridSound : Q(Backend.Sound $quotedGrid $functions) := grid.sound
    let exact := tables.rationalBackend config
    have quotedExact : Q(Backend ℚ) := exact.backend
    have exactSound : Q(Backend.Sound $quotedExact $functions) := exact.sound
    let close (constraint : Q(Constraint)) (holds : Lean.Expr) (box : Q(Box))
        (membership : Lean.Expr) (certificate : Refutation) (useGrid : Bool) : TacticM Unit := do
      have cert : Q(Refutation) := quoteRefutation certificate
      have membership : Q(Box.ContainsReal $box $values) := membership
      -- The kernel gets the heartbeats of the options and 200 more for each box, so that a
      -- certificate within the budget of the search is also checked.
      let limit := settings.maxHeartbeats + 200 * leaves certificate
      let check (proposition : Q(Prop)) : TacticM Lean.Expr := do
        try verifyClosedCheck proposition limit
        catch error =>
          if error.isInterrupt then throw error
          let advice := resourceAdvice "the certificate" limit (← resourceLimit? error)
          throwError "interval: the kernel did not accept a certificate of \
            {leaves certificate} boxes that the search found: {error.toMessageData}{advice}"
      let refuted : Q(¬ Constraint.Holds $constraint $values $functions) ← if useGrid then do
        let checked : Q(Constraint.refutes $quotedGrid $cert $constraint $box = true) ←
          check q(Constraint.refutes $quotedGrid $cert $constraint $box = true)
        pure q(Constraint.refutes_sound $gridSound $cert $checked $membership)
      else do
        let checked : Q(Constraint.refutes $quotedExact $cert $constraint $box = true) ←
          check q(Constraint.refutes $quotedExact $cert $constraint $box = true)
        pure q(Constraint.refutes_sound $exactSound $cert $checked $membership)
      have holds : Q(Constraint.Holds $constraint $values $functions) := holds
      closeMainGoal `interval q($refuted $holds)
    -- The box: bounds from the hypotheses, from the comparisons, and for known constants.
    let mut bounds := ← constantBounds atoms
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      if ← isProp decl.type then
        bounds := bounds ++ (← boundsOfProofFor atoms decl.toExpr)
    for literal in literals do
      bounds := bounds ++ (← boundsOfProofFor atoms literal.proof)
    -- An atom that the bounds pin to one value is replaced by that value.
    if ← substitutePinned atoms bounds outright then
      return some (settings, progress)
    -- Atoms without bounds: unfold those that are definitions and start again.
    let missing ← unbounded bounds atoms
    if progress.rewrites.size < 64 then
      let mut exposed := progress.rewrites
      for i in missing do
        if let some atom := atoms[i]? then
          if let some unfolded ← exposeAtom atom then exposed := exposed.push (atom, unfolded)
      if exposed.size > progress.rewrites.size then
        return some (settings, { progress with rewrites := exposed })
    -- What the steps on ranges with infinite ends need: the constraint and the exact backend.
    let decodes : Lean.Expr :=
      have registered : Q(List Extension) := tables.extensions
      q(Backend.decode_rational $config $registered)
    let called ← nameTable cache.extensions
    let ranged : RangeContext := {
      constraint, tree, values, functions, holds, decodes
      backend := quotedExact, backendValue := exactBackend, sound := exactSound
      names := called.names, namesValue := called.value, named := called.sound
      heartbeats := settings.maxHeartbeats }
    -- The constraints may fail on the whole box of ranges, whatever ends the atoms lack.
    unless missing.isEmpty do
      if ← closeOnRanges ranged atoms bounds then
        trace[interval.constraints] "closed on the ranges of the atoms, without a box"
        return none
    -- A comparison whose form has a constant matrix may fail without a box.
    unless missing.isEmpty do
      let origin := (Array.range atoms.size).map fun j => (j, (0 : ℚ))
      for literal in literals do
        let expansion ← Expansion.of atoms literal none origin
        unless expansion.isQuadratic do continue
        let (piece?, next) ← (formPiece atoms expansion 0).run cache
        let some global := piece? | continue
        if global.form.definiteOn exactBackend (!literal.strict) [] &&
            (literal.strict || global.form.excluded []) then
          let (proof, _) ← ((global.piece.prove true (mkConst ``True.intro)).run
            { context with cache := next }).run #[]
          close global.piece.constraint proof q([]) q(Box.containsReal_nil $values) .definite false
          trace[interval.constraints] "closed by a form that is definite without a box"
          return none
    -- Otherwise derive bounds from comparisons that are affine in the atom, or that confine
    -- it to a sublevel set of a quadratic, and start again.
    -- Each round gives some atom a side that it lacks, so two rounds for each atom suffice.
    if !missing.isEmpty && progress.derived < 2 * atoms.size then
      let mut facts : Array Hypothesis := #[]
      facts ← latticeBounds literals
      for i in missing do
        -- the sides that the atom has, then those that affine comparisons add
        let mut lower := false
        let mut upper := false
        for bound in bounds do
          if ← withReducible (isDefEq (atoms.getD i q(0)) bound.term) then
            if bound.lower then lower := true else upper := true
        for literal in literals do
          if let some (type, proof, isUpper) ← affineBound atoms bounds outright literal i then
            unless if isUpper then upper else lower do
              facts := facts.push { userName := `bound, type, value := proof }
            if isUpper then upper := true else lower := true
        -- then those that a comparison with an enclosed expression adds
        unless lower && upper do
          for literal in literals do
            if let some (type, proof, isUpper) ← enclosureBound atoms bounds missing literal i
                settings.toLimits then
              unless if isUpper then upper else lower do
                facts := facts.push { userName := `bound, type, value := proof }
              if isUpper then upper := true else lower := true
        if lower && upper then continue
        for literal in literals do
          if let some (type, proof) ← sublevelBound atoms bounds missing literal i
              settings.toLimits then
            facts := facts.push { userName := `bound, type, value := proof }
            break
      -- A comparison with nonnegative terms of high degree confines the atoms as well: the
      -- comparison without these terms is added once, for the next round of bounds.
      if facts.isEmpty && progress.derived == 0 then
        for literal in literals do
          if let some fact ← truncated atoms missing literal then facts := facts.push fact
      unless facts.isEmpty do
        let (_, goal) ← (← getMainGoal).assertHypotheses facts
        replaceMainGoal [goal]
        trace[interval.constraints] "derived the bounds {facts.map (·.type)}"
        return some (settings, { progress with derived := progress.derived + 1 })
    -- An atom that still lacks a side gets it from a tail on which the constraints fail.
    unless missing.isEmpty do
      let facts ← tailBounds ranged atoms bounds missing
      unless facts.isEmpty do
        let (_, goal) ← (← getMainGoal).assertHypotheses facts
        replaceMainGoal [goal]
        trace[interval.constraints] "derived the bounds {facts.map (·.type)} from the tails \
          on which the constraints fail"
        return some (settings, progress)
    unless missing.isEmpty do
      -- A value of a bounded function at an argument without bounds becomes a variable.
      if ← generalizeValues (missing.filterMap fun i => atoms[i]?) then
        return some (settings, progress)
      -- Comparisons with quotients are multiplied by their denominators, once.
      unless progress.cleared do
        if ← clearDenominators then
          if (← getUnsolvedGoals).isEmpty then return none
          return some (settings, { progress with cleared := true })
      -- Without a box, linear comparisons may still be decided, and polynomial ones that have
      -- a certificate of degree two.
      let facts ← outright
      if ← linearly facts then
        trace[interval.constraints] "closed by linarith, without a box"
        return none
      if let some step ← polynomially atoms literals facts
          (← settings.arithmeticBudget) settings.ledger then
        trace[interval.constraints] "closed by {step}, without a box"
        return none
      -- The cases of the disjunctions among the hypotheses may each have a box or a certificate.
      unless progress.split do
        if let some cases ← splitCases (← getMainGoal) then
          trace[interval.constraints] "{cases.length} cases of the disjunctions, without a box"
          refuteCases cases "the disjunctions among the hypotheses"
            (recurse settings { progress with split := true })
          return none
    let data ← reifyBox bounds atoms.toList
    have box : Q(Box) := data.box
    have membership : Q(Box.ContainsReal $box $values) := data.membership
    let boxValue ← Diagnostics.readBox box
    -- A coordinate much narrower than the widest, such as a constant, is never worth a cut and
    -- is no coordinate of a form. Neither is a slope: it stays in the matrices.
    let slopeAt := progress.slopes.filterMap fun slope => atoms.findIdx? (· == slope)
    let widths := (significantWidths boxValue).mapIdx fun i width =>
      if slopeAt.contains i then 0 else width
    -- The ball of the user: its part of the box, and the forms around its center.
    let mut ball : Array (Nat × ℚ × ℚ) := #[]
    for (atomSyntax, centerSyntax, radiusSyntax) in settings.ball do
      ball := ball.push
        (← atomIndex atoms atomSyntax, ← rationalOf centerSyntax, ← rationalOf radiusSyntax)
    let faces := ball.toList.map fun (i, center, radius) => (i, center - radius, center + radius)
    if round == 0 && !ball.isEmpty then
      let region := boxValue.zipIdx.map fun (I, i) =>
        match faces.find? (·.1 == i) with
        | some (_, lower, upper) => ⟨max I.lo lower, min I.hi upper⟩
        | none => I
      let (found, next) ← ballForms settings atoms literals ball region widths
        (fun strict form box => form.definiteOn gridBackend strict box) cache
      unless found.isEmpty do
        cache := next
        forms := forms ++ found
        trace[interval.constraints] "{found.size} forms on the ball"
        continue
    -- Forms that are definite on the whole box join the constraints before the first search.
    if round == 0 then
      if let some atRoot := oracle gridBackend boxValue then
        let (found, next) ← timed "forms on the whole box"
          ((rootForms atoms literals boxValue atRoot).run cache)
        unless found.isEmpty do
          cache := next
          forms := forms ++ found
          trace[interval.constraints] "{found.size} forms that are definite on the whole box"
          continue
    -- The cut points of the user.
    let mut points : Array (Nat × ℚ) := #[]
    for (atomSyntax, pointSyntax) in settings.cuts do
      points := points.push (← atomIndex atoms atomSyntax, ← rationalOf pointSyntax)
    -- The search, on the binary grid and then with exact rational endpoints.
    let work := Work.ofTree tree
    -- The limit of the search is its number of boxes, whatever heartbeats the declaration has.
    let run (search : Search) (depth : Nat) : MetaM (Except Stuck Refutation) := do
      let attempt : SearchM Refutation := do
        let start ← search.eval work boxValue
        if faces.isEmpty then cutThenDescend search points.toList start boxValue depth 0
        else isolateThenDescend search faces points.toList start boxValue depth 0
      let before ← IO.getNumHeartbeats
      try
        withOptions (fun options => Lean.maxHeartbeats.set options 0) <|
          withCurrHeartbeats (attempt.run' 0).run
      finally
        if let some ledger := settings.ledger then
          ledger.searched.modify (· + ((← IO.getNumHeartbeats) - before))
        IO.setNumHeartbeats before
    let finish (certificate : Refutation) (useGrid : Bool) : TacticM Unit :=
      close constraint holds box membership certificate useGrid
    let pins := tree.pins
    match ← timed "search on the binary grid"
        (run ⟨oracle gridBackend, settings.boxes, pins, widths⟩ settings.depth) with
    | .ok certificate =>
      timed "kernel check of the certificate" (finish certificate true)
      trace[interval.constraints] "closed by a certificate of {leaves certificate} boxes"
      return none
    | .error stuck =>
      trace[interval.constraints] "the search stopped at {if stuck.box.isEmpty then
        m!"constraints without atoms" else boxText atoms stuck.box}"
      trace[interval.constraints.time] "stop: {match stuck.reason with
        | .satisfied => "satisfied" | .depth => "depth" | .budget => "budget"
        | .point => "point"} after {stuck.boxes} boxes, {stuck.cuts} cuts"
      -- The report of this box is kept for a stop at the limit of the declaration, and the
      -- steps that follow are not started with less than an eighth of its heartbeats left.
      let report := stuckMessage atoms stuck settings.depth settings.boxes unread
      if let some ledger := settings.ledger then ledger.stuck.set (some report)
      if let some (used, limit) ← declarationHeartbeats then
        if limit ≤ used + limit / 8 then throwError "{report}\n{limitNote used limit}"
      -- A goal of the derivative step ends here once such goals have used their heartbeats.
      if (← settings.left) == some 0 then throwError "{report}"
      -- Rational endpoints decide what holds with equality at a rational point or matrix.
      if let .ok certificate ← timed "search with rational endpoints"
          (run ⟨oracle exactBackend, min settings.boxes 256, pins, widths⟩
            (min settings.depth 12)) then
        finish certificate false
        trace[interval.constraints] "closed by a certificate of {leaves certificate} boxes \
          with rational endpoints"
        return none
      -- At a point only sharper enclosures can decide: twice at most, the precision and the
      -- degree are doubled and the route starts again.
      if let .point := stuck.reason then
        if progress.sharpened < 2 then
          trace[interval.constraints] "the precision and the degree are doubled at a point, to \
            {2 * settings.precision} and {2 * settings.degree}"
          return some
            ({ settings with precision := 2 * settings.precision, degree := 2 * settings.degree },
              { progress with sharpened := progress.sharpened + 1 })
      unless fallbacks do
        fallbacks := true
        -- Comparisons that are linear need no boxes: `linarith` decides their conjunction.
        if ← Ledger.unlessFailed settings.ledger 1 (← outright) (do linearly (← outright)) then
          trace[interval.constraints] "closed by linarith"
          return none
      -- Forms of the comparisons that are undecided where the search stopped.
      let known (piece : FormPiece) : Bool :=
        forms.any fun old => old.piece.constraint == piece.piece.constraint
      let (found, next) ← timed "forms at the stuck box" ((formsAt atoms literals stuck boxValue
        widths (fun strict form box => form.definiteOn gridBackend strict box)
        (oracle gridBackend stuck.box)).run cache)
      cache := next
      let mut fresh := found.filter (!known ·)
      unless fresh.isEmpty do
        trace[interval.constraints] "{fresh.size} forms of the comparisons undecided there"
      -- Slopes of the values of the sine, the cosine, the hyperbolic tangent and the
      -- arctangent, once, and the route starts again.
      if fresh.isEmpty && !progress.sloped then
        let slopes ← timed "slopes" (introduceSlopes literals)
        unless slopes.isEmpty do
          trace[interval.constraints] "slopes for {slopes.size} values of the sine, the cosine, \
            the hyperbolic tangent or the arctangent"
          return some (settings, { progress with sloped := true, slopes })
      if fresh.isEmpty && !combined then
        combined := true
        -- not again for the same comparisons on the same box, where they gave no form
        let place := boxValue.foldl (init := (4 : UInt64)) fun code I =>
          mixHash (mixHash code (hash I.lo.num)) (mixHash (hash I.lo.den)
            (mixHash (hash I.hi.num) (hash I.hi.den)))
        let mut found := #[]
        if settings.margins then
          if ← Ledger.unlessFailed settings.ledger place (literals.map (·.proof)) (do
              let (made, next) ← timed "combinations of two comparisons"
                ((combinations atoms literals boxValue widths (oracle gridBackend)).run cache)
              combinationState.set (some (made, next))
              return !made.isEmpty) then
            if let some (made, next) ← combinationState.get then
              cache := next
              found := made
        fresh := found.filter (!known ·)
        -- Polynomial comparisons may have a certificate without any box: a combination of
        -- products of the linear comparisons, or of products of pairs of comparisons.
        if fresh.isEmpty then
          let facts ← outright
          if let some step ← polynomially atoms literals facts
              (← settings.arithmeticBudget) settings.ledger then
            trace[interval.constraints] "closed by {step}"
            return none
      -- Comparisons with quotients are multiplied by their denominators, and absolute values
      -- are opened into their two cases: each once, and the route starts again.
      if fresh.isEmpty && !progress.cleared then
        if ← clearDenominators then
          if (← getUnsolvedGoals).isEmpty then return none
          return some (settings, { progress with cleared := true })
      if fresh.isEmpty && !progress.opened then
        if let some cases ← openAbsoluteValues literals then
          trace[interval.constraints] "{cases.length} cases of the signs of the absolute values"
          refuteCases cases "the signs of the absolute values"
            (recurse settings { progress with opened := true, cleared := false })
          return none
      -- The cases of the disjunctions among the hypotheses, each refuted on its own: in a case
      -- the comparisons of its disjunct hold outright, and forms and combinations see them.
      if fresh.isEmpty && !progress.split then
        if let some cases ← splitCases (← getMainGoal) then
          trace[interval.constraints] "{cases.length} cases of the disjunctions"
          refuteCases cases "the disjunctions among the hypotheses"
            (recurse settings { progress with split := true })
          return none
      if fresh.isEmpty then throwError "{report}"
      forms := forms ++ fresh
  throwError "interval: the constraints were not refuted after six rounds of quadratic forms"

/--
Refute the real constraints of the local context by passes of `refuteOnce`, each of which closes
the goal or changes the hypotheses and asks for another pass; the cases of a goal get the passes
that are left. At most `fuel` passes are made along one branch.
-/
def refute (settings : Settings) (progress : Progress := {}) (fuel : Nat := 256) :
    TacticM Unit :=
  match fuel with
  | 0 => throwError "interval: the constraints were not refuted within the limit of passes"
  | fuel + 1 => do
    let next ← refuteOnce (fun settings progress => refute settings progress fuel) settings
      progress
    if let some (settings, progress) := next then refute settings progress fuel

/-- Whether `interval` treats a goal as a set of constraints: every goal that is not one
comparison under its binders. -/
def isConstraintGoal (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← instantiateMVars (← goal.getType)
  forallTelescopeReducing target fun _ body => do
    let body ← whnfR body
    match_expr body with
    | LE.le _ _ _ _ => return false
    | LT.lt _ _ _ _ => return false
    | _ => return true

/-- The settings that the options of a call give, for a goal that is a set of constraints. -/
def settingsOf (option : Array Ident) (value : Array Term) : TacticM Settings := do
  let mut settings : Settings := {}
  let mut seen : Array Name := #[]
  for option in option, value in value do
    let key := option.getId.eraseMacroScopes
    if seen.contains key then
      throwErrorAt option "duplicate interval option {key}"
    seen := seen.push key
    match key, value.raw.isNatLit? with
    | `precision, some v => settings := { settings with precision := v }
    | `degree, some v => settings := { settings with degree := v }
    | `depth, some v => settings := { settings with depth := v }
    | `boxes, some v => settings := { settings with boxes := v }
    | `maxHeartbeats, some v =>
      if v == 0 then throwErrorAt value "interval maxHeartbeats must be positive"
      settings := { settings with maxHeartbeats := v }
    | `precision, none | `degree, none | `depth, none | `boxes, none | `maxHeartbeats, none =>
      throwErrorAt value "interval {key} must be a natural number literal"
    | `cut, _ =>
      let `([$pairs,*]) := value
        | throwErrorAt value "interval cut must be a list of pairs (atom, point)"
      let mut cuts := #[]
      for pair in pairs.getElems do
        let `(($atom, $point)) := pair
          | throwErrorAt pair "interval cut must be a list of pairs (atom, point)"
        cuts := cuts.push (atom, point)
      settings := { settings with cuts }
    | `ball, _ | `box, _ =>
      let shape := if key == `ball then "(atom, center, radius)" else "(atom, lower, upper)"
      let `([$triples,*]) := value
        | throwErrorAt value "interval {key} must be a list of triples {shape}"
      let mut entries := #[]
      for triple in triples.getElems do
        let `(($atom, $first, $second)) := triple
          | throwErrorAt triple "interval {key} must be a list of triples {shape}"
        entries := entries.push (atom, first, second)
      settings := if key == `ball then { settings with ball := entries }
        else { settings with bounds := entries }
    | `form, _ =>
      let `([$rows,*]) := value
        | throwErrorAt value "interval form must be a list of rows of the upper triangle"
      let mut form := #[]
      for row in rows.getElems do
        let `([$entries,*]) := row
          | throwErrorAt row "interval form must be a list of rows of the upper triangle"
        form := form.push entries.getElems
      settings := { settings with form }
    | `facts, _ =>
      let `([$terms,*]) := value
        | throwErrorAt value "interval facts must be a list of terms"
      settings := { settings with facts := terms.getElems }
    | _, _ =>
      throwErrorAt option "expected precision, degree, depth, boxes, maxHeartbeats, cut, ball, \
        form, box or facts for a goal that is a set of constraints"
  return settings

/-- Refute the constraints of the main goal and of its context. Where the route fails, a
comparison in one variable is tried by the sign of its derivative (`byDerivative`), which hands
its own goals to the route again, at most `Settings.derivatives` times in a row. A failure
restores the proof state. -/
partial def run (settings : Settings) : TacticM Unit := do
  let saved ← saveState
  let ledger ← Ledger.new
  discard <| tryFinally'
    (do
      liftMetaTactic1 fun goal => some <$> prepare goal
      let prepared ← saveState
      -- At the limit of heartbeats of the declaration, the report of the last search that
      -- stopped says more than the timeout.
      try
        tryCatchRuntimeEx (refute { settings with ledger := some ledger }) fun error => do
          if error.isMaxHeartbeat then
            if let (some report, some (used, limit)) :=
                (← ledger.stuck.get, ← declarationHeartbeats) then
              throwError "{report}\n{limitNote used limit}"
          throw error
      catch error =>
        if error.isInterrupt || error.isRuntime || settings.derivatives == 0 then throw error
        -- a hint that states a bound or a form is what the call was asked to use
        unless settings.bounds.isEmpty && settings.ball.isEmpty && settings.form.isEmpty do
          throw error
        if let some (used, limit) ← declarationHeartbeats then
          if limit ≤ used + limit / 8 then throw error
        prepared.restore
        let passes ← match settings.passes with
          | some passes => pure passes
          | none => IO.mkRef { start := ← IO.getNumHeartbeats }
        -- the goals of the derivative step have no part in the options that name atoms
        let inner : Settings := { settings with
          derivatives := settings.derivatives - 1
          split := false
          margins := false
          passes := some passes
          arithmetic := some ((settings.arithmetic.getD settings.maxHeartbeats) / 2)
          cuts := #[], ball := #[], form := #[], bounds := #[], facts := #[] }
        let prove (goal : MVarId) : TacticM Bool := timed "a goal of the derivative step" do
          -- a goal that has failed in this call is not tried again, a call has a limit of
          -- goals, and none is started near the limit of the declaration
          let key ← goal.withContext do
            return (← mkForallFVars (← getLCtx).getFVars
              (← instantiateMVars (← goal.getType))).hash
          let done ← passes.get
          if done.count ≥ 40 || done.failed.contains key || (← inner.left) == some 0 then
            return false
          if let some (used, limit) ← declarationHeartbeats then
            if limit ≤ used + limit / 8 then return false
          passes.modify fun done => { done with count := done.count + 1 }
          let state ← saveState
          try
            let remaining ← Lean.Elab.Tactic.run goal do
              liftMetaTactic1 fun goal => return some (← goal.intros).2
              run inner
            if remaining.isEmpty then return true
          catch failure =>
            if failure.isInterrupt || failure.isRuntime then throw failure
          state.restore
          passes.modify fun done => { done with failed := done.failed.insert key }
          return false
        -- at the limit of the declaration the report of the route says more than the timeout
        let step := byDerivative prove settings.precision settings.degree settings.split
        let proved ← tryCatchRuntimeEx
          (do
            try
              -- without quotients first, where they can be cleared: the derivative of a
              -- quotient is a larger one, and a pole ends a range
              if ← clearDenominators then
                if (← getUnsolvedGoals).isEmpty || (← step) then pure true
                else
                  prepared.restore
                  step
              else step
            catch failure =>
              if failure.isInterrupt then throw failure
              pure false) fun failure => do
            if failure.isMaxHeartbeat then
              if let some (used, limit) ← declarationHeartbeats then
                throwError "{error.toMessageData}\n{limitNote used limit}"
            throw failure
        let done ← passes.get
        trace[interval.constraints.time] "the derivative step: {done.count} goals, \
          {((← IO.getNumHeartbeats) - done.start + done.hidden) / 1000} thousand heartbeats"
        unless proved do throw error)
    (fun result => do
      trace[interval.constraints.time] "heartbeats: {((← IO.getNumHeartbeats) - ledger.start) /
        1000} of the declaration, {(← ledger.searched.get) / 1000} of the searches, \
        {(← ledger.calculated.get) / 1000} of the arithmetic steps"
      -- a goal of the derivative step reports what the declaration does not pay for
      if let some passes := settings.passes then
        let hidden := (← ledger.searched.get) + (← ledger.calculated.get)
        passes.modify fun done => { done with hidden := done.hidden + hidden }
      unless result.isSome do saved.restore)

end FloatLib.Numerics.Interval.Tactic.Constraints

/-
One inequality goes to the route of `Interval` first. When that fails, and the options are not
its coefficient certificates, the constraints of the negated goal are tried with a small budget;
an inequality with an option of the constraint route goes there at once. The message of a double
failure is the one of the route of `Interval`. A goal `∃ x : ℝ, P x` is tried with a witness
first (`Constraints.proveByWitness`).
-/
open FloatLib.Numerics.Interval.Tactic in
@[no_fallback] elab_rules : tactic
  | `(tactic| interval $[($option:ident := $value:term)]*) => do
    let keys := option.map (·.getId.eraseMacroScopes)
    if ← Constraints.isConstraintGoal (← getMainGoal) then
      let settings ← Constraints.settingsOf option value
      -- an existential statement over the reals is proved by a witness
      match ← Constraints.proveByWitness
          (do evalTactic (← `(tactic| intros; interval $[($option:ident := $value:term)]*)))
          settings.precision settings.degree with
      | some true => return
      | some false =>
        try Constraints.run settings
        catch error =>
          if error.isInterrupt || error.isRuntime then throw error
          throwError "interval found no witness of the statement among the values that it \
            tries: the real variables of the context, also shifted by one, and the rationals: \
            {Constraints.witnessDescription}"
      | none => Constraints.run settings
    else if keys.any [`boxes, `cut, `ball, `form, `box, `facts].contains then
      Constraints.run (← Constraints.settingsOf option value)
    else
      try evalInequality option value
      catch error =>
        if error.isInterrupt || error.isRuntime || keys.any [`lower, `upper].contains then
          throw error
        let quiet := option.zip value |>.filter fun (name, _) =>
          name.getId.eraseMacroScopes != `depth
        try
          let settings ← Constraints.settingsOf (quiet.map (·.1)) (quiet.map (·.2))
          Constraints.run { settings with boxes := 2000 }
        catch other =>
          if other.isInterrupt || other.isRuntime then throw other
          throw error
