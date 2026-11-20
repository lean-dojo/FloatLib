/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.RangeProof
public meta import FloatLib.Numerics.Enclosure.Expression.Range
public meta import FloatLib.Tactic.Interval.Constraints.Derive

/-!
# Atoms without bounds: boxes with infinite ends

The search of the constraint route needs two rational ends for every atom. An atom that the
hypotheses bound on one side only, or not at all, still has a range with an infinite end, and the
enclosures of `FloatLib.Numerics.Enclosure.Expression.Range` evaluate the constraints on such
ranges: `Real.exp (-x)` is in `[0, 1]` for every `x ≥ 0`. This module uses them in two steps of
the route.

* `closeOnRanges` closes the goal when the constraints fail on the whole box of ranges, by one
  evaluation that the kernel repeats (`Constraint.not_holds_of_failsOn`).
* `tailBounds` gives an atom the side that it lacks. When the constraints fail on the part of the
  box where the atom is beyond some `M`, the atom is on this side of `M`: that is a bound, and the
  route goes on with a box. `M` is the nearest of the values `b ± 2 ^ k`, for `k` from `-3` to
  `10` and `b` the end that the atom has (or `0`), whose tail fails.

Neither step cuts a range, so they decide what the ends of the ranges decide: a comparison whose
two sides grow together, such as `Real.log x ≤ x`, is not refuted on a tail.

## Main definitions

* `RangeBox`, `rangeBox`: the ranges of the atoms, with the proof that the atoms are in them.
* `RangeContext`: what the two steps need of the route.
* `closeOnRanges`, `tailBounds`: the two steps.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- The constraint that a tree is the data of. -/
def Tree.constraint : Tree → Constraint
  | .atom a => .fails a.relation a.expr
  | .form strict f _ => .form strict f
  | .and l r => .and l.constraint r.constraint
  | .or l r => .or l.constraint r.constraint

/-- The ranges of some real terms, with the proof that the terms are in them. -/
structure RangeBox where
  /-- The ranges, in the order of the terms. -/
  box : Q(List Range)
  /-- The ranges as data. -/
  value : List Range
  /-- The terms. -/
  reals : Q(List ℝ)
  /-- Each term is in its range. -/
  membership : Q(Range.BoxContains $box (fun i => $reals[i]?.getD 0))

/-- The ranges of some terms: the strongest ends that the bounds give each of them
(`strongestBounds`), and an infinite end where there is none. -/
def rangeBox (bounds : Array Bound) : List Q(ℝ) → MetaM RangeBox
  | [] =>
    return ⟨q([]), [], q([]), q(Range.boxContains_nil (fun i => ([] : List ℝ)[i]?.getD 0))⟩
  | term :: tail => do
    let (lower, upper) ← strongestBounds bounds term
    let rest ← rangeBox bounds tail
    have restBox : Q(List Range) := rest.box
    have restReals : Q(List ℝ) := rest.reals
    have restProof : Q(Range.BoxContains $restBox (fun i => $restReals[i]?.getD 0)) :=
      rest.membership
    let (range, value, head) : Q(Range) × Range × Lean.Expr := match lower, upper with
      | some l, some u =>
        have lo : Q(ℚ) := l.rational
        have hi : Q(ℚ) := u.rational
        have hl : Q(($lo : ℝ) ≤ $term) := l.proof
        have hu : Q($term ≤ ($hi : ℝ)) := u.proof
        (q(⟨some $lo, some $hi⟩), ⟨some l.value, some u.value⟩, q(Range.contains_both $hl $hu))
      | some l, none =>
        have lo : Q(ℚ) := l.rational
        have hl : Q(($lo : ℝ) ≤ $term) := l.proof
        (q(⟨some $lo, none⟩), ⟨some l.value, none⟩, q(Range.contains_lower $hl))
      | none, some u =>
        have hi : Q(ℚ) := u.rational
        have hu : Q($term ≤ ($hi : ℝ)) := u.proof
        (q(⟨none, some $hi⟩), ⟨none, some u.value⟩, q(Range.contains_upper $hu))
      | none, none => (q(Range.whole), Range.whole, q(Range.contains_whole $term))
    have range : Q(Range) := range
    have head : Q(Range.Contains $range $term) := head
    let membership : Lean.Expr := q(Range.boxContains_cons (R := $range) (box := $restBox)
      (values := fun i => ($term :: $restReals)[i]?.getD 0) $head $restProof)
    return ⟨q($range :: $restBox), value :: rest.value, q($term :: $restReals), membership⟩

deriving instance ToExpr for UnaryOp

/-- The registered calls that are unary operations of the expression language, in the order of
the registrations: for each, the operation that it is, if it is one. -/
structure NameTable where
  /-- The names. -/
  names : Q(List (Option UnaryOp))
  /-- The names as data. -/
  value : List (Option UnaryOp)
  /-- The real functions of the registrations bear these names:
  `Range.NamesSound names (extensionValues functions)` for the function table of
  `extensionTables`. -/
  sound : Lean.Expr

/-- The table of names of the registrations that a reified expression calls
(`unaryRegistrations`). -/
def nameTable (registrations : Array Name) : MetaM NameTable := do
  let mut names : Q(List (Option UnaryOp)) := q([])
  let mut value : List (Option UnaryOp) := []
  let mut functions : Q(List (List ℝ → ℝ)) := q([])
  let mut sound : Lean.Expr := q(Range.namesSound_nil)
  for registration in registrations.reverse do
    let (E, function, _, _) ← extensionCertificate registration
    have f : Q(RealFunction (Extension.arity $E)) := function
    have entry : Q(List ℝ → ℝ) := q(RealFunction.apply $f)
    have rest : Q(List (Option UnaryOp)) := names
    have restFunctions : Q(List (List ℝ → ℝ)) := functions
    let (name, quoted, proof) : Option UnaryOp × Q(Option UnaryOp) × Lean.Expr :=
      match unaryRegistrations.lookup registration with
      | some op =>
        have operation : Q(UnaryOp) := toExpr op
        (some op, q(some $operation), q(Range.named $operation))
      | none => (none, q(none), q(Range.unnamed $entry))
    sound := mkAppN (mkConst ``Range.NamesSound.cons)
      #[rest, restFunctions, sound, quoted, entry, proof]
    names := q($quoted :: $rest)
    value := name :: value
    functions := q($entry :: $restFunctions)
  return { names, value, sound }

/-- What the steps on ranges need of the route: the constraint with its data and the proof that
it holds, and the backend with rational endpoints with its proofs. -/
structure RangeContext where
  /-- The constraint of the hypotheses. -/
  constraint : Q(Constraint)
  /-- Its data. -/
  tree : Tree
  /-- The real value of each variable: the atoms in their order. -/
  values : Q(Nat → ℝ)
  /-- The real function of each registered call. -/
  functions : Q(Nat → List ℝ → ℝ)
  /-- The constraint holds at the atoms. -/
  holds : Q(Constraint.Holds $constraint $values $functions)
  /-- The backend with rational endpoints. -/
  backend : Q(Backend ℚ)
  /-- The backend as data. -/
  backendValue : Backend ℚ
  /-- Its operations enclose their real results. -/
  sound : Q(Backend.Sound $backend $functions)
  /-- It decodes an endpoint to itself. -/
  decodes : Q(∀ q : ℚ, Backend.decode $backend q = some q)
  /-- The registered calls that are unary operations. -/
  names : Q(List (Option UnaryOp))
  /-- The names as data. -/
  namesValue : List (Option UnaryOp)
  /-- The registered functions bear the names. -/
  named : Q(Range.NamesSound $names $functions)
  /-- Heartbeats of a kernel check. -/
  heartbeats : Nat

/-- A proof that the constraint does not hold while the atoms are in the given ranges, when it
fails there: the evaluation is run as compiled code first, and then by the kernel. -/
def RangeContext.refuted? (ctx : RangeContext) (ranges : RangeBox) :
    TacticM (Option Lean.Expr) := do
  unless ctx.tree.constraint.failsOn ctx.backendValue ctx.namesValue (Range.env ranges.value) do
    return none
  have constraint : Q(Constraint) := ctx.constraint
  have values : Q(Nat → ℝ) := ctx.values
  have functions : Q(Nat → List ℝ → ℝ) := ctx.functions
  have backend : Q(Backend ℚ) := ctx.backend
  have sound : Q(Backend.Sound $backend $functions) := ctx.sound
  have decodes : Q(∀ q : ℚ, Backend.decode $backend q = some q) := ctx.decodes
  have names : Q(List (Option UnaryOp)) := ctx.names
  have named : Q(Range.NamesSound $names $functions) := ctx.named
  have box : Q(List Range) := ranges.box
  have membership : Q(Range.BoxContains $box $values) := ranges.membership
  try
    have checked : Q(Constraint.failsOn $backend $names (Range.env $box) $constraint = true) :=
      ← verifyClosedCheck
        q(Constraint.failsOn $backend $names (Range.env $box) $constraint = true) ctx.heartbeats
    let refuted : Q(¬ Constraint.Holds $constraint $values $functions) :=
      q(Constraint.not_holds_of_failsOn $sound $decodes $named $checked $membership)
    return some refuted
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none

/-- Close the main goal `False` when the constraints fail on the whole box of the ranges of the
atoms. The result says whether the goal was closed. -/
def closeOnRanges (ctx : RangeContext) (atoms : Array Q(ℝ)) (bounds : Array Bound) :
    TacticM Bool := do
  let some refuted ← ctx.refuted? (← rangeBox bounds atoms.toList) | return false
  closeMainGoal `interval (mkApp refuted ctx.holds)
  return true

/-- The candidates for the end of a tail, from the largest tail to the smallest: `b + 2 ^ k` for
an upward tail and `b - 2 ^ k` for a downward one, with `k` from `-3` to `10`, where `b` is the
end that the atom has; without one, the values `±2 ^ k` and zero. -/
def tailEnds (bound? : Option ℚ) (upward : Bool) : Array ℚ :=
  let steps : List ℚ := (List.range 14).map fun k => (2 : ℚ) ^ ((k : ℤ) - 3)
  match bound? with
  | some b => (steps.map fun step => if upward then b + step else b - step).toArray
  | none =>
    let ascending := steps.reverse.map (-·) ++ [0] ++ steps
    (if upward then ascending else ascending.reverse).toArray

/--
Bounds for the atoms that lack a side, from the tails on which the constraints fail. For an atom
`x` without an upper bound, the constraints are evaluated on the box of ranges with `x` in
`[M, +∞)`; when they fail there for some `M` of `tailEnds`, the least such `M` is found by
bisection and `x < M` is proved: under `M ≤ x` the atoms are in that box, where the constraint
does not hold. The same for a lower bound, with `(-∞, M]` and `M < x`. `missing` lists the
atoms that lack a side. The result is the bounds with their proofs.
-/
def tailBounds (ctx : RangeContext) (atoms : Array Q(ℝ)) (bounds : Array Bound)
    (missing : Array Nat) : TacticM (Array Hypothesis) := do
  let ranges ← rangeBox bounds atoms.toList
  let mut facts : Array Hypothesis := #[]
  for i in missing do
    let some (x : Q(ℝ)) := atoms[i]? | continue
    let some range := ranges.value[i]? | continue
    for upward in [true, false] do
      -- only the side that the atom lacks
      if (if upward then range.hi else range.lo).isSome then continue
      let ends := tailEnds (if upward then range.lo else range.hi) upward
      let fails (k : Nat) : Bool :=
        let tail : Range := if upward then ⟨some (ends.getD k 0), none⟩
          else ⟨none, some (ends.getD k 0)⟩
        ctx.tree.constraint.failsOn ctx.backendValue ctx.namesValue
          (Range.env (ranges.value.set i tail))
      unless fails (ends.size - 1) do continue
      -- the largest tail on which the constraints fail
      let mut low := 0
      let mut high := ends.size - 1
      for _ in [0:ends.size] do
        if high ≤ low then break
        let middle := (low + high) / 2
        if fails middle then high := middle else low := middle + 1
      let limit ← ratTerm (ends.getD high 0)
      let beyond : Q(Prop) := if upward then q($limit ≤ $x) else q($x ≤ $limit)
      let proof? ← withLocalDeclD `h beyond fun h => do
        let tail ← rangeBox (bounds ++ (← boundsOfProofFor atoms h)) atoms.toList
        let some refuted ← ctx.refuted? tail | return none
        return some (← mkLambdaFVars #[h] (mkApp refuted ctx.holds))
      let some proof := proof? | continue
      if upward then
        have never : Q(¬ $limit ≤ $x) := proof
        facts := facts.push
          { userName := `bound, type := q($x < $limit), value := q(not_le.mp $never) }
      else
        have never : Q(¬ $x ≤ $limit) := proof
        facts := facts.push
          { userName := `bound, type := q($limit < $x), value := q(not_le.mp $never) }
  return facts

end FloatLib.Numerics.Interval.Tactic.Constraints
