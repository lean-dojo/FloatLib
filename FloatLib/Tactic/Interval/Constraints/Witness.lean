/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.Interval.Constraints.Slopes

/-!
# Existential statements by a witness

The constraint route refutes sets of constraints, and the negation of `∃ x : ℝ, P x` is a
statement about every `x`, not a constraint on some. Such a goal is proved by a witness instead:
`proveByWitness` tries values for `x` and hands `P` at the value to `interval`. The values are
each real variable `y` of the context with `y + 1` and `y - 1`, and then the rationals of
`witnessCandidates`:

* zero, and the powers of two `2 ^ k` and `-(2 ^ k)` for every integer `k` from `-reach` to
  `reach`;
* the rational constants that `P` names, each with the two numbers at distance one from it, and
  the mean of each two of them, so that `5 < x ∧ x < 7` finds `6`.

Neither a numerator nor a denominator of a value is above `2 ^ reach`, and the values are tried
in the order of the larger of the two, the simplest first. `reach` and the two other bounds are
the fields of `WitnessBounds`.

A statement `P` at a rational value that is a combination of comparisons of numbers is first
evaluated with the enclosures of the search (`holdsByEvaluation`), so that the tactic runs only
on a value at which it holds. The enclosure of an exponential at a large argument is long, so
at a value above `2 ^ plain` in size that evaluation has no enclosure of an exponential, a
hyperbolic function or a real power at an argument above `2 ^ plain` (`guardedExtension?`),
and such a value is passed over. Where the
evaluation is not possible, because `P` has quantifiers of its own or other variables, the
tactic is tried on the first few values. A statement with several existential quantifiers is
proved one quantifier at a time.

## Main definitions

* `WitnessBounds`: the bounds on the values.
* `witnessCandidates`: the rational values for a statement.
* `holdsByEvaluation`: the evaluation of a statement about numbers.
* `proveByWitness`: the step.
-/

public meta section

open Lean Elab Tactic Meta Qq

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- The bounds on the witnesses that are tried, the first two as exponents of two. -/
structure WitnessBounds where
  /-- A witness whose numerator or denominator is above `2 ^ plain` is tried only where the
  statement takes no exponential of a number above `2 ^ plain`. -/
  plain : Nat := 10
  /-- The largest exponent `k` of a power of two `2 ^ k` or `2 ^ (-k)` that is tried. No
  numerator and no denominator of a witness is above `2 ^ reach`. -/
  reach : Nat := 20
  /-- How many rational constants of a statement give witnesses: the first ones it names. -/
  named : Nat := 8

/-- The larger of the numerator and the denominator of a rational, and zero for zero: the
order of the witnesses. -/
def witnessHeight (value : ℚ) : Nat := if value = 0 then 0 else max value.num.natAbs value.den

/-- The rational constants that a statement names: the closed real terms of `statement` with a
rational value, the largest such terms only, in the order in which they occur and each once.
The search ends after `limit` of them. -/
partial def statementConstants (statement : Lean.Expr) (limit : Nat) : MetaM (Array ℚ) := do
  let rec visit (term : Lean.Expr) (found : Array ℚ) : MetaM (Array ℚ) := do
    if found.size ≥ limit then return found
    if !term.hasLooseBVars && !term.hasFVar && !term.hasMVar then
      -- a closed term: a constant of the statement when it is a real number with a rational
      -- value, and otherwise its parts may be
      let rational? ← try
          if ← isDefEq (← inferType term) q(ℝ) then
            pure ((← rationalValue? term).map (·.value))
          else pure none
        catch error =>
          if error.isInterrupt || error.isRuntime then throw error
          pure none
      if let some value := rational? then
        return if found.contains value then found else found.push value
    match term with
    | .app function argument => visit argument (← visit function found)
    | .lam _ _ body _ | .forallE _ _ body _ => visit body found
    | .letE _ _ value body _ => visit body (← visit value found)
    | .mdata _ inner | .proj _ _ inner => visit inner found
    | _ => return found
  visit statement #[]

/--
The rational numbers that are tried as witnesses of a statement that names the rational
constants `constants`, the simplest first: zero, the powers of two `2 ^ k` and `-(2 ^ k)` for
`-reach ≤ k ≤ reach`, each constant with the two numbers at distance one from it, and the mean
of each two constants. A number whose numerator or denominator is above `2 ^ reach` is left
out. The order is that of `witnessHeight`, an integer before a fraction, a positive number
before a negative one, and then the smaller number first.
-/
def witnessCandidates (constants : Array ℚ := #[]) (reach : Nat := ({} : WitnessBounds).reach) :
    Array ℚ := Id.run do
  let mut values : Array ℚ := #[0, 1, -1]
  for k in [1:reach + 1] do
    let power : ℚ := 2 ^ k
    values := values ++ #[power, -power, 1 / power, -(1 / power)]
  for constant in constants do
    values := values ++ #[constant, constant + 1, constant - 1]
  for i in [:constants.size] do
    for j in [i + 1:constants.size] do
      values := values.push ((constants[i]! + constants[j]!) / 2)
  let mut distinct : Array ℚ := #[]
  for value in values do
    if witnessHeight value ≤ 2 ^ reach && !distinct.contains value then
      distinct := distinct.push value
  let key (value : ℚ) : Nat :=
    4 * witnessHeight value + (if value.den = 1 then 0 else 2) + (if value < 0 then 1 else 0)
  return distinct.qsort fun left right =>
    key left < key right || (key left == key right && left < right)

/-- What is tried within `bounds`, for the message of a statement without a witness. -/
def witnessDescription (bounds : WitnessBounds := {}) : String :=
  s!"zero, the powers of two from 2 ^ -{bounds.reach} to 2 ^ {bounds.reach} with both signs, \
    and the first {bounds.named} rational constants of the statement, each with the two \
    numbers at distance one from it, and the mean of each two, without the numbers whose \
    numerator or denominator is above 2 ^ {bounds.reach}; a value above 2 ^ {bounds.plain} in \
    size only where the statement takes no exponential of a number of that size"

/-- The executable enclosure of a registration of `Functions` for a witness above `2 ^ plain`
in size: the exponential, the hyperbolic sine, cosine and tangent and the real power have none
at an argument above `2 ^ plain` in size, where their enclosure is long, and every other
function has its own. -/
def guardedExtension? (plain : Nat) (registration : Name) : Option Extension := do
  let extension ← compiledExtension? registration
  let exponential := registration == ``rpow_extension_sound ||
    (unaryRegistrations.lookup registration).any fun op =>
      op matches .exp | .sinh | .cosh | .tanh
  if !exponential then return extension
  return { extension with
    enclose? := fun config inputs =>
      if inputs.any fun I => max |I.lo| |I.hi| > 2 ^ plain then none
      else extension.enclose? config inputs }

/--
Whether a statement about numbers holds, by one evaluation of its comparisons with the
enclosures of the search: `some true` when it does, `some false` when the enclosures do not show
it, and `none` when the statement is not a combination of real comparisons without variables.
With `guard := some plain`, the enclosures of the functions are those of
`guardedExtension? plain`. The answer is not trusted: it selects the values on which
`interval` is run.
-/
def holdsByEvaluation (statement : Q(Prop)) (precision degree : Nat)
    (guard : Option Nat := none) : MetaM (Option Bool) := do
  let (piece?, cache) ← (reifyProp #[] true statement).run {}
  let some piece := piece? | return none
  unless cache.atoms.isEmpty do return none
  let some extensions := cache.extensions.toList.mapM
      (match guard with
        | some plain => guardedExtension? plain
        | none => compiledExtension?)
    | return none
  let config : Backend.Config := ⟨precision, degree⟩
  let some atPoint :=
      oracle (Backend.withExtensions (Backend.binaryGrid config) config extensions) []
    | return none
  return some (match (Work.ofTree piece.tree).eval atPoint with
    | .holds => true
    | _ => false)

/--
Prove a main goal `∃ x : ℝ, P x` by a witness. The candidates are each real variable `y` of the
context with `y + 1` and `y - 1`, and then the rationals of `witnessCandidates` for the
constants that `P` names, within `bounds`. `prove` is run
on `P` at a rational value at which `holdsByEvaluation` finds it true, with the enclosures of
`guardedExtension?` at a value above `2 ^ bounds.plain` in size; at a value where `P`
cannot be evaluated, `prove` is run for the first `blind` of them only, unless `P` is
existential again and so selects its own values. The result is `none` when the goal is not such
a statement, and otherwise says whether it was proved.
-/
def proveByWitness (prove : TacticM Unit) (precision degree : Nat) (blind : Nat := 8)
    (bounds : WitnessBounds := {}) : TacticM (Option Bool) := withMainContext do
  let goal ← getMainGoal
  let target ← whnfR (← instantiateMVars (← goal.getType))
  let_expr Exists α predicate := target | return none
  unless ← isDefEq α q(ℝ) do return none
  -- the real variables of the context, then the rationals
  let mut candidates : Array (Q(ℝ) × Option ℚ) := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isDefEq decl.type q(ℝ) then
      have y : Q(ℝ) := decl.toExpr
      candidates := candidates ++ #[(y, none), (q($y + 1), none), (q($y - 1), none)]
  let constants ← statementConstants predicate bounds.named
  for value in witnessCandidates constants bounds.reach do
    candidates := candidates.push (← ratTerm value, some value)
  let mut unseen := 0
  for (witness, rational?) in candidates do
    let body := (mkApp predicate witness).headBeta
    let known ← match rational? with
      | some value =>
        holdsByEvaluation body precision degree
          (if witnessHeight value > 2 ^ bounds.plain then some bounds.plain else none)
      | none => pure none
    if known == some false then continue
    -- a body that is existential again selects its own values
    if known.isNone && !body.isAppOf ``Exists then
      if unseen ≥ blind then continue
      unseen := unseen + 1
    let saved ← saveState
    try
      let inner ← mkFreshExprMVar body
      goal.assign (mkApp4 (mkConst ``Exists.intro [Level.one]) α predicate witness inner)
      setGoals [inner.mvarId!]
      prove
      if (← getUnsolvedGoals).isEmpty then
        trace[interval.constraints] "proved with the witness {witness}"
        return some true
      saved.restore
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      saved.restore
  return some false

end FloatLib.Numerics.Interval.Tactic.Constraints
