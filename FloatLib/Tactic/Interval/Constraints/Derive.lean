/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.ConstraintProof
public meta import FloatLib.Tactic.Interval.Constraints.Forms

/-!
# Bounds and equations that the constraints imply

The search of the constraint route needs a rational box, and the hypotheses do not always state
one. This module derives, with proofs, what the comparisons imply about single atoms, as new
hypotheses for the route:

* bounds of an atom from a comparison that is affine in it (`affineBound`), from a comparison
  with an expression that has an enclosure on the box of the other atoms (`enclosureBound`),
  from `|t| ≤ r`, `max p q ≤ r` and `r ≤ min p q` (`latticeBounds`), and from a comparison that
  confines the atoms without bounds to a sublevel set of a quadratic (`sublevelBound`), after its
  nonnegative terms of higher degree are dropped (`truncated`);
* equations: each term of a sum of nonnegative terms that a comparison bounds by zero vanishes
  (`vanishingTerms`), and an atom that the bounds pin to one rational value is replaced by it
  (`substitutePinned`).

Every result is a proposition with its proof term. The steps that check a quadratic form have
the kernel evaluate `Form.definiteOn` on the box of the atoms that have bounds (`partialBox`),
which is empty when no atom has any.

## Main definitions

* `Constraints.Limits`: precision, degree and heartbeats of a check.
* `Constraints.partialBox`: the box of the atoms with bounds, the others after it.
* `Constraints.affineBound`, `Constraints.enclosureBound`, `Constraints.sublevelBound`,
  `Constraints.latticeBounds`, `Constraints.truncated`: bounds.
* `Constraints.vanishingTerms`, `Constraints.substitutePinned`: equations.
-/

public meta section

open Lean Elab Tactic Meta Qq FloatLib.Util.Polynomial

namespace FloatLib.Numerics.Interval.Tactic.Constraints

/-- The limits of a check: the precision and the degree of its enclosures and the heartbeats of
its kernel evaluation. -/
structure Limits where
  /-- Fractional endpoint bits of the binary grid. -/
  precision : Nat := 64
  /-- Approximation degree of the elementary functions. -/
  degree : Nat := 16
  /-- Heartbeats of the kernel check, to which 200 are added for each box of a certificate. -/
  maxHeartbeats : Nat := 20000

/--
Replace each atom that the bounds pin to one rational value by that value: an atom `x` with the
bounds `c ≤ x` and `x ≤ c` is the number `c`, which `linarith` proves from the given facts. The
facts are computed only when an atom is pinned. The value replaces the atom in every hypothesis
except those that bound it, so the hypotheses that pin it stay. The result says whether a
hypothesis changed.
-/
def substitutePinned (atoms : Array Q(ℝ)) (bounds : Array Bound)
    (facts : TacticM (Array Lean.Expr)) : TacticM Bool := do
  let mut changed := false
  for (atom : Q(ℝ)) in atoms do
    let mut lower : Option ℚ := none
    let mut upper : Option ℚ := none
    for bound in bounds do
      unless ← withReducible (isDefEq atom bound.term) do continue
      if bound.lower then
        if lower.all (· < bound.value) then lower := some bound.value
      else if upper.all (bound.value < ·) then upper := some bound.value
    let (some lo, some hi) := (lower, upper) | continue
    unless lo == hi do continue
    -- the hypotheses that bound the atom stay; without another one there is nothing to do
    let goal ← getMainGoal
    let own (decl : LocalDecl) : MetaM Bool := do
      (← boundsOfProofFor atoms decl.toExpr).anyM fun bound =>
        withReducible (isDefEq atom bound.term)
    let needed ← goal.withContext do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        unless ← isProp decl.type do continue
        if ((← instantiateMVars decl.type).find? (· == atom)).isSome && !(← own decl) then
          return true
      return false
    unless needed do continue
    -- the equation, and each such hypothesis with the value in place of the atom
    let value ← ratTerm lo
    let some equation ← linarithProof? q($atom = $value) (← facts) | continue
    let (next, rewritten) ← rewriteHypotheses goal atom value equation own
    unless rewritten do continue
    replaceMainGoal [next]
    trace[interval.constraints] "{atom} is pinned to {value} and replaced by it"
    changed := true
  return changed

/-- The atoms without a lower or an upper bound among the given bounds. -/
def unbounded (bounds : Array Bound) (atoms : Array Q(ℝ)) : MetaM (Array Nat) := do
  let mut missing := #[]
  for atom in atoms, i in [0:atoms.size] do
    let mut lower := false
    let mut upper := false
    for bound in bounds do
      if ← withReducible (isDefEq atom bound.term) then
        if bound.lower then lower := true else upper := true
    unless lower && upper do missing := missing.push i
  return missing

/-- The box of the atoms that have bounds, for a step that runs while others have none. -/
structure PartialBox where
  /-- The atoms, those with bounds first. -/
  atoms : Array Q(ℝ)
  /-- How many atoms have bounds. -/
  count : Nat
  /-- The box of the atoms with bounds, with the proof that they belong to it; the environment
  continues with the atoms without bounds. -/
  data : ReifiedBox
  /-- The box as data. -/
  value : Box

/-- The box of the atoms with bounds. `missing` lists the atoms without. -/
def partialBox (atoms : Array Q(ℝ)) (bounds : Array Bound) (missing : Array Nat) :
    MetaM PartialBox := do
  let inside := (Array.range atoms.size).filter (!missing.contains ·)
  let outside : Q(List ℝ) := missing.foldr (fun j (rest : Q(List ℝ)) =>
    match atoms[j]? with
    | some (atom : Q(ℝ)) => q($atom :: $rest)
    | none => rest) q([])
  let data ← reifyBoxWithTail bounds (inside.toList.filterMap (atoms[·]?)) outside
  let value ← Diagnostics.readBox data.box
  return { atoms := (inside ++ missing).filterMap (atoms[·]?), count := inside.size, data, value }

/--
A bound on the atom `x` from a comparison in which `x` occurs once, with a rational coefficient,
and whose other terms have an enclosure on the box of the atoms with bounds: `α * x + R ≤ 0`
gives `x ≤ -lo / α` for `α > 0` and `-lo / α ≤ x` for `α < 0`, where `lo` is a rational below
the enclosure of `R`. The route of single inequalities proves `lo ≤ R`, and `linarith` the bound.
This is how `y ≤ Real.exp x` bounds `y` once `x` has bounds, and how an equation `y = f x`
gives `y` its box. The result is the bound, its proof and whether it is an upper bound.
-/
def enclosureBound (atoms : Array Q(ℝ)) (bounds : Array Bound) (missing : Array Nat)
    (literal : Literal) (i : Nat) (settings : Limits) :
    TacticM (Option (Q(Prop) × Lean.Expr × Bool)) := do
  let some (x : Q(ℝ)) := atoms[i]? | return none
  let expansion ← Expansion.of atoms literal none #[]
  let some index := expansion.generators.terms.findIdx? (· == x) | return none
  let slope := expansion.firstPoly.getD [(index, 1)] 0
  unless slope != 0 do return none
  -- `x` occurs in no other monomial, and no other atom without bounds occurs at all
  let rest : Poly := expansion.firstPoly.erase [(index, 1)]
  let unbounded := missing.filterMap fun j => atoms[j]?
  for (monomial, _) in Poly.monomials rest do
    for (g, _) in monomial do
      let some term := expansion.generators.terms[g]? | return none
      if unbounded.any fun atom => (term.find? (· == atom)).isSome then return none
  let R : Q(ℝ) ← polyTerm expansion.generators rest
  -- a rational with a short denominator below the enclosure of the rest
  let part ← partialBox atoms bounds missing
  let (expression, cache) ← (reify R).run { atoms := part.atoms }
  let some extensions := cache.extensions.toList.mapM compiledExtension? | return none
  let configValue : Backend.Config := ⟨settings.precision, settings.degree⟩
  let some onBox := oracle
      (Backend.withExtensions (Backend.binaryGrid configValue) configValue extensions) part.value
    | return none
  let some range := onBox.range (← Diagnostics.readExpr expression true) | return none
  let lower : ℚ := (Rat.floor (range.lo * 2 ^ 20) : ℤ) / 2 ^ 20
  let lowerTerm ← ratTerm lower
  let enclosed ← mkFreshExprMVar q($lowerTerm ≤ $R)
  let limit ← ratTerm (-lower / slope)
  let type : Q(Prop) := if 0 < slope then q($x ≤ $limit) else q($limit ≤ $x)
  try
    unless (← Lean.Elab.Tactic.run enclosed.mvarId! (evalInequality #[] #[])).isEmpty do
      return none
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none
  let some proof ← linarithProof? type #[literal.proof, ← instantiateMVars enclosed]
    | return none
  return some (type, proof, 0 < slope)

/--
A bound `-e < x ∧ x < e` on the atom `x` from a comparison `a ≤ b` that confines the atoms
without bounds to a sublevel set of a quadratic: its difference has degree two in these atoms, the
coefficient of `x ^ 2` is a positive rational, and the other coefficients are expressions in the
atoms with bounds, such as `π`. For `λ` below that coefficient and `e` large enough, the form of
`a - b + λ * (e ^ 2 - x ^ 2)` in the atoms without bounds, with the constant one among its
coordinates, is positive definite for all values of these atoms and all values of the others in
their box, which the kernel checks with exact rational arithmetic on that box
(`Constraint.abs_lt_of_form`). The smallest such `e` is searched for a few values of `λ` below
the largest that admits one. When the coefficients are rational and the set touches `x = ±e` for
a rational `e` that the constant term gives, the bound is the weak `-e ≤ x ∧ x ≤ e`, from a
semidefinite matrix (`Constraint.abs_le_of_form`). The result is the bound and its proof, or
`none` when the comparison is not of this kind. `missing` lists the atoms without bounds, and
`x` is the atom `i`, one of them.
-/
def sublevelBound (atoms : Array Q(ℝ)) (bounds : Array Bound) (missing : Array Nat)
    (literal : Literal) (i : Nat) (settings : Limits) :
    TacticM (Option (Q(Prop) × Lean.Expr)) := do
  let some (x : Q(ℝ)) := atoms[i]? | return none
  -- The atoms with bounds come first, so that their box is the box of the matrix entries.
  let part ← partialBox atoms bounds missing
  let ordered := part.atoms
  let some position := missing.findIdx? (· == i) | return none
  let centers := (Array.range missing.size).map fun k => (part.count + k, (0 : ℚ))
  let base ← Expansion.of ordered literal none centers
  let some (_, square) := base.generators.shifted[part.count + position]? | return none
  let leading := base.firstPoly.getD [(square, 2)] 0
  unless base.degreeTwo && 0 < leading do return none
  let data := part.data
  have box : Q(Box) := data.box
  have reals : Q(List ℝ) := data.reals
  have values : Q(Nat → ℝ) := q(fun i => $reals[i]?.getD 0)
  have membership : Q(Box.ContainsReal $box $values) := data.membership
  -- The enclosures of the generators on that box.
  let configValue : Backend.Config := ⟨settings.precision, settings.degree⟩
  let (_, cache) ← (base.generators.terms.forM fun term => discard (reify term)).run
    { atoms := ordered }
  let some extensions := cache.extensions.toList.mapM compiledExtension? | return none
  let some onBox := oracle
      (Backend.withExtensions (Backend.rational configValue) configValue extensions) part.value
    | return none
  let (ranges, cache) ← (base.ranges onBox).run cache
  let accepts (lam e : ℚ) (strict : Bool) : Bool :=
    let poly := (base.firstPoly.addMonomial [] (lam * e ^ 2)).addMonomial [(square, 2)] (-lam)
    (FormData.ofPoly base.generators poly).screen ranges strict
  -- The bound that the sublevel set touches, when it is rational: weak, by semidefiniteness.
  let touching : Option ℚ := do
    guard base.isQuadratic
    let ratio := -(base.firstPoly.getD [] 0) / leading
    guard (0 ≤ ratio)
    let root : ℚ := mkRat (Nat.sqrt ratio.num.natAbs) (Nat.sqrt ratio.den)
    guard (root ^ 2 == ratio && accepts leading root false)
    pure root
  let mut best : Option (ℚ × ℚ) := touching.map fun e => (leading, e)
  if best.isNone then
    -- The supremum of the `λ` for which some `e` is accepted, by bisection below `leading`.
    let feasible (lam : ℚ) : Bool := accepts lam ((2 : ℚ) ^ 60) true
    let some start := (List.range 40).findSome? fun k =>
        let lam := leading / 2 ^ (k + 1)
        if feasible lam then some lam else none
      | return none
    let mut inner := start
    let mut outer := 2 * start
    for _ in [0:10] do
      let middle := (inner + outer) / 2
      if feasible middle then inner := middle else outer := middle
    -- The smallest `e`, for a few `λ` below the supremum.
    for k in [1:6] do
      let lam := inner * (1 - (1 / 2 : ℚ) ^ k)
      let some top := (List.range 70).findSome? fun m =>
          let e := (2 : ℚ) ^ ((m : ℤ) - 10)
          if accepts lam e true then some e else none
        | continue
      let mut low := top / 2
      let mut high := top
      for _ in [0:6] do
        let middle := (low + high) / 2
        if accepts lam middle true then high := middle else low := middle
      if best.all fun (_, old) => high < old then best := some (lam, high)
  let some (lam, e) := best | return none
  let eTerm ← ratTerm e
  let expansion ← Expansion.of ordered literal
    (some ⟨false, q($eTerm ^ 2), q($x ^ 2), mkConst ``True.intro⟩) centers
  let (identity?, cache) ← (formIdentity ordered expansion lam).run cache
  let some identity := identity? | return none
  let exact := (← extensionTables cache.extensions).rationalBackend
    (have precision : Q(Nat) := mkNatLit settings.precision
     have degree : Q(Nat) := mkNatLit settings.degree
     q(⟨$precision, $degree⟩))
  have a : Q(ℝ) := literal.lhs
  have b : Q(ℝ) := literal.rhs
  have lamTerm : Q(ℝ) := identity.multiplier
  have form : Q(Form) := identity.quoted
  have functions : Q(Nat → List ℝ → ℝ) := exact.functions
  have backend : Q(Backend ℚ) := exact.backend
  have sound : Q(Backend.Sound $backend $functions) := exact.sound
  let (equation, _) ← ((identity.equation.run { values, functions, cache }).run #[] : MetaM _)
  have heq : Q($a - $b + $lamTerm * ($eTerm ^ 2 - $x ^ 2) = Form.eval $form $values $functions) :=
    equation
  have hab : Q($a ≤ $b) := if literal.strict then
    (have h : Q($a < $b) := literal.proof; q(le_of_lt $h)) else literal.proof
  let some hlam ← positivityProof? q((0 : ℝ) < $lamTerm) | return none
  let some he ← positivityProof? q((0 : ℝ) ≤ $eTerm) | return none
  if touching.isSome then
    have hsemidefinite : Q(Form.definiteOn $backend false $form $box = true) :=
      ← verifyClosedCheck q(Form.definiteOn $backend false $form $box = true)
        settings.maxHeartbeats
    return some (q(-$eTerm ≤ $x ∧ $x ≤ $eTerm),
      q(Constraint.abs_le_of_form $sound $hsemidefinite $membership $heq $hab $hlam $he))
  have hdefinite : Q(Form.definiteOn $backend true $form $box = true) :=
    ← verifyClosedCheck q(Form.definiteOn $backend true $form $box = true) settings.maxHeartbeats
  have hexcluded : Q(Form.excluded $form $box = true) := (q(Eq.refl true) : Lean.Expr)
  return some (q(-$eTerm < $x ∧ $x < $eTerm),
    q(Constraint.abs_lt_of_form $sound $hdefinite $hexcluded $membership $heq $hab $hlam $he))

/--
A bound on the atom `x` from a comparison whose difference is affine in atoms with rational
coefficients, `α * x + Σ βⱼ * yⱼ + γ` with `α ≠ 0`, when every other atom `yⱼ` has the bound it
needs: `x ≤ c` for `α > 0` and `c ≤ x` for `α < 0`, where `c` is the extreme value of
`-(Σ βⱼ * yⱼ + γ) / α` on the bounds of the `yⱼ`. `linarith` proves it from the given facts,
which are the comparisons that hold outright and the facts about constants, and which are
computed only when the comparison gives a bound. The result is the bound, its proof and whether
it is an upper bound.
-/
def affineBound (atoms : Array Q(ℝ)) (bounds : Array Bound) (facts : TacticM (Array Lean.Expr))
    (literal : Literal) (i : Nat) : TacticM (Option (Q(Prop) × Lean.Expr × Bool)) := do
  let some (x : Q(ℝ)) := atoms[i]? | return none
  let expansion ← Expansion.of atoms literal none #[]
  let some index := expansion.generators.terms.findIdx? (· == x) | return none
  let slope := expansion.firstPoly.getD [(index, 1)] 0
  unless slope != 0 do return none
  -- The extreme value of `-(Σ βⱼ * yⱼ + γ) / α`, with the bounds of the `yⱼ` that give it.
  let mut extreme : ℚ := 0
  for (monomial, coefficient) in expansion.firstPoly.monomials do
    match monomial with
    | [] => extreme := extreme - coefficient / slope
    | [(j, 1)] =>
      if j == index then continue
      let some (other : Q(ℝ)) := expansion.generators.terms[j]? | return none
      -- `-(β / α) * y` is largest at the upper bound of `y` when `-(β / α) > 0`
      let wantUpper := (0 < -(coefficient / slope)) == (0 < slope)
      let mut chosen : Option Bound := none
      for bound in bounds do
        if bound.lower == wantUpper then continue
        unless ← withReducible (isDefEq other bound.term) do continue
        if chosen.all fun old => if wantUpper then bound.value < old.value
            else old.value < bound.value then
          chosen := some bound
      let some bound := chosen | return none
      extreme := extreme - coefficient / slope * bound.value
    | _ => return none
  let limit ← ratTerm extreme
  let type : Q(Prop) := if 0 < slope then q($x ≤ $limit) else q($limit ≤ $x)
  let some proof ← linarithProof? type (← facts) | return none
  return some (type, proof, 0 < slope)

/--
The comparisons that a comparison with an absolute value, a maximum or a minimum implies, as
far as the goal does not have them yet: `|t| ≤ r` gives `-r ≤ t ∧ t ≤ r`, `max p q ≤ r` gives
`p ≤ r ∧ q ≤ r`, and `r ≤ min p q` gives `r ≤ p ∧ r ≤ q`, and the same for `<`. These bound the
terms inside.
-/
def latticeBounds (literals : Array Literal) : MetaM (Array Hypothesis) := do
  let mut facts : Array Hypothesis := #[]
  for literal in literals do
    have a : Q(ℝ) := literal.lhs
    have b : Q(ℝ) := literal.rhs
    let above : Array (Q(Prop) × Lean.Expr) ← match a with
      | ~q(|$t|) =>
        have h : Q(|$t| ≤ $b) := if literal.strict then
          (have h : Q(|$t| < $b) := literal.proof; q(le_of_lt $h)) else literal.proof
        pure #[(q(-$b ≤ $t ∧ $t ≤ $b), q(abs_le.mp $h))]
      | ~q(max $p $q) =>
        if literal.strict then
          have h : Q(max $p $q < $b) := literal.proof
          pure #[(q($p < $b ∧ $q < $b), q(max_lt_iff.mp $h))]
        else
          have h : Q(max $p $q ≤ $b) := literal.proof
          pure #[(q($p ≤ $b ∧ $q ≤ $b), q(max_le_iff.mp $h))]
      | _ => pure #[]
    let below : Array (Q(Prop) × Lean.Expr) ← match b with
      | ~q(min $p $q) =>
        if literal.strict then
          have h : Q($a < min $p $q) := literal.proof
          pure #[(q($a < $p ∧ $a < $q), q(lt_min_iff.mp $h))]
        else
          have h : Q($a ≤ min $p $q) := literal.proof
          pure #[(q($a ≤ $p ∧ $a ≤ $q), q(le_min_iff.mp $h))]
      | _ => pure #[]
    for (type, value) in above ++ below do
      unless (← getLCtx).any fun decl => decl.type == type do
        facts := facts.push { userName := `bound, type, value }
  return facts

/-- The summands of a real term with their signs: sums, differences and negations are opened,
and a zero is left out. The sign is `true` for a summand that is added. -/
partial def summands (e : Q(ℝ)) (sign : Bool := true) : MetaM (Array (Bool × Q(ℝ))) := do
  match e with
  | ~q($a + $b) => return (← summands a sign) ++ (← summands b sign)
  | ~q($a - $b) => return (← summands a sign) ++ (← summands b !sign)
  | ~q(-$a) => summands a !sign
  | ~q(0) => return #[]
  | _ => return #[(sign, e)]

/-- From `t = 0`, the equation for the part of `t` that must vanish: the base of a power, and
the other factor of a product with a factor that `positivity` proves positive. -/
partial def vanishingPart (t : Q(ℝ)) (h : Q($t = 0)) : MetaM (Q(ℝ) × Lean.Expr) := do
  match t with
  | ~q($p ^ ($n : ℕ)) =>
    have h : Q($p ^ $n = 0) := h
    vanishingPart p q(eq_zero_of_pow_eq_zero $h)
  | ~q($p * $q) =>
    have h : Q($p * $q = 0) := h
    if let some hp ← positivityProof? q(0 < $p) then
      return ← vanishingPart q q((mul_eq_zero.mp $h).resolve_left (ne_of_gt $hp))
    if let some hq ← positivityProof? q(0 < $q) then
      return ← vanishingPart p q((mul_eq_zero.mp $h).resolve_right (ne_of_gt $hq))
    return (t, h)
  | _ => return (t, h)

/--
The terms that a comparison forces to vanish. When the difference `a - b` of a comparison
`a ≤ b` is a sum of terms that `positivity` proves nonnegative, each of them is zero, and with it
the base of a power and the other factor of a positive factor: `x ^ 2 * Real.exp y + z ^ 2 ≤ 0`
gives `x = 0` and `z = 0`, and `(x ^ 2 + y ^ 2 - 1) ^ 2 + z ^ 2 ≤ 0` gives the circle and
`z = 0`. The sum is read from the expansion of the difference in monomials, and failing that
from the difference as it is written. The result is the equations, with their proofs.
-/
def vanishingTerms (atoms : Array Q(ℝ)) (literal : Literal) : TacticM (Array Hypothesis) := do
  if literal.strict then return #[]
  have a : Q(ℝ) := literal.lhs
  have b : Q(ℝ) := literal.rhs
  have hab : Q($a ≤ $b) := literal.proof
  -- the two readings of the sum; a bound on one atom says nothing new
  let expansion ← Expansion.of atoms literal none #[]
  if expansion.isBound then return #[]
  let monomials := expansion.firstPoly.monomials
  let mut readings : Array (Array Q(ℝ)) := #[]
  if monomials.all (fun (monomial, coefficient) => 0 < coefficient && !monomial.isEmpty) then
    readings := readings.push (← monomials.mapM fun (monomial, coefficient) =>
      polyTerm expansion.generators (Poly.addMonomial {} monomial coefficient))
  let written ← summands q($a - $b)
  if written.all (·.1) then readings := readings.push (written.map (·.2))
  for terms in readings do
    if terms.isEmpty then continue
    -- each term is nonnegative
    let mut nonneg : Array Lean.Expr := #[]
    for (term : Q(ℝ)) in terms do
      let some proof ← positivityProof? q(0 ≤ $term) | break
      nonneg := nonneg.push proof
    unless nonneg.size == terms.size do continue
    -- so each term is zero
    let mut found : Array Hypothesis := #[]
    for (term : Q(ℝ)) in terms do
      let some zero ← linarithProof? q($term = 0) (nonneg.push hab) | continue
      let (part, proof) ← vanishingPart term zero
      found := found.push { userName := `vanishes, type := q($part = 0), value := proof }
    unless found.isEmpty do
      trace[interval.constraints] "a sum of nonnegative terms is at most zero, so each is \
        zero: {found.map (·.type)}"
      return found
  return #[]

/--
A comparison without its terms of high degree. When the difference `a - b` of `a ≤ b`, expanded
in monomials, has monomials of degree above two in the atoms without bounds that `positivity`
proves nonnegative, such as `x ^ 4 / 40`, the rest of the difference is at most zero as well.
The result is that comparison `rest ≤ 0` with its proof, when a monomial was dropped and the
rest has degree two: it confines the atoms to a sublevel set of a quadratic, from which
`sublevelBound` reads their bounds. `missing` lists the atoms without bounds.
-/
def truncated (atoms : Array Q(ℝ)) (missing : Array Nat) (literal : Literal) :
    TacticM (Option Hypothesis) := do
  let expansion ← Expansion.of atoms literal none #[]
  let unbounded := missing.filterMap fun i => atoms[i]?
  let degree (monomial : Monomial) : Nat := monomial.foldl (init := 0) fun total (g, exponent) =>
    if (expansion.generators.terms[g]?).any (unbounded.contains ·) then total + exponent
    else total
  let mut rest : Poly := {}
  let mut dropped : Array Lean.Expr := #[]
  for (monomial, coefficient) in expansion.firstPoly.monomials do
    if degree monomial ≤ 2 then
      rest := rest.addMonomial monomial coefficient
      continue
    unless 0 < coefficient do return none
    let term : Q(ℝ) ← polyTerm expansion.generators (Poly.addMonomial {} monomial coefficient)
    let some proof ← positivityProof? q(0 ≤ $term) | return none
    dropped := dropped.push proof
  if dropped.isEmpty then return none
  let kept : Q(ℝ) ← polyTerm expansion.generators rest
  let some proof ← linarithProof? q($kept ≤ 0) (dropped.push literal.proof) | return none
  return some { userName := `truncated, type := q($kept ≤ 0), value := proof }

end FloatLib.Numerics.Interval.Tactic.Constraints
