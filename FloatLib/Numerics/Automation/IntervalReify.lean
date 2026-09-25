/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.IntervalAggregate
public import FloatLib.Numerics.Enclosure.Expression.Real
public import Mathlib.Tactic.NormNum
public meta import FloatLib.Numerics.Enclosure.Expression.Basic
public meta import Mathlib.Util.Qq

/-!
# Reification for interval proofs

The interval tactic translates real arithmetic into the common expression language and extracts
rational variable bounds from hypotheses. Numerical constants are recognized by `norm_num`,
which also supplies the equalities used when converting bounds. Unrecognized real subexpressions
become variables and require explicit bounds; they are never assigned guessed values.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Tactic

open Mathlib.Meta.NormNum

/-- Interpret the rational certificate produced by `norm_num` as a real equality. -/
theorem eq_rat_of_isRat {x : ℝ} {n : ℤ} {d : ℕ} (h : IsRat x n d) :
    x = ((mkRat n d : ℚ) : ℝ) := by
  rw [Rat.cast_mkRat_of_ne_zero n h.den_nz]
  exact h.to_raw_eq

end FloatLib.Numerics.Interval.Tactic

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

open Mathlib.Meta.NormNum

/-- A rational value, its syntax, and a proof that a real expression has that value. -/
structure RationalValue (e : Q(ℝ)) where
  /-- The normalized rational value, used when comparing candidate bounds. -/
  value : ℚ
  /-- Quoted rational expression for the value. -/
  rational : Q(ℚ)
  /-- Proof that the original real expression equals this rational. -/
  equality : Q($e = ($rational : ℝ))

/-- Obtain a rational certificate using the registered `norm_num` extensions. -/
def deriveRationalValue (e : Q(ℝ)) : MetaM (RationalValue e) := do
  let ⟨value, n, d, h⟩ ← deriveRat e q(inferInstance)
  let rational : Q(ℚ) := q(mkRat $n $d)
  let equality : Lean.Expr := q(eq_rat_of_isRat $h)
  return ⟨value, rational, equality⟩

/-- Recognize a closed rational expression, exposing numerical coercions when necessary. -/
def rationalValue? (e : Q(ℝ)) : MetaM (Option (RationalValue e)) := do
  let reduced : Q(ℝ) ← zetaReduce e
  if reduced.hasFVar then return none
  try
    let value ← deriveRationalValue reduced
    return some ⟨value.value, value.rational, value.equality⟩
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    try
      let normalized ← normalizeAggregateNumerals reduced
      if normalized.expr == reduced then return none
      let scalar : Q(ℝ) := normalized.expr
      let value ← deriveRationalValue scalar
      let equality ← mkEqTrans (← normalized.getProof) value.equality
      return some ⟨value.value, value.rational, equality⟩
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      return none

/-- The real subexpressions used as numbered variables in a reified expression. -/
abbrev Variables := Array Q(ℝ)

/-- Reuse an existing atom index, or allocate one for a new real subexpression. -/
def reifyAtom (e : Q(ℝ)) : StateRefT Variables MetaM Q(Interval.Expr) := do
  let atoms ← get
  if let some i := atoms.findIdx? (· == e) then
    let i : Q(Nat) := mkNatLit i
    return q(Interval.Expr.var $i)
  let i : Q(Nat) := mkNatLit atoms.size
  modify (·.push e)
  return q(Interval.Expr.var $i)

/-- A rational leaf and the equality certificate already obtained while reifying it. -/
structure RationalCertificate where
  /-- The rational used in the constant expression node. -/
  rational : Q(ℚ)
  /-- A proof that the map key equals the real cast of `rational`. -/
  equality : Lean.Expr

/-- Successful rational recognitions, indexed by their original real expressions. -/
abbrev RationalCache := Lean.ExprMap RationalCertificate

/-- Share reified subexpressions and retain their rational certificates. -/
structure ReifyCache where
  /-- Successful rational recognitions. -/
  rationals : RationalCache := {}
  /-- Reified expressions, including atoms and repeated scalar subexpressions. -/
  expressions : Lean.ExprMap Q(Interval.Expr) := {}

/--
Reify real arithmetic, natural powers, and elementary functions.

Rational constants are evaluated before the structural cases. An unsupported operation is kept
as an atom, so the caller must supply an interval for that complete real subexpression.
-/
partial def reifyCore (e : Q(ℝ)) :
    StateRefT ReifyCache (StateRefT Variables MetaM) Q(Interval.Expr) := do
  let e : Q(ℝ) ← pure e.consumeMData
  if let some result := (← get).expressions.get? e then return result
  let result ← build e
  modify fun cache ↦ { cache with expressions := cache.expressions.insert e result }
  return result
where
  /-- Recognize a scalar expression that has not yet been reified. -/
  build (e : Q(ℝ)) :
      StateRefT ReifyCache (StateRefT Variables MetaM) Q(Interval.Expr) := do
    if let some value ← rationalValue? e then
      modify fun cache ↦
        { cache with rationals := cache.rationals.insert e ⟨value.rational, value.equality⟩ }
      let q := value.rational
      return q(Interval.Expr.const $q)
    match e with
    | ~q($a * $b + $c) => do
      let a ← reifyCore a
      let b ← reifyCore b
      let c ← reifyCore c
      return q(Interval.Expr.ternary .fma $a $b $c)
    | ~q($a + $b) => binary .add a b
    | ~q($a - $b) => binary .sub a b
    | ~q($a * $b) => binary .mul a b
    | ~q($a / $b) => binary .div a b
    | ~q(min $a $b) => binary .min a b
    | ~q(max $a $b) => binary .max a b
    | ~q(-$a) => unary .neg a
    | ~q(abs $a) => unary .abs a
    | ~q($a⁻¹) => unary .inv a
    | ~q($a ^ ($n : Nat)) =>
      let n : Q(Nat) ← whnf n
      if let some value := n.rawNatLit? then
        let n : Q(Nat) := mkNatLit value
        let a ← reifyCore a
        return q(Interval.Expr.unary (.pow $n) $a)
      liftM (reifyAtom e)
    | ~q(Real.exp $a) => unary .exp a
    | ~q(Real.log $a) => unary .log a
    | ~q(Real.sin $a) => unary .sin a
    | ~q(Real.cos $a) => unary .cos a
    | ~q(Real.tan $a) => unary .tan a
    | ~q(Real.arcsin $a) => unary .asin a
    | ~q(Real.arccos $a) => unary .acos a
    | ~q(Real.arctan $a) => unary .atan a
    | ~q(Real.sinh $a) => unary .sinh a
    | ~q(Real.cosh $a) => unary .cosh a
    | ~q(Real.tanh $a) => unary .tanh a
    | ~q(Real.sqrt $a) => unary .sqrt a
    | _ => liftM (reifyAtom e)
  /-- Reify one operand and build its unary expression node. -/
  unary (op : UnaryOp) (a : Q(ℝ)) :
      StateRefT ReifyCache (StateRefT Variables MetaM) Q(Interval.Expr) := do
    let a ← reifyCore a
    let op := match op with
      | .neg => mkConst ``UnaryOp.neg
      | .abs => mkConst ``UnaryOp.abs
      | .inv => mkConst ``UnaryOp.inv
      | .pow n => mkApp (mkConst ``UnaryOp.pow) (mkNatLit n)
      | .exp => mkConst ``UnaryOp.exp
      | .log => mkConst ``UnaryOp.log
      | .sin => mkConst ``UnaryOp.sin
      | .cos => mkConst ``UnaryOp.cos
      | .tan => mkConst ``UnaryOp.tan
      | .asin => mkConst ``UnaryOp.asin
      | .acos => mkConst ``UnaryOp.acos
      | .atan => mkConst ``UnaryOp.atan
      | .sinh => mkConst ``UnaryOp.sinh
      | .cosh => mkConst ``UnaryOp.cosh
      | .tanh => mkConst ``UnaryOp.tanh
      | .sqrt => mkConst ``UnaryOp.sqrt
    return mkApp2 (mkConst ``Interval.Expr.unary) op a
  /-- Reify both operands and build their binary expression node. -/
  binary (op : BinaryOp) (a b : Q(ℝ)) :
      StateRefT ReifyCache (StateRefT Variables MetaM) Q(Interval.Expr) := do
    let a ← reifyCore a
    let b ← reifyCore b
    let op := mkConst <| match op with
      | .add => ``BinaryOp.add | .sub => ``BinaryOp.sub | .mul => ``BinaryOp.mul
      | .div => ``BinaryOp.div | .min => ``BinaryOp.min | .max => ``BinaryOp.max
    return mkApp3 (mkConst ``Interval.Expr.binary) op a b

/-- Reify an already normalized scalar expression, retaining its rational certificates. -/
def reifyScalarWithCache (e : Q(ℝ)) :
    StateRefT Variables MetaM (Q(Interval.Expr) × RationalCache) := do
  let (expression, cache) ← (reifyCore e).run {}
  return (expression, cache.rationals)

/--
Reify a real expression, retaining rational certificates for structural equality proofs.

The atom state has the same ordering as `reify`. Aggregate normalization is deterministic; callers
can normalize first and compose its equality with a proof about the resulting scalar expression.
-/
def reifyWithCache (e : Q(ℝ)) :
    StateRefT Variables MetaM (Q(Interval.Expr) × RationalCache) := do
  let normalized ← normalizeAggregates e
  let scalar : Q(ℝ) := normalized.expr
  reifyScalarWithCache scalar

/-- Reify scalar arithmetic and concrete finite aggregates into the common expression language. -/
def reify (e : Q(ℝ)) : StateRefT Variables MetaM Q(Interval.Expr) := do
  return (← reifyWithCache e).1

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
def boundsOfLE {a b : Q(ℝ)} (h : Q($a ≤ $b)) : MetaM (Array Bound) := do
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
partial def boundsOfProof (proof : Lean.Expr) : MetaM (Array Bound) := do
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
partial def boundTerms (type : Lean.Expr) : MetaM (Array Q(ℝ)) := do
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
def dischargeBoundGuard (argument : Lean.Expr) : MetaM Bool := do
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
def boundsAtAtom (atom : Q(ℝ)) (type proof : Lean.Expr) : MetaM (Array Bound) :=
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
partial def boundsOfProofFor (atoms : Variables) (proof : Lean.Expr) : MetaM (Array Bound) := do
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

end FloatLib.Numerics.Interval.Tactic
