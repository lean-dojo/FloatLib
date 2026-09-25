/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.Real
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Matrix.Normed
public meta import Mathlib.Tactic.NormNum.BigOperators
public meta import Mathlib.Util.Qq

/-!
# Finite aggregates for interval reification

Concrete finite sums and norms are expanded into scalar arithmetic with equality certificates.
Splitting `Fin` and range sums in halves keeps the resulting additions balanced.
-/

@[expose] public section

namespace FloatLib.Numerics.Interval.Tactic

open scoped NNReal

/-- Split a finite supremum along the two consecutive blocks of a `Fin` index. -/
theorem sup_univ_fin_add {a b : ℕ} (f : Fin (a + b) → ℝ≥0) :
    Finset.univ.sup f =
      max (Finset.univ.sup fun i : Fin a ↦ f (Fin.castAdd b i))
        (Finset.univ.sup fun i : Fin b ↦ f (Fin.natAdd a i)) := by
  rw [← Finset.map_univ_equiv finSumFinEquiv, Finset.sup_map,
    ← Finset.univ_disjSum_univ, Finset.sup_disjSum]
  rfl

end FloatLib.Numerics.Interval.Tactic

public meta section

open Lean Meta Qq
open scoped NNReal

namespace FloatLib.Numerics.Interval.Tactic

/-- Turn an equality into a simplifier result without normalizing either side. -/
def aggregateEquality (proof : Lean.Expr) : MetaM Simp.Result := do
  let some (_, _, rhs) := (← inferType proof).eq?
    | throwError "expected an aggregate equality"
  return { expr := rhs, proof? := some proof }

/-- Expand one finite real sum, using balanced partitions for numerical dimensions. -/
def expandAggregateSum (e : Lean.Expr) : MetaM (Option Simp.Result) := do
  let .const ``Finset.sum [u, _] := e.getAppFn | return none
  let #[αExpr, _, _, sExpr, fExpr] := e.getAppArgs | return none
  unless ← isDefEq (← inferType e) q(ℝ) do return none
  have α : Q(Type u) := αExpr
  have s : Q(Finset $α) := sExpr
  have f : Q($α → ℝ) := fExpr
  if α.isAppOfArity ``Fin 1 then
    have n : Q(ℕ) := α.appArg!
    have s : Q(Finset (Fin $n)) := s
    if ← isDefEq s q(Finset.univ : Finset (Fin $n)) then
      let some count ← getNatValue? (← withTransparency .default (whnf n)) | return none
      if count == 0 then
        have f : Q(Fin 0 → ℝ) := f
        return some (← aggregateEquality q(Fin.sum_univ_zero $f))
      if count == 1 then
        have f : Q(Fin 1 → ℝ) := f
        return some (← aggregateEquality q(Fin.sum_univ_one $f))
      have a : Q(ℕ) := mkNatLit (count / 2)
      have b : Q(ℕ) := mkNatLit (count - count / 2)
      have f : Q(Fin ($a + $b) → ℝ) := f
      return some (← aggregateEquality q(Fin.sum_univ_add (a := $a) (b := $b) $f))
  if s.isAppOfArity ``Finset.range 1 then
    have n : Q(ℕ) := s.appArg!
    let some count ← getNatValue? (← withTransparency .default (whnf n)) | return none
    have f : Q(ℕ → ℝ) := f
    if count == 0 then
      return some (← aggregateEquality q(Finset.sum_range_zero $f))
    if count == 1 then
      return some (← aggregateEquality q(Finset.sum_range_one $f))
    have a : Q(ℕ) := mkNatLit (count / 2)
    have b : Q(ℕ) := mkNatLit (count - count / 2)
    return some (← aggregateEquality q(Finset.sum_range_add $f $a $b))
  try
    match ← Mathlib.Meta.Finset.proveEmptyOrCons s with
    | .empty hs =>
      return some (← aggregateEquality
        q(Eq.trans (congrArg (fun t : Finset $α ↦ Finset.sum t $f) $hs)
          (Finset.sum_empty : Finset.sum ∅ $f = 0)))
    | .cons _a _tail ha hs =>
      return some (← aggregateEquality
        q(Eq.trans (congrArg (fun t : Finset $α ↦ Finset.sum t $f) $hs)
          (Finset.sum_cons $ha)))
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none

/-- Expand a nonnegative finite supremum; coercions then expose real maxima. -/
def expandAggregateSup (e : Lean.Expr) : MetaM (Option Simp.Result) := do
  let .const ``Finset.sup [_, u] := e.getAppFn | return none
  let #[_, αExpr, _, _, sExpr, fExpr] := e.getAppArgs | return none
  unless ← isDefEq (← inferType e) q(ℝ≥0) do return none
  have α : Q(Type u) := αExpr
  have s : Q(Finset $α) := sExpr
  have f : Q($α → ℝ≥0) := fExpr
  if α.isAppOfArity ``Fin 1 then
    have n : Q(ℕ) := α.appArg!
    have s : Q(Finset (Fin $n)) := s
    if ← isDefEq s q(Finset.univ : Finset (Fin $n)) then
      let some count ← getNatValue? (← withTransparency .default (whnf n)) | return none
      if count == 0 then
        have f : Q(Fin 0 → ℝ≥0) := f
        return some (← aggregateEquality q(Finset.sup_empty (f := $f)))
      if count == 1 then
        have f : Q(Fin 1 → ℝ≥0) := f
        return some (← aggregateEquality q(Finset.sup_singleton (f := $f) (b := 0)))
      if count > 1 then
        have a : Q(ℕ) := mkNatLit (count / 2)
        have b : Q(ℕ) := mkNatLit (count - count / 2)
        have f : Q(Fin ($a + $b) → ℝ≥0) := f
        return some (← aggregateEquality q(sup_univ_fin_add (a := $a) (b := $b) $f))
  try
    match ← Mathlib.Meta.Finset.proveEmptyOrCons s with
    | .empty hs =>
      return some (← aggregateEquality
        q(Eq.trans (congrArg (fun t : Finset $α ↦ Finset.sup t $f) $hs)
          (Finset.sup_empty : Finset.sup ∅ $f = 0)))
    | .cons _a _tail ha hs =>
      return some (← aggregateEquality
        q(Eq.trans (congrArg (fun t : Finset $α ↦ Finset.sup t $f) $hs)
          (Finset.sup_cons $ha)))
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none

/-- Reduce closed natural coefficients, including projections of generated `Fin` indices. -/
def aggregateNat : Simp.Simproc := fun e ↦ do
  if !e.hasFVar && !e.hasMVar && (← inferType e).isConstOf ``Nat then
    if let some n ← getNatValue? (← withTransparency .default (whnf e)) then
      return .done { expr := mkNatLit n }
  return .continue

/-- The aggregate expansion is local to the interval tactic. -/
def aggregatePre : Simp.Simproc := fun e ↦ do
  if let some result ← expandAggregateSum e then return .visit result
  if let some result ← expandAggregateSup e then return .visit result
  aggregateNat e

/-- Keep unsupported real functions intact instead of simplifying inside their arguments. -/
def aggregateAtoms : Simp.Simproc := fun e ↦ do
  if e.isMData || e.isLet || e.getAppFn.isLambda then return .continue
  unless ← isDefEq (← inferType e) q(ℝ) do return .continue
  let heads := #[
    ``dotProduct, ``Matrix.mulVec, ``Matrix.vecMul,
    ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``Min.min, ``Max.max,
    ``Neg.neg, ``abs, ``Inv.inv, ``HPow.hPow, ``Nat.cast, ``Int.cast, ``Rat.cast,
    ``Subtype.val, ``NNReal.toReal, ``OfNat.ofNat, ``ite, ``dite,
    ``Real.exp, ``Real.log, ``Real.sin, ``Real.cos, ``Real.tan, ``Real.arcsin,
    ``Real.arccos, ``Real.arctan, ``Real.sinh, ``Real.cosh, ``Real.tanh, ``Real.sqrt]
  if let .const head _ := e.getAppFn then
    if heads.contains head then return .continue
  if e.isAppOfArity ``Finset.sum 5 then
    let s := e.getAppArgs[3]!
    if s.isAppOf ``Insert.insert || s.isAppOf ``Singleton.singleton then return .continue
  return .done { expr := e }

/-- Prove a closed guard only after its decision procedure reduces to true. -/
def decideAggregateGuard? (p : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let p ← instantiateMVars p
  if p.hasFVar || p.hasMVar then return none
  try
    let decision ← mkDecide p
    unless (← withTransparency .default (whnf decision)).isConstOf ``Bool.true do return none
    return some (← mkDecideProof p)
  catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    return none

/-- Scalar coercions preserve arithmetic; truncated subtraction becomes a maximum. -/
def aggregateScalarTheorems : MetaM SimpTheorems := do
  let names := #[
    ``NNReal.coe_zero, ``NNReal.coe_one, ``NNReal.coe_natCast, ``NNReal.coe_ofNat,
    ``NNReal.coe_ofScientific, ``NNReal.coe_add, ``NNReal.coe_mul, ``NNReal.coe_inv,
    ``NNReal.coe_div, ``NNReal.coe_pow, ``NNReal.coe_min, ``NNReal.coe_max,
    ``NNReal.coe_sub_def, ``NNReal.bot_eq_zero]
  names.foldlM (fun s name ↦ s.addConst name (post := false)) ({} : SimpTheorems)

/-- Expose numerical coefficients without expanding aggregates or evaluating real arithmetic. -/
def normalizeAggregateNumerals (e : Q(ℝ)) : MetaM Simp.Result := do
  let context ← Simp.mkContext (simpTheorems := #[← aggregateScalarTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main e context (methods := {
    pre := Simp.andThen aggregateNat (Simp.preDefault #[])
    post := Simp.postDefault #[] })).1

/--
Normalize concrete finite sums, dot products, matrix entries, and l1/infinity norms.

The result contains the scalar expression and a proof of equality to the input. A caller proving
reification correctness can compose this proof with a structural proof for the normalized scalar
expression, without running arithmetic simplification on the expanded aggregate.
-/
def normalizeAggregates (e : Q(ℝ)) : MetaM Simp.Result := do
  let names := #[
    ``Matrix.mul_apply,
    ``Matrix.linfty_opNorm_def, ``Matrix.norm_eq_sup_sup_nnnorm,
    ``PiLp.norm_eq_of_L1, ``PiLp.norm_toLp, ``WithLp.ofLp_toLp,
    ``Pi.norm_def, ``Pi.nnnorm_def,
    ``NNReal.coe_sum, ``coe_nnnorm,
    ``Real.norm_eq_abs, ``Finset.sum_Ico_eq_sum_range, ``Finset.sum_filter,
    ``Finset.sum_insert, ``Finset.sum_singleton, ``Finset.insert_eq_of_mem,
    ``if_pos, ``if_neg, ``dif_pos, ``dif_neg]
  let theorems ← names.foldlM (fun s name ↦ s.addConst name (post := false))
    (← aggregateScalarTheorems)
  let theorems ← #[``Matrix.mulVec, ``Matrix.vecMul, ``dotProduct].foldlM
    (fun s name ↦ s.addDeclToUnfold name) theorems
  let context ← Simp.mkContext (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  return (← Simp.main e context (methods := {
    pre := Simp.andThen aggregatePre (Simp.andThen (Simp.preDefault #[]) aggregateAtoms)
    post := Simp.postDefault #[]
    discharge? := fun p ↦ decideAggregateGuard? p })).1

end FloatLib.Numerics.Interval.Tactic
