/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Term
public meta import Mathlib.Data.Nat.Factors
public import FloatLib.Numerics.Kernel.Multiplicative

/-!
# `cover% ν y`: a checked split, written out as a literal

`cover% ν y` is a `Cover` for the bound `ν` whose small primes are those up to `y`:

* `rough`: the integers up to `ν` without a prime factor up to `y`, in increasing order, each as
  the list of its prime factors;
* `count`: how many there are;
* `plan`: the forest of the products of primes up to `y` that are at most `ν`, each node with the
  number of those integers up to `ν` divided by its product;
* `ok`: the proof of `Split.splitOk plan rough count ν = true`, by `decide +kernel`.

Compiled code computes the first three while the term is elaborated and writes them out as
constructors and raw literals, so the kernel never builds them. It only checks them: the factor
lists and the forest are trusted for nothing, and a wrong one makes the proof of `ok` fail.

-/

public meta section

namespace FloatLib.Numerics.Kernel.CoverLit

open Lean Elab Term

/-- The integers from `1` to `ν` whose prime factors are all above `y`, ascending. -/
def roughInts (ν y : Nat) : Array Nat :=
  (Array.range (ν + 1)).filter fun n => n ≥ 1 && n.primeFactorsList.all (· > y)

/-- The number of members of the ascending array that are at most `x`. -/
def countLE (a : Array Nat) (x : Nat) : Nat := (a.takeWhile (· ≤ x)).size

/-- The primes up to `y`. -/
def smallPrimes (y : Nat) : List Nat := (List.range (y + 1)).filter (Nat.Prime ·)

/-- The forest below `m` for the small primes `ps`, ascending, as a term of the constructors of
`Split` and raw literals. -/
partial def planExpr (ν : Nat) (ps : List Nat) (rough : Array Nat) (bound m : Nat) : Expr :=
  ps.foldr (fun p rest =>
    if p ≤ bound && p * m ≤ ν then
      mkApp4 (mkConst ``Split.node) (mkRawNatLit p) (mkRawNatLit (countLE rough (ν / (p * m))))
        (planExpr ν ps rough p (p * m)) rest
    else mkConst ``Split.nil) (mkConst ``Split.nil)

/-- A list of naturals as a term of raw literals. -/
def natListExpr (l : List Nat) : Expr :=
  l.foldr (fun n acc =>
      mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat) (mkRawNatLit n) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat))

/-- A list of lists of naturals as a term of raw literals. -/
def natListListExpr (l : List (List Nat)) : Expr :=
  let listNat := mkApp (mkConst ``List [Level.zero]) (mkConst ``Nat)
  l.foldr (fun r acc =>
      mkApp3 (mkConst ``List.cons [Level.zero]) listNat (natListExpr r) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) listNat)

end FloatLib.Numerics.Kernel.CoverLit

/--
`cover% ν y` is the `Cover` of the integers `1, …, ν` whose small primes are those up to `y`,
written out as a literal, with the proof of `Split.splitOk` by `decide +kernel`. It fails if the
kernel does not accept that proof.
-/
elab "cover% " n:num y:num : term => do
  let ν := n.getNat
  let rough := FloatLib.Numerics.Kernel.CoverLit.roughInts ν y.getNat
  let plan := FloatLib.Numerics.Kernel.CoverLit.planExpr ν
    (FloatLib.Numerics.Kernel.CoverLit.smallPrimes y.getNat) rough y.getNat 1
  let roughExpr := FloatLib.Numerics.Kernel.CoverLit.natListListExpr
    (rough.toList.map Nat.primeFactorsList)
  let count := Lean.mkRawNatLit rough.size
  let bound := Lean.mkRawNatLit ν
  let passed := Lean.mkApp4 (Lean.mkConst ``FloatLib.Numerics.Kernel.Split.splitOk) plan
    roughExpr count bound
  let statement ← Lean.Meta.mkEq passed (Lean.mkConst ``Bool.true)
  let proof ← Lean.Elab.Term.elabTermEnsuringType (← `(by decide +kernel)) statement
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  return Lean.mkApp5 (Lean.mkConst ``FloatLib.Numerics.Kernel.Cover.mk) bound plan roughExpr
    count (← Lean.instantiateMVars proof)

end
