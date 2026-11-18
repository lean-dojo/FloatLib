/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Rat.Defs
public meta import Std.Data.HashMap.Basic

/-!
# Sparse rational polynomials for metaprograms

`Monomial` stores positive powers in increasing generator order. `Poly` stores only
nonzero rational coefficients in a hash map. Addition, scaling, multiplication and
natural powers preserve this representation; `Poly.monomials` gives a deterministic
term order.

These are untrusted computations for expression normalization, shared by quadratic
form construction and derived-bound searches. Callers prove each resulting identity
with `ring`; no algebraic correctness claim depends on this implementation.
-/

public meta section

namespace FloatLib.Util.Polynomial

/-- A monomial in generators: pairs of a generator and its positive exponent, by generator. -/
abbrev Monomial := List (Nat × Nat)

/-- The product of two monomials. -/
partial def Monomial.mul : Monomial → Monomial → Monomial
  | [], n => n
  | m, [] => m
  | (i, a) :: m, (j, b) :: n =>
    if i < j then (i, a) :: Monomial.mul m ((j, b) :: n)
    else if j < i then (j, b) :: Monomial.mul ((i, a) :: m) n
    else (i, a + b) :: Monomial.mul m n

/-- A fixed total order of monomials, for a reproducible order of terms. -/
def Monomial.before : Monomial → Monomial → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | (i, a) :: m, (j, b) :: n =>
    i < j || (i == j && (a < b || (a == b && Monomial.before m n)))

/-- A polynomial with rational coefficients: its monomials with their nonzero coefficients. -/
abbrev Poly := Std.HashMap Monomial ℚ

namespace Poly

/-- Add `c` times a monomial. -/
def addMonomial (p : Poly) (m : Monomial) (c : ℚ) : Poly :=
  let total := p.getD m 0 + c
  if total == 0 then p.erase m else p.insert m total

/-- A constant. -/
def const (c : ℚ) : Poly := addMonomial {} [] c

/-- A generator. -/
def gen (i : Nat) : Poly := addMonomial {} [(i, 1)] 1

/-- The sum. -/
def add (p q : Poly) : Poly := q.fold (init := p) addMonomial

/-- The multiple by a rational. -/
def scale (c : ℚ) (p : Poly) : Poly := p.fold (init := {}) fun acc m d => addMonomial acc m (c * d)

/-- The product. -/
def mul (p q : Poly) : Poly :=
  p.fold (init := {}) fun acc m c => q.fold (init := acc) fun acc n d =>
    addMonomial acc (m.mul n) (c * d)

/-- The power. -/
def pow (p : Poly) : Nat → Poly
  | 0 => const 1
  | n + 1 => mul (pow p n) p

/-- The monomials in a fixed order. -/
def monomials (p : Poly) : Array (Monomial × ℚ) :=
  p.toArray.qsort fun a b => a.1.before b.1

end Poly

end FloatLib.Util.Polynomial
