/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module


/-!
# Declared zero in exact numerical domains

Checked arithmetic needs a domain-specific way to recognize every representation that should
behave as zero. Structural equality is enough for ordinary exact domains, but a carrier may
deliberately retain distinctions that its arithmetic forgets. For example, `SignedRat` has
separate positive and negative zeros.

`ExactZero` keeps that choice explicit and executable. The class guarantees only that canonical
`0` is included; concrete domains provide bridge theorems connecting their declared predicate to
the representation's numerical meaning. Generic algorithms branch only on this capability.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u

/-- A decidable predicate declaring which exact values checked arithmetic treats as zero. -/
class ExactZero (Exact : Type u) [Zero Exact] where
  /-- Proposition saying that checked arithmetic should treat an exact value as zero. -/
  isZero : Exact → Prop
  /-- The domain's canonical `0` is included in the declared zero values. -/
  zero_is_zero : isZero 0
  /-- Executable decision procedure for the declared zero predicate. -/
  decidableIsZero : DecidablePred isZero

namespace ExactZero

variable {Exact : Type u} [Zero Exact]

/--
Use ordinary equality when the domain's Boolean equality is lawful.

The low priority lets a domain with several zero representations install its own declared-zero
relation.
-/
instance (priority := low) ofLawfulBEq [BEq Exact] [LawfulBEq Exact] : ExactZero Exact where
  isZero value := value = 0
  zero_is_zero := rfl
  decidableIsZero value := instDecidableEqOfLawfulBEq value 0

/-- Decide whether an exact value satisfies its domain's declared zero predicate. -/
@[inline] def test [self : ExactZero Exact] (value : Exact) : Bool :=
  @decide (self.isZero value) (self.decidableIsZero value)

/-- The executable zero test decides the exact domain's declared proposition. -/
@[simp, grind =] theorem test_eq_true_iff [self : ExactZero Exact] (value : Exact) :
    test value = true ↔ self.isZero value := by
  simp [test]

/-- A failed executable zero test is the negation of the domain's declared zero proposition. -/
@[simp, grind =] theorem test_eq_false_iff [self : ExactZero Exact] (value : Exact) :
    test value = false ↔ ¬self.isZero value := by
  simp [test]

/-- Every exact domain's canonical zero passes its zero test. -/
@[simp, grind =] theorem test_zero [self : ExactZero Exact] :
    test (0 : Exact) = true :=
  (test_eq_true_iff 0).2 self.zero_is_zero

end ExactZero
end FloatLib.Numerics
