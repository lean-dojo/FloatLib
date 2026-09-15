/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# One-point views of optional values

Posits and quires both have a partial exact semantics `toRat? : Model → Option Rat` whose `none`
case is the unique NaR word. Their intentional one-point projections send `some x` to the point
`x` and `none` to the added point of `OnePoint`. This module defines that map once, as
`Option.toOnePoint`, and proves the characterisations that the posit and quire projective views
instantiate.
-/

@[expose] public section

namespace Option

variable {K L : Type*}

/-- Send `some x` to the point `x` of the one-point compactification and `none` to the added point. -/
def toOnePoint : Option K → OnePoint K
  | some x => (x : OnePoint K)
  | none => OnePoint.infty

/-- `some x` maps to the finite point `x` of the one-point compactification. -/
@[simp] theorem toOnePoint_some (x : K) : (some x).toOnePoint = (x : OnePoint K) :=
  rfl

/-- `none` maps to the point at infinity. -/
@[simp] theorem toOnePoint_none : (none : Option K).toOnePoint = OnePoint.infty :=
  rfl

/-- The one-point view is a finite point exactly when the option holds that value. -/
theorem toOnePoint_eq_coe_iff (option : Option K) (x : K) :
    option.toOnePoint = (x : OnePoint K) ↔ option = some x := by
  cases option <;> simp

/-- The one-point view is the added point exactly when the option is `none`. -/
theorem toOnePoint_eq_infty_iff (option : Option K) :
    option.toOnePoint = OnePoint.infty ↔ option = none := by
  cases option <;> simp

/-- Mapping through an injective function before the one-point view preserves finite points. -/
theorem toOnePoint_map_eq_coe_iff {f : K → L} (hf : Function.Injective f)
    (option : Option K) (x : K) :
    (option.map f).toOnePoint = (f x : OnePoint L) ↔ option = some x := by
  cases option <;> simp [hf.eq_iff]

/-- Mapping before the one-point view does not change which options reach the added point. -/
theorem toOnePoint_map_eq_infty_iff (f : K → L) (option : Option K) :
    (option.map f).toOnePoint = OnePoint.infty ↔ option = none := by
  cases option <;> simp

end Option

namespace OnePoint

/-- The projective-line equivalence reflects equality of one-point values. -/
theorem equivProjectivization_eq_iff (K : Type*) [DivisionRing K] [DecidableEq K]
    (left right : OnePoint K) :
    equivProjectivization K left = equivProjectivization K right ↔ left = right :=
  (equivProjectivization K).injective.eq_iff

end OnePoint
