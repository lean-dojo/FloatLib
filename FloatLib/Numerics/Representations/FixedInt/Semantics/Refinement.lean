/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.FixedInt.Semantics.Arithmetic
public import FloatLib.Numerics.Operation.Semantics

/-!
# Operation refinements for fixed-width signed integers

Fixed-width arithmetic has three useful policies: wrapping returns centered modular arithmetic,
checked arithmetic returns a result only when the exact integer is representable, and saturating
arithmetic clamps at the signed endpoints.

This module exposes all three through the same generic `Operation` contracts used by the rest of
the library. Algorithms can therefore state the policy they require without depending on
`BitVec` internals, while execution still uses the compact two's-complement carrier.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations.FixedInt

/-- Wrapping addition refines centered reduction modulo `2 ^ width`. -/
theorem wrapAdd_refines (width : Nat) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) wrapAdd
      (fun left right : Int => (left + right).bmod (2 ^ width)) := by
  intro left right leftValue rightValue hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  apply (numericalSystem_represents_iff _ _).2
  exact toInt_wrapAdd left right

/-- Wrapping subtraction refines centered reduction modulo `2 ^ width`. -/
theorem wrapSub_refines (width : Nat) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) wrapSub
      (fun left right : Int => (left - right).bmod (2 ^ width)) := by
  intro left right leftValue rightValue hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  apply (numericalSystem_represents_iff _ _).2
  exact toInt_wrapSub left right

/-- Wrapping multiplication refines centered reduction modulo `2 ^ width`. -/
theorem wrapMul_refines (width : Nat) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) wrapMul
      (fun left right : Int => (left * right).bmod (2 ^ width)) := by
  intro left right leftValue rightValue hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  apply (numericalSystem_represents_iff _ _).2
  exact toInt_wrapMul left right

/-- Checked addition returns the exact sum whenever it is representable. -/
theorem checkedAdd_refines {width : Nat} (hwidth : 0 < width) :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checkedAdd
      (fun left right : Int => .finite (left + right))
      (fun left right : Int => InRange width (left + right)) := by
  intro left right leftValue rightValue hresult hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  rw [checkedAdd_eq_some hwidth left right hresult]
  simp [numericalSystem, toInt_wrapAdd_of_inRange hwidth left right hresult]

/-- Checked subtraction returns the exact difference whenever it is representable. -/
theorem checkedSub_refines {width : Nat} (hwidth : 0 < width) :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checkedSub
      (fun left right : Int => .finite (left - right))
      (fun left right : Int => InRange width (left - right)) := by
  intro left right leftValue rightValue hresult hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  rw [checkedSub_eq_some hwidth left right hresult]
  simp [numericalSystem, toInt_wrapSub_of_inRange hwidth left right hresult]

/-- Checked multiplication returns the exact product whenever it is representable. -/
theorem checkedMul_refines {width : Nat} (hwidth : 0 < width) :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checkedMul
      (fun left right : Int => .finite (left * right))
      (fun left right : Int => InRange width (left * right)) := by
  intro left right leftValue rightValue hresult hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  rw [checkedMul_eq_some hwidth left right hresult]
  simp [numericalSystem, toInt_wrapMul_of_inRange hwidth left right hresult]

/-- Saturating addition refines exact addition followed by signed-range clamping. -/
theorem saturatingAdd_refines {width : Nat} (hwidth : 0 < width) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) saturatingAdd
      (fun left right : Int => clamp width (left + right)) := by
  intro left right leftValue rightValue hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  apply (numericalSystem_represents_iff _ _).2
  exact toInt_saturatingAdd hwidth left right

/-- Saturating subtraction refines exact subtraction followed by signed-range clamping. -/
theorem saturatingSub_refines {width : Nat} (hwidth : 0 < width) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) saturatingSub
      (fun left right : Int => clamp width (left - right)) := by
  intro left right leftValue rightValue hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  apply (numericalSystem_represents_iff _ _).2
  exact toInt_saturatingSub hwidth left right

/-- Saturating multiplication refines exact multiplication followed by signed-range clamping. -/
theorem saturatingMul_refines {width : Nat} (hwidth : 0 < width) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) saturatingMul
      (fun left right : Int => clamp width (left * right)) := by
  intro left right leftValue rightValue hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue
  subst rightValue
  apply (numericalSystem_represents_iff _ _).2
  exact toInt_saturatingMul hwidth left right

end FloatLib.Numerics.Representations.FixedInt
