/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.FixedInt.Semantics.Arithmetic
public import FloatLib.Numerics.Operation.Semantics
public import FloatLib.Numerics.Operation.Proof.Finite

/-!
# Operation refinements for fixed-width signed integers

Fixed-width arithmetic has three useful policies: wrapping returns centered modular arithmetic,
checked arithmetic returns a result only when the exact integer is representable, and saturating
arithmetic clamps at the signed endpoints.

This module exposes all three through the same generic `Operation` contracts used by the rest of
the library. Algorithms can therefore state the policy they require without depending on
`BitVec` internals, while execution still uses the compact two's-complement carrier.

A `Checked2On` contract covers only inputs whose exact result is in range, where the operation
succeeds with that result. The other half of the checked policy, `none` on overflow, is
`checkedAdd_eq_none_iff`, `checkedSub_eq_none_iff` and `checkedMul_eq_none_iff` in
`Semantics.Arithmetic`.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations.FixedInt

/-- Wrapping addition refines centered reduction modulo `2 ^ width`. -/
theorem wrapAdd_refines (width : Nat) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) wrapAdd
      (fun left right : Int => (left + right).bmod (2 ^ width)) :=
  Operation.Finite2.ofFinite (toInt_wrapAdd)

/-- Wrapping subtraction refines centered reduction modulo `2 ^ width`. -/
theorem wrapSub_refines (width : Nat) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) wrapSub
      (fun left right : Int => (left - right).bmod (2 ^ width)) :=
  Operation.Finite2.ofFinite (toInt_wrapSub)

/-- Wrapping multiplication refines centered reduction modulo `2 ^ width`. -/
theorem wrapMul_refines (width : Nat) :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) wrapMul
      (fun left right : Int => (left * right).bmod (2 ^ width)) :=
  Operation.Finite2.ofFinite (toInt_wrapMul)

/--
A checked operation that returns its wrapping result whenever the exact value is in range, where
the wrapping result is then exact, refines the exact operation under that range precondition.
-/
private theorem checked_refines {width : Nat}
    {checked : FixedInt width → FixedInt width → Option (FixedInt width)}
    {wrap : FixedInt width → FixedInt width → FixedInt width} {op : Int → Int → Int}
    (hchecked : ∀ left right, InRange width (op left.toInt right.toInt) →
      checked left right = some (wrap left right))
    (hwrap : ∀ left right, InRange width (op left.toInt right.toInt) →
      (wrap left right).toInt = op left.toInt right.toInt) :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checked
      (fun left right : Int => .finite (op left right))
      (fun left right : Int => InRange width (op left right)) := by
  intro left right leftValue rightValue hresult hleft hright
  have hleft' := (numericalSystem_represents_iff left leftValue).1 hleft
  have hright' := (numericalSystem_represents_iff right rightValue).1 hright
  subst leftValue rightValue
  rw [hchecked left right hresult]
  simp [numericalSystem, hwrap left right hresult]

/-- Checked addition returns the exact sum whenever it is representable. -/
theorem checkedAdd_refines {width : Nat} :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checkedAdd
      (fun left right : Int => .finite (left + right))
      (fun left right : Int => InRange width (left + right)) :=
  checked_refines checkedAdd_eq_some toInt_wrapAdd_of_inRange

/-- Checked subtraction returns the exact difference whenever it is representable. -/
theorem checkedSub_refines {width : Nat} :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checkedSub
      (fun left right : Int => .finite (left - right))
      (fun left right : Int => InRange width (left - right)) :=
  checked_refines checkedSub_eq_some toInt_wrapSub_of_inRange

/-- Checked multiplication returns the exact product whenever it is representable. -/
theorem checkedMul_refines {width : Nat} :
    Operation.Checked2On (numericalSystem width) (numericalSystem width)
      (numericalSystem width) checkedMul
      (fun left right : Int => .finite (left * right))
      (fun left right : Int => InRange width (left * right)) :=
  checked_refines checkedMul_eq_some toInt_wrapMul_of_inRange

/-- Saturating addition refines exact addition followed by signed-range clamping. -/
theorem saturatingAdd_refines {width : Nat} :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) saturatingAdd
      (fun left right : Int => clamp width (left + right)) :=
  Operation.Finite2.ofFinite toInt_saturatingAdd

/-- Saturating subtraction refines exact subtraction followed by signed-range clamping. -/
theorem saturatingSub_refines {width : Nat} :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) saturatingSub
      (fun left right : Int => clamp width (left - right)) :=
  Operation.Finite2.ofFinite toInt_saturatingSub

/-- Saturating multiplication refines exact multiplication followed by signed-range clamping. -/
theorem saturatingMul_refines {width : Nat} :
    Operation.Finite2 (numericalSystem width) (numericalSystem width)
      (numericalSystem width) saturatingMul
      (fun left right : Int => clamp width (left * right)) :=
  Operation.Finite2.ofFinite toInt_saturatingMul

end FloatLib.Numerics.Representations.FixedInt
