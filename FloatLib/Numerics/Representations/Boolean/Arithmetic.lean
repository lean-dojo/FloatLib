/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.Boolean
public import FloatLib.Numerics.Operation.Semantics

/-!
# Executable Boolean numerical operations

Boolean masks use their native `Bool` carrier. These definitions are direct inline operations, and
their contracts expose the same functions through the representation-independent numerical API.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations.Boolean

/-- Boolean negation. -/
@[inline] def not (value : Bool) : Bool :=
  !value

/-- Boolean conjunction. -/
@[inline] def and (left right : Bool) : Bool :=
  left && right

/-- Boolean disjunction. -/
@[inline] def or (left right : Bool) : Bool :=
  left || right

/-- Boolean exclusive disjunction. -/
@[inline] def xor (left right : Bool) : Bool :=
  Bool.xor left right

/-- Native Boolean negation has exact Boolean semantics. -/
theorem not_refines :
    Operation.Finite1 numericalSystem numericalSystem not (!·) := by
  intro value scalar hvalue
  cases value <;> cases scalar <;> simp_all [NumericalSystem.Represents, numericalSystem, not]

/-- Native Boolean conjunction has exact Boolean semantics. -/
theorem and_refines :
    Operation.Finite2 numericalSystem numericalSystem numericalSystem and (· && ·) := by
  intro left right x y hleft hright
  cases left <;> cases right <;> cases x <;> cases y <;>
    simp_all [NumericalSystem.Represents, numericalSystem, and]

/-- Native Boolean disjunction has exact Boolean semantics. -/
theorem or_refines :
    Operation.Finite2 numericalSystem numericalSystem numericalSystem or (· || ·) := by
  intro left right x y hleft hright
  cases left <;> cases right <;> cases x <;> cases y <;>
    simp_all [NumericalSystem.Represents, numericalSystem, or]

/-- Native Boolean exclusive disjunction has exact Boolean semantics. -/
theorem xor_refines :
    Operation.Finite2 numericalSystem numericalSystem numericalSystem xor Bool.xor := by
  intro left right x y hleft hright
  cases left <;> cases right <;> cases x <;> cases y <;>
    simp_all [NumericalSystem.Represents, numericalSystem, xor]

end FloatLib.Numerics.Representations.Boolean
