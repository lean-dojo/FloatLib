/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Proof
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# Bounded fixed-point rules for numerical automation

Automation handles bounded fixed point in two ways. A symbolic goal is solved with the proved
operation contracts, and the signed-word kernels are unfolded only in the closed-term phase, when
the operands are concrete.
-/

public meta section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.FixedPoint.Bounded

attribute [aesop safe apply (rule_sets := [Numerics])]
  wrapAdd_refines
  wrapSub_refines
  wrapMul_refines
  checkedAdd_refines
  checkedSub_refines
  checkedMul_refines
  saturatingAdd_refines
  saturatingSub_refines
  saturatingMul_refines

attribute [numerics_reduction]
  scale
  coefficient
  toRat
  ofInt
  wrapAdd
  wrapSub
  wrapMul
  checkedAdd
  checkedSub
  checkedMul
  saturatingAdd
  saturatingSub
  saturatingMul
  valueOfCoefficient
  coefficientOf
  wrapAddValue
  wrapSubValue
  wrapMulValue
  saturatingAddValue
  saturatingSubValue
  saturatingMulValue
  toUnbounded
  numericalSystem
  numericalSystem_represents_iff

end FloatLib.Floats.Formats.FixedPoint.Bounded
