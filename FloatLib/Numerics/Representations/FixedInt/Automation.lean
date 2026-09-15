/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.FixedInt.Semantics.Refinement
public import FloatLib.Numerics.Automation.Numerics -- shake: keep
public import Mathlib.Tactic.NormNum

/-!
# Fixed-width integer rules for numerical automation

Symbolic goals use the proved modular, checked, and saturating contracts.  Concrete reduction
unfolds the `BitVec` kernels only during the explicit closed-term phase.
-/

public meta section

namespace FloatLib.Numerics.Representations.FixedInt

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
  ofNatBits
  toNatBits
  toInt
  ofInt
  minValue
  maxValue
  InRange
  clamp
  minCode
  maxCode
  wrapAdd
  wrapSub
  wrapMul
  checkedAdd
  checkedSub
  checkedMul
  ofIntSaturating
  saturatingAdd
  saturatingSub
  saturatingMul
  numericalSystem

end FloatLib.Numerics.Representations.FixedInt
