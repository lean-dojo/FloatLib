/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# Fixed-point rules for numerical automation

The rules expose exact rational semantics. Runtime addition, subtraction, negation, and
multiplication remain the direct integer-coefficient kernels in `FixedPoint.Code`.
-/

public meta section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.FixedPoint

attribute [numerics_simps]
  Code.toRat_add
  Code.toRat_neg
  Code.toRat_sub
  Code.toRat_mul
  numericalSystem_represents_iff

attribute [aesop safe apply (rule_sets := [Numerics])]
  add_refines
  neg_refines
  sub_refines
  mul_refines

attribute [numerics_reduction]
  decimalRadix
  scale
  Code.toRat
  Code.add
  Code.neg
  Code.sub
  Code.mul
  numericalSystem

end FloatLib.Floats.Formats.FixedPoint
