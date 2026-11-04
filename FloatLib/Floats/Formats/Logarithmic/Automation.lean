/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# Logarithmic-system rules for numerical automation

This module hands the logarithmic rules to numerical automation. Multiplication is exact in the
encoded sign and exponent form, so its refinement theorem and the product law for `toReal` go in
as rules. The real-valued decoder is there for proofs and never appears in compiled kernels.
-/

public meta section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Logarithmic

attribute [numerics_simps]
  Code.toReal_mul
  numericalSystem_represents_iff

attribute [aesop safe apply (rule_sets := [Numerics])]
  mul_refines

attribute [numerics_reduction]
  Code.toReal
  Code.mul
  numericalSystem

end FloatLib.Floats.Formats.Logarithmic
