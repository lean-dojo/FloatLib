/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.Boolean.Arithmetic
public import FloatLib.Numerics.Automation.Numerics -- shake: keep
public import Mathlib.Tactic.NormNum

/-!
# Boolean rules for numerical automation

Symbolic proofs select the exact Boolean operation contracts. Closed reduction unfolds only the
small native kernels.
-/

public meta section

namespace FloatLib.Numerics.Representations.Boolean

attribute [aesop safe apply (rule_sets := [Numerics])]
  not_refines
  and_refines
  or_refines
  xor_refines

attribute [numerics_reduction]
  numericalSystem
  not
  and
  or
  xor

end FloatLib.Numerics.Representations.Boolean
