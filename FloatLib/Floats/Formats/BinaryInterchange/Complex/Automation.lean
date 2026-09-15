/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Complex.NumericalSystem
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# Complex `Model` rules for numerical automation

These rules expose the rounded complex semantics through the same operation contracts used by
scalar floats and other numerical systems. Executable complex arithmetic remains the direct
definitions in `Complex.Core`.
-/

public meta section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.BinaryInterchange.ExecComplex

attribute [aesop safe apply (rule_sets := [Numerics])]
  neg_refines
  conj_refines
  add_refines
  sub_refines
  mul_refines
  div_refines
  normSq_refines
  magnitude_refines
  NormSqFinite.result
  MagnitudeFinite.result
  toReal_normSq_of_represents
  toReal_magnitude_of_represents

attribute [numerics_simps]
  represents_iff

end FloatLib.Floats.Formats.BinaryInterchange.ExecComplex
