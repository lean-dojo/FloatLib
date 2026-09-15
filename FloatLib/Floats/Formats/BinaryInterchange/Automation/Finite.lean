/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.FiniteSemantics
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# Exact finite-operation automation for `Model`

The exact-dyadic representation and checked finite-operation contracts are registered with the
representation-independent `numerics` tactic. The runtime carrier remains `Model fmt`; the exact
representation is a proof view used only by refinement.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

open FloatLib.Numerics

attribute [aesop safe apply (rule_sets := [Numerics])]
  negExact_refines
  addFinite_refines
  subFinite_refines
  mulFinite_refines
  fmaFinite_refines
  mulAddFinite_refines
  divFinite_refines
  castFinite_refines

attribute [numerics_reduction]
  exactNumericalSystem
  Model.ofNatBits
  Model.toNatBits
  Model.toDyadic?
  Model.isFinite
  Model.isNaN
  Model.isInf
  Model.isZero
  FloatFormat.binary16
  FloatFormat.bfloat16
  FloatFormat.binary32
  FloatFormat.binary64
  FloatFormat.binary128
  FloatFormat.binary256
  FloatFormat.tf32
  FloatFormat.e5m2
  FloatFormat.e4m3fn
  FloatFormat.e4m3fnuz
  FloatFormat.e5m2fnuz
  FloatFormat.e2m1
  FloatFormat.e2m3
  FloatFormat.e3m2

end FloatLib.Floats.Formats.BinaryInterchange.Model
