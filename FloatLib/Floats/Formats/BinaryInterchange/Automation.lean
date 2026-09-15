/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.Error
public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Exact
public import FloatLib.Numerics.Automation.Numerics -- shake: keep

/-!
# Binary-interchange rules for numerical automation

This format-family plugin registers the descriptor model's semantic equations and concrete
decoder definitions with the representation-independent `numerics` tactic. The
`binary_interchange_spec` tactic rewrites descriptor-model arithmetic to its exact
specifications. Universal capability arithmetic is handled separately by
`FloatLib.Floats.ExecFloat.Automation`, so the family-independent layer does not depend on this
binary layout.
-/

public meta section

open FloatLib.Numerics

/--
Register a static `FloatFormat` definition for concrete `Model` proof reduction.

The format remains ordinary compile-time data; this attribute only lets `numerics` unfold its
name when checking a closed encoded value.
-/
macro "floatFormat" : attr => `(attr| numerics_reduction)

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/--
Rewrite binary-interchange descriptor arithmetic in the goal and local hypotheses to its exact
specifications. Use `grind` directly when a public-to-specification equality is itself the goal.
-/
syntax (name := binaryInterchangeSpec) "binary_interchange_spec" : tactic

macro_rules
| `(tactic| binary_interchange_spec) =>
    `(tactic|
      simp_all (failIfUnchanged := false) only [
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.add_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.sub_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.mul_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.div_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.sqrt_eq_spec,
        FloatLib.Floats.Formats.BinaryInterchange.Model.Proof.fma_eq_spec
      ])

end FloatLib.Floats.Formats.BinaryInterchange.Model

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

attribute [aesop safe apply (rule_sets := [Numerics])]
  neg_refines
  add_refines
  sub_refines
  mul_refines
  fma_refines
  cast_refines

attribute [numerics_simps]
  toReal_add_eq_roundAt
  toReal_sub_eq_roundAt
  toReal_mul_eq_roundAt
  toReal_div_eq_roundAt
  toReal_sqrt_eq_roundAt
  toReal_fma_eq_roundAt
  cast_eq_roundAt
  toReal_neg
  roundAt_toReal_eq
  toReal_roundDyadic_eq_roundAt
  abs_roundAt_sub_le
  roundAt_mem_Icc
  represents_iff
  AtExact.denote
  AtValue.denote
  AtValue.numericalSystem_denote
  OutcomeAt.denote
  OutcomeAt.status_eq
  At.represents
  At.isFinite
  At.toReal
  At.toEReal

attribute [numerics_side]
  FloatFormat.isIEEE_ieee
  FloatFormat.isIEEE_binary16
  FloatFormat.isIEEE_bfloat16
  FloatFormat.isIEEE_binary32
  FloatFormat.isIEEE_binary64
  FloatFormat.isIEEE_binary128

attribute [numerics_reduction]
  exactSemantics
  exactValue
  ExactValue.toNumericalValue
  toNumericalValue
  toReal_eq
  toDyadic?
  ieeeToDyadic?
  isFinite
  isNaN
  isSNaN
  isInf
  IEEE.isNaN
  IEEE.isInf
  signBit
  expField
  fracField
  Numerics.Dyadic.toReal
  pow2
  ofNatBits
  ofBits
  FloatFormat.ieee
  FloatFormat.ieeeBias
  FloatFormat.isIEEE
  FloatFormat.binary16
  FloatFormat.bfloat16
  FloatFormat.binary32
  FloatFormat.binary64
  FloatFormat.binary128
  FloatFormat.bitWidth
  FloatFormat.ofWordNat
  FloatFormat.fracMask
  FloatFormat.fracMaskNat
  FloatFormat.expAllOnes
  FloatFormat.expAllOnesNat
  FloatFormat.ieeeNormalMantissaExpOffset
  FloatFormat.normalMantissaExpOffset
  FloatFormat.bias
  FloatLib.Floats.Formats.Flocq.bpow
  FloatLib.Numerics.binaryRadix
  FloatLib.Numerics.Radix.toReal

end Model
end FloatLib.Floats.Formats.BinaryInterchange
