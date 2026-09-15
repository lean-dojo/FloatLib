/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Automation.Numerics -- shake: keep
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Block
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics

/-!
# Automation for E8M0 and block formats

Exact descriptor-driven arithmetic automation lives in
`FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite`. This module registers only the
E8M0 scale and block-decoding contracts.
-/

public meta section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

attribute [aesop safe apply (rule_sets := [Numerics])]
  E8M0.scaleDyadic_refines
  E8M0.decodeElement_refines
  BlockCode.decode_refines

attribute [numerics_reduction]
  E8M0.numericalSystem
  E8M0.ofNatBits
  E8M0.toNatBits
  E8M0.isNaN
  E8M0.exponent?
  E8M0.toDyadic?
  E8M0.scaleDyadic?
  E8M0.decodeElement?
  E8M0.decodeBlock?
  BlockCode.decode?
  blockSystem

end FloatLib.Floats.Formats.OCP.MX
