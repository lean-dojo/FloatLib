/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics
public import FloatLib.Tactic.Numerics -- shake: keep

/-!
# Automation for E8M0 scales

Automation for exact arithmetic driven by the binary descriptors lives in
`FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite`. This module adds just the E8M0
scale contracts, which have no binary descriptor to drive them.
-/

-- The exported attribute registrations are this module's public effect.
set_option linter.privateModule false

public meta section

namespace FloatLib.Floats.Formats.OCP.MX

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics

attribute [aesop safe apply (rule_sets := [Numerics])]
  E8M0.scaleDyadic_refines

attribute [numerics_reduction]
  E8M0.numericalSystem
  E8M0.ofNatBits
  E8M0.toNatBits
  E8M0.isNaN
  E8M0.exponent?
  E8M0.toDyadic?
  E8M0.scaleDyadic?

end FloatLib.Floats.Formats.OCP.MX
