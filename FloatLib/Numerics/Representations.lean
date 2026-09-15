/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.Boolean
public import FloatLib.Numerics.Representations.Boolean.Arithmetic
public import FloatLib.Numerics.Representations.Boolean.Automation
public import FloatLib.Numerics.Representations.FixedInt
public import FloatLib.Numerics.Representations.FixedInt.Automation

/-!
# Concrete non-floating numerical representations

This package contains executable code types that use the universal `NumericalSystem` and
operation-contract interfaces but are not floating-point formats. Keeping them separate from
`Numerics.Core` preserves the format-independent foundation, while keeping them outside
`Floats.Formats` avoids classifying Boolean masks and fixed-width integers as floats.
-/

@[expose] public section
