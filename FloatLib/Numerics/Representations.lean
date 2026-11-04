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

These are executable code types that use the universal `NumericalSystem` and operation-contract
interfaces but aren't floating-point formats. Keeping them out of `Numerics.Core` keeps the
foundation format-independent, and keeping them out of `Floats.Formats` avoids classifying Boolean
masks and fixed-width integers as floats.
-/

@[expose] public section
