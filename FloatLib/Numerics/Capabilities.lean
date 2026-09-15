/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Capabilities.BlockScaled
public import FloatLib.Numerics.Capabilities.Elementary
public import FloatLib.Numerics.Capabilities.Error
public import FloatLib.Numerics.Capabilities.Ordered
public import FloatLib.Numerics.Capabilities.Radix

/-!
# Optional numerical-system capabilities

Optional data and laws for block scaling, scalar functions, error bounds, representable neighbors,
and positional radices. `NumericalSystem` requires none of these capabilities.
-/

@[expose] public section
