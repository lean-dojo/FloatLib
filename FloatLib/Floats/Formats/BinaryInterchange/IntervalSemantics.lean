/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Arithmetic
public import FloatLib.Floats.Formats.BinaryInterchange.IntervalSemantics.Activations

/-!
# Semantics of arbitrary-format executable intervals

Import this module for what `Model.Interval fmt` means: semantic membership, four-corner
endpoint selection, and the soundness of outward-rounded arithmetic and activations.

Start with `Core` and `Order` for finite and extended-real membership, then read `MinMax` for
endpoint selection. `Arithmetic` groups negation, the four binary operations, and reciprocal, and
`Activations` groups ReLU, absolute value, and square root. For all-words-finite encodings,
`Finite` supplies range-checked arithmetic. Each theorem states its own IEEE and finiteness
requirements.
-/

@[expose] public section
