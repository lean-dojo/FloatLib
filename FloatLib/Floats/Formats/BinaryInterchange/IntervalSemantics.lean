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

Public entry point for semantic membership, four-corner endpoint selection, and outward-rounded
arithmetic and activation soundness over `Model.Interval fmt`.

Read `Core` and `Order` for finite and extended-real membership, then `MinMax` for endpoint
selection. `Arithmetic` groups negation, the four binary operations, and reciprocal; `Activations`
groups ReLU, absolute value, and square root. `Finite` supplies range-checked arithmetic for
all-words-finite encodings. Individual theorems state their IEEE and finiteness requirements.
-/

@[expose] public section
