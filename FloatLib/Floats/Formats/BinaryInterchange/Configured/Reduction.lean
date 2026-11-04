/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction.Tree

/-!
# Configured binary reductions

This is the public entry point for executable configured `sum` and `dot` operations and their
refinement theorems, together with error bounds for user-selected trees of rounded additions.
Code that only executes exact accumulation may import `Configured.Reduction.Runtime` instead.
-/
