/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Magnitude

/-!
# Binary total-order correctness

This proof entry point exports complete-data and encoded-word order laws, numerical comparison
bridges, signed-zero and NaN rules, and the magnitude-order specification. Runtime clients can
import `TotalOrder.Runtime` alone.
-/
