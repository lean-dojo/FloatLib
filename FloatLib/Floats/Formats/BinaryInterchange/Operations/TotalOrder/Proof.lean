/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Magnitude

/-!
# Binary total-order correctness

Import this file for the proofs about total order: the order laws on complete data and on encoded
words, the bridges to numerical comparison, the signed-zero and NaN rules, and the specification
of magnitude order. Code that only runs the order can import `TotalOrder.Runtime` alone.
-/
