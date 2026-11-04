/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-! # Uniqueness of finite binary representations

The decoded exponent is the canonical exponent of every nonzero finite value, which connects
numerical conversion theorems to representation round trips. Signed zero gets its own treatment,
because real numbers forget its sign.
-/
