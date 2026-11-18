/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.ShortAddition
public import FloatLib.Tactic.KernelInline

/-!
# The `inline_short%` term elaborator

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

/--
Unfold the short paths and the rounding stages they share with the general operations, and keep
as calls the general operation they fall back to and the `round` that normalizes a difference
whose leading bits cancelled, so that the common path does not carry their code.
-/
macro "inline_short% " body:term : term =>
  `(kernel_inline% [KernelPath.addFastWith, KernelPath.mulFastWith, KernelPath.sumOrdered,
      KernelPath.neg, KernelPath.roundAt, KernelPath.roundUpShift, KernelPath.roundQuotient,
      KernelPath.roundUp,
      KernelPath.pack] $body)

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
