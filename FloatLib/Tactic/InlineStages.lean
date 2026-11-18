/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop -- shake: keep
public import FloatLib.Kernels.Execution.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.CastStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.Multiplication
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Fast.ShortAddition
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.IntegerStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lift
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.LiteralStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.SqrtStatus
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.ToRat
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.TotalOrder
public import FloatLib.Tactic.FloatDecide -- shake: keep
public import FloatLib.Tactic.KernelInline

/-!
# The `inline_stages%` term elaborator

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Unfold every stage of the natural-number operations, so that an operation is one definition for
Lean's kernel to unfold.
-/
macro "inline_stages% " body:term : term =>
  `(kernel_inline% [KernelPath.add, KernelPath.sub, KernelPath.neg, KernelPath.mul,
      KernelPath.fma, KernelPath.div, KernelPath.divCore, KernelPath.sqrt, KernelPath.sqrtCore,
      KernelPath.sqrtChecked,
      KernelPath.rootUp, KernelPath.newtonRoot, KernelPath.newton, KernelPath.sumAligned,
      KernelPath.sumSigned,
      BinaryInterchange.KernelPath.round, KernelPath.roundAt, KernelPath.roundUpShift,
      KernelPath.roundQuotient,
      KernelPath.roundUp, KernelPath.pack, Kernel.bitLength, Kernel.laneLength,
      KernelPath.significandLength,
      KernelPath.nonFinite,
      KernelPath.cast, KernelPath.roundToIntegral, KernelPath.intMagnitude,
      KernelPath.shiftRound] $body)

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
