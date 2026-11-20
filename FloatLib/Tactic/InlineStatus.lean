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
# The `inline_status%` term elaborator

This frontend generates the declarations documented below. Its expansions are checked
in the importing mathematical module.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
Unfold every stage of a status computation and of the general operation whose result it reads.
-/
macro "inline_status% " body:term : term =>
  `(kernel_inline% [KernelPath.addStatus, KernelPath.subStatus, KernelPath.mulStatus,
      KernelPath.fmaStatus, KernelPath.divStatus, KernelPath.addStatusWith,
      KernelPath.subStatusWith, KernelPath.mulStatusWith, KernelPath.fmaStatusWith,
      KernelPath.divStatusWith, KernelPath.roundToIntegralStatusWith,
      KernelPath.divideByZeroStatus,
      KernelPath.infinityTernary, KernelPath.castStatus, KernelPath.castStatusWith,
      KernelPath.cast,
      KernelPath.div, KernelPath.divCore, KernelPath.roundToIntegralStatus,
      KernelPath.roundToIntegral, KernelPath.shiftRound, KernelPath.roundStatus,
      KernelPath.overflowFlag, KernelPath.tinyFlag,
      KernelPath.signedCompare, KernelPath.sumSign, KernelPath.sumMagnitude,
      KernelPath.invalidStatus, KernelPath.gtFlag, KernelPath.geFlag,
      KernelPath.add, KernelPath.neg, KernelPath.mul, KernelPath.fma, KernelPath.sumAligned,
      KernelPath.sumSigned, BinaryInterchange.KernelPath.round, KernelPath.roundAt,
      KernelPath.roundUpShift,
      KernelPath.roundQuotient, KernelPath.roundUp, KernelPath.pack, Kernel.bitLength,
      Kernel.laneLength, KernelPath.significandLength,
      KernelPath.nonFinite] $body)

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
