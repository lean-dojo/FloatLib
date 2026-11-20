/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.KernelPath.Quire
public import FloatLib.Tactic.KernelInline
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# PositInlineStages generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Floats.ExecFloat.KernelPath

set_option hygiene false in
/-- Unfold every stage of a posit operation on encodings. -/
macro (name := positInlineStages) "posit_inline_stages% " body:term : term =>
  `(kernel_inline% [KernelPath.add, KernelPath.sub, KernelPath.mul, KernelPath.div,
      KernelPath.sqrt, KernelPath.fma, KernelPath.cast, KernelPath.sumFinite,
      KernelPath.sumFields, KernelPath.encode, KernelPath.roundTail, KernelPath.exponent,
      KernelPath.significand, KernelPath.fractionBits, KernelPath.tailLength,
      KernelPath.complement, KernelPath.magnitude, KernelPath.withSign, KernelPath.neg,
      KernelPath.jam, KernelPath.nar, KernelPath.bias, KernelPath.regimeBias,
      KernelPath.quotient, KernelPath.ofRatio, KernelPath.nearestNat, KernelPath.toSigned,
      KernelPath.toUnsigned,
      KernelPath.quireAddPosit, KernelPath.quireAddProduct, KernelPath.quireAddQuire,
      KernelPath.quireRound, KernelPath.quireAccumulate, KernelPath.quireNar,
      KernelPath.quireWidth,
      FloatLib.Numerics.Kernel.lowBits, FloatLib.Numerics.Kernel.minNat,
      FloatLib.Numerics.Kernel.maxNat, FloatLib.Numerics.Kernel.size,
      FloatLib.Numerics.Kernel.bitLength, FloatLib.Numerics.Kernel.laneLength,
      FloatLib.Numerics.Kernel.laneOnes, FloatLib.Numerics.Kernel.laneOffsets,
      FloatLib.Numerics.Kernel.isqrt, FloatLib.Numerics.Kernel.sqrtGuess,
      FloatLib.Numerics.Kernel.isRoot, FloatLib.Numerics.Kernel.ceilDiv] $body)


end FloatLib.Floats.Formats.Posit.KernelPath
