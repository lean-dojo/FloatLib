/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.KernelPath.Core
public import FloatLib.Tactic.KernelInline
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

/-!
# P3109InlineStages generators

The commands expand into declarations checked in the importing module.
-/

public meta section

namespace FloatLib.Floats.Formats.P3109.KernelPath

open FloatLib.Floats.ExecFloat.KernelPath

set_option hygiene false in
/-- Unfold every stage of a P3109 operation on encodings. -/
macro (name := p3109InlineStages) "p3109_inline_stages% " body:term : term =>
  `(kernel_inline% [KernelPath.add, KernelPath.mul, KernelPath.div, KernelPath.fma,
      KernelPath.convert, KernelPath.project, KernelPath.projectFinite, KernelPath.roundedOf,
      KernelPath.roundAway, KernelPath.quantumOf, KernelPath.magnitudeCode, KernelPath.exceeds,
      KernelPath.aboveCode, KernelPath.belowCode, KernelPath.minFiniteCode, KernelPath.classOf,
      KernelPath.signOf, KernelPath.magnitudeOf, KernelPath.significandOf,
      KernelPath.exponentOf, KernelPath.numeratorOf, KernelPath.denominatorOf,
      KernelPath.addClass, KernelPath.addSign, KernelPath.addMagnitude, KernelPath.mulClass,
      KernelPath.divClass, KernelPath.negClass, KernelPath.trailingBits,
      KernelPath.exponentBias, KernelPath.signBoundary, KernelPath.nanBits,
      KernelPath.positiveInfinityBits, KernelPath.negativeInfinityBits,
      KernelPath.maxFiniteBits, KernelPath.nearestEven, FloatLib.Numerics.Kernel.lowBits,
      FloatLib.Numerics.Kernel.maxNat] $body)


end FloatLib.Floats.Formats.P3109.KernelPath
