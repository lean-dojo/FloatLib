/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Runtime
public import FloatLib.Tactic.KernelPrepare
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Exact
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Root

/-!
# Prepared P3109 decoding and projection

P3109 Interim Report v4.1 (14 September 2026), §§4.7 and 4.10, an unapproved draft.
Three prepared functions share exact decoding, rational projection and square-root
projection across the arithmetic operations. Each carries a kernel-checked equality
for every valid descriptor, rounding mode, saturation mode and input. Source and
destination descriptors remain independent.

Preparation exposes the existing proved integer, bit and rational kernels once.
It preserves precision rounding before saturation and every exceptional branch.
For stochastic modes the equality holds for each supplied random word; it is not
a statement about a distribution. Compiled execution keeps the existing algorithms.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.P3109

open Formats.P3109 Numerics

namespace Kernel

section

attribute [local kernel_optimize unfold]
  toClosedRat projectRat projectSqrt decode
  ExecFloat.Codebook.decode ExecFloat.Codebook.toCode
  Arithmetic.toRat Dyadic.toRat
  Format.projectRatCode Format.projectRatValue Format.roundRatToPrecision
  Format.roundFiniteRatToPrecision Format.Internal.roundRationalAway
  Format.Internal.roundRationalAwayWithParity Format.lowerCodeIsEven
  Format.Internal.scaleRationalFractionFloor
  Format.Internal.scaleRationalFractionNearestEven
  Format.saturate Format.Internal.saturateBelow Format.Internal.saturateAbove
  Format.Internal.encodeDatumNat Format.Internal.encodePositiveFinite
  Format.minimumNormalExponent Format.minimumQuantumExponent
  Format.exponentBias Format.exponentBits Format.trailingBits
  Format.decode Format.decodeNat Format.decodePositiveFinite Format.codebook
  Format.maxFinite Format.minFinite Format.maxFiniteBits
  Format.signBoundary Format.modulus Format.nanBits
  Format.positiveInfinityBits Format.negativeInfinityBits
  RationalBinary.floorLog2 RationalBinary.lessThanPowerOfTwo
  RationalBinary.atLeastPowerOfTwo RationalBinary.scaleByPowerOfTwo
  Dyadic.Internal.compareScalable Dyadic.Internal.compareScalableFields
  Dyadic.Internal.compareNonzeroMagnitudes Dyadic.signedSignificand Dyadic.neg
  Arithmetic.sqrtCode Arithmetic.sqrtValue Arithmetic.sqrtRounded
  Arithmetic.roundSqrtRatToPrecision Arithmetic.sqrtQuantum Arithmetic.sqrtFloor
  Arithmetic.sqrtRoundAway Arithmetic.compareSqrt Format.roundMagnitudeUp
  Rat.zpow

/-- P3109 interim report v4.1, §4.7.2: prepared exact rational decoding at every valid
    descriptor. -/
noncomputable def decode (source : Format) :
    { run : ExecFloat.P3109 source → NumericalValue Rat // run = toClosedRat } :=
  kernel_prepare% (fun (value : ExecFloat.P3109 source) => toClosedRat value)

/-- P3109 interim report v4.1, §4.7.3: prepared rational projection with precision rounding
    before saturation. -/
noncomputable def projectRat (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    { run : NumericalValue Rat → ExecFloat.P3109 target //
      run = fun value => ExecFloat.P3109.projectRat value mode saturation } :=
  kernel_prepare% (fun (value : NumericalValue Rat) =>
    ExecFloat.P3109.projectRat (format := target) value mode saturation)

/-- P3109 interim report v4.1, §4.10.8: prepared root projection, including its exact threshold
    comparisons. -/
noncomputable def projectSqrt (target : Format) (mode : RoundingMode)
    (saturation : SaturationMode) :
    { run : NumericalValue Rat → ExecFloat.P3109 target //
      run = fun value => ExecFloat.P3109.projectSqrt value mode saturation } :=
  kernel_prepare% (fun (value : NumericalValue Rat) =>
    ExecFloat.P3109.projectSqrt (format := target) value mode saturation)

end

end Kernel

/-- P3109 interim report v4.1, §4.7.2: replace exact decoding by the equal prepared function. -/
@[kernel_optimize] theorem toClosedRat_eq_prepared {source : Format}
    (value : ExecFloat.P3109 source) :
    toClosedRat value = (Kernel.decode source).val value :=
  congrFun (Kernel.decode source).property.symm value

/-- P3109 interim report v4.1, §4.7.3: prepared projection preserves every policy and closed
    rational input. -/
@[kernel_optimize] theorem projectRat_eq_prepared {target : Format}
    (value : NumericalValue Rat) (mode : RoundingMode) (saturation : SaturationMode) :
    projectRat (format := target) value mode saturation =
      (Kernel.projectRat target mode saturation).val value :=
  congrFun (Kernel.projectRat target mode saturation).property.symm value

/-- P3109 interim report v4.1, §4.10.8: prepared root projection preserves every policy and
    exceptional case. -/
@[kernel_optimize] theorem projectSqrt_eq_prepared {target : Format}
    (value : NumericalValue Rat) (mode : RoundingMode) (saturation : SaturationMode) :
    projectSqrt (format := target) value mode saturation =
      (Kernel.projectSqrt target mode saturation).val value :=
  congrFun (Kernel.projectSqrt target mode saturation).property.symm value

-- The public defining equations feed the same prepared stages for every operation.
attribute [kernel_optimize unfold]
  unary binary ternary
  Arithmetic.Negate Arithmetic.Abs Arithmetic.CopySign
  Arithmetic.Add Arithmetic.Subtract Arithmetic.Multiply Arithmetic.Divide
  Arithmetic.Recip Arithmetic.FMA Arithmetic.FAA
  Arithmetic.rsqrtRadicand Arithmetic.hypotRadicand

end FloatLib.Floats.ExecFloat.P3109
