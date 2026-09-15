/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Addition.Runtime

/-!
# Wide-limb fused multiply-add runtime

The exact product of two normal significands, formed by the schoolbook limb product, is combined
with the third operand's significand by the same alignment core as addition, `alignAndRound?`,
with the product at twice the significand offset. There is a single rounding. All three operands
must be normal to enter this core. Exact cancellation returns positive zero; a nonzero result
must pass `roundNormal?`'s lower check before rounding and upper check after rounding carry.
Thus normal operands alone do not guarantee acceptance, even when rounding would produce the
smallest normal value. The total operation computes declined cases with `Model.Spec.fma`;
`Fma.Proof` proves agreement on all operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/--
Try fused multiply-add of three normal stored values.

Exact cancellation is accepted as positive zero. Otherwise the aligned significand reaches
`roundNormal?`, which requires `fmt.bias + 2 * fmt.fracWidth - 1 ≤ leading + jam + scale` and
`normalizedPosition ≤ 3 * fmt.bias + 2 * fmt.fracWidth - 2`, with the latter position including
any rounding carry. Non-normal operands and failures of either range check return `none`.
-/
def fmaNormal? (fmt : FloatFormat) (x y z : Value fmt) : Option (Value fmt) :=
  let xExponent := expWord x
  let yExponent := expWord y
  let zExponent := expWord z
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt ||
      zExponent == 0 || zExponent == expAllOnes fmt then
    none
  else
    alignAndRound? fmt 0
      (Bool.xor (signBit x) (signBit y)) ((normalMantissa x).mul (normalMantissa y))
      ((xExponent.toNat - 1) + (yExponent.toNat - 1))
      (signBit z) (normalMantissa z)
      ((zExponent.toNat - 1) + FiniteKernel.finiteScaleOffset fmt)

/-- Wide-limb fused multiply-add with the reference operation for declined cases. -/
def fma (fmt : FloatFormat) (x y z : Value fmt) : Value fmt :=
  match fmaNormal? fmt x y z with
  | some result => result
  | none => ofModel (Spec.fma (toModel x) (toModel y) (toModel z))

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
