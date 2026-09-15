/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.WideLimb.Round.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic

/-!
# Wide-limb multiplication runtime

Normal operands are multiplied exactly by the schoolbook limb product and passed to
`roundNormal?` for one rounding. Normal inputs can still be declined: the product's leading
position must reach the normal range before rounding, and its position after rounding carry
must stay in the finite range. In particular, the lower check can decline a product that would
round up to the smallest normal value. Zero, subnormal, and exceptional operands are also
declined. The total operation computes every declined case with `Model.Spec.mul` through the
model codec; `Multiplication.Proof` proves agreement on all operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb

open FloatLib.Numerics

/--
Try multiplication of two normal stored values.

With `position = product.log2 + (xExponent.toNat - 1) + (yExponent.toNat - 1)`,
acceptance also requires `fmt.bias + 2 * fmt.fracWidth - 1 ≤ position` and
`normalizedPosition ≤ 3 * fmt.bias + 2 * fmt.fracWidth - 2`, where rounding carry increments
`position` to obtain `normalizedPosition`. See `roundNormal?`.
-/
def mulNormal? (fmt : FloatFormat) (x y : Value fmt) : Option (Value fmt) :=
  let xExponent := expWord x
  let yExponent := expWord y
  if xExponent == 0 || xExponent == expAllOnes fmt ||
      yExponent == 0 || yExponent == expAllOnes fmt then
    none
  else
    roundNormal? fmt (Bool.xor (signBit x) (signBit y))
      ((normalMantissa x).mul (normalMantissa y)) 0
      ((xExponent.toNat - 1) + (yExponent.toNat - 1))

/-- Wide-limb multiplication with the reference operation for declined cases. -/
def mul (fmt : FloatFormat) (x y : Value fmt) : Value fmt :=
  match mulNormal? fmt x y with
  | some product => product
  | none => ofModel (Spec.mul (toModel x) (toModel y))

end FloatLib.Floats.Formats.BinaryInterchange.Model.WideLimb
