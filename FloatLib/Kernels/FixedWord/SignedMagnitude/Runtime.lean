/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Kernels.FixedWord.Difference.Runtime
public import FloatLib.Kernels.FixedWord.Product.Runtime

/-!
# Shared native signed-magnitude arithmetic

Binary interchange and posit arithmetic both decode a finite value into a sign and an unsigned
significand, so they can share these one- and two-word operations on aligned magnitudes. A
subtraction keeps the sign of the larger magnitude. Exact cancellation gives positive zero.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
Add or subtract two unsigned magnitudes according to their independent signs.

Exact cancellation returns positive zero. A same-sign caller has to show on its own that the sum
fits in `UInt64`, while opposite-sign subtraction can't overflow.
-/
@[inline] def addSignedMagnitudes
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt64) : Bool × UInt64 :=
  if leftNegative == rightNegative then
    (leftNegative, leftMagnitude + rightMagnitude)
  else if leftMagnitude == rightMagnitude then
    (false, 0)
  else if leftMagnitude < rightMagnitude then
    (rightNegative, rightMagnitude - leftMagnitude)
  else
    (leftNegative, leftMagnitude - rightMagnitude)

/--
Add or subtract two unsigned two-limb magnitudes according to their independent signs.

Exact cancellation returns positive zero. Same-sign addition discards the carry from `add128`, so
callers must show that the sum fits in `UInt128`. Opposite-sign subtraction can't overflow.
-/
@[inline] def addSignedMagnitudes128
    (leftNegative rightNegative : Bool)
    (leftMagnitude rightMagnitude : UInt128) : Bool × UInt128 :=
  if leftNegative == rightNegative then
    (leftNegative, (add128 leftMagnitude rightMagnitude).value)
  else if leftMagnitude == rightMagnitude then
    (false, ⟨0, 0⟩)
  else if UInt128.less leftMagnitude rightMagnitude then
    (rightNegative, UInt128.sub rightMagnitude leftMagnitude)
  else
    (leftNegative, UInt128.sub leftMagnitude rightMagnitude)

end FloatLib.Numerics.FixedWord
