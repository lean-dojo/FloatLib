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

Binary interchange and posit arithmetic both decode finite values into a sign and an unsigned
significand. These one- and two-word operations combine aligned magnitudes, retaining the sign
of the larger magnitude on subtraction and choosing positive zero on exact cancellation.
-/

@[expose] public section

namespace FloatLib.Numerics.FixedWord

/--
Add or subtract two unsigned magnitudes according to their independent signs.

Exact cancellation returns positive zero. Same-sign callers must establish separately that the
sum fits in `UInt64`; opposite-sign subtraction cannot overflow.
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

Exact cancellation returns positive zero. Same-sign addition discards the carry from `add128`,
so callers must establish that the sum fits in `UInt128`; opposite-sign subtraction cannot overflow.
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
