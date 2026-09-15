/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Arithmetic

/-!
# Activation ranges for `Model.Interval`

Monotone operations are evaluated at interval endpoints. Absolute value handles the two monotone
regions separately, and square root uses directed rounding at both endpoints.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Interval

/-- Sharp endpoint-grid image enclosure for ReLU. -/
@[inline] def relu {fmt : FloatFormat} (A : Interval fmt) : Interval fmt :=
  { lo := Model.maximum A.lo (Model.zero fmt false)
    hi := Model.maximum A.hi (Model.zero fmt false) }

/--
Image enclosure for absolute value.

Intervals on the negative side are negated, positive intervals are preserved, and intervals
crossing zero map to `[0, max(-lo, hi)]`.
-/
def abs {fmt : FloatFormat} (A : Interval fmt) : Interval fmt :=
  if leB A.hi (Model.zero fmt true) then
    neg A
  else if leB (Model.zero fmt false) A.lo then
    A
  else
    { lo := Model.zero fmt false
      hi := Model.maximum (Model.neg A.lo) A.hi }

/--
Outward-rounded square-root image.

The executable operation is total. A real-valued enclosure theorem additionally requires
a conventional IEEE descriptor and a valid input interval with nonnegative lower endpoint.
-/
@[inline] def sqrt {fmt : FloatFormat} (A : Interval fmt) : Interval fmt :=
  { lo := Model.sqrtDown A.lo
    hi := Model.sqrtUp A.hi }

end Interval
end Model
end FloatLib.Floats.Formats.BinaryInterchange
