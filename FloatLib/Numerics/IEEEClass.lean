/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

/-!
# IEEE floating-point classes

IEEE 754-2019 §5.7.2 gives binary and decimal formats the same ten classification results, and each
format decides normality and its supported special values, and the result type doesn't depend on
radix, precision, bias, or storage.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- The ten mutually exclusive floating-point classes of IEEE 754-2019 §5.7.2. -/
inductive IEEEClass where
  /-- A NaN whose use by signaling operations raises invalid. -/
  | signalingNaN
  /-- A quiet NaN. -/
  | quietNaN
  /-- Negative infinity. -/
  | negativeInfinity
  /-- A negative finite normal number. -/
  | negativeNormal
  /-- A negative finite subnormal number. -/
  | negativeSubnormal
  /-- Zero with its sign bit set. -/
  | negativeZero
  /-- Zero with its sign bit clear. -/
  | positiveZero
  /-- A positive finite subnormal number. -/
  | positiveSubnormal
  /-- A positive finite normal number. -/
  | positiveNormal
  /-- Positive infinity. -/
  | positiveInfinity
  deriving DecidableEq, Repr

end FloatLib.Numerics
