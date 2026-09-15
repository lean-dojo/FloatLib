/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

/-!
# IEEE floating-point classes

IEEE 754-2019 §5.7.2 specifies the same ten classification results for binary
and decimal formats. Each format determines normality and its supported special
values; the result type is independent of radix, precision, bias, and storage.
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
