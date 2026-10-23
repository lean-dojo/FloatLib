/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Representation-independent operation context

Rounding direction, overflow handling, and treatment of tiny outputs describe how an exact value is
written into a finite numerical representation. They are operation context rather than properties
of a binary bit layout, so they live in the family-independent operation layer.

A concrete format may support only part of this vocabulary. Its quantizer gives each policy a
meaning or rejects unsupported combinations at a higher API layer.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Rule used when an exact value lies between adjacent representable values. -/
inductive RoundingMode where
  /-- Take the nearer neighbour, breaking a tie toward an even significand. -/
  | nearest
  /-- Take the nearer neighbour, breaking a tie toward the neighbour of larger magnitude. -/
  | nearestAway
  /-- Take the neighbour of smaller magnitude. -/
  | towardZero
  /-- Take the neighbour toward positive infinity. -/
  | up
  /-- Take the neighbour toward negative infinity. -/
  | down
  /--
  Take the neighbour of larger magnitude whenever the value is not representable. This is GNU
  MPFR's `MPFR_RNDA`, which is not an IEEE 754 rounding-direction attribute.
  -/
  | away
  /-- Randomized rounding driven by entropy supplied to the operation. -/
  | stochastic
  deriving DecidableEq, Repr

/-- Behavior when an exact magnitude lies outside the ordinary finite range. -/
inductive OverflowMode where
  /-- Use the representation's ordinary overflow result. -/
  | native
  /-- Clamp to the nearest finite endpoint. -/
  | saturate
  deriving DecidableEq, Repr

/-- Behavior when a nonzero result lies below the normal range. -/
inductive UnderflowMode where
  /-- Preserve the representation's gradual-underflow values when they exist. -/
  | gradual
  /-- Replace tiny stored outputs with the representation's zero. -/
  | flushToZero
  deriving DecidableEq, Repr

/-- Shared policy for converting an exact scalar to a finite numerical representation. -/
structure QuantizationPolicy where
  /-- Rule used to choose between adjacent representable values. -/
  rounding : RoundingMode := .nearest
  /-- Rule used when the exact magnitude exceeds the finite range. -/
  overflow : OverflowMode := .native
  /-- Rule used for nonzero results below the normal range. -/
  underflow : UnderflowMode := .gradual
  deriving DecidableEq, Repr

namespace QuantizationPolicy

/-- Nearest-even rounding with native overflow and gradual underflow. -/
def nearest : QuantizationPolicy := {}

/-- Nearest-even rounding with saturation and gradual underflow. -/
def saturating : QuantizationPolicy := { overflow := .saturate }

/-- Nearest-even rounding with native overflow and output flush-to-zero. -/
def flushToZero : QuantizationPolicy := { underflow := .flushToZero }

end QuantizationPolicy
end FloatLib.Numerics
