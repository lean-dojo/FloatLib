/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Operation.Context

/-!
# IEEE rounding modes for `Model`

This type provides nearest-even rounding and the three directed rounding attributes. The broader
quantization-policy vocabulary also contains nearest-away and stochastic rounding.

This is the shared mode definition for executable rounding and its proofs.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Deterministic IEEE-754 rounding-direction attribute. -/
inductive IEEERoundingMode where
  /-- Round to the nearest representable value, breaking ties toward an even significand. -/
  | nearestEven
  /-- Round toward zero. -/
  | towardZero
  /-- Round toward positive infinity. -/
  | towardPositiveInfinity
  /-- Round toward negative infinity. -/
  | towardNegativeInfinity
  deriving DecidableEq, Repr

namespace IEEERoundingMode

/--
All constructors of `IEEERoundingMode`, in their shared traversal order.

Update this list when adding a constructor; callers can use it without duplicating the enumeration.
-/
def all : List IEEERoundingMode :=
  [ .nearestEven, .towardZero, .towardPositiveInfinity, .towardNegativeInfinity ]

/--
A concise, stable name for diagnostics and interchange files.

The directed modes use the customary `towardPositive` and `towardNegative` spellings; their
constructors retain the more explicit `Infinity` suffix used in proofs and APIs.
-/
def name : IEEERoundingMode → String
  | .nearestEven => "nearestEven"
  | .towardZero => "towardZero"
  | .towardPositiveInfinity => "towardPositive"
  | .towardNegativeInfinity => "towardNegative"

instance : ToString IEEERoundingMode where
  toString := name

/--
The quantization-policy rounding mode with the same direction.

`Numerics.RoundingMode` also contains nearest-away and stochastic rounding, which have no
constructor in `IEEERoundingMode`; this map is therefore an embedding, not a bijection.
-/
def toRoundingMode : IEEERoundingMode → Numerics.RoundingMode
  | .nearestEven => .nearestEven
  | .towardZero => .towardZero
  | .towardPositiveInfinity => .towardPositive
  | .towardNegativeInfinity => .towardNegative

end IEEERoundingMode

end Model
end FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLib.IEEERounding

/-!
The optional `FloatLib.IEEERounding` scope provides mathematical spellings for the two directed
infinity modes. Keeping these notations scoped prevents them from changing the meaning of `∞` in
files that use extended real numbers.
-/

/-- Round toward positive infinity. Requires `open scoped FloatLib.IEEERounding`. -/
scoped notation "+∞" =>
  Floats.Formats.BinaryInterchange.Model.IEEERoundingMode.towardPositiveInfinity

/-- Round toward negative infinity. Requires `open scoped FloatLib.IEEERounding`. -/
scoped notation "-∞" =>
  Floats.Formats.BinaryInterchange.Model.IEEERoundingMode.towardNegativeInfinity

end FloatLib.IEEERounding
