/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.RoundingKernel.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode

/-!
# Directed rounding of exact dyadics

Exact signed dyadics round into a binary format under each `IEEERoundingMode`. Toward-zero,
toward-positive, and toward-negative rounding are implemented by one pair of magnitude rounders,
`roundDyadicMagnitudeDown` and `roundDyadicMagnitudeUp`, that the sign of the value selects
between. Nearest-even delegates to `Model.roundDyadic`.

Two further rounders are built from the same pieces. `roundDyadicAway` (MPFR's
`MPFR_RNDA`) always rounds the magnitude up. `roundDyadicNearestAway` (IEEE 754-2019
`roundTiesToAway`) is nearest-even except at an exact tie on the format's grid, which
`dyadicIsGridTie` detects and which then rounds away from zero.

Overflow follows `directedOverflow`: a magnitude carried upward becomes the format's native
overflow value and a magnitude carried downward becomes the largest finite value. The policy
entry point `Policy.roundDyadic` in `Rounding.Policy.Runtime` delegates to
`Internal.Directed.roundDyadic` for the six directions with native overflow and gradual underflow.
`Policy.roundDyadicGeneral` is a separate rational core whose agreement with these rounders is
proved in `Rounding.Policy.Agreement`.

Every threshold is derived from `FloatFormat`. The magnitude helpers require a positive
mantissa, and the signed entry points handle zero before selecting a magnitude helper.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Directed rounding of exact dyadics -/

/-- Round an exact positive magnitude downward, attaching `sign` to the result. -/
def roundDyadicMagnitudeDown (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let leading := Nat.log2 mantissa
  let totalExponent := Int.ofNat leading + exponent
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  if totalExponent > maxNormal then
    maxFinite fmt sign
  else if totalExponent < minSubnormal then
    zero fmt sign
  else if totalExponent < minNormal then
    let fraction :=
      match exponent - minSubnormal with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => Nat.shiftRight mantissa (shift + 1)
    if fraction == 0 then zero fmt sign else ofFields fmt sign 0 fraction
  else
    let roundedMantissa :=
      if leading ≥ precision then
        Nat.shiftRight mantissa (leading - precision)
      else
        Nat.shiftLeft mantissa (precision - leading)
    let encodedExponent := Int.toNat (totalExponent + Int.ofNat fmt.exponentBias)
    let fraction := roundedMantissa - pow2 precision
    if encodedExponent > fmt.maxFiniteExpField ||
        (encodedExponent == fmt.maxFiniteExpField &&
          fraction > fmt.maxFiniteFracField) then
      maxFinite fmt sign
    else
      ofFields fmt sign encodedExponent fraction

/-- Round an exact positive magnitude upward, attaching `sign` to the result. -/
def roundDyadicMagnitudeUp (fmt : FloatFormat) (sign : Bool)
    (mantissa : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let leading := Nat.log2 mantissa
  let totalExponent := Int.ofNat leading + exponent
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  if totalExponent > maxNormal then
    nativeOverflow fmt sign
  else if totalExponent < minSubnormal then
    ofFields fmt sign 0 1
  else if totalExponent < minNormal then
    let fraction :=
      match exponent - minSubnormal with
      | .ofNat shift => Nat.shiftLeft mantissa shift
      | .negSucc shift => Numerics.shiftRightCeil mantissa (shift + 1)
    packRoundedSubnormal fmt sign (ofFields fmt sign 0 1) fraction
  else
    let roundedMantissa :=
      if leading ≥ precision then
        Numerics.shiftRightCeil mantissa (leading - precision)
      else
        Nat.shiftLeft mantissa (precision - leading)
    packRoundedNormal fmt sign (nativeOverflow fmt sign) totalExponent roundedMantissa

/-- Round a positive exact dyadic toward negative infinity. -/
@[inline] def roundDyadicPosDown
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  roundDyadicMagnitudeDown fmt false mantissa exponent

/-- Round a positive exact dyadic toward positive infinity. -/
@[inline] def roundDyadicPosUp
    (fmt : FloatFormat) (mantissa : Nat) (exponent : Int) : Model fmt :=
  roundDyadicMagnitudeUp fmt false mantissa exponent

/-- Round an exact dyadic toward negative infinity. -/
def roundDyadicDown (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else if value.negative then
    roundDyadicMagnitudeUp fmt true value.significand value.exponent
  else
    roundDyadicMagnitudeDown fmt false value.significand value.exponent

/-- Round an exact dyadic toward positive infinity. -/
def roundDyadicUp (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else if value.negative then
    roundDyadicMagnitudeDown fmt true value.significand value.exponent
  else
    roundDyadicMagnitudeUp fmt false value.significand value.exponent

/-- Round an exact dyadic toward zero. -/
def roundDyadicTowardZero (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundDyadicMagnitudeDown fmt value.negative value.significand value.exponent

/--
Round an exact dyadic away from zero, MPFR's `MPFR_RNDA`.

The magnitude rounds up and keeps its sign, so a nonzero value below the least subnormal becomes
that subnormal and a magnitude carried past the largest finite value becomes the native overflow
value.
-/
def roundDyadicAway (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if value.significand == 0 then
    zero fmt value.negative
  else
    roundDyadicMagnitudeUp fmt value.negative value.significand value.exponent

/--
Whether an exact dyadic lies exactly halfway between two adjacent values of the binary grid of
`fmt` with gradual underflow and no upper exponent bound.

A magnitude whose leading bit has exponent `L` lies on a grid of spacing
`2^(max fmt.minSubnormalExponent (L - fmt.fracWidth))`: the subnormal spacing below the normal
range and the spacing of its own binade above it, as `roundDyadic` rounds. The value is a tie
when the bits below that spacing are exactly one half of it, as `Numerics.shiftRightIsTie` tests.
Zero is never a tie, and neither is a magnitude below half the least subnormal, whose guard bit is
clear. The grid continues past the largest finite value, so the midpoint between that value and
the next grid value is a tie, and so are ties in binades above the finite range.
-/
def dyadicIsGridTie (fmt : FloatFormat) (value : Numerics.Dyadic) : Bool :=
  match value.exponent -
      max fmt.minSubnormalExponent
        ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth) with
  | .ofNat _ => false
  | .negSucc shift => Numerics.shiftRightIsTie value.significand (shift + 1)

/-- Zero is never a grid tie. -/
@[simp] theorem dyadicIsGridTie_zero (fmt : FloatFormat) (sign : Bool) (exponent : Int) :
    dyadicIsGridTie fmt { negative := sign, significand := 0, exponent := exponent } = false := by
  unfold dyadicIsGridTie
  split <;> simp [Numerics.shiftRightIsTie]

/--
Round an exact dyadic to nearest with ties away from zero, IEEE 754-2019 `roundTiesToAway`.

Off a grid tie the nearer neighbour is unique and this is nearest-even rounding, `roundDyadic`. At
a tie both neighbours are equally near and the magnitude rounds up, as `roundDyadicAway`
computes. Overflow and underflow therefore behave as in nearest-even rounding, except that a tie
at the overflow midpoint overflows whatever the parity of the largest finite significand, and the
midpoint between zero and the least subnormal rounds to that subnormal.
-/
def roundDyadicNearestAway (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  if dyadicIsGridTie fmt value then roundDyadicAway fmt value else roundDyadic fmt value

namespace Internal.Directed

/--
Round an exact dyadic in the direction `mode`, the rounding step of every directed kernel.
Nearest-even is `Model.roundDyadic`.
-/
@[inline] def roundDyadic (fmt : FloatFormat) (mode : IEEERoundingMode)
    (value : Numerics.Dyadic) : Model fmt :=
  match mode with
  | .nearest => Model.roundDyadic fmt value
  | .nearestAway => roundDyadicNearestAway fmt value
  | .towardZero => roundDyadicTowardZero fmt value
  | .up => roundDyadicUp fmt value
  | .down => roundDyadicDown fmt value
  | .away => roundDyadicAway fmt value

end Internal.Directed

end Model
end FloatLib.Floats.Formats.BinaryInterchange
