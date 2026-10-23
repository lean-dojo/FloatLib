/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Nearest
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Dyadic
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Classification

/-!
# Executable directed rounding

Exact rational intermediates support the six `IEEERoundingMode` choices. Together with the
dyadic rounders of `Rounding.Directed.Dyadic`, they implement the directed kernels of addition,
subtraction, multiplication, division, fused multiply-add, and square root in
`Model.Internal.Directed`. `Model.add x y (mode := .up)` and its siblings in `Arithmetic.Runtime`
call them for every direction except nearest-even. `roundRatNearestAwayScaled` and its tie test
`rationalIsGridTieScaled` are the rational twins of the dyadic nearest-away rounder.

Rounding thresholds, signed-zero behavior, and exceptional results follow the `FloatFormat`
descriptor. `DirectedSemantics` proves the real and extended-real correctness theorems, with
their format and input hypotheses.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-! ## Directed rounding of exact rationals -/

/--
Round a scaled positive rational magnitude to the adjacent lower or upper representable magnitude.

`roundMagnitudeUp = false` selects the lower magnitude and `true` selects the upper magnitude.
The `sign` parameter supplies the sign to the format's packing, zero, and overflow constructors.
-/
def roundRatMagnitudeDirectedScaled (fmt : FloatFormat) (roundMagnitudeUp sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  let precision := fmt.fracWidth
  let maxNormal := fmt.maxNormalExponent
  let minNormal := fmt.minNormalExponent
  let minSubnormal := fmt.minSubnormalExponent
  let subnormalAlign := fmt.exponentBias + precision - 1
  if denominator == 0 then
    invalidResult fmt
  else if numerator == 0 then
    zero fmt sign
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    if totalExponent > maxNormal then
      directedOverflow fmt sign roundMagnitudeUp
    else if totalExponent < minSubnormal then
      if roundMagnitudeUp then
        if sign then negMinSubnormal fmt else posMinSubnormal fmt
      else
        zero fmt sign
    else if totalExponent < minNormal then
      let (scaledNumerator, scaledDenominator) :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator (exponent + Int.ofNat subnormalAlign)
      let fraction :=
        roundQuotDirected roundMagnitudeUp scaledNumerator scaledDenominator
      packRoundedSubnormal fmt sign (zero fmt sign) fraction
    else
      let shift : Int := Int.ofNat precision - rationalExponent
      let (scaledNumerator, scaledDenominator) := Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
      let roundedMantissa :=
        roundQuotDirected roundMagnitudeUp scaledNumerator scaledDenominator
      packRoundedNormal fmt sign (directedOverflow fmt sign roundMagnitudeUp)
        totalExponent roundedMantissa

/--
Whether the scaled rational `(numerator / denominator) * 2^exponent` lies exactly halfway between
two adjacent values of the binary grid of `fmt` with gradual underflow and no upper exponent bound.

This is the rational twin of `dyadicIsGridTie`, on the same grid. The rational is scaled as
`roundRatScaledGeneral` scales it, to the subnormal spacing below the normal range and to
`fracWidth + 1` significant bits above it, and it is a tie when twice the remainder of that
quotient equals its denominator. A zero numerator or denominator is never a tie. A magnitude below
half the least subnormal is recognized from its leading exponent alone, so the subnormal shift
stays bounded by the operand widths and the destination precision.
-/
def rationalIsGridTieScaled (fmt : FloatFormat) (numerator denominator : Nat)
    (exponent : Int) : Bool :=
  if denominator == 0 || numerator == 0 then
    false
  else
    let rationalExponent := Numerics.RationalBinary.floorLog2 numerator denominator
    let totalExponent := rationalExponent + exponent
    if totalExponent + 1 < fmt.minSubnormalExponent then
      false
    else
      let shift : Int :=
        if totalExponent < fmt.minNormalExponent then
          exponent + Int.ofNat (fmt.exponentBias + fmt.fracWidth - 1)
        else
          Int.ofNat fmt.fracWidth - rationalExponent
      let (scaledNumerator, scaledDenominator) :=
        Numerics.RationalBinary.scaleByPowerOfTwo numerator denominator shift
      2 * (scaledNumerator % scaledDenominator) == scaledDenominator

/--
Round an exact scaled signed rational to nearest with ties away from zero, IEEE 754-2019
`roundTiesToAway`.

This is the rational twin of `roundDyadicNearestAway`. Off a grid tie it is nearest-even rounding,
`roundRatScaled`. At a tie the magnitude rounds up with `roundRatMagnitudeDirectedScaled`. A zero
denominator is never a tie and takes the result of `roundRatScaled`.
-/
def roundRatNearestAwayScaled (fmt : FloatFormat) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  if rationalIsGridTieScaled fmt numerator denominator exponent then
    roundRatMagnitudeDirectedScaled fmt true sign numerator denominator exponent
  else
    roundRatScaled fmt sign numerator denominator exponent

namespace Internal.Directed

/--
Round the exact scaled signed rational `±(numerator / denominator) * 2^exponent` in the direction
`mode`. Nearest-even is `Model.roundRatScaled`.
-/
def roundRatScaled (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  match mode with
  | .nearest => Model.roundRatScaled fmt sign numerator denominator exponent
  | .nearestAway => roundRatNearestAwayScaled fmt sign numerator denominator exponent
  | .towardZero =>
      roundRatMagnitudeDirectedScaled fmt false sign numerator denominator exponent
  | .up =>
      roundRatMagnitudeDirectedScaled fmt (!sign) sign numerator denominator exponent
  | .down =>
      roundRatMagnitudeDirectedScaled fmt sign sign numerator denominator exponent
  | .away =>
      roundRatMagnitudeDirectedScaled fmt true sign numerator denominator exponent

/--
Round the exact signed rational `±numerator / denominator` in the direction `mode`. Nearest-even
is `Model.roundRat`.
-/
def roundRat (fmt : FloatFormat) (mode : IEEERoundingMode) (sign : Bool)
    (numerator denominator : Nat) : Model fmt :=
  roundRatScaled fmt mode sign numerator denominator 0

end Internal.Directed

/-- Round an exact scaled signed rational toward negative infinity. -/
@[inline] def roundRatDownScaled (fmt : FloatFormat) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  Internal.Directed.roundRatScaled fmt .down sign numerator denominator exponent

/-- Round an exact scaled signed rational toward positive infinity. -/
@[inline] def roundRatUpScaled (fmt : FloatFormat) (sign : Bool)
    (numerator denominator : Nat) (exponent : Int) : Model fmt :=
  Internal.Directed.roundRatScaled fmt .up sign numerator denominator exponent

/-- Round an exact signed rational toward negative infinity. -/
@[inline] def roundRatDown (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat) :
    Model fmt :=
  Internal.Directed.roundRat fmt .down sign numerator denominator

/-- Round an exact signed rational toward positive infinity. -/
@[inline] def roundRatUp (fmt : FloatFormat) (sign : Bool) (numerator denominator : Nat) :
    Model fmt :=
  Internal.Directed.roundRat fmt .up sign numerator denominator

/-! ## Arithmetic under an explicit rounding direction -/

/--
Zero for an exactly cancelling addition under `mode`. It requests the sign
`IEEERoundingMode.zeroSumSign`, and `zero` delivers positive zero instead in a format without a
signed zero.
-/
@[inline] def zeroForExactSum (fmt : FloatFormat) (mode : IEEERoundingMode)
    (leftSign rightSign : Bool) : Model fmt :=
  zero fmt (mode.zeroSumSign leftSign rightSign)

namespace Internal.Directed

/--
IEEE addition in rounding direction `mode`, the kernel of `Model.add x y (mode := mode)`.

Nearest-even addition is the dispatched `Nearest.add`, and every other direction rounds the exact
dyadic sum once.
-/
def add {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  match mode with
  | .nearest => Nearest.add x y
  | .nearestAway | .towardZero | .up | .down
    | .away =>
      withNaNSelection (chooseNaN2 x y) fun hnan =>
        let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
        if hxInf : isInf x then
          if isInf y then
            if Model.signBit x == Model.signBit y then x else invalidResult fmt
          else
            x
        else if hyInf : isInf y then
          y
        else
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1
              (Bool.eq_false_of_not_eq_true hxInf)
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2
              (Bool.eq_false_of_not_eq_true hyInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let exact := Model.addDyadic dx dy
          if exact.significand == 0 then
            zeroForExactSum fmt mode dx.negative dy.negative
          else
            Internal.Directed.roundDyadic fmt mode exact

/--
IEEE subtraction in rounding direction `mode`, the kernel of `Model.sub x y (mode := mode)`:
directed addition of the negated right operand.
-/
@[inline] def sub {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  add mode x (neg y)

/--
IEEE multiplication in rounding direction `mode`, the kernel of `Model.mul x y (mode := mode)`.

Nearest-even multiplication is the dispatched `Nearest.mul`, and every other direction rounds the
exact dyadic product once.
-/
def mul {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  match mode with
  | .nearest => Nearest.mul x y
  | .nearestAway | .towardZero | .up | .down
    | .away =>
      withNaNSelection (chooseNaN2 x y) fun hnan =>
        let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
        if hxInf : isInf x then
          if isZero y then invalidResult fmt
          else nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else if hyInf : isInf y then
          if isZero x then invalidResult fmt
          else nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1
              (Bool.eq_false_of_not_eq_true hxInf)
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2
              (Bool.eq_false_of_not_eq_true hyInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let exact : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          Internal.Directed.roundDyadic fmt mode exact

/--
IEEE division in rounding direction `mode`, the kernel of `Model.div x y (mode := mode)`.

Nearest-even division is the dispatched `Nearest.div`, and every other direction rounds the exact
scaled rational quotient once.
-/
def div {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y : Model fmt) : Model fmt :=
  match mode with
  | .nearest => Nearest.div x y
  | .nearestAway | .towardZero | .up | .down
    | .away =>
      withNaNSelection (chooseNaN2 x y) fun hnan =>
        let hnotNaN := (chooseNaN2_eq_none_iff x y).1 hnan
        if hxInf : isInf x then
          if isInf y then invalidResult fmt
          else nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else if hyInf : isInf y then
          zero fmt (Model.signBit x != Model.signBit y)
        else if isZero y then
          if isZero x then invalidResult fmt
          else nativeOverflow fmt (Model.signBit x != Model.signBit y)
        else
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1
              (Bool.eq_false_of_not_eq_true hxInf)
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2
              (Bool.eq_false_of_not_eq_true hyInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let sign := Bool.xor dx.negative dy.negative
          if dx.significand == 0 then
            zero fmt sign
          else
            Internal.Directed.roundRatScaled fmt mode sign dx.significand dy.significand
              (dx.exponent - dy.exponent)

/--
IEEE fused multiply-add in rounding direction `mode`, the kernel of
`Model.fma x y z (mode := mode)`.

Nearest-even FMA is the dispatched `Nearest.fma`, and every other direction rounds the exact
dyadic `x * y + z` once.
-/
def fma {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x y z : Model fmt) : Model fmt :=
  match mode with
  | .nearest => Nearest.fma x y z
  | .nearestAway | .towardZero | .up | .down
    | .away =>
      withNaNSelection (chooseNaN3 x y z) fun hnan =>
        let hnotNaN := (chooseNaN3_eq_none_iff x y z).1 hnan
        if hxyInf : isInf x || isInf y then
          if isZero x || isZero y then
            invalidResult fmt
          else
            let productSign := Bool.xor (Model.signBit x) (Model.signBit y)
            let productInfinity := nativeOverflow fmt productSign
            if isInf z then
              if Model.signBit z != productSign then invalidResult fmt else productInfinity
            else
              productInfinity
        else if hzInf : isInf z then
          z
        else
          let hxInf : isInf x = false := by
            cases hx : isInf x
            · rfl
            · simp [hx] at hxyInf
          let hyInf : isInf y = false := by
            cases hy : isInf y
            · rfl
            · simp [hy] at hxyInf
          let hxFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN.1 hxInf
          let hyFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false y hnotNaN.2.1 hyInf
          let hzFinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false z hnotNaN.2.2
              (Bool.eq_false_of_not_eq_true hzInf)
          let dx := finiteDyadic x hxFinite
          let dy := finiteDyadic y hyFinite
          let dz := finiteDyadic z hzFinite
          let product : Numerics.Dyadic :=
            { negative := Bool.xor dx.negative dy.negative
              significand := dx.significand * dy.significand
              exponent := dx.exponent + dy.exponent }
          let exact := Model.addDyadic product dz
          if exact.significand == 0 then
            zeroForExactSum fmt mode product.negative dz.negative
          else
            Internal.Directed.roundDyadic fmt mode exact

end Internal.Directed

/-! ## Directed square root -/

/-- Dyadic endpoint pair used to enclose a nonnegative square root. -/
structure SqrtDyadicBracket where
  /-- Lower endpoint. -/
  lower : Numerics.Dyadic
  /-- Upper endpoint. -/
  upper : Numerics.Dyadic

/-- Compute a dyadic enclosure of the square root of a nonnegative exact dyadic. -/
def sqrtDyadicBracket (fmt : FloatFormat) (value : Numerics.Dyadic) : SqrtDyadicBracket :=
  let exponentOdd := value.exponent % 2 != 0
  let mantissa := if exponentOdd then value.significand * 2 else value.significand
  let evenExponent := if exponentOdd then value.exponent - 1 else value.exponent
  let halfExponent := evenExponent / 2
  let leading := Nat.log2 mantissa
  let rootLeading := leading / 2
  let extraPrecision := fmt.fracWidth - rootLeading
  let scaled := Nat.shiftLeft mantissa (2 * extraPrecision)
  let lowerMantissa := Nat.sqrt scaled
  let remainder := scaled - lowerMantissa * lowerMantissa
  let endpointExponent := halfExponent - Int.ofNat extraPrecision
  { lower := { negative := false, significand := lowerMantissa, exponent := endpointExponent }
    upper :=
      { negative := false
        significand := if remainder == 0 then lowerMantissa else lowerMantissa + 1
        exponent := endpointExponent } }

namespace Internal.Directed

/--
IEEE square root in rounding direction `mode`, the kernel of `Model.sqrt x (mode := mode)`.

Both nearest modes use the dispatched nearest-even `Nearest.sqrt`. The exact square root of a
value of the format is never halfway between two adjacent values of the format's grid, because the
square of such a midpoint is not a value of the format: in a normal binade its odd part has more
significant bits than any significand, and below the normal range it is not a multiple of the least
subnormal. Nearest-away rounding therefore never meets a tie here. The directed modes round an
endpoint of `sqrtDyadicBracket`: the upper one when the positive result rounds up, toward positive
infinity or away from zero, and the lower one otherwise.
-/
def sqrt {fmt : FloatFormat} (mode : IEEERoundingMode)
    (x : Model fmt) : Model fmt :=
  match mode with
  | .nearest | .nearestAway => Nearest.sqrt x
  | .towardZero | .up | .down | .away =>
      withNaNSelection (chooseNaN1 x) fun hnan =>
        let hnotNaN := (chooseNaN1_eq_none_iff x).1 hnan
        if hxInf : isInf x then
          if Model.signBit x then invalidResult fmt else nativeOverflow fmt false
        else if isZero x then
          x
        else if Model.signBit x then
          invalidResult fmt
        else
          let hfinite :=
            isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x hnotNaN
              (Bool.eq_false_of_not_eq_true hxInf)
          let value := finiteDyadic x hfinite
          let bracket := sqrtDyadicBracket fmt value
          match mode with
          | .up | .away => roundDyadicUp fmt bracket.upper
          | .towardZero | .down => roundDyadicDown fmt bracket.lower
          | .nearest | .nearestAway => Nearest.sqrt x

end Internal.Directed

end Model
end FloatLib.Floats.Formats.BinaryInterchange
