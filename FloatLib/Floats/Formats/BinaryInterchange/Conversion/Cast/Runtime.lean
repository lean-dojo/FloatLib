/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Widening
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

/-!
# Executable binary format casts

This module converts a value from one binary descriptor (`src`) to another (`dst`), for example
binary32 to bfloat16 or binary16 to binary64. It works from the exact value of the source
encoding, with no host floating-point number in between.

## Finite values

Normal numbers, subnormals, and zeros decode to a signed dyadic:

```text
(±)  mant × 2^exp
```

The integer significand and the power-of-two scale represent the source value with no error.
Binary32 `1.0` decodes to `1`, while binary32 `0.1` decodes to the already rounded binary32 value.
Widening the latter keeps that value, including its difference from the rational `1/10`.

`cast src dst x` rounds once to nearest, with ties to even, in the destination.
`cast src dst x (mode := .up)` rounds in another direction, and `(status := true)` adds the IEEE
exception flags and the ternary value. Identity casts and compatible fraction-field widenings
skip rounding, because they preserve every finite source value.

| Situation | Result |
|-----------|--------|
| The destination represents the source value | Exact conversion, including binary16 to binary32 |
| The source lies between destination values | One rounding step in the selected mode |
| The magnitude exceeds the destination range | The destination encoding's overflow behavior |
| The magnitude is below the smallest normal | A subnormal or zero, according to rounding |

The general finite path is:

```text
Model src
    │  finiteDyadic
    ▼
  Numerics.Dyadic  (± mant × 2^exp)     -- exact meaning of the source bits
    │  roundDyadic dst                -- or Internal.Directed.roundDyadic
    ▼
Model dst
```

## NaNs and infinities

A NaN cast to the same descriptor is quieted and keeps its sign and payload. Between different
descriptors the cast uses `propagatedNaN`, as IEEE 754-2019 §6.2.3 recommends. An IEEE
destination keeps the source sign and the IEEE payload (the fraction without its quiet bit, read
as a natural number) when that payload fits, and otherwise uses the zero payload. A maximum-NaN
destination keeps the sign, an FNUZ destination has its single NaN, and a fully finite destination
gets positive zero. `ExecFloat` conversion applies the same rule.

Infinity follows the destination's overflow policy. That means same-sign infinity for IEEE
encodings, canonical NaN for finite-with-NaN encodings, and the same-sign maximum finite value for
a fully finite encoding.

Once NaN and infinity have been excluded, finiteness is proved and `finiteDyadic` is total. With
`status := true`, a cast also reports invalid input, overflow, underflow, inexactness and the
ternary value, all from the same conversion result.

The public `cast` is a `@[macro_inline]` selector over three kernels: `Internal.Nearest.cast`
for the default, `Internal.Directed.cast` for the other directions, and `Internal.Status.cast`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Widen `x` field by field into a destination `dst` with the same exponent semantics.

The sign and exponent fields are copied, and the source fraction moves into the high end of the
wider destination fraction. The operation is total and ignores the value class. For a finite `x`
it preserves the value (`isFinite_widenExact` and `toReal_widenExact`, which assume
`isFinite x = true`), and the casts call it only on finite inputs. A non-finite `x` need not keep
its class. In the `finiteMaxNaN` encoding a NaN (all-ones exponent and fraction, either sign) gains
zero low fraction bits when `dst` has a wider fraction, and that is a finite pattern.

The four proof arguments (equal exponent width, equal declared bias, equal encoding, and a
destination fraction at least as wide) play no part in the computation. They restrict callers to
compatible widening, so the operation cannot narrow or cross an encoding boundary.
-/
@[inline] def widenExact {src dst : FloatFormat} (x : Model src)
    (_ : src.expWidth = dst.expWidth)
    (_ : src.exponentBias = dst.exponentBias)
    (_ : src.encoding = dst.encoding)
    (_ : src.fracWidth ≤ dst.fracWidth) : Model dst :=
  let shift := dst.fracWidth - src.fracWidth
  ofFields dst (signBit x) (expField x)
    (Nat.shiftLeft (fracField x) shift)

/-- Implement compatible widening with one shift of the complete stored word. -/
@[inline] def Internal.widenExact {src dst : FloatFormat} (x : Model src)
    (hexp : src.expWidth = dst.expWidth)
    (_ : src.exponentBias = dst.exponentBias)
    (_ : src.encoding = dst.encoding)
    (hfrac : src.fracWidth ≤ dst.fracWidth) : Model dst :=
  widenBits x hexp hfrac

/--
The compiler uses the whole-word shift in every caller of compatible widening.

This equality covers every bit pattern, and the surrounding cast keeps its NaN and infinity
policy. It is registered before the public casts are compiled.
-/
@[csimp] theorem widenExact_eq_internal : @widenExact = @Internal.widenExact := by
  funext src dst x hexp hbias hencoding hfrac
  exact (widenBits_eq_ofFields x hexp hfrac).symm

/--
Cast `x` from format `src` into format `dst` with nearest-even rounding, the kernel of
`Model.cast src dst x`.

* A finite value decodes to an exact dyadic (`mant × 2^exp`), which `roundDyadic` packs into
  `dst` with round-to-nearest, ties-to-even. Out-of-range magnitudes follow the destination
  encoding's overflow and underflow rules, and a coarser precision can introduce rounding error.
* An infinity gets the destination's native overflow result, as an overflowing finite input does:
  same-sign infinity for IEEE encodings, NaN for finite-with-NaN encodings, and the same-sign
  maximum finite value for fully finite encodings. Saturating conversion is a policy of
  `ExecFloat.Binary.Conversion.Context`.
* A NaN with `src = dst` is quieted and keeps its sign and payload. Otherwise the result is
  `propagatedNaN dst` with the source sign and IEEE payload. The payload survives when it fits the
  destination, and a finite-only destination receives positive zero.
* A finite `x` with `src = dst` comes back unchanged. Decoding to a dyadic and rounding back into
  the same grid is the identity on finite values, so this skips the decode and round work. That
  matters for uniform-format `SitePolicy`s, where `mulAcc` and `dotSequential` cast every operand
  even though storage, product, and accumulator formats agree.
-/
@[inline] def Internal.Nearest.cast (src dst : FloatFormat) (x : Model src) : Model dst :=
  if hnan : isNaN x = true then
    if h : src = dst then
      -- The dependent equality transports the exact-width payload without truncation.
      h ▸ quietNaN x
    else
      propagatedNaN dst (Model.signBit x) (nanPayload x)
  else if hinf : isInf x = true then
    nativeOverflow dst (Model.signBit x)
  else
    have hfinite : isFinite x = true :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
        (Bool.eq_false_of_not_eq_true hnan)
        (Bool.eq_false_of_not_eq_true hinf)
    if h : src = dst then
      h ▸ x
    else if hexp : src.expWidth = dst.expWidth then
      if hbias : src.exponentBias = dst.exponentBias then
        if hencoding : src.encoding = dst.encoding then
          if hfrac : src.fracWidth ≤ dst.fracWidth then
            Model.widenExact x hexp hbias hencoding hfrac
          else
            Model.roundDyadic dst (finiteDyadic x hfinite)
        else
          Model.roundDyadic dst (finiteDyadic x hfinite)
      else
        Model.roundDyadic dst (finiteDyadic x hfinite)
    else
      Model.roundDyadic dst (finiteDyadic x hfinite)

namespace Internal

/--
Cast `x` using any rounding direction, the kernel of `Model.cast src dst x (mode := mode)`.

NaNs and infinities follow the same value-class policy as nearest-even `Nearest.cast`, because a
rounding direction has no numerical effect on them. Finite identity casts and compatible
widenings are exact fast paths here too. Every other finite conversion decodes once to an exact
dyadic and rounds once in the destination format.
-/
@[inline] def Directed.cast (src dst : FloatFormat) (x : Model src)
    (mode : IEEERoundingMode) : Model dst :=
  match mode with
  | .nearest => Nearest.cast src dst x
  | mode =>
      if hnan : isNaN x = true then
        Nearest.cast src dst x
      else if hinf : isInf x = true then
        Nearest.cast src dst x
      else
        have hfinite : isFinite x = true :=
          isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
            (Bool.eq_false_of_not_eq_true hnan)
            (Bool.eq_false_of_not_eq_true hinf)
        if h : src = dst then
          h ▸ x
        else if hexp : src.expWidth = dst.expWidth then
          if hbias : src.exponentBias = dst.exponentBias then
            if hencoding : src.encoding = dst.encoding then
              if hfrac : src.fracWidth ≤ dst.fracWidth then
                Model.widenExact x hexp hbias hencoding hfrac
              else
                Directed.roundDyadic dst mode (finiteDyadic x hfinite)
            else
              Directed.roundDyadic dst mode (finiteDyadic x hfinite)
          else
            Directed.roundDyadic dst mode (finiteDyadic x hfinite)
        else
          Directed.roundDyadic dst mode (finiteDyadic x hfinite)

/--
Cast `x` and also report the IEEE exception indicators and the ternary value of the conversion.
This is the kernel of `Model.cast src dst x (mode := mode) (status := true)`.

A signaling NaN raises invalid, and a quiet NaN raises invalid only when the destination cannot
represent a NaN at all. Infinity is exact when the destination preserves infinity. A destination
without infinity reports overflow and inexactness, even when its overflow encoding is a NaN, and
does not raise invalid. Finite values use one exact dyadic witness for directed rounding, status
classification and the ternary value.

The ternary value of a NaN is `.eq`. An infinity uses `exactInfinityTernary`, which is `.eq` when
the destination keeps it and otherwise `.lt` for `+∞` and `.gt` for `-∞`, whether the destination
saturates or delivers its overflow NaN.
-/
def Status.cast (src dst : FloatFormat) (x : Model src)
    (mode : IEEERoundingMode) : IEEEOutcome dst :=
  let value := Directed.cast src dst x mode
  if hnan : isNaN x = true then
    outcomeWithInvalid value (isSNaN x || !isNaN value)
  else if hinf : isInf x = true then
    let ternary := exactInfinityTernary (Model.signBit x) value
    if isInf value then
      { value, status := .clear, ternary }
    else
      { value, status := { overflow := true, inexact := true }, ternary }
  else
    have hfinite : isFinite x = true :=
      isFinite_eq_true_of_isNaN_eq_false_of_isInf_eq_false x
        (Bool.eq_false_of_not_eq_true hnan)
        (Bool.eq_false_of_not_eq_true hinf)
    let exact := finiteDyadic x hfinite
    Model.dyadicRoundingOutcome dst mode exact value

end Internal

/--
Cast `x` from format `src` into format `dst`, rounding in `mode` (nearest-even by default). With
`status := true` the result is the `IEEEOutcome` carrying the exception flags and the ternary
value.

A finite value decodes to its exact value and rounds once in the destination. An identity cast or
a compatible fraction-field widening returns the value without rounding. A NaN cast to the same
descriptor is quieted with its sign and payload, and across descriptors it follows
`propagatedNaN`. An infinity takes the destination's native overflow result.
-/
@[macro_inline] def cast (src dst : FloatFormat) (x : Model src)
    (mode : IEEERoundingMode := .nearest) (status : Bool := false) :
    match status with
    | true => IEEEOutcome dst
    | false => Model dst :=
  match status with
  | true => Internal.Status.cast src dst x mode
  | false =>
      match mode with
      | .nearest => Internal.Nearest.cast src dst x
      | mode => Internal.Directed.cast src dst x mode

end Model
end FloatLib.Floats.Formats.BinaryInterchange
