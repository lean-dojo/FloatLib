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

Convert a value from one binary descriptor (`src`) to another (`dst`), for example binary32 to
bfloat16 or binary16 to binary64. Conversion uses the source encoding's exact value, without a
host floating-point intermediate.

## Finite values

Normal numbers, subnormals, and zeros decode to a signed dyadic:

```text
(±)  mant × 2^exp
```

The integer significand and power-of-two scale represent the source value exactly. Binary32
`1.0` decodes to exactly `1`, while binary32 `0.1` decodes to the already rounded binary32 value.
Widening the latter preserves that value, including its difference from the rational `1/10`.

`cast src dst x` rounds once to nearest, with ties to even, in the destination.
`cast src dst x (mode := .up)` rounds in another direction, and `(status := true)` adds the IEEE
exception flags and the ternary value. Identity casts and compatible fraction-field widenings
bypass rounding because they preserve every finite source value exactly.

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

A NaN cast to the same descriptor is quieted while retaining its sign and payload.
Across unequal descriptors, conversion uses `propagatedNaN`, as IEEE 754-2019 §6.2.3 recommends:
an IEEE destination keeps the source sign and the IEEE payload (the fraction without its quiet
bit, read as a natural number) when that payload fits, and otherwise uses the zero payload. A
maximum-NaN destination keeps the sign, an FNUZ destination has its single NaN, and a fully finite
destination receives positive zero. `ExecFloat` conversion applies the same rule.

Infinity follows the destination's overflow policy: same-sign infinity for IEEE encodings,
canonical NaN for finite-with-NaN encodings, and the same-sign maximum finite value for a fully
finite encoding.

Once NaN and infinity have been excluded, finiteness is proved and `finiteDyadic` is total.
With `status := true`, a cast also reports invalid input, overflow, underflow, inexactness, and the
ternary value according to the same conversion result.

The public `cast` is a `@[macro_inline]` selector over three kernels: `Internal.Nearest.cast`
for the default, `Internal.Directed.cast` for the other directions, and `Internal.Status.cast`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/--
Widen a finite value when source and destination have the same exponent semantics.

The exponent field is copied and the source fraction is shifted into the high end of the wider
destination fraction. Equal exponent width, bias, and encoding make this field copy
value-preserving. The hypotheses stay in the signature so callers cannot use this operation as a
narrowing conversion or across an encoding boundary.
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
Cast `x` from format `src` into format `dst`, the nearest-even kernel of `Model.cast src dst x`.

**Finite values:** decode the source bits to an exact dyadic (`mant × 2^exp`), then
pack that value into `dst` with round-to-nearest, ties-to-even (`roundDyadic`).
Out-of-range magnitudes follow the destination encoding's overflow and underflow rules;
coarser precision can introduce rounding error.

**Inf:** the destination's native overflow result, just as for an overflowing finite input:
same-sign infinity for IEEE encodings, NaN for finite-with-NaN encodings, and the same-sign maximum
finite value for fully finite encodings. Saturating conversion is a policy of
`ExecFloat.Binary.Conversion.Context`.

**NaN:** if `src = dst`, quiet the existing encoding while retaining its sign and payload.
Otherwise emit `propagatedNaN dst` with the source sign and IEEE payload: the payload survives when
it fits the destination, and a finite-only destination receives positive zero.

**Finite, `src = dst`:** short-circuits to `x` unchanged. Decoding to a dyadic and rounding back
into the same grid is the identity on finite values, so this skips the decode/round work. This
matters for uniform-format `SitePolicy`s, where `mulAcc` and
`dotSequential` cast every operand even though storage, product, and accumulator formats agree.
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
Cast `x` and report the IEEE exception indicators and the ternary value of the conversion, the
kernel of `Model.cast src dst x (mode := mode) (status := true)`.

A signaling NaN raises invalid. A quiet NaN raises invalid only when the destination cannot
represent a NaN at all. Infinity is exact when the destination preserves infinity. A destination
without infinity reports overflow and inexactness, including when its overflow encoding is a NaN,
and does not raise invalid. Finite values use the same exact dyadic witness for
directed rounding, status classification, and the ternary value.

The ternary value of a NaN is `.eq`. An infinity uses `exactInfinityTernary`: `.eq` when the
destination keeps it, and otherwise `.lt` for `+∞` and `.gt` for `-∞`, whether the destination
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

A finite value decodes exactly and rounds once in the destination. An identity cast or a
compatible fraction-field widening returns the exact value without rounding. A NaN cast to the
same descriptor is quieted with its sign and payload, and across descriptors it follows
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
