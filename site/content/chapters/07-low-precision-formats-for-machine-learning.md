---
number: "07"
slug: low-precision-formats-for-machine-learning
title: Small formats for machine learning
summary: "How FloatLib describes, rounds and proves things about the 16-, 8-, 6- and 4-bit floats of machine learning, from bfloat16 and FP8 to MX blocks and the IEEE P3109 family."
phases: [ml-formats, p3109]
---

Storing neural-network weights in eight bits instead of binary32 cuts the space they occupy by a factor of four. To load those weights, a program also needs to know which eight-bit format produced them. The byte `0x7c` denotes $384$ in OCP's E4M3 and positive infinity in E5M2 [@ocpOfp8]. We can use that one byte to see how a format's exponent, precision and exceptional values affect a computation.

## What does "FP8" mean?

FP8 is short for eight-bit floating point. In E4M3 the sign takes one bit, the exponent four and the fraction three. E5M2 spends one more bit on the exponent and one fewer on the fraction. This extends the range and doubles the spacing between normal values of the same magnitude.

## What is a format family?

These formats share four parts: an exponent width, a fraction width, a bias (subtracted from the stored exponent so that exponents can be negative) and an encoding saying which codes are infinities, NaNs and zeros. FloatLib writes them in one record, a descriptor, of type [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]], with an [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] for the last part. A format family consists of the formats obtained by varying these descriptor parameters.

The encoding also decides which proofs you get. Bfloat16, TF32 and E5M2 use the IEEE encoding and get its real-number theorems for free. Those compare results with exact reals and give the IEEE real error bounds. The others use one of three encodings with fewer exceptional patterns. Each finite code still means one exact number $m \cdot 2^e$ (a whole number times a power of two, called a dyadic), and refinement proofs show that what you run matches its reference definition, the plain version of what it should compute. They don't get those error bounds, as we'll see later.

## What is bfloat16?

Mixed-precision training in binary16, the IEEE 16-bit float, needed loss scaling on some networks so that small gradients, which steer the weight updates, didn't underflow, becoming too small for the format [@micikevicius2018mixed]. Bfloat16 changes the format instead, keeping binary32's eight exponent bits and bias of 127 and cutting the fraction to seven bits. [Google's TPU v2 and v3](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus) chips use it, and Kalamkar and colleagues studied it systematically [@kalamkarBfloat2019]. Near 1.0 the gap between neighbours, the ulp (short for "unit in the last place"), is

$$\operatorname{ulp}_{\text{binary16}}(1) = 2^{-10}, \qquad \operatorname{ulp}_{\text{bfloat16}}(1) = 2^{-7},$$

so bfloat16's spacing is eight times wider, but binary16 stops at 65504 while bfloat16, like binary32, reaches about $3.4 \times 10^{38}$. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] is a plain IEEE descriptor, binary32 with the bottom sixteen fraction bits cut off. Unlike the TPUs, which Google describes as flushing bfloat16 subnormals (the extra-small numbers near zero) to zero, we keep subnormals. Lean checks the shared exponent:

```lean
open FloatLib.Floats.Formats.BinaryInterchange

example : FloatFormat.bfloat16.expWidth = FloatFormat.binary32.expWidth := by decide
example : FloatFormat.bfloat16.exponentBias = FloatFormat.binary32.exponentBias := by decide
example : FloatFormat.bfloat16.bitWidth = 16 := by decide
example : FloatFormat.bfloat16.isIEEE = true := FloatFormat.isIEEE_bfloat16
```

Lean accepts all four.

`roundRat` rounds an exact rational, here `false 1 10` (sign, numerator, denominator) for $+1/10$, once to nearest-even with integer arithmetic alone:

```lean
#eval Model.toNatBits (Model.roundRat FloatFormat.bfloat16 false 1 10)
-- 15821
#eval Model.toDyadic? (Model.roundRat FloatFormat.bfloat16 false 1 10)
-- some { negative := false, significand := 205, exponent := -11 }
#eval Model.toDyadic? (Model.roundRat FloatFormat.binary16 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

The first line is the raw stored word. Bfloat16 gets $205 \cdot 2^{-11} = 0.10009765625$ and binary16, with three more fraction bits, the closer $1638 \cdot 2^{-14} = 0.0999755859375$.

A finite bfloat16 value widens to binary32 exactly:

```lean
example (x : Model FloatFormat.bfloat16) (hx : Model.isFinite x = true) :
    Model.toReal (Model.cast FloatFormat.bfloat16 FloatFormat.binary32 x) =
      Model.toReal x :=
  Model.toReal_cast_bfloat16_binary32 hx
```

Here `hx` says `x` is finite. The theorem is [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_cast_bfloat16_binary32]], an instance of [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_compatibleWidening]] for formats that share their exponent field and encoding. And `bfloat16_add_eq_bf16Round` says that for a finite result, bfloat16 addition is the exact real sum rounded once, by [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] with `decide` proving the IEEE hypothesis.

## What is TF32?

On NVIDIA Ampere tensor cores, TensorFloat-32 (TF32) is a matrix multiplication mode. Its inputs are stored in binary32, the multiplication uses eight exponent bits and ten fraction bits, and the accumulator uses binary32 [@nvidiaTf32]. Our [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.tf32]], `FloatFormat.ieee 8 10`, describes the multiplication's precision, not how hardware stores the operands, and like binary16 it has eleven significant bits, so one tenth rounds the same way:

```lean
example : FloatFormat.tf32 = FloatFormat.ieee 8 10 := rfl
example : FloatFormat.tf32.bitWidth = 19 := by decide

#eval Model.toDyadic? (Model.roundRat FloatFormat.tf32 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

`rfl` confirms the definition, and one tenth rounds as in binary16.

## What are the FP8 formats?

In 2022 NVIDIA's H100 brought hardware for two eight-bit formats [@micikevicius2022fp8], which the Open Compute Project standardized as OFP8 [@ocpOfp8]. E5M2 keeps the IEEE encoding and binary16's exponent range, so [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]] is `FloatFormat.ieee 5 2`. E4M3 has only eighteen binades (a binade runs from one power of two to the next), and an IEEE top exponent for infinity and NaN would cost one of them. In E4M3 ("finite with NaN") the all-ones exponent is ordinary, there's no infinity, and the only NaN has every exponent and fraction bit set, in either sign. The largest finite value is

$$\left(1 + \tfrac{6}{8}\right) \cdot 2^{15 - 7} = 1.75 \cdot 256 = 448,$$

encoded as `0x7e`, with NaN at `0x7f`. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteMaxNaN]] builds a descriptor with the conventional bias and this non-IEEE encoding, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3]] is `finiteMaxNaN 4 3`.

Now we can decode our byte, $0\,1111\,100$ in bits. E5M2 reads exponent $11111_2 = 31$ and fraction $00_2$, which is $+\infty$. E4M3 reads exponent $1111_2 = 15$ and fraction $100_2 = 4$, which is $1.5 \cdot 2^{8} = 384$. `Model.ofNatBits` reads a byte in the format you name:

```lean
#eval Model.isInfinite (Model.ofNatBits (fmt := FloatFormat.e5m2) 0x7c)
-- true
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3) 0x7c)
-- some { negative := false, significand := 12, exponent := 5 }
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3) 0x7e)
-- some { negative := false, significand := 14, exponent := 5 }
#eval Model.isNaN (Model.ofNatBits (fmt := FloatFormat.e4m3) 0x7f)
-- true
```

Lean agrees, and the last two lines show E4M3's 448 and NaN. Try it yourself with other bytes.

### How does a value convert to E4M3?

Converting 464 to E4M3 shows why a format needs more than a bit layout. E4M3's greatest finite value is 448, and yet in the non-saturating mode 464 converts to 448, while the next binary32 value above 464 converts to NaN. Why? Rounding to the precision comes first, and the overflow decision after it. 464 lies exactly halfway between 448 and the next value of the precision grid, 480, and the tie goes to the even one, which is 448. Its binary32 successor rounds to 480, and that is where the overflow rule takes over.

```lean standalone
import FloatLib.Floats.Formats.OCP.FP8.Conversion
import FloatLib.Floats.Formats.OCP.FP8.E4M3

open FloatLib.Floats FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Floats.Formats.OCP.FP8

/-- The stored word of a conversion from a binary32 word, or 256 when the conversion fails. -/
def e4m3Word (overflow : OverflowMode) (bits : Nat) : Nat :=
  match convert FloatFormat.e4m3 overflow (Model.ofNatBits (fmt := FloatFormat.binary32) bits) with
  | .success value _ => Model.toNatBits value
  | .failure _ => 256

-- 464 ties to 448, the code `0x7e`
example : e4m3Word .native 0x43e80000 = 126 := by decide +kernel
-- its binary32 successor overflows: NaN without saturation, 448 with it
example : e4m3Word .native 0x43e80001 = 127 := by decide +kernel
example : e4m3Word .saturate 0x43e80001 = 126 := by decide +kernel
```

OFP8 revision 1.0 defines the two formats and requires nearest-even conversion with two overflow modes. With saturation both formats return the greatest finite value of the sign. Without it, E4M3 overflows to NaN and E5M2 to a signed infinity. `OCP.FP8.convert` takes an exact source decoder and a destination, and its theorems cover the exceptional inputs, connect the finite result to a real rounding grid defined on its own, and say exactly when a non-saturating conversion is finite.

## What are the FNUZ formats?

AMD's accelerators use two formats, E4M3FNUZ and E5M2FNUZ, from the float8 definitions of ONNX, a common file format for trained networks [@onnxFloat8]. UZ stands for "unsigned zero". The would-be negative zero `0x80` is the one NaN, `0x00` the only zero, and there's no infinity. ONNX also raises the bias by one, to 8 and 16, moving the extra binade from the top of the range to the bottom, so E4M3FNUZ tops out at 240 instead of 448, while E5M2FNUZ, whose all-ones exponent row is finite, keeps 57344. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteUnsignedZero]] builds [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2fnuz]]. Here are the biases and the special bytes:

```lean
example : FloatFormat.e4m3.exponentBias = 7 := by decide
example : FloatFormat.e4m3fnuz.exponentBias = 8 := by decide
example : FloatFormat.e5m2fnuz.exponentBias = 16 := by decide

#eval Model.isNaN (Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 0x80)
-- true
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 0x7f)
-- some { negative := false, significand := 15, exponent := 4 }
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e5m2fnuz) 0x7f)
-- some { negative := false, significand := 7, exponent := 13 }
```

You get biases 7, 8 and 16, NaN at `0x80`, and the two maxima at `0x7f`.

IEEE formats and E4M3 flip the sign of zero, but FNUZ negation returns the single zero, as the [finite-format negation proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/FiniteSemantics.lean) specify. Three encoding rules are theorems: [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInfinite_eq_false_of_encoding_ne_ieee]] (no pattern is infinite in a non-IEEE encoding), [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero_eq_true_iff_of_encoding_finiteUnsignedZero]] (an FNUZ value is zero exactly when all its bits are) and `signMask_isNaN_of_encoding_finiteUnsignedZero` (the would-be negative zero is NaN). Here they are in use:

```lean
example (x : Model FloatFormat.e4m3) : Model.isInfinite x = false :=
  Model.isInfinite_eq_false_of_encoding_ne_ieee (by decide) x

example (x : Model FloatFormat.e4m3fnuz) : Model.isZero x = true ↔ x.bits = 0 :=
  Model.isZero_eq_true_iff_of_encoding_finiteUnsignedZero rfl x

example :
    Model.isNaN (Model.ofBits FloatFormat.e4m3fnuz.signMask : Model FloatFormat.e4m3fnuz) =
      true :=
  Model.signMask_isNaN_of_encoding_finiteUnsignedZero rfl
```

In each, `by decide` or `rfl` proves the format has the right encoding.

## What are FP6 and FP4?

The element formats of the OCP Microscaling (MX) specification [@ocpMx], FP6 as E2M3 or E3M2 and FP4 as E2M1, drop infinities and NaNs and keep both zeros. An element is one number in an MX block, which we'll meet later. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m1]], `e2m3` and `e3m2` use the `finite` encoding, and by [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN_eq_false_of_encoding_finite]] and `isFinite_eq_true_of_encoding_finite` every word is finite and none is NaN. FP4's sixteen codes denote

$$0,\ \pm\tfrac{1}{2},\ \pm 1,\ \pm\tfrac{3}{2},\ \pm 2,\ \pm 3,\ \pm 4,\ \pm 6,$$

fifteen distinct numerical values, since the two zeros are equal. Lean can list them, and each format's largest finite value:

```lean
example (x : Model FloatFormat.e2m1) : Model.isNaN x = false :=
  Model.isNaN_eq_false_of_encoding_finite rfl x

#eval (List.range 16).map fun code =>
  (Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e2m1) code)).map
    FloatLib.Numerics.Dyadic.toRat
-- [some 0, some (1 / 2), some 1, some (3 / 2), some 2, some 3, some 4, some 6, some 0, some (-1 / 2), some (-1),
--   some (-3 / 2), some (-2), some (-3), some (-4), some (-6)]

#eval [FloatFormat.e2m1, FloatFormat.e2m3, FloatFormat.e3m2, FloatFormat.e4m3,
    FloatFormat.e4m3fnuz, FloatFormat.e5m2, FloatFormat.e5m2fnuz].map fun fmt =>
  (Model.toDyadic? (Model.maxFinite fmt (negative := false))).map FloatLib.Numerics.Dyadic.toRat
-- [some 6, some (15 / 2), some 28, some 448, some 240, some 57344, some 57344]
```

Codes 8 through 15 are 0 through 7 negated, and the maxima run from 6 in FP4 to 57344. An overflow in FP6 or FP4, a result too large to hold, has only the largest finite magnitude left, so our native rule, `nativeOverflow`, saturates (clamps) there. [Figure 7.1](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-element-values) puts all seven formats on one logarithmic scale.

![Seven rows on one logarithmic axis from 2^-18 to 2^17, one for each format, with a tall mark at each positive normal value and a short mark at each subnormal one. E5M2 and E5M2FNUZ span about 2^-16 to 2^16 with 123 and 127 values, E4M3 and E4M3FNUZ about 2^-9 to 2^9 with 126 and 127, E2M3 and E3M2 a few binades around 1 with 31 each, and E2M1 has 7 values from 1/2 to 6. The count and the least and greatest value are written beside each row](assets/ch13-element-values.png "Every positive finite value of seven low-precision formats on one logarithmic axis. Each row is labelled with the widths of its sign, exponent and fraction fields, the number of its positive finite values, and the least and the greatest of them. Zero, infinities and NaNs are not drawn.")

## What happens when a result doesn't fit?

OFP8 specifies two overflow modes for conversion. In CUDA, `__NV_SATFINITE` clamps a positive E4M3 overflow to 448 and `__NV_NOSAT` returns NaN. Gradual underflow and flushing subnormals to zero are a separate choice. FloatLib's configurable dyadic rounder takes a [[FloatLib.Numerics.QuantizationPolicy]] (quantizing turns an exact value into a code) of three choices, a [[FloatLib.Numerics.RoundingMode]], an `OverflowMode` and an `UnderflowMode`:

| Choice | Options |
| --- | --- |
| Rounding | `nearest` (ties to even), `nearestAway`, `towardZero`, `up`, `down`, `away`, `stochastic` |
| Overflow | native or saturate |
| Underflow | gradual or flush to zero |

If nearest-even rounding carries $x$ past $M_F$, the largest finite magnitude of $F$, then

$$Q_F^{\text{sat}}(x) = M_F, \qquad Q_F^{\text{native}}(x) = \begin{cases} +\infty & F \text{ is IEEE} \\ \text{NaN} & F \text{ is FN or FNUZ} \\ M_F & F \text{ is fully finite,} \end{cases}$$

and within $\pm M_F$ the two agree. A theorem about one isn't about the other, so the policy is an argument to [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]], not a global setting. If you start with 500 and round it in E4M3 under two policies, then in E2M1, you get:

```lean
open FloatLib.Numerics

def exact500 : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 500, exponent := 0 }

#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3 QuantizationPolicy.nearest 0 exact500
-- 127
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3 QuantizationPolicy.saturating 0 exact500
-- 126
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e2m1 QuantizationPolicy.nearest 0 exact500
-- 7
```

Native overflow gives 127, the NaN word, and saturation 126, which is 448, while E2M1 has no NaN and saturates either way, to 6. The `0` is entropy, random input for stochastic rounding, which picks a neighbour at random. It is unbiased per step when the entropy is uniform modulo the denominator of the discarded fraction, but not over a whole quantization with saturation or flush to zero, since those only move results toward zero. Flush to zero sends a result that rounds to a subnormal to the zero of the same sign. Here's the smallest E4M3 subnormal both ways:

```lean
def minE4M3Subnormal : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 1,
    exponent := FloatFormat.e4m3.minSubnormalExponent }

#eval FloatFormat.e4m3.minSubnormalExponent
-- -9
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3 QuantizationPolicy.nearest 0 minE4M3Subnormal
-- 1
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3 QuantizationPolicy.flushToZero 0 minE4M3Subnormal
-- 0

example (fmt : FloatFormat) (entropy : Nat) (value : FloatLib.Numerics.Dyadic) :
    Model.Policy.roundDyadic fmt QuantizationPolicy.nearest entropy value =
      Model.roundDyadic fmt value :=
  Model.Policy.roundDyadic_nearest_eq_execFloat fmt entropy value
```

Nearest keeps code 1, flush to zero gives code 0, and the theorem says the nearest policy is `Model.roundDyadic` whatever the entropy. So the default policy is the canonical [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]] for every descriptor, and its theorems apply. Directed rounding, with native overflow and gradual underflow, runs on a separate engine, and `roundDyadicGeneral_toRoundingMode` proves the two agree on the packed word for every descriptor, all six `IEEERoundingMode` directions, both signs and every exact dyadic.

<a id="using-the-low-precision-types"></a>

## How to compute with the one-byte types

In a program you use the one-byte types in `FloatLib.Floats`, one per named small format, such as `E4M3`, `E5M2`, `E2M1` and `E4M3FNUZ`. They're distinct types, so mixing E5M2 and E5M2FNUZ takes a conversion. At eight bits or fewer, addition, subtraction, multiplication, division and square root are exhaustive lookup tables, like a times table, each a [[FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary]] or its unary cousin with a proof that it equals the reference specification. An FMA (fused multiply-add) table would need 16,777,216 entries, so the FP8 and FNUZ types use the proved generic single-rounding kernel, the general arithmetic code. Here are a few operations on bytes:

```lean
open FloatLib.Floats

#eval E4M3.toUInt8 (E4M3.ofNatBits 0x38 + E4M3.ofNatBits 0x40)
-- 68
#eval E4M3.toUInt8 (E4M3.ofNatBits 0x7e + E4M3.ofNatBits 0x7e)
-- 127
#eval E5M2.toUInt8 (E5M2.ofNatBits 0x7b + E5M2.ofNatBits 0x7b)
-- 124
#eval E4M3FNUZ.toUInt8 (-(E4M3FNUZ.ofNatBits 0x00))
-- 0
#eval E4M3FNUZ.toUInt8 (E4M3FNUZ.ofNatBits 0x7f + E4M3FNUZ.ofNatBits 0x7f)
-- 128

example (x y : E4M3) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

In E4M3, 1 plus 2 is 3 and 448 plus itself is NaN, code 127. E5M2 overflows to infinity, E4M3FNUZ to its NaN, and negating FNUZ zero gives zero, because the format has only one zero encoding. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says the `+` on any static-byte family, the kind behind each one-byte type, equals [[FloatLib.Floats.ExecFloat.Spec.add]], the exact dyadic sum rounded once in the family's descriptor, and matching theorems cover subtraction, multiplication, division, square root and FMA. The [ONNX comparison](#/chapter/external-validation) checks the model's decoding against an independent implementation of the specification, which doesn't settle how hardware converts values or how block arithmetic behaves.

## What is a block with a shared scale?

MX (microscaling) stores a block of narrow elements with one shared scale, like the note "in thousands" at the top of a spreadsheet column. The scale moves the whole block's range and adds no significand precision. It's an E8M0 word, all exponent: code $c$ from 0 through 254 denotes $2^{c - 127}$, and 255 is NaN. [[FloatLib.Floats.Formats.OCP.MX.E8M0]] is its own type, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.exponent?]] and `ofExponent?` translate between codes and exponents. Let's convert a few:

```lean
open FloatLib.Floats.Formats.OCP.MX

#eval E8M0.exponent? (E8M0.ofNatBits 0)
-- some (-127)
#eval E8M0.exponent? (E8M0.ofNatBits 128)
-- some 1
#eval E8M0.exponent? (E8M0.ofNatBits 254)
-- some 127
#eval E8M0.exponent? (E8M0.ofNatBits 255)
-- none
#eval E8M0.ofExponent? 128
-- none
```

Code 255, the NaN, and exponent 128 have no partner, so both give `none`.

### How to decode a block

FloatLib has one block-scaled format, [[FloatLib.Floats.Formats.Block.CodedFormat]], and an MX block is an instance of it: [[FloatLib.Floats.Formats.OCP.MX.Standard.format]] takes the blocks, as a map from positions to block labels, and one of the six element profiles, and gives a storage format with the profile's element codec and one E8M0 scale per block. A stored block is a [[FloatLib.Floats.Formats.Block.Tensor]] of that format: a scale code per block and an element code per position. Applying a scale is exact, since it just multiplies by a power of two. [[FloatLib.Floats.Formats.Block.Tensor.decode]] gives each position its exact value and its class, and `value` the rational value alone. If you start with scale $2^{-2}$, E2M1's nonnegative values become

$$
0,\quad \tfrac18,\quad \tfrac14,\quad \tfrac38,\quad
\tfrac12,\quad \tfrac34,\quad 1,\quad \tfrac32.
$$

Decoding only applies the scale it's given, so changing a stored scale without requantizing, rounding again for the new scale, changes every nonzero value in the block.

### How to take the dot product of two blocks

A dot product multiplies two blocks lane by lane, position by position, and adds the products. Here four E2M1 weights share the scale $2^{-2}$ and four activations, values the network computes, share $2^{1}$. [[FloatLib.Floats.Formats.Block.Tensor.dotExact]] sums in exact rational arithmetic, and [[FloatLib.Floats.Formats.OCP.MX.Dot]] rounds that sum once into the output format you name:

```lean
open FloatLib.Floats.Formats in
/-- Four E2M1 elements in one block. -/
abbrev Block4 := Block.Tensor (Standard.format (fun _ : Fin 4 => ()) .e2m1)

def weights : Block4 where
  scales := (fun _ => E8M0.ofNatBits 125, ())
  elements lane := #v[0x2#4, 0x5#4, 0xb#4, 0x7#4][lane]

def activations : Block4 where
  scales := (fun _ => E8M0.ofNatBits 128, ())
  elements lane := #v[0x4#4, 0x1#4, 0x6#4, 0xa#4][lane]

#eval Array.ofFn weights.value
-- #[1 / 4, 3 / 4, -3 / 8, 3 / 2]
#eval Array.ofFn activations.value
-- #[4, 1, 8, -2]

#eval weights.dotExact activations (List.finRange 4)
-- FloatLib.Numerics.NumericalValue.finite (-17 : Rat)/4
#eval Model.toNatBits
  (FloatLib.Floats.Formats.OCP.MX.Dot .bfloat16 weights activations (List.finRange 4))
-- 49288
#eval Model.toNatBits
  (FloatLib.Floats.Formats.OCP.MX.Dot .e4m3 weights activations (List.finRange 4))
-- 200
#eval ({ weights with scales := (fun _ => E8M0.ofNatBits 255, ()) } : Block4).dotExact activations
  (List.finRange 4)
-- FloatLib.Numerics.NumericalValue.exceptional .nan
```

The exact dot product is $1 + \tfrac34 - 3 - 3 = -\tfrac{17}{4}$, which bfloat16 holds exactly. E4M3 gives $-4$, because its spacing there is $\tfrac12$ and the tie goes to the even neighbour. A NaN scale makes every position of its block NaN, so the last dot is NaN. [Figure 7.2](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-mx-block) draws the computation.

![A flow diagram. Two boxes at the top hold the weights (1, 3, −3/2, 6) times 2^-2, equal to (1/4, 3/4, −3/8, 3/2), with scale code 125, and the activations (2, 1/2, 4, −1) times 2^1, equal to (4, 1, 8, −2), with scale code 128. Arrows lead to the lane products (1, 3/4, −3, −3) and on to the exact sum −17/4, from which two arrows labelled round lead to bfloat16, −17/4, and to E4M3, −4](assets/ch13-mx-block.png "A dot product of two blocks of four E2M1 elements, each block with its own shared E8M0 scale. The lane products and their sum are exact, and each output format rounds that one sum once. bfloat16 holds −17/4 exactly, and E4M3 returns −4 because the sum is a tie that goes to the even neighbour.")

The dot trusted decoding, so that's what the proofs pin down, for every element and scale format at once. [[FloatLib.Floats.Formats.Block.Tensor.decode_finite]] says a finite element under finite scales decodes to the exact product, `decode_of_not_isFinite` that a scale with no finite value makes the position NaN, and `decode_infinity_of_pos` and `decode_exceptional` that an element infinity or NaN survives a positive finite scale. Under a finite scale of any sign the result is the closed product, so a negative scale changes the sign of an infinity and the scale zero makes it NaN (`decode_infinity`). [[FloatLib.Floats.Formats.OCP.MX.Standard.Tensor.decode_finite]] reads the first for an E8M0 exponent, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines]] proves that scaling one dyadic succeeds with the exact product of scale and value. Here's the link between the two views of a position:

```lean
example (block : Block4) (lane : Fin 4) {value : SignedRat}
    (h : block.decode lane = .finite value) : value.value = block.value lane :=
  block.value_of_decode lane h
```

<a id="choosing-a-scale-for-32-lanes"></a>

## How is a block's scale chosen?

The standard has 32 elements per block, in six profiles: E5M2, E4M3 (finite-max-NaN), E3M2, E2M3, E2M1, and INT8, a signed coefficient divided by 64. The storage format doesn't say how a scale is chosen. That is a policy, which the quantizer [[FloatLib.Floats.Formats.Block.CodedFormat.quantize]] takes as an argument, and [[FloatLib.Floats.Formats.OCP.MX.Standard.policy]] is the recommended rule of Section 6.3 of the MX specification: the scale is $2^e$, where $e$ is the binary exponent of the largest absolute input minus the element format's largest power-of-two exponent. Each input is then divided by the scale and rounded to the nearest element, ties to even, saturating by default.

The rule can clip. Take 32 E4M3 lanes all holding $15/8$. Their binade starts at $2^0$ and E4M3's largest power of two is $2^8$, so the scale is $2^{-8}$ and each lane asks to store

$$
\frac{15/8}{2^{-8}}=480.
$$

```lean
open FloatLib.Floats.Formats in
def clipped := (Standard.format (fun _ : Fin 32 => ()) .e4m3).quantize
  (Standard.policy (fun _ : Fin 32 => ()) .e4m3) fun _ => SignedRat.ofRat (15 / 8)

#eval (E8M0.exponent? (clipped.scales.1 ()), clipped.value 0)
-- (some (-8), 7 / 4)
```

E4M3 ends at 448, so saturation reconstructs $448\cdot2^{-8}=7/4$, an error of $1/8$, where $2^{-7}$ would have represented $15/8$ exactly. So our error theorem fixes the scale first. [[FloatLib.Floats.Formats.Block.CodedFormat.value_quantize]] proves the stored values are one rounding of each input in the element format scaled by the selected scale, for every format and policy, and at a finite selected scale [[FloatLib.Floats.Formats.OCP.MX.Standard.abs_value_quantize_sub_le]] proves each saturated lane has the smallest absolute reconstruction error among all finite element words **at that scale**. [[FloatLib.Floats.Formats.Block.mx_scaled_max]] gives the binade of the scaled maximum, and the element proofs give exactness for representable inputs and the even choice on ties.

Beyond that, the choices are ours:

| Situation | What our quantizer does |
| --- | --- |
| All-zero block | Scale one |
| Requested exponent below $-127$ | Clamped |
| Requested exponent above 127 | NaN scale |
| A nonfinite input | Rejected by the conversion; the quantizer takes finite inputs |
| FP8 elements overflow | Saturate by default, or `(overflow := .native)` |
| FP4, FP6 and INT8 elements overflow | Always saturate |

Under a finite scale an infinite or NaN element keeps its class and leaves its neighbours alone, but a NaN scale takes out every lane. Finite scaling is exact rational arithmetic and keeps its meaning beyond binary32's range. These contracts are about the six logical block formats, not how a block sits in memory.

The same general format covers the other block formats of ML accelerators. NVFP4 has E2M1 elements in blocks of 16, an E4M3 scale per block and a binary32 scale per tensor, and its rule maps the largest magnitude of a block to 6, the largest E2M1 value. In the [catalog of block formats](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Catalog.lean) it is [[FloatLib.Floats.Formats.Block.nvfp4]], next to Four Over Six and a fixed-point format with power-of-two scales. The [general theory](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Quantization/Block/Format.lean) proves, for all of them at once, the error of an element, which elements are flushed to zero ([[FloatLib.Floats.Formats.Block.Format.reconstruct_eq_zero_iff_abs_le]]) and when quantizing a matrix and its transpose agree ([[FloatLib.Floats.Formats.Block.Format.reconstruct_relabel]]).

## How do MX dot products round?

The MX specification doesn't fix the precision or the order of a dot product's accumulation, so `OCP.MX.Dot` and `OCP.MX.DotGeneral` make you say which one you want. `Dot` takes two stored tensors over the same positions, each with its own element format and scales, a list of positions, and the output descriptor. With exact intermediates, which is the default, the products and sums are kept exact and the final sum is rounded once to nearest even, the way you'd keep every line of a long bill exact and round only the total. Over $n$ blocks of 32 and binary32:

$$
S=\sum_{j=0}^{n-1}\sum_{i=0}^{31}a_{j,i}b_{j,i},
\qquad
\text{result}=\operatorname{round}_{\mathrm{binary32}}(S).
$$

So at scale $2^{127}$, blocks holding $1,-1,0,\ldots,0$ and $1,1,0,\ldots,0$ give positive zero, even across blocks, where rounding the products $\pm 2^{254}$ to binary32 would give opposite infinities and a NaN sum. When the decoded positions and the final result are finite and the output descriptor is IEEE, [[FloatLib.Floats.Formats.Block.Tensor.abs_toReal_Dot_sub_le]] proves the result is one real rounding of $S$, with absolute error at most half an ulp at $S$, gradual underflow included, and no accumulation term. That bound starts from decoded operands, so it leaves out the error of quantizing real inputs into blocks.

With a finite accumulator, which is what hardware has, each projected product, each addition and the final conversion round. Three products show the difference: $2048$, $1$ and $-2048$.

```lean
section MXDot

open FloatLib.Floats.Formats

/-- The decoded values are 2048, 1 and -2048: E4M3 elements 128, 1/16 and -128 at scale 16. -/
def mxLeft : Block.Tensor (OCP.MX.Standard.format (fun _ : Fin 3 => ()) .e4m3) where
  scales := (fun _ => OCP.MX.E8M0.ofNatBits 131, ())
  elements i := BitVec.ofNat 8 (if i.val = 0 then 0x70 else if i.val = 1 then 0x18 else 0xf0)

/-- Three ones at scale one. -/
def mxRight : Block.Tensor (OCP.MX.Standard.format (fun _ : Fin 3 => ()) .e4m3) where
  scales := (fun _ => OCP.MX.E8M0.ofNatBits 127, ())
  elements _ := BitVec.ofNat 8 0x38

-- exact intermediates keep the unit between the two large opposite products: the result is one
example : (OCP.MX.Dot .binary32 mxLeft mxRight (List.finRange 3)).toNatBits = 0x3f800000 := by
  decide +kernel

-- a binary16 accumulator rounds 2048 + 1 back to 2048, so the result is zero
example : (OCP.MX.Dot .binary32 mxLeft mxRight (List.finRange 3)
    (.binary .binary16 (Block.Extended.round .binary16))).toNatBits = 0 := by
  decide +kernel

-- two blocks give the same zero: the accumulator is carried across the block boundary
example : (OCP.MX.DotGeneral .binary32 mxLeft mxRight [[0, 1], [2]]
    (.binary .binary16 (Block.Extended.round .binary16))).toNatBits = 0 := by
  decide +kernel

end MXDot
```

Above 2048 the spacing of binary16 is two, and the tie goes to the even significand, which is why the unit disappears. For a finite accumulator the error theorem (`Block.Tensor.Dot_nearest_binary_rounding`) bounds the result under the premise that the projected products, every partial sum and the delivered result are finite, and [[FloatLib.Floats.Formats.Block.abs_accumulate_sub_le]] and `abs_accumulateChunked_sub_le` bound ordered accumulation in any accumulator format, with and without promotion to a wider one. `BlockedDot.kernelEntry`, the blocked dot product with its fused multiply-adds rounded in the narrow format and its block partials added in the wide one, is that promotion and has its bound (`abs_kernelEntry_sub_le`). `BlockedDot.kernelEntry_eq_blocks` writes it for every block width as a loop over the full blocks followed by one short last block, which is the form a generated kernel has. The API is value-only, with no NaN payloads or status flags:

| Case | Result |
| --- | --- |
| Exact-zero sum, the empty dot among them | Positive zero |
| Negative sum that underflows | Keeps its sign |
| NaN scale | NaN |
| Zero times infinity, or adding opposite infinities | Invalid |

## Which error bounds hold for which formats?

Here's the promised catch. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] connects executable rounding to the rounded-real grid [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] and carries the hypothesis `fmt.isIEEE = true`, as do the arithmetic theorems built on it. So they don't cover E4M3, FNUZ or the fully finite formats, and our MX results don't carry the IEEE half-ulp bounds of the [Rounding](#/chapter/the-mathematics-of-rounding) chapter over to operations rounded into those element formats. Directed and stochastic policies over non-IEEE scalar formats have executable semantics and an agreement theorem for the IEEE directions, but no real error theorems.

A sequential mixed-precision dot product rounds as it goes. `dotSequential` takes a `SitePolicy` naming the storage, product, accumulator and output formats, so the policy-aware `mulAddFinite?` can accumulate E4M3 products into bfloat16 or binary32. Its error budget, [[FloatLib.Floats.Formats.BinaryInterchange.Model.dotSequential_abs_error_le_budget]], needs IEEE product, accumulator and output formats and a finite value at every step. The standard MX contracts write down our choices, and they don't tell you how an H100 or an MI300 behaves.

Integer inference often uses an affine quantizer instead, where code $k$ means $s(k-z)$ for a scale $s>0$ and zero point $z$ ([Jacob and colleagues' 2018 inference scheme, §2.1](https://openaccess.thecvf.com/content_cvpr_2018/html/Jacob_Quantization_and_Training_CVPR_2018_paper.html)), and the [affine quantization example](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled/what-is-affine-quantization) derives its half-step error bound and shows why clipping breaks it.

## What is IEEE P3109?

Every format so far hands out its zero, infinity and NaN codes its own way. The IEEE P3109 working group does it once, for a family. We follow version 4.1 of the *IEEE Working Group P3109 Interim Report on Arithmetic Formats for Machine Learning*, dated 14 September 2026 [@p3109InterimReport]. It's a working-group draft and hasn't been approved as an IEEE standard, and section numbers below refer to it.

A P3109 format has four knobs: total width $K$, precision $P$ (the number of significant bits), signedness, and domain, finite without infinities or extended with them. A representable value is a *datum*. The required instances are Binary8p4se, Binary8p3se, Binary4p2sf, and Binary8p1uf for block scales, and we implement the whole family and prove its decoding, projection and arithmetic rules. FLoPS formalizes P3109 in Lean too, in a paper [@flopsPaper] and an FMCAD artifact [@flopsArtifact], and [How we test FloatLib](#/chapter/external-validation/how-does-floatlib-relate-to-other-verified-libraries) compares the two developments and their proof coverage.

## How to describe a P3109 format

A [[FloatLib.Floats.Formats.P3109.Format]] holds `bitWidth` $K$, `precision` $P$ (counting the implicit leading bit), a `Signedness`, a `Domain`, and proofs of $K > 2$, $P > 0$, and $P < K$ for signed formats or $P \le K$ for unsigned ones. [[FloatLib.Floats.Formats.P3109.Format.signed]] and `unsigned` prove them with `decide` for literal parameters, and `ofParameters?` checks them at run time. The exponent field has $K - P$ bits when signed or $K - P + 1$ when unsigned, and the bias is $B = 2^{w_e - 1}$ for exponent width $w_e$, one more than the IEEE bias. [[FloatLib.Floats.Formats.P3109.Format.binary8p4se]] is Section 3.2's shorthand for eight bits, precision four, signed, extended, and `binary8p3se` has precision three. Let's look inside, with two formats of our own:

```lean
open FloatLib
open FloatLib.Floats
open FloatLib.Floats.Formats
open FloatLib.Numerics
open FloatLib.Floats.Formats.P3109.Format (binary8p3se binary8p4se)

/-- The same layout with a finite datum set: no infinities. -/
def b8p4sf : P3109.Format := .signed 8 4 .finite

/-- Eight unsigned bits with precision eight: one exponent bit and no sign. -/
def b8p8uf : P3109.Format := .unsigned 8 8 .finite

#eval (binary8p4se.exponentBits, binary8p4se.trailingBits, binary8p4se.exponentBias)
-- (4, 3, 8)

#eval (binary8p4se.minimumNormalExponent, binary8p4se.minimumQuantumExponent)
-- (-7, -10)

#eval (b8p8uf.exponentBits, b8p8uf.trailingBits, b8p8uf.exponentBias)
-- (1, 7, 1)

#eval (P3109.Format.ofParameters? 8 8 .signed .finite).isSome
-- false

#eval (P3109.Format.ofParameters? 8 8 .unsigned .finite).isSome
-- true
```

`binary8p4se` gets bias 8, `b8p8uf` bias 1, and precision eight in eight bits is accepted only unsigned. An unsigned format with $P = K$ has a single exponent bit, while a signed one would have no exponent field, so the checked constructor refuses it.

## Where do zero, NaN and infinity go?

Every P3109 format has one NaN, one zero and, depending on the knobs, two infinities, one, or none. A signed format splits its codes at $2^{K-1}$ into positives below and their negations above, with NaN on the boundary, where negative zero would be, so no format has a negative zero. An unsigned format puts NaN last. An extended domain puts positive infinity just below NaN and, if signed, negative infinity at the top, as [Figure 7.3](#/chapter/low-precision-formats-for-machine-learning/figure-ch15-code-space) shows.

![Four horizontal strips, one for each format, that show every code from 0 on the left to the last code on the right, coloured by class. In b8p4se, code 0 is zero, positive subnormals and normals follow up to 126, plus infinity is 127, NaN is 128, negative values run from 129 to 254 and minus infinity is 255. b8p4sf is the same without the infinities. b8p8uf has zero and positive values up to 254 and NaN at 255. b6p1sf has 64 codes, no subnormals and NaN at 32](assets/ch15-code-space.png "The code space of four P3109 formats, one strip for each format with every code in code order. Ticks mark code 0, the NaN and the last code. The signed formats put NaN on the boundary between positive and negative codes, and the unsigned format puts it last. Only b8p4se has infinities, and b6p1sf, with precision one, has no subnormals.")

Every other code is a finite number. For a positive code with biased exponent field $e$ and trailing field $t$ (the $T = P - 1$ stored fraction bits), `decodePositiveFinite` computes

$$
x = \begin{cases}
t \cdot 2^{\,2 - P - B} & e = 0, \\[4pt]
(2^{T} + t) \cdot 2^{\,e - B + 1 - P} & e \ge 1,
\end{cases}
$$

a subnormal in the first row and a normal number in the second, as in [How floating-point numbers work](#/chapter/from-reals-to-machine-numbers). [[FloatLib.Floats.Formats.P3109.Format.decode]] puts a reserved-code test in front and returns a `NumericalValue Dyadic`: an exact dyadic, a signed infinity, or NaN. Let's decode a few `binary8p4se` codes:

```lean
#eval (binary8p4se.nanBits, binary8p4se.positiveInfinityBits, binary8p4se.negativeInfinityBits)
-- (128, 127, 255)

#eval binary8p4se.decode 0x01
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 1, exponent := -10 }

#eval binary8p4se.decode 0x08
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 8, exponent := -10 }

#eval binary8p4se.decode 0x7e
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 14, exponent := 4 }

#eval binary8p4se.decode 0x7f
-- FloatLib.Numerics.NumericalValue.infinity false

#eval binary8p4se.decode 0x80
-- FloatLib.Numerics.NumericalValue.exceptional .nan

#eval binary8p4se.decode 0x81
-- FloatLib.Numerics.NumericalValue.finite { negative := true, significand := 1, exponent := -10 }

#eval binary8p4se.decode 0xff
-- FloatLib.Numerics.NumericalValue.infinity true
```

`0x01` is the smallest subnormal and `0x08` the smallest normal value. Code 126 is the largest finite value, $14 \cdot 2^4 = 224$, because infinity took code 127. Drop the infinities and code 127 is free for 240:

```lean
#eval (b8p4sf.nanBits, b8p4sf.maxFiniteBits)
-- (128, 127)

#eval b8p4sf.decode 0x7f
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 15, exponent := 4 }

#eval (binary8p4se.maxFinite.toRat, b8p4sf.maxFinite.toRat)
-- (224, 240)
```

NaN stays at 128. With $P = K$ the unsigned format turns into fixed point, evenly spaced codes 0 through 254 on the grid $c / 128$, with NaN at 255:

```lean
#eval (b8p8uf.nanBits, b8p8uf.maxFiniteBits)
-- (255, 254)

#eval b8p8uf.decode 0x7f
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 127, exponent := -7 }

#eval b8p8uf.decode 0x80
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 128, exponent := -7 }

#eval b8p8uf.maxFinite.toRat
-- 127 / 64
```

So `0x80` is exactly one, and the top value is 127/64. We prove these readings for every valid descriptor, with [[FloatLib.Floats.Formats.P3109.Format.decode_nanBits]] for NaN and infinity theorems that assume an extended domain and, for negative infinity, a signed format. By [[FloatLib.Floats.Formats.P3109.Format.decodePositiveFinite_strictMono]] a larger positive finite code has a larger value, at $P = 1$ too, which proves that an in-range value never lands on a reserved code.

## How to convert a number into a P3109 format

Now let's go the other way. Converting an exact number to a code, which the report calls projection, takes three steps in this order: round to precision, apply the saturation rule, encode. [[FloatLib.Floats.Formats.P3109.Format.projectValue]] gives the datum before encoding and `projectCode` the stored code, so we can prove two things: that conversions follow the order, and how big the error can get.

### How to choose a rounding and saturation policy

A [[FloatLib.Floats.Formats.P3109.ProjectionPolicy]] pairs a [[FloatLib.Floats.Formats.P3109.RoundingMode]] with a [[FloatLib.Floats.Formats.P3109.SaturationMode]]. Section 4.7.4 has nine rounding modes, `towardZero`, `up`, `down`, `nearestAway`, `nearest`, `toOdd`, and `stochasticA` through `stochasticC`, which take the report's $N$ random bits as an argument, so they stay pure functions, with no hidden randomness. Section 4.7.5 has three saturation modes: finite, propagate, and none. The report names no default, but Section 4.5 requires its minimum operation specializations, the least an implementation must support, under (NearestTiesToEven, SatNone) [@p3109InterimReport], so that pair is our default policy `{}` and the default of every P3109 operation's `mode` and `saturation` options.

For a nonzero input $x$ (zero stays zero), [[FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision]] first picks the exponent of the quantum, the report's word for the spacing between values,

$$
Q = \max\bigl(\lfloor \log_2 |x| \rfloor,\; 1 - B\bigr) - P + 1,
$$

where the `max` covers subnormals. Let's round 17:

```lean
def seventeen : Numerics.Dyadic := { negative := false, significand := 17, exponent := 0 }

#eval binary8p4se.quantumExponent seventeen
-- 1

#eval binary8p4se.decode (binary8p4se.projectCode {} (.finite seventeen))
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 8, exponent := 1 }

#eval binary8p4se.decode (binary8p4se.projectCode { rounding := .nearestAway } (.finite seventeen))
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 9, exponent := 1 }

#eval binary8p4se.decode (binary8p4se.projectCode { rounding := .toOdd } (.finite seventeen))
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 9, exponent := 1 }
```

The quantum exponent is 1, so the spacing near 17 is 2, and 17 is a tie between 16 and 18. Ties to even picks 16, and ties away and round-to-odd pick 18. At $P = 1$ every nonzero significand is 1, so Section 4.7.4 has nearest-even test the parity of the code, $Q + B$, instead, with zero counted as even. For $P > 1$ this is ordinary significand parity. Here's a tie at $P = 1$:

```lean
def b6p1sf : P3109.Format := .signed 6 1 .finite

/-- Exactly halfway between the codes 1 and 2 of `b6p1sf`, which denote 2^-15 and 2^-14. -/
def tie : Numerics.Dyadic := { negative := false, significand := 3, exponent := -16 }

#eval (b6p1sf.projectCode {} (.finite tie)).toNat
-- 2

#eval (b6p1sf.projectCode { rounding := .toOdd } (.finite tie)).toNat
-- 1

#eval [0, 1, 2, 3].map fun r =>
  (b6p1sf.projectCode { rounding := .stochasticA (.ofNat 2 r) } (.finite tie)).toNat
-- [1, 1, 2, 2]
```

Here $Q + B = -15 + 16$ is odd, like the lower code 1, so nearest-even rounds up to code 2 and round-to-odd keeps 1. Stochastic rounding compares the discarded fraction with the supplied bits, so half of the four two-bit draws round up.

## What happens when a value is too big?

A rounded value between `minFinite` and `maxFinite` passes. Outside that range, the rounding and saturation modes decide together:

| Saturation mode | A finite value that rounds above the largest finite datum | An infinite input |
| --- | --- | --- |
| `none`, the default | Positive infinity in an extended format, NaN in a finite one, but the largest finite value when rounding toward zero or toward negative, as in IEEE 754 | Stays infinite where the format has an infinity, NaN otherwise |
| `finite` | The nearest finite endpoint | The nearest finite endpoint |
| `propagate` | The nearest finite endpoint | Passes through when the format has an infinity, otherwise the nearest finite endpoint |

Let's try 300, past 224:

```lean
def exact300 : Numerics.Dyadic := { negative := false, significand := 300, exponent := 0 }

#eval (binary8p4se.projectCode {} (.finite exact300)).toNat
-- 127

#eval (binary8p4se.projectCode { saturation := .finite } (.finite exact300)).toNat
-- 126

#eval (binary8p4se.projectCode { rounding := .towardZero } (.finite exact300)).toNat
-- 126

#eval (b8p4sf.projectCode {} (.finite exact300)).toNat
-- 128

#eval (b8p4sf.projectCode { saturation := .finite } (.finite exact300)).toNat
-- 127
```

By default it overflows to infinity, code 127, or to NaN in `b8p4sf`. Finite saturation and rounding toward zero stop at the largest finite code.

Rounding comes before the range test, so a value slightly above `maxFinite` can round back down to it, as Section 4.7.3 notes, and the conversion status follows that. In `binary8p4se`, 232 converts to 224 while 233, just one more, becomes infinity:

```lean
def exact232 : Numerics.Dyadic := { negative := false, significand := 232, exponent := 0 }
def exact233 : Numerics.Dyadic := { negative := false, significand := 233, exponent := 0 }

#eval (binary8p4se.projectCode {} (.finite exact232)).toNat
-- 126

#eval (binary8p4se.projectCode {} (.finite exact233)).toNat
-- 127
```

Both have leading exponent 7, so $Q=7-4+1=4$ and the spacing is 16:

| Input | Input in units of $2^4$ | Rounded coefficient | Rounded value | Default projected code |
| --- | --- | --- | --- | --- |
| 232 | $14+\tfrac12$ | 14, even | 224 | `0x7e`, finite |
| 233 | $14+\tfrac9{16}$ | 15 | 240 | `0x7f`, infinity |

Precision isn't the problem for 240. Its fields would spell `0 1111 111`, the infinity code, which is free only in the finite domain. So fitting the precision grid, `FitsPrecisionGrid`, doesn't make a value a finite datum, and the encoder needs an in-range hypothesis. Here's an infinite input to the finite format:

```lean
#eval (b8p4sf.projectCode {} (.infinity false)).toNat
-- 128

#eval (b8p4sf.projectCode { saturation := .propagate } (.infinity false)).toNat
-- 127

#eval (b8p4sf.projectCode { saturation := .finite } (.infinity false)).toNat
-- 127
```

By default it becomes NaN, code 128, and the others give 127, the nearest finite endpoint. Unsigned formats have lower endpoint zero, so a negative input becomes NaN by default, and zero under finite saturation or a directed mode that rounds toward it. Here's -1:

```lean
def minusOne : Numerics.Dyadic := { negative := true, significand := 1, exponent := 0 }

#eval (b8p8uf.projectCode {} (.finite minusOne)).toNat
-- 255

#eval (b8p8uf.projectCode { rounding := .up } (.finite minusOne)).toNat
-- 0

#eval (b8p8uf.projectCode { saturation := .finite } (.finite minusOne)).toNat
-- 0
```

The default gives NaN, code 255, and the others give zero.

<a id="using-the-p3109-apis"></a>

## How to create P3109 values in a program

In a program you use [[FloatLib.Floats.ExecFloat.P3109]], one Lean type per descriptor on the `Codebook` representation of [Fixed point, logarithmic and other formats](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled), and `decode_eq_format_decode` carries the decoding theorems over. `positiveInfinity` and `negativeInfinity` need a proof that the infinity exists, which `decide` supplies for literal descriptors. `ofFiniteFields?` builds a value from a sign, an exponent field and a trailing field and rejects reserved combinations, and `encode?` accepts only an exactly representable datum. Let's try both:

```lean
#eval ExecFloat.P3109.toNatBits (ExecFloat.P3109.nan (format := binary8p4se))
-- 128

#eval (ExecFloat.P3109.ofFiniteFields? (format := binary8p4se) false 15 6).map ExecFloat.P3109.toNatBits
-- some 126

#eval (ExecFloat.P3109.ofFiniteFields? (format := binary8p4se) false 15 7).map ExecFloat.P3109.toNatBits
-- none

#eval (ExecFloat.P3109.ofFiniteFields? (format := b8p8uf) true 0 1).map ExecFloat.P3109.toNatBits
-- none

#eval (binary8p4se.encode? (.finite exact300)).map BitVec.toNat
-- none

#eval (binary8p4se.encode? (.finite { negative := false, significand := 224, exponent := 0 })).map
  BitVec.toNat
-- some 126
```

Fields 15 and 6 give 126, the largest finite code. The pair $(15, 7)$ is the infinity code, and the unsigned format has no negatives, so both requests fail. And `encode?` refuses 300 but takes 224 as code 126.

To round instead, `project` and `ofDyadic` take an exact dyadic and `projectRat` and `ofRat` an exact rational, rounded once with no dyadic approximation first, under `mode` and `saturation`, and `toRat?` reads a value back, with `none` for NaN and the infinities. The conversion API of [FloatLib for absolute beginners](#/chapter/using-the-library) takes the same path, with the saturation mode in `(context := ...)`. Here are 3/16 and one third:

```lean
abbrev B8P4SE := ExecFloat.P3109 binary8p4se

#eval (.ofRat (3 / 16) : B8P4SE).toRat?
-- some (3 / 16)

#eval (.ofRat (1 / 3) : B8P4SE).toRat?
-- some (11 / 32)

#eval (ExecFloat.P3109.ofRat (1 / 3) (mode := .towardZero) : B8P4SE).toRat?
-- some (5 / 16)

#eval ExecFloat.convert (target := B8P4SE) (1 / 3 : Rat) (mode := .towardZero)
-- .success 0.3125 { inexact := true }

#eval ExecFloat.P3109.decode (ExecFloat.P3109.ofRat (format := b8p8uf) (1 / 3))
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 43, exponent := -7 }
```

Here 3/16 comes back unchanged. The quantum near one third is $2^{-5}$, so nearest-even gives $11/32$ and toward zero $5/16$, which `convert` also flags `inexact`.

### What do the status flags mean?

`convert` also returns FloatLib status flags. The P3109 report does not define these flags. They use the same record as the [beginners' chapter](#/chapter/using-the-library):

| Flag | Raised in a P3109 conversion when |
| --- | --- |
| `inexact` | The returned datum differs from the exact input |
| `overflow` | The value rounded in the requested mode lies outside the finite interval, whatever the saturation mode |
| `underflow` | A nonzero input is below the least positive datum in magnitude, narrower than IEEE tininess |
| `saturated` | Saturation moved the rounded result to a finite endpoint |
| `mappedSpecial` | A special input's class changed in projection |
| `invalid` | The source is a signaling NaN, which also gives the single NaN |
| `wrapped` | Never, in a P3109 projection |

Here's 232 again:

```lean
#eval ExecFloat.convert (target := B8P4SE) (232 : Rat)
-- .success 224 { inexact := true }
```

Only `inexact` is raised, because 232 rounds back to 224. The table's conversions are inexact too.

| Exact input | Projection policy | `overflow` | `underflow` | `saturated` |
| --- | --- | --- | --- | --- |
| 300 | default | `true` | `false` | `false` |
| 300 | finite | `true` | `false` | `true` |
| $1/3000$ | default | `false` | `true` | `false` |

## What is proved about P3109 conversions?

We prove that decoding a code and encoding the datum again gives the code back, for every code of every valid descriptor and both encoders. Conversely, a successful checked encoding decodes to the same datum under `SameDatum`, which compares finite values numerically and infinities by sign and treats all NaN payloads as one.

The direct encoder maps every in-range grid value to itself. For projection, rounding in any of the nine modes lands on the grid, even when rounding carries into the next power of two, by [[FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_fitsPrecisionGrid]], and the stored result decodes to the datum that rounding and saturation specify, by [[FloatLib.Floats.Formats.P3109.Format.sameDatum_decode_projectCode]] and its carrier form [[FloatLib.Floats.ExecFloat.P3109.decode_project]]. Rationals get the same, and conversions meet the quantizer contract of the [beginners' chapter](#/chapter/using-the-library) by [[FloatLib.Floats.ExecFloat.P3109.Conversion.implements_run]]. All hold uniformly in $K$, $P$, signedness, domain, and policy. Here are four of them:

```lean
example (format : P3109.Format) (code : BitVec format.bitWidth) :
    format.encode? (format.decode code) = some code :=
  format.encode?_decode code

example (format : P3109.Format) (mode : P3109.RoundingMode) (saturation : P3109.SaturationMode)
    (value : NumericalValue Numerics.Dyadic) :
    P3109.Format.SameDatum
      (ExecFloat.P3109.decode
        (ExecFloat.P3109.project (format := format) value (mode := mode) (saturation := saturation)))
      (format.projectValue { rounding := mode, saturation } value) :=
  ExecFloat.P3109.decode_project value mode saturation

example (format : P3109.Format) (mode : P3109.RoundingMode) (saturation : P3109.SaturationMode)
    (value : NumericalValue Rat) :
    P3109.Format.SameDatum
      (ExecFloat.P3109.decode
        (ExecFloat.P3109.projectRat (format := format) value (mode := mode)
          (saturation := saturation)))
      (format.projectRatValue { rounding := mode, saturation } value) :=
  ExecFloat.P3109.decode_projectRat value mode saturation

example : StrictMono (fun bits => (binary8p4se.decodePositiveFinite bits).toRat) :=
  binary8p4se.decodePositiveFinite_strictMono
```

In order: the round trip, `decode_project` and its rational twin, and the ordering of positive codes.

The [direction and error proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Projection/Direction.lean) say which multiple of $2^Q$ the six deterministic modes of the dyadic kernel pick before saturation. Directed modes never cross the input and stay within one quantum. Nearest modes stay within half a quantum, by [[FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_nearest_abs_sub_le]] and its ties-away twin, with ties going to the larger magnitude or the even code, $P = 1$ included. Round-to-odd stays within one quantum and gives an inexact result an odd significand. Three of them in Lean:

```lean
example (format : P3109.Format) (value : Numerics.Dyadic) :
    |(format.roundFiniteToPrecision .towardZero value).toRat| ≤ |value.toRat| ∧
      |value.toRat| <
        |(format.roundFiniteToPrecision .towardZero value).toRat| +
          (2 : Rat) ^ format.quantumExponent value :=
  format.roundFiniteToPrecision_towardZero value

example (format : P3109.Format) (value : Numerics.Dyadic) :
    |(format.roundFiniteToPrecision .nearest value).toRat - value.toRat| ≤
      (2 : Rat) ^ format.quantumExponent value / 2 :=
  format.roundFiniteToPrecision_nearest_abs_sub_le value

example (format : P3109.Format) (value : Numerics.Dyadic) (hprecision : 1 < format.precision)
    (hinexact : (format.roundFiniteToPrecision .toOdd value).toRat ≠ value.toRat) :
    (format.roundFiniteToPrecision .toOdd value).significand % 2 = 1 :=
  format.roundFiniteToPrecision_toOdd_odd value hprecision hinexact
```

The truncation and nearest-even bounds hold for every valid descriptor and dyadic input, and the parity theorem needs precision above one and an inexact result.

For the stochastic modes, [[FloatLib.Floats.Formats.P3109.Format.roundFiniteToPrecision_report_spec]] proves that the dyadic kernel follows the report's formula for every random word, and we prove that formula for all nine modes on the rational path, code parity and exact ties included. [[FloatLib.Floats.ExecFloat.P3109.Conversion.status_overflow_implies_outside]] proves that a raised overflow flag means the exact input is outside the finite range. Small descriptors, such as $3 \le K \le 10$, can be tested code by code, and our [independent comparison](#/chapter/external-validation) checks the bit layout against the working group's value tables. That tests our reading of the report, while the theorems establish the rounding formulas.

## How does P3109 arithmetic round?

How much you compute before projecting matters. In `binary8p4se` the operands and answer of

$$
16 \cdot 16 - 224 = 32
$$

are all representable. In two steps the default policy overflows 256 to infinity and stays there, while finite saturation clamps it to 224 and ends at zero. `fma` forms $xy+z$ before any rounding or saturation and gets 32 either way, and for finite operands the [arithmetic theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/Proof.lean) `decode_fma_finite` says its output is the same datum as projecting the exact $x y + z$ once.

`ExecFloat.P3109.Add`, `sub`, `mul`, `div` and `fma` take `(target := ...)`, by default the operands' format, plus `mode` and `saturation`. Each forms the exact rational result before projecting, with division's finite quotient rule needing a nonzero denominator. The exceptional cases follow the P3109 model and are proved too: opposite infinities in addition, zero times infinity, and every division by zero give the single NaN, with no IEEE signaling metadata or status flags. `square` provably equals multiplication for every target and policy. A literal such as `(1.5 : B8P4SE)` rounds once by the default policy, and `==` is numerical, so NaN is unequal to itself.

### How do square roots round?

$\sqrt{2}$ isn't rational, but rounding it needs only squares of rational boundaries. In `binary8p4se` the candidates are $11/8$ and $12/8$, with midpoint $23/16$, and

$$
2 = \frac{512}{256} < \left(\frac{23}{16}\right)^2 = \frac{529}{256},
$$

so nearest-even returns $11/8$. The [square-root kernel](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/Sqrt/Runtime.lean) decides this way for `Sqrt`, `RSqrt` and `Hypot`, which forms $x^2+y^2$ exactly first, and rounds before saturating. We prove it agrees with the reference rounder on the exact real square root, through encoding and for all nine modes, and the stochastic tests follow the report's formulas through the exact root's fractional part, with no approximate square root. Negative square-root and nonpositive reciprocal-square-root inputs give NaN. The catch is that exact rational intermediates can get large in formats with a wide exponent range.

## How to mix P3109 formats with other formats

Section 4.5 of the report [@p3109InterimReport] spells out minimum operation specializations over three sets of formats, and we supply them, taking all three formats the report allows for the external set, the formats from outside P3109.

| Set | Formats |
| --- | --- |
| `F4` | Binary4p2sf |
| `F8` | Binary8p4se and Binary8p3se |
| `FX` | binary16, binary32, and BFloat16 |

The [mixed-format API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/P3109/Arithmetic/Mixed) gives each operand its own type and lets a `Destination` argument pick the final projection, for conversions, reciprocals, the basic operations, and fused multiply-add and add-add, under the default policy unless `mode` and `saturation` say otherwise. `Mixed.FAA` keeps all three terms until it knows the destination. With `binary8p4se` inputs 16 and 1 and a binary32 accumulator of $-16$, the exact expression is

$$
(16+1)+(-16)=1.
$$

Rounding the first sum into `binary8p4se` would lose the one, since 17 is our tie and goes to 16, but `Mixed.FAA` sends the exact 1 to binary32, as `faa_eq_project_finite` states, and `fma_eq_project_finite` states the same for the fused product. An external destination keeps its own precision, bias and endpoints, and the [external-destination theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/External/Proof.lean) proves that encoding preserves the rounded and saturated datum's finite value, infinity sign, or prescribed exceptional representation, with no second rounding. Following the report, external negative zero enters as the single zero, zero results are written as positive zero, and NaN diagnostics collapse to the one NaN, written in the canonical quiet encoding. Ordinary binary arithmetic keeps its IEEE signed-zero and NaN rules.

### How do scaled operations work?

Binary8p1uf, the required instance for block scales, goes with `F4` or `F8` elements and an `F8` or external result in the minimum scaled operations. `Mixed.ScaledAdd`, `ScaledSubtract` and `ScaledMultiply` form $sx+ty$, $sx-ty$ and $(sx)(ty)$ exactly and project once, with an implicit result scale of one, as their theorems state. A zero scale times an infinite element is NaN, and a NaN scale propagates over a zero element, so scaling isn't a bit shift.

## How to compare values and find the next one

Comparisons are unordered at NaN, even NaN with itself, so NaN never compares as less, equal or greater. `minimum` propagates NaN, `minimumNumber` can return the other operand and `minimumFinite` prefers a finite operand even over an infinity, and the [extrema proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/Extrema/Proof.lean) cover them and their maximum twins, and the magnitude variants settle equal magnitudes by numerical order. At precision one, with no nonzero subnormals, `maxSubnormalOf` provably returns NaN. `nextGreaterThan` and `nextLessThan` step to a strictly greater or lesser datum, so above 224 in `binary8p4se` comes positive infinity, then NaN, because no greater datum exists. The proofs connect consecutive finite codes to numerical order with no value in between. Every operation in this section has decoding, projection, ordering and classification proofs, but they don't show compliance with every requirement of the interim report.

## How to inspect a P3109 type

`#float_info` shows what a P3109 type means, and `#float_info!` adds its contracts' conditions and special values:

```lean
#float_info B8P4SE
-- Float information: B8P4SE
--   family: P3109 binary floating-point format
--   standard: IEEE P3109 Interim Report v4.1, 14 September 2026 (unapproved draft)
--
-- Format:
--   storage: BitVec 8
--   total bits (K): 8
--   precision (P): 4
--   signed: yes
--   datum set: extended
```

It reports the source specification, width, precision, signedness and datum set.

## Where is each operation of the P3109 report?

P3109 separates the stored format from the policy that projects a result into it. Width $K$, precision $P$, signedness and domain belong to the format, and rounding and saturation belong to the projection. The table maps the report's operations to Lean. Our independent comparisons with formulas from Interim Report v4.1 include 9,818,928 projection cases, 635,040 elementary-function projections and 7,278,336 block cases. [Test methods and counts](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md#the-standards-operations-and-the-complex-functions)

| Section | Operations | In FloatLib |
| --- | --- | --- |
| 4.7 | decoding, projection, rounding to precision, saturation, encoding | `P3109.Format.decode`, `projectCode`, `roundFiniteRatToPrecision`, `saturate` and `encode?` |
| 4.9.1 | `Convert` | `P3109.Arithmetic.Mixed.Convert` |
| 4.10.1 to 4.10.8 | `Abs`, `Negate`, `CopySign`, `Add`, `Subtract`, `Multiply`, `Divide`, `FMA`, `FAA`, `Sqrt`, `Recip`, `RSqrt` | the same names under `ExecFloat.P3109` |
| 4.10.9 to 4.10.16 | `Log`, `Log2`, `LogOnePlus`, `Exp`, `Exp2`, `ExpMinusOne`, the trigonometric and hyperbolic functions with their inverses and their `Pi` forms, `Softplus`, `Hypot`, `ArcTan2`, `ArcTan2Pi` | the same names under `ExecFloat.P3109` |
| 4.11 | `Minimum`, `Maximum` and their `Number`, `Magnitude` and `Finite` forms, `Clamp` | the same names under `ExecFloat.P3109` |
| 4.12, 4.13 | `CompareLess` to `CompareGreaterEqual`, `TotalOrder`, `IsZero` to `IsSubnormal`, `Class` | the same names under `ExecFloat.P3109` |
| 4.14, 4.15 | `BitwidthOf`, `PrecisionOf` and the other format queries, `RoundOf`, `SatOf` | `P3109.Format`, `P3109.ProjectionPolicy` |
| 4.16 | `NextGreaterThan`, `NextLessThan` | the same names under `ExecFloat.P3109` |
| 5.5, 5.6 | `ConvertFromBlock`, `ConvertToBlock`, `ConvertToBlockMaxAbsFinite`, `BlockReduceAdd`, `BlockReduceMultiply`, `BlockDotProduct` | the same names under `P3109.Block` |
| 5.7, 5.8 | the 52 `Block…` operations and the 52 `Scaled…` operations | `P3109.Block`, `P3109.Arithmetic.Mixed` |

```lean
-- operands of two formats and a destination of a third: 1.5 + 2.5 = 4
example :
    (ExecFloat.P3109.Add (1.5 : ExecFloat.P3109 .binary8p4se) (2.5 : ExecFloat.P3109 .binary8p3se)
        (target := P3109.Format.unsigned 16 5 .finite)).toNatBits =
      (4 : ExecFloat.P3109 (P3109.Format.unsigned 16 5 .finite)).toNatBits := by
  float_decide
```

The report stops at the natural and base-two exponentials and logarithms, the trigonometric and hyperbolic functions, `Sqrt`, `RSqrt` and `Hypot`. IEEE 754-2019 recommends more in its clause 9.2, so we add `Exp10`, `Exp2MinusOne`, `Exp10MinusOne`, `Log10`, `Log2OnePlus`, `Log10OnePlus`, `Rootn`, `Cbrt`, `Pown`, `Pow`, `Powr` and `Compound` under `ExecFloat.P3109`, for every format, rounding mode and saturation mode, with the source and target formats you choose. These twelve are FloatLib's own, outside the report. They keep its conventions: one zero, one NaN, and NaN at a pole at zero, as `Recip` gives there. Each compares the exact real function with every rounding threshold of the destination, so nothing is rounded on the way, and we compare them with MPFR enclosures and exact rationals ([test methods](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md#ieee-754-2019-additions)).

Lean's kernel evaluates these operations on the encodings, with no rational number: an arithmetic operation of section 4.10 on operands of any formats, an extremum, the clamp, a comparison, a classification query or a neighbour is one function of natural numbers, and each is proved to store the reference result for every format, rounding mode, random word and saturation mode. On `Binary8p4se` the kernel takes 0.36 to 0.58 ms for an arithmetic operation, a square root, an extremum or the clamp, 0.29 ms for a comparison and 0.13 to 0.19 ms for a query ([`benchmarks/kernel/P3109.lean`](https://github.com/lean-dojo/FloatLib/blob/main/benchmarks/kernel/P3109.lean), Lean v4.36.0). A value of a binary interchange format converts into a P3109 format on its encoding as well (`convertBinary_eq`, for every binary descriptor), in 0.45 ms from binary32. The mixed operations of the report on values of P3109 formats, values of binary interchange formats and rationals, in any combination, are one projection of a class, a sign and a ratio computed from the operands (`mixedAdd_eq` and its siblings), in 0.8 to 1.4 ms. An independent `Fraction` implementation of the same sections agrees on 18,554,428 encodings. Conversions into a binary format, the scaled and the block operations and the elementary functions are evaluated by their definitions.

```lean
example :
    (ExecFloat.P3109.Sqrt (2 : ExecFloat.P3109 .binary8p4se) (mode := .up)).toNatBits =
        (1.5 : ExecFloat.P3109 .binary8p4se).toNatBits ∧
      (ExecFloat.P3109.MaximumNumber (ExecFloat.P3109.nan : ExecFloat.P3109 .binary8p4se)
        (2 : ExecFloat.P3109 .binary8p4se)).toNatBits =
        (2 : ExecFloat.P3109 .binary8p4se).toNatBits ∧
      ExecFloat.P3109.CompareLess (1.5 : ExecFloat.P3109 .binary8p4se)
        (2 : ExecFloat.P3109 .binary8p3se) = true := by
  float_decide
```

How does a P3109 format round? For a nonzero finite input $x$, section 4.7.4 of the report chooses the quantum

$$Q=\max(\lfloor\log_2|x|\rfloor,\,1-B)-P+1,$$

where the maximum is what gives the subnormals a fixed spacing. Dividing $|x|$ by $2^Q$ exposes a fractional part, and the rounding policy compares it with its threshold. At precision three near one, $13/8$ lies halfway between $3/2$ and $7/4$, and nearest-even chooses $3/2$, whose integer significand is even. Saturation is applied to the rounded value, as section 4.7.3 requires. What runs is proved to follow this formula for every admitted format and policy, values outside the stored range included.

One limit to know about the stochastic modes. They are deterministic once their random-bit operand is fixed, and the theorems are about that function of the operand. They don't establish a distribution law, and they don't establish that a caller supplies independent random bits to different lanes of a block.

## How is P3109 different from the OCP formats?

It starts with that one unit of bias. E4M3 has bias 7, NaN at `0x7f` and `0xff`, and negative zero at `0x80`, while `binary8p4se` has bias 8, NaN at `0x80`, and infinities at `0x7f` and `0xff`. E4M3FNUZ makes the signed finite P3109 choices, which `sameByteValues` checks on every code:

```lean
open FloatLib.Floats.Formats.BinaryInterchange

/-- Whether a P3109 descriptor and a binary `FloatFormat` give every eight-bit code the same meaning. -/
def sameByteValues (format : P3109.Format) (fmt : FloatFormat) : Bool :=
  (List.range 256).all fun code =>
    let word : Model fmt := Model.ofNatBits code
    match format.decode (BitVec.ofNat format.bitWidth code), Model.toDyadic? word with
    | .finite d, some m => d.toRat == m.toRat
    | .exceptional _, none => Model.isNaN word
    | _, _ => false

#eval sameByteValues b8p4sf FloatFormat.e4m3fnuz
-- true

#eval sameByteValues (.signed 8 3 .finite) FloatFormat.e5m2fnuz
-- true

#eval sameByteValues binary8p4se FloatFormat.e4m3
-- false

#eval sameByteValues binary8p3se FloatFormat.e5m2
-- false
```

The first two print `true`, so [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] matches the signed finite descriptor with $K = 8$, $P = 4$ on all 256 codes, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2fnuz]] the one with $P = 3$. That's an evaluation, not a theorem, and says only that the value sets coincide, not that arithmetic agrees. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]] aren't P3109 formats under any descriptor. Their bias is one less, E5M2 spends eight codes on infinities and NaNs where P3109 spends three, and both keep a negative zero. Let's end with the bytes we started with:

```lean
#eval (FloatFormat.e4m3.exponentBias, binary8p4se.exponentBias)
-- (7, 8)

#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3) 0x7e)
-- some { negative := false, significand := 14, exponent := 5 }

#eval binary8p4se.decode 0x7e
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 14, exponent := 4 }

#eval Model.isInfinite (Model.ofNatBits (fmt := FloatFormat.e5m2) 0x7c)
-- true

#eval binary8p3se.decode 0x7c
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 4, exponent := 13 }
```

Byte `0x7e` is 448 in E4M3 and 224 in P3109, because of that one unit of bias. And `0x7c`, E5M2's infinity, is $2^{15}$ in the matching P3109 format. `FloatFormat` doesn't admit unsigned formats, $P = 1$ or $P = K$, so P3109 has a decoder of its own. Binary-interchange real-number proofs assume the IEEE reading of the reserved patterns, while P3109 evaluates the closed expression and then applies its policy, even into a binary destination, so a matching value table doesn't make the APIs interchangeable.
