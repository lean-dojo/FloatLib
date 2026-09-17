---
number: "09"
slug: low-precision-formats-for-machine-learning
title: Low-precision formats for machine learning
summary: Small formats choose different ranges, precisions, and special values, while shared scales control the range of whole blocks.
phases: [ml-formats]
---

With an eight-bit format, we have 256 codes to divide among finite values, zeros, infinities, and NaNs. Reserving fewer exceptional codes leaves more room for finite numbers. Moving a bit from the exponent to the fraction places those numbers closer together but narrows their range. Bfloat16, TF32, FP8, FP6, and FP4 make different choices about this allocation, even when they retain the familiar sign, biased exponent, and fraction fields.

Field widths alone therefore do not specify a format. FloatLib uses the same [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] descriptor as for binary32, with four fields: the exponent width, the fraction width, the exponent bias, and an [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] that identifies infinities, NaNs, and zeros. Bfloat16, TF32, and E5M2 use the IEEE encoding and inherit its real-number theorems. The other element formats use one of three encodings with fewer exceptional patterns; their exact dyadic semantics and arithmetic refinement proofs do not yet extend to those IEEE real error bounds. E8M0, the shared block scale, has neither a sign nor a fraction and uses a separate type.

## Bfloat16: range and fraction width

Training a network can involve gradient descent on millions or billions of parameters. Gradients estimated from a random mini-batch are noisy to begin with, which gives us a reason to test how much precision training needs. Micikevicius and colleagues showed in 2018 [@micikevicius2018mixed] that networks train in 16 bits with a binary32 master copy of the weights, provided the loss is multiplied by a large constant before backpropagation and divided out afterward. That trick, loss scaling, exists because gradients were underflowing binary16, whose smallest normal value is $2^{-14}$. Loss scaling addressed the limited range without adding fraction bits.

Bfloat16, which Google had already built into its TPUs and Kalamkar and colleagues studied systematically [@kalamkarBfloat2019], keeps binary32's eight exponent bits and bias of 127 and cuts the fraction to seven bits. Both binary16 and bfloat16 spend sixteen bits, and near 1.0 the spacing of representable values is

$$\operatorname{ulp}_{\text{binary16}}(1) = 2^{-10}, \qquad \operatorname{ulp}_{\text{bfloat16}}(1) = 2^{-7},$$

so bfloat16 has eight times the spacing in their shared normal range, but its largest finite value is about $3.4 \times 10^{38}$, essentially binary32's, where binary16 stops at 65504. The exponent field is identical to binary32, so widening a bfloat16 value to binary32 is exact, and narrowing only rounds the fraction, except at the very top of the range where rounding up can carry past the largest bfloat16 value.

Because bfloat16 uses the IEEE encoding, [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] is a plain descriptor and every theorem proved for IEEE descriptors applies without a new proof.

```lean
open FloatLib.Floats.Formats.BinaryInterchange

example : FloatFormat.bfloat16.expWidth = FloatFormat.binary32.expWidth := by decide
example : FloatFormat.bfloat16.exponentBias = FloatFormat.binary32.exponentBias := by decide
example : FloatFormat.bfloat16.bitWidth = 16 := by decide
example : FloatFormat.bfloat16.isIEEE = true := FloatFormat.isIEEE_bfloat16
```

A binary float cannot hold one tenth exactly, because $1/10$ is not a dyadic rational. We'll supply the exact rational to `roundRat` so we can compare the two formats without first rounding the input in another format. The function rounds to nearest, ties to even, using integer arithmetic only.

```lean
#eval Model.toNatBits (Model.roundRat FloatFormat.bfloat16 false 1 10)
-- 15821
#eval Model.toDyadic? (Model.roundRat FloatFormat.bfloat16 false 1 10)
-- some { negative := false, significand := 205, exponent := -11 }
#eval Model.toDyadic? (Model.roundRat FloatFormat.binary16 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

The bfloat16 word is 15821, that is `0x3dcd`, and it denotes $205 \cdot 2^{-11} = 0.10009765625$, about $9.8 \times 10^{-4}$ relative error. Binary16 gets $1638 \cdot 2^{-14} = 0.0999755859375$, about $2.4 \times 10^{-4}$ relative error, because it has three more fraction bits. Neither is "the value 0.1", and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] returns exactly what is stored.

We can use the binary theory directly for two useful bfloat16 results. Widening to binary32 is exact, by [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_cast_bfloat16_binary32]], which applies [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_compatibleWidening]]: equal exponent widths, equal biases, equal encodings, and at least as many fraction bits make a cast exact. For finite operands and a finite result, addition is exact real addition followed by one bfloat16 rounding. The theorem `bfloat16_add_eq_bf16Round` applies [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] with the IEEE hypothesis discharged by `decide`.

```lean
example (x : Model FloatFormat.bfloat16) (hx : Model.isFinite x = true) :
    Model.toReal (Model.cast FloatFormat.bfloat16 FloatFormat.binary32 x) =
      Model.toReal x :=
  Model.toReal_cast_bfloat16_binary32 hx
```

## TF32 multiplication and binary32 accumulation

NVIDIA's tensor cores, starting with Ampere, multiply binary32 inputs in TensorFloat-32 mode using the sign, the eight exponent bits, and ten fraction bits, then accumulate in binary32 [@nvidiaTf32]. The values remain in 32-bit registers; the multiplier uses reduced fraction precision without requiring a separate 19-bit storage format. TF32 therefore has binary32's range with binary16's precision.

[[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.tf32]] is `FloatFormat.ieee 8 10`, nineteen bits wide as a descriptor. It specifies the values used by the policy-aware rounding and multiply-accumulate functions. This describes the multiplication precision; it does not prescribe how hardware stores the binary32 operands.

```lean
example : FloatFormat.tf32 = FloatFormat.ieee 8 10 := rfl
example : FloatFormat.tf32.bitWidth = 19 := by decide

#eval Model.toDyadic? (Model.roundRat FloatFormat.tf32 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

One tenth rounds to the same dyadic as in binary16: eleven significant bits either way, only the range differs.

## FP8: reserving fewer exceptional codes

In 2022 NVIDIA announced the H100 with hardware for two eight-bit formats, and the same year Micikevicius and colleagues at NVIDIA, Arm, and Intel wrote those formats up as FP8 Formats for Deep Learning [@micikevicius2022fp8]; the Open Compute Project then standardized them as OFP8 [@ocpOfp8]. Two FP8 values fit where one binary16 value did. The naming convention gives the field widths: E5M2 has five exponent bits and two fraction bits, E4M3 has four and three, and the sign bit is always present and unnamed.

E5M2 keeps the IEEE exceptional-value encoding. With bias 15 it has exactly binary16's exponent range: an all-ones exponent means infinity when the fraction is zero and NaN otherwise. In our catalog [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]] is `FloatFormat.ieee 5 2`, and like bfloat16 it inherits the IEEE real-number theorems.

Moving one bit from the exponent to the fraction in E4M3 leaves sixteen exponent codes. Reserving one for infinity and NaN would cost a whole binade, one of only eighteen the format ends up with. E4M3FN, where FN stands for "finite with NaN", instead uses the all-ones exponent as an ordinary exponent. It has no infinity, and only the pattern with all exponent bits and all fraction bits set is NaN, for either sign. The largest finite value is therefore

$$\left(1 + \tfrac{6}{8}\right) \cdot 2^{15 - 7} = 1.75 \cdot 256 = 448,$$

encoded as `0x7e`, with `0x7f` immediately above it being NaN. Using two NaN codes, one per sign, instead of sixteen leaves room for the extra binade in a format with 256 codes.

For positive values in that last exponent row, the fraction codes 0 through 6 give 256, 288, 320, 352, 384, 416, and 448. The step is 32 throughout; reclaiming the row extends the range without making these values any closer together. Fraction code 7 would give 480 under the finite decoding formula, but the reserved-code test intercepts it as NaN. The seven negative counterparts account for the other seven reclaimed codes.

The count of eighteen binades includes the subnormals. Fifteen normal leading exponents run from $-6$ through $8$, and subnormals reach three more, $-9$, $-8$, and $-7$. Those bottom binades are sparsely populated: there is only one positive value in the first, two in the second, and four in the third. The element-value figure below shows those short subnormal ticks separately from the normal ones.

This is the first format that needs a non-IEEE encoding, and it is the reason the `Encoding` field exists. The constructor [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteMaxNaN]] builds a descriptor with the conventional bias and the `finiteMaxNaN` encoding, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fn]] is `finiteMaxNaN 4 3`.

Keep the byte fixed while we change its descriptor: the same bits can have different meanings. The byte `0x7c` has bits $0\,1111\,100$. Read as E5M2 the exponent field is $11111_2 = 31$ and the fraction is $00_2$, which is $+\infty$. Read as E4M3FN the exponent field is $1111_2 = 15$ and the fraction is $100_2 = 4$, which is the finite value $1.5 \cdot 2^{8} = 384$.

```lean
#eval Model.isInf (Model.ofNatBits (fmt := FloatFormat.e5m2) 0x7c)
-- true
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3fn) 0x7c)
-- some { negative := false, significand := 12, exponent := 5 }
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3fn) 0x7e)
-- some { negative := false, significand := 14, exponent := 5 }
#eval Model.isNaN (Model.ofNatBits (fmt := FloatFormat.e4m3fn) 0x7f)
-- true
```

The third line reads `0x7e` as E4M3FN and gets $14 \cdot 2^5 = 448$, the maximum we computed above. Every value has type `Model fmt` for a specific descriptor, so it is impossible to ask whether a raw byte is infinite without saying which format it is in. The classifiers [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]], and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]] each begin with a match on `fmt.encoding`.

## FNUZ: one zero, one NaN, and a shifted bias

The ONNX float8 definitions [@onnxFloat8] add two more eight-bit formats, E4M3FNUZ and E5M2FNUZ, which AMD's accelerators use. The UZ stands for "unsigned zero": the code for negative zero becomes the unique NaN. So `0x80`, the sign bit alone, is NaN; `0x00` is the only zero; there is no infinity; and every other pattern is finite.

The ONNX specification also shifts the FNUZ exponent bias up by one. E4M3FNUZ has bias 8 rather than 7, and E5M2FNUZ has bias 16 rather than 15. The effect is to move the extra binade from the top of the range to the bottom. E4M3FNUZ's largest finite value is $1.875 \cdot 2^{7} = 240$ rather than 448, and its smallest normal is $2^{-7}$ rather than $2^{-6}$; E5M2FNUZ keeps E5M2's maximum of 57344 and gains a smallest normal of $2^{-15}$. Our constructor [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteUnsignedZero]] sets `exponentBias := ieeeBias expWidth + 1` for exactly this reason, and the two descriptors [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2fnuz]] are built from it.

```lean
example : FloatFormat.e4m3fn.exponentBias = 7 := by decide
example : FloatFormat.e4m3fnuz.exponentBias = 8 := by decide
example : FloatFormat.e5m2fnuz.exponentBias = 16 := by decide

#eval Model.isNaN (Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 0x80)
-- true
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3fnuz) 0x7f)
-- some { negative := false, significand := 15, exponent := 4 }
#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e5m2fnuz) 0x7f)
-- some { negative := false, significand := 7, exponent := 13 }
```

The word `0x7f`, which is NaN in E4M3FN, is $15 \cdot 2^4 = 240$ in E4M3FNUZ, and $7 \cdot 2^{13} = 57344$ in E5M2FNUZ.

The classifier theorems describe every word of these encodings. [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf_eq_false_of_encoding_ne_ieee]] says that no bit pattern is infinite in any non-IEEE encoding. [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero_eq_true_iff_of_encoding_finiteUnsignedZero]] says that in FNUZ a value is zero exactly when every stored bit is zero, and `signMask_isNaN_of_encoding_finiteUnsignedZero` says that the would-be negative zero is NaN.

```lean
example (x : Model FloatFormat.e4m3fn) : Model.isInf x = false :=
  Model.isInf_eq_false_of_encoding_ne_ieee (by decide) x

example (x : Model FloatFormat.e4m3fnuz) : Model.isZero x = true ↔ x.bits = 0 :=
  Model.isZero_eq_true_iff_of_encoding_finiteUnsignedZero rfl x

example :
    Model.isNaN (Model.ofBits FloatFormat.e4m3fnuz.signMask : Model FloatFormat.e4m3fnuz) =
      true :=
  Model.signMask_isNaN_of_encoding_finiteUnsignedZero rfl
```

Having only one zero changes negation. IEEE and E4M3FN negation flips the sign of zero; FNUZ negation returns its single zero, as the [finite-format negation proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/FiniteSemantics.lean) specify. This rule belongs to the format. The common `ExecFloat` interface of [chapter 14](#/chapter/backends-and-the-planner) also supports IEEE families, where negation still flips the sign of zero.

## FP6 and FP4: fully finite encodings

The OCP Microscaling (MX) specification [@ocpMx] defines the element formats that go inside a scaled block: FP6 in two variants, E2M3 and E3M2, and FP4 as E2M1. These are fully finite. There is no infinity and no NaN; every one of the 64 or 16 codes is a number, and both signs of zero remain. The encoding `finite` describes this, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m1]], `e2m3`, and `e3m2` are `finite 2 1`, `finite 2 3`, and `finite 3 2`. By [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN_eq_false_of_encoding_finite]] and `isFinite_eq_true_of_encoding_finite`, every word of such a format is finite and none is NaN.

FP4 is small enough to write out completely. With bias 1 and one fraction bit, the sixteen codes denote

$$0,\ \pm\tfrac{1}{2},\ \pm 1,\ \pm\tfrac{3}{2},\ \pm 2,\ \pm 3,\ \pm 4,\ \pm 6,$$

fifteen distinct values because both zeros are present. The gap between the two largest values is 2, a third of the larger one. At this precision, rounding can change a substantial fraction of the number. In MX, E2M1 elements share a block scale that adjusts their range to the values being represented.

```lean
example (x : Model FloatFormat.e2m1) : Model.isNaN x = false :=
  Model.isNaN_eq_false_of_encoding_finite rfl x

#eval (List.range 16).map fun code =>
  (Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e2m1) code)).map
    FloatLib.Numerics.Dyadic.toRat
-- [some 0, some (1 / 2), some 1, some (3 / 2), some 2, some 3, some 4, some 6, some 0, some (-1 / 2), some (-1),
--   some (-3 / 2), some (-2), some (-3), some (-4), some (-6)]

#eval [FloatFormat.e2m1, FloatFormat.e2m3, FloatFormat.e3m2, FloatFormat.e4m3fn,
    FloatFormat.e4m3fnuz, FloatFormat.e5m2, FloatFormat.e5m2fnuz].map fun fmt =>
  (Model.toDyadic? (Model.maxFinite fmt false)).map FloatLib.Numerics.Dyadic.toRat
-- [some 6, some (15 / 2), some 28, some 448, some 240, some 57344, some 57344]
```

The second evaluation computes each format's largest finite value from its descriptor rather than copying it from a specification; the two FP6 formats split their five payload bits differently, E2M3 favouring precision and E3M2 range. Compare the seven layouts in [Figure 9.1](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-element-values), drawn to one scale. Beside each layout, all the positive finite values the format can hold are marked on a shared logarithmic axis; the count under each name is the number of those values. E5M2 spreads four values per binade over the widest range, E4M3FN packs eight into each binade over a narrower one, the FNUZ variants move their extra binade from the top of the range to the bottom, and the FP6 and FP4 formats live within a handful of binades on either side of one.

![Every positive finite value of the seven element formats on one logarithmic axis, tall ticks for normals and short ticks for subnormals, beside each format's stored word drawn to scale](assets/ch13-element-values.png "Positive finite values of seven low-precision element formats. The logarithmic axis shows how each format divides its bit budget between range and precision.")

A fully finite format has no infinity or NaN code for an overflow result, so FloatLib's native policy saturates to the largest finite magnitude. The rule, `nativeOverflow`, follows the encoding: signed infinity for `ieee`, the NaN word for `finiteMaxNaN` and `finiteUnsignedZero`, and the largest finite value with the appropriate sign for `finite`.

<a id="encoding-versus-policy"></a>

## Rounding and overflow policies

The encoding says what the stored bits mean. It does not say what an operation should do when its exact result does not fit, and the specifications leave that choice to the implementation. The FP8 paper describes saturating conversion, with a non-saturating mode as an option, and CUDA's conversion intrinsics expose both: `__NV_NOSAT` turns an E4M3 result beyond 448 into the NaN word `0x7f`, and `__NV_SATFINITE` clamps it to 448. Both are E4M3FN; they differ in overflow policy. Similarly, a format may have subnormal patterns while the hardware flushes subnormal results to zero.

The descriptor fixes the encoding; each operation takes a separate [[FloatLib.Numerics.QuantizationPolicy]]. The policy records three independent choices: a [[FloatLib.Numerics.RoundingMode]] (nearest even, nearest away, toward zero, toward positive, toward negative, or stochastic), an `OverflowMode` (native or saturate), and an `UnderflowMode` (gradual or flush to zero). The named policies `nearestEven`, `saturating`, and `flushToZero` cover the common cases. If $M_F$ is the largest finite magnitude of format $F$ and $x$ is large enough that nearest-even rounding carries it past $M_F$, then

$$Q_F^{\text{sat}}(x) = M_F, \qquad Q_F^{\text{native}}(x) = \begin{cases} +\infty & F \text{ is IEEE} \\ \text{NaN} & F \text{ is FN or FNUZ} \\ M_F & F \text{ is fully finite,} \end{cases}$$

and whenever the rounding stays within $\pm M_F$ the two agree. They are different functions, and a theorem about one is not a theorem about the other, so the policy is an explicit argument of [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] rather than a global setting.

In the first two evaluations, we keep the exact input and format fixed and change only the policy:

```lean
open FloatLib.Numerics

def exact500 : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 500, exponent := 0 }

#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.nearestEven 0 exact500
-- 127
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.saturating 0 exact500
-- 126
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e2m1 QuantizationPolicy.nearestEven 0 exact500
-- 7
```

Native E4M3FN overflow gives 127, the NaN word `0x7f`; saturating gives 126, which is `0x7e` or 448; and E2M1, having no NaN, saturates under its native policy to the word 7, which is the value 6. The `0` argument is entropy for stochastic rounding and is ignored by the deterministic modes. Stochastic rounding is unbiased when the entropy is uniform modulo the denominator of the discarded fraction, and that is a statement about one rounding step, not about a whole quantization with saturation or flush to zero, which only ever move a result toward zero.

Flush to zero acts on the rounded result, not on the input: whatever rounds to a subnormal word is replaced by the zero of the same sign. E4M3FN's smallest positive subnormal is $2^{-9}$; under the default policy it is stored as the word `0x01`, and under flush to zero it becomes `0x00`.

```lean
def minE4M3Subnormal : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 1,
    exponent := FloatFormat.e4m3fn.minSubnormalExponent }

#eval FloatFormat.e4m3fn.minSubnormalExponent
-- -9
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.nearestEven 0 minE4M3Subnormal
-- 1
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.flushToZero 0 minE4M3Subnormal
-- 0

example (fmt : FloatFormat) (entropy : Nat) (value : FloatLib.Numerics.Dyadic) :
    Model.Policy.roundDyadic fmt QuantizationPolicy.nearestEven entropy value =
      Model.roundDyadic fmt value :=
  Model.Policy.roundDyadic_nearestEven_eq_execFloat fmt entropy value
```

Under the default policy, `roundDyadic_nearestEven_eq_execFloat` says that policy rounding is exactly the canonical [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]], for every descriptor. Theorems about the canonical rounder therefore apply to this policy too.

The two rounding engines compute that result differently. The policy engine works on exact rationals and takes a `QuantizationPolicy`; the directed rounders shift a dyadic significand and support the four IEEE directions with native overflow and gradual underflow. Neither engine delegates to the other. `roundDyadicGeneral_toRoundingMode_eq_roundDyadicWithRounding` proves that they nevertheless agree on the complete packed word for every descriptor, all four IEEE directions, both signs, and every exact dyadic.

<a id="how-the-executable-types-are-built"></a>

## Executable types and lookup tables

Each named small format has a nominal type with a one-byte carrier: `E4M3FN` and `E5M2` for OFP8, `E2M1`, `E2M3`, and `E3M2` for the MX elements, and `E4M3FNUZ` and `E5M2FNUZ` for the ONNX formats. A value of `ExecFloat E4M3FN` is a `UInt8` with an erased range proof; no descriptor is stored in it. E5M2 and E5M2FNUZ thus occupy the same amount of memory but remain different types, so mixing their encodings requires an explicit conversion.

Each type has a `Family` instance naming its proof-model descriptor, a proof that the width fits in eight bits, and its kernels. At eight bits or fewer, the kernels for addition, subtraction, multiplication, division, and square root are exhaustive tables, each a [[FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary]] or its unary cousin, carrying the model operation it was generated from and a proof that this operation equals the reference specification. For E4M3FN the five tables total roughly 257 KiB.

Fused multiply-add is the exception: a ternary table for an eight-bit format would have 16,777,216 entries, so the FP8 and FNUZ types use the proved generic single-rounding kernel for FMA. E2M1's 4,096-entry FMA table is small enough to keep, and the two FP6 types keep both a 262,144-entry table and the generic kernel, so the planner of [chapter 14](#/chapter/backends-and-the-planner) can pick the table for throughput and the kernel when the lookup footprint matters.

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.OCP.FP8
open FloatLib.Floats.Formats.FiniteOnly

#eval E4M3FN.toUInt8 (E4M3FN.ofNatBits 0x38 + E4M3FN.ofNatBits 0x40)
-- 68
#eval E4M3FN.toUInt8 (E4M3FN.ofNatBits 0x7e + E4M3FN.ofNatBits 0x7e)
-- 127
#eval E5M2.toUInt8 (E5M2.ofNatBits 0x7b + E5M2.ofNatBits 0x7b)
-- 124
#eval E4M3FNUZ.toUInt8 (-(E4M3FNUZ.ofNatBits 0x00))
-- 0
#eval E4M3FNUZ.toUInt8 (E4M3FNUZ.ofNatBits 0x7f + E4M3FNUZ.ofNatBits 0x7f)
-- 128

example (x y : ExecFloat E4M3FN) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

In E4M3FN, `0x38` is 1 and `0x40` is 2, and their sum is 68, the word `0x44`, which is 3. Adding 448 to itself overflows to 127, the NaN word `0x7f`. The same experiment in E5M2 overflows 57344 to 124, which is `0x7c`, positive infinity, because E5M2 kept the IEEE encoding. In E4M3FNUZ negating zero gives zero, and overflow lands on 128, the NaN word `0x80`. The final example is the refinement theorem [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]]: the `+` on any static-byte family equals [[FloatLib.Floats.ExecFloat.Spec.add]], the exact dyadic sum followed by one rounding in the family's descriptor. Corresponding theorems cover subtraction, multiplication, division, square root, and fused multiply-add.

The [ONNX comparison](#/chapter/external-validation) checks the model's decoding rules against an independent implementation of the specification. Decoding agreement alone does not establish hardware conversion or block-arithmetic behavior.

## E8M0 and microscaling blocks

In the MX specification, a block of narrow elements shares one scale. That scale moves the block's range together; each four-bit element describes a value relative to it. This helps when neighbouring values fit within a few binades, but it does not increase E2M1's significand precision. The scale is an E8M0 word: eight bits, all of them exponent, with no sign, no fraction, and no zero. Code $c$, for $c$ from 0 through 254, denotes $2^{c - 127}$, so the scales run from $2^{-127}$ to $2^{127}$, and code 255 is NaN.

With no sign or fraction field, E8M0 is represented separately from the three-field `FloatFormat`. [[FloatLib.Floats.Formats.OCP.MX.E8M0]] is its own type, transparent over `BitVec 8`, with checked decoders [[FloatLib.Floats.Formats.OCP.MX.E8M0.exponent?]] and `toDyadic?` that return `none` for the NaN code, and constructors `ofExponent?`, which refuses exponents outside $[-127, 127]$, and `ofExponentSaturating`, which clamps and says so in its name.

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

Applying a scale is exact. `scaleDyadic?` adds the scale's exponent to an element's dyadic exponent, leaving its sign and significand unchanged. `decodeElement?` decodes and scales one element word; [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeBlock?]] does this for a whole array, failing if the scale or any element is not finite. A [[FloatLib.Floats.Formats.OCP.MX.BlockCode]] stores the scale beside the element words, since both are needed to recover their values. Its `decode?` reads them together.

With scale $2^{-2}=\tfrac14$, E2M1's nonnegative values become

$$
0,\quad \tfrac18,\quad \tfrac14,\quad \tfrac38,\quad
\tfrac12,\quad \tfrac34,\quad 1,\quad \tfrac32.
$$

The largest gap is now $\tfrac12$ instead of 2, but the largest value is also four times smaller. To store a target value we divide it by the scale and quantize the quotient to E2M1. A target of $\tfrac38$ then becomes the exact element value $\tfrac32$, code `0x3`. A target of 2 would require the element value 8, beyond E2M1's maximum of 6, so native finite overflow would clamp its reconstruction to $\tfrac32$.

Changing the scale to $\tfrac12$ lets that target 2 fit exactly, as element value 4. The smaller target $\tfrac38$ now asks for element value $\tfrac34$, halfway between $\tfrac12$ and 1. Nearest-even selects 1, code `0x2`, and reconstruction gives $\tfrac12$, an error of $\tfrac18$. One scale choice preserves the small value; the other accommodates the larger one. Increasing the scale cannot add the missing element code between those neighbours. These are choices made while encoding a block. The decoder only applies the scale it was given, so changing a stored scale without requantizing the elements changes every nonzero represented value.

For a dot product we can check by hand, take four E2M1 weights sharing the scale $2^{-2}$ and four E2M1 activations sharing the scale $2^{1}$. We decode both blocks, multiply corresponding elements, and sum in exact dyadic arithmetic. Only the final sum is rounded into the output format.

```lean
def weights : BlockCode FloatFormat.e2m1 :=
  { scale := E8M0.ofNatBits 125
    values := #[Model.ofNatBits 0x2, Model.ofNatBits 0x5,
                Model.ofNatBits 0xb, Model.ofNatBits 0x7] }

def activations : BlockCode FloatFormat.e2m1 :=
  { scale := E8M0.ofNatBits 128
    values := #[Model.ofNatBits 0x4, Model.ofNatBits 0x1,
                Model.ofNatBits 0x6, Model.ofNatBits 0xa] }

#eval weights.decode?.map (·.map FloatLib.Numerics.Dyadic.toRat)
-- some #[1 / 4, 3 / 4, -3 / 8, 3 / 2]
#eval activations.decode?.map (·.map FloatLib.Numerics.Dyadic.toRat)
-- some #[4, 1, 8, -2]

def exactDot (xs ys : Array FloatLib.Numerics.Dyadic) : FloatLib.Numerics.Dyadic :=
  (Array.zipWith FloatLib.Numerics.Dyadic.mul xs ys).foldl
    FloatLib.Numerics.Dyadic.add FloatLib.Numerics.Dyadic.zero

def blockDot? (a b : BlockCode FloatFormat.e2m1) : Option FloatLib.Numerics.Dyadic := do
  let xs ← a.decode?
  let ys ← b.decode?
  pure (exactDot xs ys)

#eval (blockDot? weights activations).map FloatLib.Numerics.Dyadic.toRat
-- some (-17 / 4)
#eval (blockDot? weights activations).map fun d =>
  Model.toNatBits (Model.roundDyadic FloatFormat.bfloat16 d)
-- some 49288
#eval (blockDot? weights activations).map fun d =>
  Model.toNatBits (Model.roundDyadic FloatFormat.e4m3fn d)
-- some 200
#eval (blockDot? { weights with scale := E8M0.ofNatBits 255 } activations).isSome
-- false
```

The weights decode to $\tfrac14, \tfrac34, -\tfrac38, \tfrac32$ and the activations to $4, 1, 8, -2$, so the exact dot product is $1 + \tfrac34 - 3 - 3 = -\tfrac{17}{4}$. Rounded once into bfloat16 that is the word 49288, `0xc088`, which is exactly $-4.25$. Rounded once into E4M3FN it is 200, `0xc8`, which is $-4$: at that magnitude E4M3FN's spacing is $\tfrac12$, so $-4.25$ is a tie, and ties go to the even neighbour.

For a small experiment, increase the stored weight scale by one code and rerun the two decoders before the dot product. Keep the element codes fixed so we can see exactly what changing the scale does to their values.

Rounding occurs when the elements are first quantized and when the final sum is converted; decoding and the products contribute no error. When the scale is the NaN code the decoder returns `none` rather than a number. In [Figure 9.2](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-mx-block), we can follow each block from its eight-bit scale and four four-bit elements through the values before and after scaling to the two rounded results.

![The chapter's two E2M1 blocks drawn to scale, one E8M0 scale beside four elements, with each element's value before and after scaling, the lane products, the exact sum, and its two roundings](assets/ch13-mx-block.png "Two E2M1 blocks with separate E8M0 scales. Exact lane products are accumulated before the selected destination rounding.")

To prove that decoding preserves a block's values, we need to say which array the block represents. The numerical system interface from [chapter 12](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled) gives us that statement: `blockSystem` assigns an exact dyadic array to a block that decodes successfully, and a NaN exception otherwise. `blockSystem_represents_iff` says that a block represents an array exactly when its decoder returns that array.

The theorems [[FloatLib.Floats.Formats.OCP.MX.BlockCode.decode_refines]], [[FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines]], and [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines]] prove that, whenever the inputs represent values, decoding succeeds and returns the specified result: the array itself for the block decoder, and an exponent shift for the two scaling functions. [[FloatLib.Floats.Formats.OCP.MX.E8M0.toDyadic?_significand_eq_one]] and `toDyadic?_negative_eq_false` also establish that every decoded scale is a positive power of two.

```lean
example (block : BlockCode FloatFormat.e2m1) (values : Array FloatLib.Numerics.Dyadic) :
    (blockSystem FloatFormat.e2m1).Represents block values ↔ block.decode? = some values :=
  blockSystem_represents_iff block values
```

Programs can use the configured `E8M0` and `Block` wrappers through the common executable interface. `ofElements` builds a block from an array of nominal `ExecFloat E2M1` values. There is a second, more general block family, [[FloatLib.Floats.Formats.Block.SharedScaleCode]], with an unbounded integer exponent and integer significands; [chapter 12](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled) covers it.

<a id="choosing-a-scale-for-32-lanes"></a>

## Choosing a scale for 32 elements

The four-element example above uses `MX.BlockCode`, whose array can have any length. The [standard MX implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/OCP/MX/Standard) provides the standard MX block: an E8M0 scale and a `Vector` of exactly 32 elements. Its six profiles are E5M2, E4M3, E3M2, E2M3, E2M1, and INT8. Here E4M3 uses the finite-max-NaN encoding, and INT8 means a signed two's-complement coefficient divided by 64, with values from $-2$ to $127/64$.

We'll keep the two quantization decisions separate: first choose a shared scale, then round every lane at that scale. The [quantizer](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/Runtime.lean) implements the recommended rule from Section 6.3 of the MX specification: find the largest absolute input, take its binary exponent, and subtract the element format's largest power-of-two exponent. If that gives $e$, the scale is $2^e$. Each input is divided by this scale and rounded to the nearest element, with ties to an even low bit and finite saturation by default.

The scale rule can clip a value even when another scale could represent it exactly. Consider 32 E4M3 lanes all holding $15/8$. The input lies in the binade starting at $2^0$, and E4M3's largest power of two is $2^8$, so the rule chooses $2^{-8}$. A lane then asks to store

$$
\frac{15/8}{2^{-8}}=480.
$$

E4M3 ends at 448, so saturation reconstructs $448\cdot2^{-8}=7/4$, an error of $1/8$. Choosing $2^{-7}$ instead would ask for element value 240 and reconstruct $15/8$ exactly. The recommended scale rule does not search all possible scales for the best reconstruction.

The error theorem fixes the scale before comparing possible element words. `quantizeFinite_quantizes` proves the block follows the selected scale and element policy. At a finite selected scale, `quantizeFinite_error_le` proves that each saturated lane minimizes absolute reconstruction error among all finite element words **at that scale**. Thus $7/4$ is the best available result with scale $2^{-8}$, even though it is not the best result across all E8M0 scales. The [scale-selection proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/ScaleProof.lean) establish the binade and scale bounds; the element proofs also establish exactness when the scaled input is representable and the even choice on ties.

The implementation chooses scale one for an all-zero block, clamps a requested exponent below $-127$, and returns a NaN block if it exceeds 127 or any input lane is nonfinite. These choices cover cases where the scale-selection recommendation leaves room for policy. FP8 also exposes the specification's overflow mode alongside saturation; FP4, FP6, and INT8 always saturate.

Decoding an existing standard block preserves each lane's exceptional class. With a finite scale, an infinity or NaN in one element does not erase finite neighbours; a NaN scale affects every lane. Finite scaling uses exact rational arithmetic, so it remains meaningful beyond binary32's range. These quantization and decoding contracts describe the six logical block formats, without prescribing a physical memory layout.

<a id="a-dot-product-rounds-after-the-last-block"></a>

## MX dot products with one final rounding

The standard MX operations `dot` and `dotGeneral` turn those decoded lanes into a binary32 result. The two operands may use different element profiles, covering all 36 pairs of the six profiles. `dot` takes one 32-lane block from each operand; `dotGeneral` takes equally many blocks on each side, with each operand keeping its own profile and each block its own scale.

The MX specification leaves internal accumulation precision and operation order to the implementation. FloatLib chooses exact rational products and sums, followed by one nearest-even binary32 rounding. For decoded lanes $a_{j,i}$ and $b_{j,i}$, it computes

$$
S=\sum_{j=0}^{n-1}\sum_{i=0}^{31}a_{j,i}b_{j,i},
\qquad
\text{result}=\operatorname{round}_{\mathrm{binary32}}(S).
$$

No product or partial block sum is rounded. To see why this matters, take an E2M1 block with scale $2^{127}$ and element values $1,-1,0,\ldots,0$, paired with a block at the same scale holding $1,1,0,\ldots,0$. The first two products are $2^{254}$ and $-2^{254}$. Rounding each product to binary32 would give opposite infinities, whose sum is NaN. Exact accumulation cancels them and returns positive zero. Splitting cancelling terms across blocks gives the same result because `dotGeneral` also postpones rounding past the block boundary.

The [dot-product proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/DotProduct/Proof.lean) establish the shared-scale formula in `dotExact_eq_scaled_sum` and the multi-block exact sum in `dotGeneralExact_finite`. When the decoded lanes and final binary32 result are finite, `toReal_dotGeneral_eq_roundAt` identifies the packed result with one real rounding of $S$. The theorem `abs_toReal_dotGeneral_sub_le` then gives an absolute error of at most half an ulp at $S$, including gradual underflow. There is no accumulation-error term. This bound starts with the decoded operands; it does not include error from quantizing earlier real-valued inputs into MX blocks.

The [configured dot-product proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/Configured/DotProduct/Proof.lean) carries the same result to `ExecFloat.OCP.MX.Standard.dotGeneral`: packing into the executable binary32 carrier adds no further rounding. Exact-zero sums, including an empty dot, return positive zero; a negative nonzero sum that underflows keeps its negative sign. NaN scales propagate NaN, and zero times infinity or addition of opposite infinities is invalid. This value-only API does not return NaN payloads or status flags.

<a id="where-the-proofs-stop"></a>

## Conditions on the error bounds

The scalar arithmetic has exact dyadic semantics, while its real-number error theorems have a narrower scope. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]], which connects executable rounding to the rounded-real grid [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]], carries the hypothesis `fmt.isIEEE = true`, and so do the arithmetic theorems built on it. They therefore cover bfloat16, TF32, and E5M2, and not E4M3FN, the FNUZ formats, or the fully finite element formats. The MX results above bound quantization at a selected scale and the single binary32 rounding of an exact dot. They do not extend the IEEE half-ulp arithmetic bounds of [chapter 07](#/chapter/the-mathematics-of-rounding) to operations rounded into those element formats.

A sequential mixed-precision dot product rounds intermediate results too. `dotSequential` takes a `SitePolicy` naming the storage, product, accumulator, and output formats. The policy-aware `mulAddFinite?` can execute, for example, an E4M3FN times E4M3FN product accumulated into bfloat16 or binary32. Both run on any descriptor. The error budget theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.dotSequential_abs_error_le_budget]] requires all four formats to be IEEE and every intermediate to be finite. Those intermediate rounding steps are absent from the exact MX dot.

Directed and stochastic policies over the non-IEEE scalar formats have executable semantics and an agreement theorem for the IEEE directions, but no real error theorems. The standard MX quantizer uses nearest-even rounding with its explicit scale and overflow policies. Its contracts describe FloatLib's choices of scale and accumulation precision; they do not establish the behavior of an H100 or MI300.

<a id="finding-the-low-precision-implementations"></a>

## Affine integer quantization

An integer quantizer stores a code $k$ and reconstructs the value $s(k-z)$, where $s>0$ is a scale and $z$ is the zero point. To encode $x$, it rounds $x/s$ to an integer, adds $z$, and clips the result to the storage interval. FloatLib's executable `AffineQuantizer` uses exact rational inputs and scales, so a host floating-point conversion does not change a tie before the integer rounder sees it.

```lean standalone
import FloatLib

open FloatLib.Numerics.Quantization
open FloatLib.Floats.Formats.Flocq

def quarterGrid : AffineQuantizer where
  scale := 1 / 4
  zeroPoint := 0
  qmin := -128
  qmax := 127
  scale_pos := by norm_num
  codeRange := by norm_num

#eval quarterGrid.quantize (3 / 8)
-- 2
#eval quarterGrid.quantize (-3 / 8)
-- -2
#eval quarterGrid.quantize 100
-- 127

example (x : ℚ) :
    quarterGrid.toReal.quantize nearestEven (x : ℝ) = quarterGrid.quantize x :=
  affine_toReal_quantize quarterGrid x
```

The first two inputs lie halfway between grid points; nearest-even selects codes $2$ and $-2$. The third input exceeds the code range and is clipped. The final theorem connects the whole executable operation, including clipping, to its real-valued specification.

[[FloatLib.Numerics.Quantization.RealAffineQuantizer]] also accepts irrational scales and inputs, and takes its integer rounding function as an argument. Its order theorem needs a monotone rounder; its code round-trip theorem needs a rounder that fixes integers. With a nearest rounder, reconstruction differs from the input by at most $s/2$ when clipping is inactive. This last condition matters: a clipped input can be arbitrarily far from the largest reconstructed value. [[FloatLib.Floats.Formats.Flocq.affine_toReal_quantize]] proves that the rational implementation and real nearest-even specification agree for every rational input.

## Using the low-precision types

Use the named FP8, FP6, and FP4 types for individual values. For a block, [[FloatLib.Floats.Formats.OCP.MX.E8M0]] supplies the shared scale, and the [standard block implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/OCP/MX/Standard) provides the six 32-element formats. Its quantizer follows the [scale rule above](#/chapter/low-precision-formats-for-machine-learning/choosing-a-scale-for-32-lanes); the minimum-error theorem compares element choices at that selected scale.

To multiply and sum blocks, use the configured `dot` and `dotGeneral` operations. The [dot-product example](#/chapter/low-precision-formats-for-machine-learning/a-dot-product-rounds-after-the-last-block) shows why postponing rounding can preserve a cancellation that binary32 products would lose.
