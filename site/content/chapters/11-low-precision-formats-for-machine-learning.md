---
number: "11"
slug: low-precision-formats-for-machine-learning
title: Low-precision formats for machine learning
summary: Small formats choose different ranges, precisions, and special values, while shared scales control the range of whole blocks.
phases: [ml-formats]
---

With an eight-bit format, we have 256 codes to divide among finite values, zeros, infinities and NaNs. Reserving fewer exceptional codes leaves more room for finite numbers. Moving a bit from the exponent to the fraction places those numbers closer together but narrows their range. Even the same byte can mean different things: `0x7c` is positive infinity in E5M2 and the finite value 384 in E4M3FN, because the two formats split their fields and reserve their exceptional patterns differently.

FloatLib describes these formats with the same [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] descriptor it uses for binary32. The descriptor has four data fields: the exponent width, the fraction width, the exponent bias, and an [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] that says which patterns are infinities, NaNs and zeros. Bfloat16, TF32 and E5M2 use the IEEE encoding, so they inherit its real-number theorems. Every other element format uses one of three encodings with fewer exceptional patterns. For those we have exact dyadic semantics and arithmetic refinement proofs, but the proofs don't yet extend to the IEEE real error bounds. The odd one out is E8M0, the shared block scale, which has neither a sign nor a fraction, so it gets a type of its own.

## Bfloat16: range and fraction width

In 2018 Micikevicius and colleagues showed mixed-precision training working across several network families [@micikevicius2018mixed]. Storage and arithmetic were in binary16, while accumulation and the master weights stayed in binary32. Some networks also needed loss scaling, which multiplies the loss before backpropagation and unscales the computed gradients before the weight update. That step protected small gradients from underflow in binary16, whose smallest normal value is $2^{-14}$, and it did so without adding any fraction bits. [Google's TPU v2 and v3](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus) use bfloat16, and Kalamkar and colleagues studied it systematically [@kalamkarBfloat2019]. The format keeps binary32's eight exponent bits and its bias of 127 and cuts the fraction to seven bits. Binary16 and bfloat16 both spend sixteen bits, so let's compare them near 1.0, where the spacing of representable values is

$$\operatorname{ulp}_{\text{binary16}}(1) = 2^{-10}, \qquad \operatorname{ulp}_{\text{bfloat16}}(1) = 2^{-7},$$

so in their shared normal range bfloat16's spacing is eight times wider, but binary16 stops at 65504. Bfloat16 and binary32 share the normal exponent range $-126$ through $127$. Their largest finite values differ, since bfloat16 ends at $(2-2^{-7})2^{127}$ and binary32 at $(2-2^{-23})2^{127}$, though both are about $3.4 \times 10^{38}$. The nice thing is that every finite bfloat16 value widens to binary32 with no rounding at all. Going the other way rounds the fraction, and at the top of the range rounding up can carry past the largest finite bfloat16 value. Bfloat16 uses the IEEE field encoding, so [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.bfloat16]] is a plain descriptor, and every theorem proved for IEEE descriptors applies to it with no new proof. One thing differs from the TPUs, though. FloatLib keeps subnormals in this descriptor, while Google describes the TPUs as flushing bfloat16 subnormals to zero.

```lean
open FloatLib.Floats.Formats.BinaryInterchange

example : FloatFormat.bfloat16.expWidth = FloatFormat.binary32.expWidth := by decide
example : FloatFormat.bfloat16.exponentBias = FloatFormat.binary32.exponentBias := by decide
example : FloatFormat.bfloat16.bitWidth = 16 := by decide
example : FloatFormat.bfloat16.isIEEE = true := FloatFormat.isIEEE_bfloat16
```

Neither format can hold one tenth, because $1/10$ is not a dyadic rational. We give `roundRat` the exact rational, so neither format sees an input that was first rounded in some other format, and it rounds to nearest, ties to even, with nothing but integer arithmetic.

```lean
#eval Model.toNatBits (Model.roundRat FloatFormat.bfloat16 false 1 10)
-- 15821
#eval Model.toDyadic? (Model.roundRat FloatFormat.bfloat16 false 1 10)
-- some { negative := false, significand := 205, exponent := -11 }
#eval Model.toDyadic? (Model.roundRat FloatFormat.binary16 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

The bfloat16 word is 15821, or `0x3dcd`, and it denotes $205 \cdot 2^{-11} = 0.10009765625$, a relative error of about $9.8 \times 10^{-4}$. Binary16 has three more fraction bits and gets $1638 \cdot 2^{-14} = 0.0999755859375$, about $2.4 \times 10^{-4}$ relative error. Neither equals the rational $1/10$. We print them with [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] because it returns what is actually stored. Exact widening and correctly rounded bfloat16 addition both come straight from the general binary theorems. Widening to binary32 is exact by [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_cast_bfloat16_binary32]], which applies [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_exact_of_compatibleWidening]], and that theorem says a cast is exact when the exponent widths, the biases and the encodings are equal and there are at least as many fraction bits. For finite operands and a finite result, addition is exact real addition followed by one bfloat16 rounding. `bfloat16_add_eq_bf16Round` gets that from [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]], and `decide` discharges the IEEE hypothesis.

```lean
example (x : Model FloatFormat.bfloat16) (hx : Model.isFinite x = true) :
    Model.toReal (Model.cast FloatFormat.bfloat16 FloatFormat.binary32 x) =
      Model.toReal x :=
  Model.toReal_cast_bfloat16_binary32 hx
```

## TF32 multiplication and binary32 accumulation

Starting with Ampere, NVIDIA's tensor cores have a TensorFloat-32 mode. They multiply binary32 inputs using the sign, the eight exponent bits and ten fraction bits, then accumulate in binary32 [@nvidiaTf32]. Values stay in 32-bit registers and the multiplier works at the reduced fraction precision, so nothing needs a separate 19-bit storage format. That gives TF32 binary32's normal exponent range with binary16's significand precision. Our [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.tf32]] is `FloatFormat.ieee 8 10`, nineteen bits wide as a descriptor, and it gives the values that the policy-aware rounding and multiply-accumulate functions use. It describes the precision of the multiplication and says nothing about how hardware stores the binary32 operands.

```lean
example : FloatFormat.tf32 = FloatFormat.ieee 8 10 := rfl
example : FloatFormat.tf32.bitWidth = 19 := by decide

#eval Model.toDyadic? (Model.roundRat FloatFormat.tf32 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

So one tenth rounds to the same dyadic as in binary16. That makes sense, because both have eleven significant bits and only the range differs.

## FP8: reserving fewer exceptional codes

In 2022 NVIDIA announced the H100 with hardware for two eight-bit formats. That same year Micikevicius and colleagues at NVIDIA, Arm and Intel wrote those formats up as FP8 Formats for Deep Learning [@micikevicius2022fp8], and the Open Compute Project then standardized them as OFP8 [@ocpOfp8]. Two FP8 values fit where one binary16 value did. The names give the field widths. E5M2 has five exponent bits and two fraction bits, E4M3 has four and three, and the sign bit is always there and never named. E5M2 keeps the IEEE exceptional-value encoding, and with bias 15 it has the same exponent range as binary16. An all-ones exponent means infinity when the fraction is zero and NaN otherwise. In our catalog [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]] is `FloatFormat.ieee 5 2`, and like bfloat16 it inherits the IEEE real-number theorems. E4M3 moves one bit from the exponent to the fraction, which leaves sixteen exponent codes. Reserving one of them for infinity and NaN would cost a whole binade, and the format only ends up with eighteen. So E4M3FN, where FN stands for "finite with NaN", uses the all-ones exponent as an ordinary exponent. There is no infinity, and the only NaN is the pattern with every exponent bit and every fraction bit set, in either sign. That makes the largest finite value

$$\left(1 + \tfrac{6}{8}\right) \cdot 2^{15 - 7} = 1.75 \cdot 256 = 448,$$

encoded as `0x7e`, and the code right above it, `0x7f`, is NaN. Spending two NaN codes, one per sign, instead of sixteen leaves room for the extra binade in a format with 256 codes. For positive values in that last exponent row, fraction codes 0 through 6 give 256, 288, 320, 352, 384, 416, and 448, a step of 32 all the way, so reclaiming the row extends the range but doesn't put these values any closer together. Fraction code 7 would give 480 under the finite decoding formula, but the reserved-code test catches it first as NaN. Seven negative counterparts make up the other seven reclaimed codes. Those eighteen binades include the subnormals. Fifteen normal leading exponents run from $-6$ through $8$, and the subnormals reach three more, $-9$, $-8$ and $-7$. Down at the bottom the binades are thinly populated, with only one positive value in the first, two in the second and four in the third. In the element-value figure below they show up as short subnormal ticks, drawn apart from the normal ones.

E4M3FN is the first format that needs a non-IEEE encoding, and it's the reason the `Encoding` field exists. The constructor [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteMaxNaN]] builds a descriptor with the conventional bias and the `finiteMaxNaN` encoding, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fn]] is `finiteMaxNaN 4 3`. With both descriptors in hand, let's go back to the byte `0x7c` from the first paragraph and split its bits $0\,1111\,100$ at the two field boundaries. Read as E5M2, its exponent field is $11111_2 = 31$ and its fraction is $00_2$, so it's $+\infty$. Read as E4M3FN, the exponent field is $1111_2 = 15$ and the fraction is $100_2 = 4$, which makes it the finite value $1.5 \cdot 2^{8} = 384$.

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

The third line reads `0x7e` as E4M3FN and gets $14 \cdot 2^5 = 448$, the maximum we computed above. Every value has type `Model fmt` for a specific descriptor, so you can't even ask whether a raw byte is infinite without saying which format it's in. Each of the classifiers [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf]], [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isFinite]] starts with a match on `fmt.encoding`.

## FNUZ: one zero, one NaN, and a shifted bias

The ONNX float8 definitions [@onnxFloat8] add two more eight-bit formats, E4M3FNUZ and E5M2FNUZ, which AMD's accelerators use. UZ stands for "unsigned zero", because the code for negative zero becomes the one NaN. So `0x80`, the sign bit alone, is NaN, `0x00` is the only zero, there's no infinity, and every other pattern is finite. ONNX also shifts the FNUZ exponent bias up by one, so E4M3FNUZ has bias 8 where E4M3FN has 7, and E5M2FNUZ has bias 16 where E5M2 has 15. That moves the extra binade from the top of the range to the bottom. E4M3FNUZ's largest finite value is $1.875 \cdot 2^{7} = 240$, down from 448, and its smallest normal is $2^{-7}$, down from $2^{-6}$, while E5M2FNUZ keeps E5M2's maximum of 57344 and gains a smallest normal of $2^{-15}$. That's why our constructor [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteUnsignedZero]] sets `exponentBias := ieeeBias expWidth + 1`, and the two descriptors [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2fnuz]] are built from it.

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

So `0x7f`, which is NaN in E4M3FN, is $15 \cdot 2^4 = 240$ in E4M3FNUZ and $7 \cdot 2^{13} = 57344$ in E5M2FNUZ. Classifier theorems describe every word of these encodings. [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf_eq_false_of_encoding_ne_ieee]] says that no bit pattern is infinite in any non-IEEE encoding, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero_eq_true_iff_of_encoding_finiteUnsignedZero]] says that in FNUZ a value is zero exactly when every stored bit is zero. `signMask_isNaN_of_encoding_finiteUnsignedZero` says that the would-be negative zero is NaN.

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

With only one zero, negation changes too. IEEE and E4M3FN negation flips the sign of zero, but FNUZ negation returns its single zero, as the [finite-format negation proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/FiniteSemantics.lean) specify. That rule belongs to the format and not to the interface. The common `ExecFloat` interface of [chapter 16](#/chapter/backends-and-the-planner) also supports IEEE families, and in those negation still flips the sign of zero.

## FP6 and FP4: fully finite encodings

The OCP Microscaling (MX) specification [@ocpMx] defines the element formats that go inside a scaled block. FP6 comes in two variants, E2M3 and E3M2, and FP4 is E2M1. These formats are fully finite, so there's no infinity and no NaN, every one of the 64 or 16 codes is a number, and both signs of zero stay. This is the `finite` encoding, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m1]], `e2m3` and `e3m2` are `finite 2 1`, `finite 2 3` and `finite 3 2`. By [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN_eq_false_of_encoding_finite]] and `isFinite_eq_true_of_encoding_finite`, every word of such a format is finite and none is NaN. FP4 is small enough that we can just write it out. With bias 1 and one fraction bit, its sixteen codes denote

$$0,\ \pm\tfrac{1}{2},\ \pm 1,\ \pm\tfrac{3}{2},\ \pm 2,\ \pm 3,\ \pm 4,\ \pm 6,$$

which is fifteen distinct values, because both zeros are present. The gap between the two largest values is 2, a third of the larger one, so at this precision rounding can change a big fraction of the number. In MX, E2M1 elements share a block scale that moves their range to fit the values being represented.

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

The second evaluation computes each format's largest finite value from its descriptor instead of copying it from a specification. Both FP6 formats have five payload bits and split them differently, with E2M3 favouring precision and E3M2 favouring range. [Figure 11.1](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-element-values) puts all seven formats on one logarithmic scale, and each panel marks every positive finite value and lists the format's total bit width, value limits and value count. E5M2 spreads four values per binade over the widest range, while E4M3FN packs eight into each binade over a narrower one. The FNUZ variants move their extra binade from the top of the range to the bottom, and the FP6 and FP4 formats live within a handful of binades on either side of one.

![Seven low-precision formats on the same logarithmic value scale, with tall blue ticks for normals and short orange ticks for subnormals; labels give total bit widths, smallest and largest positive finite values, and counts](assets/ch13-element-values.png "Positive finite values of seven low-precision formats on a common logarithmic scale.")

A fully finite format has no infinity or NaN code to put an overflow in, so FloatLib's native policy saturates to the largest finite magnitude. That rule, `nativeOverflow`, follows the encoding. It gives signed infinity for `ieee`, the NaN word for `finiteMaxNaN` and `finiteUnsignedZero`, and the largest finite value with the right sign for `finite`.

## Rounding and overflow policies

The encoding says what the stored bits mean, but it doesn't say what an operation should do when its exact result doesn't fit, and the specifications leave that choice to the implementation. For FP8, the paper describes saturating conversion with an optional non-saturating mode, and CUDA's conversion intrinsics expose both. Say an E4M3 result lands beyond 448. `__NV_NOSAT` turns it into the NaN word `0x7f`, and `__NV_SATFINITE` clamps it to 448. Both are E4M3FN, and only the overflow policy differs. In the same way, a format can have subnormal patterns while the hardware flushes subnormal results to zero. So the descriptor fixes the encoding, and each operation takes its own [[FloatLib.Numerics.QuantizationPolicy]]. A policy records three independent choices. A [[FloatLib.Numerics.RoundingMode]] is one of `nearest` with ties to even, `nearestAway`, `towardZero`, `up`, `down`, `away` and `stochastic`. An `OverflowMode` is native or saturate, and an `UnderflowMode` is gradual or flush to zero. Three named policies, `nearest`, `saturating` and `flushToZero`, cover the common cases. If $M_F$ is the largest finite magnitude of format $F$ and $x$ is large enough that nearest-even rounding carries it past $M_F$, then

$$Q_F^{\text{sat}}(x) = M_F, \qquad Q_F^{\text{native}}(x) = \begin{cases} +\infty & F \text{ is IEEE} \\ \text{NaN} & F \text{ is FN or FNUZ} \\ M_F & F \text{ is fully finite,} \end{cases}$$

and whenever the rounding stays within $\pm M_F$ the two agree. They're still different functions, though, and a theorem about one isn't a theorem about the other. That's why you pass the policy to [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] as an argument instead of setting it globally. Let's try it on a value that's too big for E4M3FN. The first two evaluations hold the exact input and the format fixed and change only the policy.

```lean
open FloatLib.Numerics

def exact500 : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 500, exponent := 0 }

#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.nearest 0 exact500
-- 127
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.saturating 0 exact500
-- 126
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e2m1 QuantizationPolicy.nearest 0 exact500
-- 7
```

Native E4M3FN overflow gives 127, the NaN word `0x7f`, and saturating gives 126, which is `0x7e` or 448. E2M1 has no NaN, so it saturates even under its native policy, to the word 7, which is the value 6. The `0` argument is entropy for stochastic rounding, and the deterministic modes ignore it. Stochastic rounding is unbiased when the entropy is uniform modulo the denominator of the discarded fraction, but that's a statement about one rounding step. It doesn't cover a whole quantization with saturation or flush to zero, since those only ever move a result toward zero. Flush to zero acts on the rounded result instead of the input. Whatever rounds to a subnormal word is replaced by the zero of the same sign. Take E4M3FN's smallest positive subnormal, $2^{-9}$. Under the default policy it's stored as the word `0x01`, and flush to zero turns it into `0x00`.

```lean
def minE4M3Subnormal : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 1,
    exponent := FloatFormat.e4m3fn.minSubnormalExponent }

#eval FloatFormat.e4m3fn.minSubnormalExponent
-- -9
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.nearest 0 minE4M3Subnormal
-- 1
#eval Model.toNatBits <|
  Model.Policy.roundDyadic FloatFormat.e4m3fn QuantizationPolicy.flushToZero 0 minE4M3Subnormal
-- 0

example (fmt : FloatFormat) (entropy : Nat) (value : FloatLib.Numerics.Dyadic) :
    Model.Policy.roundDyadic fmt QuantizationPolicy.nearest entropy value =
      Model.roundDyadic fmt value :=
  Model.Policy.roundDyadic_nearest_eq_execFloat fmt entropy value
```

Under the default policy, `roundDyadic_nearest_eq_execFloat` says that policy rounding is the canonical [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]] for every descriptor, so theorems about the canonical rounder apply to this policy too. Two rounding engines compute that result, and they do it in different ways. The policy engine works on exact rationals and takes a `QuantizationPolicy`. The directed rounders shift a dyadic significand, with native overflow and gradual underflow, and they support all six `IEEERoundingMode` directions, which are the five IEEE attributes plus MPFR's rounding away from zero. Neither engine delegates to the other, but `roundDyadicGeneral_toRoundingMode` proves that they agree on the complete packed word for every descriptor, all six directions, both signs and every exact dyadic.

<a id="using-the-low-precision-types"></a>

## Executable types and lookup tables

Each named small format has a type with a one-byte carrier, in `FloatLib.Floats` next to `Binary32`. OFP8 gets `E4M3FN` and `E5M2`, the MX elements get `E2M1`, `E2M3` and `E3M2`, and the ONNX formats get `E4M3FNUZ` and `E5M2FNUZ`. A value of `E4M3FN` is a `UInt8` with an erased range proof, and no descriptor is stored in it. So E5M2 and E5M2FNUZ take up the same memory but stay different types, and mixing their encodings means writing a conversion. The same layouts exist on the general carrier, for example `ExecFloat.Binary (exponentBits := 4) (fractionBits := 3) (encoding := .finiteMaxNaN)`, where they add directed rounding and status options at a lower arithmetic speed.

Each type has a type-level identity, such as `E4M3FN.Family`, and its `Family` instance names the proof-model descriptor, proves that the width fits in eight bits and supplies the kernels. At eight bits or fewer, the kernels for addition, subtraction, multiplication, division and square root are exhaustive tables. Each one is a [[FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary]] or its unary cousin, and it carries the model operation it was generated from, plus a proof that this operation equals the reference specification. For E4M3FN the five tables come to roughly 257 KiB. Fused multiply-add is the exception, because a ternary table for an eight-bit format would have 16,777,216 entries. So the FP8 and FNUZ types use the proved generic single-rounding kernel for FMA. E2M1's 4,096-entry FMA table is small enough to keep. Both FP6 types keep a 262,144-entry table as well as the generic kernel, so the planner of [chapter 16](#/chapter/backends-and-the-planner) can pick the table for throughput and the kernel when the lookup footprint matters. Let's add a few bytes and see what comes out.

```lean
open FloatLib.Floats

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

example (x y : E4M3FN) : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

In E4M3FN, `0x38` is 1 and `0x40` is 2, and their sum is 68, the word `0x44`, which is 3. Add 448 to itself and it overflows to 127, the NaN word `0x7f`. In E5M2 the same experiment overflows 57344 to 124, which is `0x7c`, positive infinity, because E5M2 kept the IEEE encoding. In E4M3FNUZ overflow lands on 128, the NaN word `0x80`, and negating zero gives zero, since there's no other zero to give :) The final example is the refinement theorem [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]]. It says the `+` on any static-byte family equals [[FloatLib.Floats.ExecFloat.Spec.add]], the exact dyadic sum followed by one rounding in the family's descriptor, and matching theorems cover subtraction, multiplication, division, square root and fused multiply-add. That part is proved. In the [ONNX comparison](#/chapter/external-validation) we also test the model's decoding rules against an independent implementation of the specification, and agreeing on decoding doesn't settle how hardware converts values or how block arithmetic behaves.

## E8M0 and microscaling blocks

In the MX specification, a block of narrow elements shares one scale. The scale moves the whole block's range at once, and each four-bit element describes a value relative to it. That helps when neighbouring values fit within a few binades, but it adds nothing to E2M1's significand precision. The scale is stored as an E8M0 word, eight bits that are all exponent, with no sign, no fraction and no zero. Code $c$, for $c$ from 0 through 254, denotes $2^{c - 127}$, so the scales run from $2^{-127}$ to $2^{127}$, and code 255 is NaN. Since it has no sign or fraction field, E8M0 lives outside the three-field `FloatFormat`, and [[FloatLib.Floats.Formats.OCP.MX.E8M0]] is its own type, transparent over `BitVec 8`. Its checked decoders [[FloatLib.Floats.Formats.OCP.MX.E8M0.exponent?]] and `toDyadic?` return `none` for the NaN code. It has two constructors. `ofExponent?` refuses exponents outside $[-127, 127]$, and `ofExponentSaturating` clamps and says so in its name.

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

Applying a scale is exact, because `scaleDyadic?` adds the scale's exponent to an element's dyadic exponent and leaves its sign and significand alone. `decodeElement?` decodes and scales one element word, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeBlock?]] does the same for a whole array and fails if the scale or any element isn't finite. A [[FloatLib.Floats.Formats.OCP.MX.BlockCode]] keeps the scale next to the element words, because you need both to recover their values, and its `decode?` reads them together. Now say the scale is $2^{-2}=\tfrac14$. Then E2M1's nonnegative values become

$$
0,\quad \tfrac18,\quad \tfrac14,\quad \tfrac38,\quad
\tfrac12,\quad \tfrac34,\quad 1,\quad \tfrac32.
$$

The largest gap is now $\tfrac12$ instead of 2, but the largest value is four times smaller too. To store a target value we divide it by the scale and quantize the quotient to E2M1, so a target of $\tfrac38$ becomes the exact element value $\tfrac32$, code `0x3`. A target of 2 would need the element value 8, which is past E2M1's maximum of 6, so native finite overflow would clamp its reconstruction to $\tfrac32$. Change the scale to $\tfrac12$ and the target 2 fits exactly, as element value 4. Now the smaller target $\tfrac38$ asks for element value $\tfrac34$, halfway between $\tfrac12$ and 1. Nearest-even picks 1, code `0x2`, and reconstruction gives $\tfrac12$, an error of $\tfrac18$. So one scale keeps the small value and the other makes room for the larger one, and increasing the scale can't add the missing element code between those neighbours. All of this happens while a block is encoded, and the decoder only applies the scale it was given. If you change a stored scale without requantizing the elements, every nonzero represented value changes.

Now let's do a dot product that's small enough to check by hand. Say we have four E2M1 weights sharing the scale $2^{-2}$ and four E2M1 activations sharing the scale $2^{1}$. We decode both blocks, multiply corresponding elements and sum in exact dyadic arithmetic, so only the final sum is rounded into the output format.

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

The weights decode to $\tfrac14, \tfrac34, -\tfrac38, \tfrac32$ and the activations to $4, 1, 8, -2$. The exact dot product is $1 + \tfrac34 - 3 - 3 = -\tfrac{17}{4}$. Rounded once into bfloat16, that's the word 49288, `0xc088`, which is exactly $-4.25$. Rounded once into E4M3FN it's 200, `0xc8`, which is $-4$. At that magnitude E4M3FN's spacing is $\tfrac12$, so $-4.25$ is a tie, and ties go to the even neighbour. If you increase the weight scale by one code, every decoded weight doubles while the element words stay fixed, so the exact dot product doubles too before output rounding. Rounding happens at two points, when the elements are first quantized and when the final sum is converted, and decoding and the products add no error. If the scale is the NaN code, the decoder returns `none` instead of a number. In [Figure 11.2](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-mx-block), each block's card shows its scale and its four element values before and after scaling. The lane products sum exactly, and two independent branches then round that same sum into bfloat16 and E4M3FN.

![Two E2M1 blocks scaled by their E8M0 codes, followed by lane products and the exact sum -17/4; separate branches round that sum to -4.25 in bfloat16 and -4 in E4M3FN](assets/ch13-mx-block.png "Each output rounds the same exact dot product once.")

To prove that decoding preserves a block's values, we first have to say which array the block represents, and for that we use the numerical system interface from [chapter 14](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled). `blockSystem` assigns an exact dyadic array to a block that decodes successfully and a NaN exception to one that doesn't. `blockSystem_represents_iff` then says that a block represents an array exactly when its decoder returns that array. Whenever the inputs represent values, [[FloatLib.Floats.Formats.OCP.MX.BlockCode.decode_refines]], [[FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines]] and [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines]] prove that decoding succeeds and returns the specified result. For the block decoder that's the array itself, and for the two scaling functions it's an exponent shift. [[FloatLib.Floats.Formats.OCP.MX.E8M0.toDyadic?_significand_eq_one]] and `toDyadic?_negative_eq_false` add that every decoded scale is a positive power of two.

```lean
example (block : BlockCode FloatFormat.e2m1) (values : Array FloatLib.Numerics.Dyadic) :
    (blockSystem FloatFormat.e2m1).Represents block values ↔ block.decode? = some values :=
  blockSystem_represents_iff block values
```

Programs can use the configured `E8M0` and `Block` wrappers through the common executable interface, where `ofElements` builds a block from an array of `E2M1` values. There's also a second, more general block family, [[FloatLib.Floats.Formats.Block.SharedScaleCode]], with an unbounded integer exponent and integer significands, and [chapter 14](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled) covers it.

<a id="choosing-a-scale-for-32-lanes"></a>

## Choosing a scale for 32 elements

The four-element example above used `MX.BlockCode`, whose array can have any length. The [standard MX implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/OCP/MX/Standard) provides the standard MX block, an E8M0 scale plus a `Vector` of exactly 32 elements, and it has six profiles, E5M2, E4M3, E3M2, E2M3, E2M1 and INT8. Here E4M3 uses the finite-max-NaN encoding, and INT8 means a signed two's-complement coefficient divided by 64, with values from $-2$ to $127/64$. Quantizing a block first chooses a shared scale, then rounds every lane at that scale. Our [quantizer](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/Runtime.lean) implements the recommended rule from Section 6.3 of the MX specification. You find the largest absolute input, take its binary exponent, and subtract the element format's largest power-of-two exponent, and if that gives $e$, the scale is $2^e$. Each input is then divided by this scale and rounded to the nearest element, with ties to an even low bit and finite saturation by default. That rule can clip a value even when another scale could represent it exactly. Say we take 32 E4M3 lanes, all holding $15/8$. All of them lie in the binade starting at $2^0$, and E4M3's largest power of two is $2^8$, so the rule chooses $2^{-8}$ and each lane asks to store

$$
\frac{15/8}{2^{-8}}=480.
$$

E4M3 ends at 448, so saturation reconstructs $448\cdot2^{-8}=7/4$, an error of $1/8$. With $2^{-7}$ the lanes would ask for element value 240 and reconstruct $15/8$ exactly. The recommended rule doesn't search the other scales for a smaller reconstruction error, so here it gives away an eighth that the next scale up would have kept :) Our error theorem therefore fixes the scale first and only then compares possible element words. `quantizeFinite_quantizes` proves the block follows the selected scale and element policy. At a finite selected scale, `quantizeFinite_error_le` proves that each saturated lane minimizes absolute reconstruction error among all finite element words **at that scale**. That makes $7/4$ the best result available with scale $2^{-8}$, even though it isn't the best across all E8M0 scales. The [scale-selection proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/ScaleProof.lean) establish the binade and scale bounds, and the element proofs give exactness when the scaled input is representable and the even choice on ties.

The scale-selection recommendation leaves some room for policy, and there we had to choose. An all-zero block gets scale one, and a requested exponent below $-127$ is clamped. The result is a NaN block if the exponent exceeds 127 or any input lane is nonfinite. FP8 also exposes the specification's overflow mode as `(overflow := .native)`, next to the default `.saturate`, while FP4, FP6 and INT8 always saturate. Decoding an existing standard block keeps each lane's exceptional class, so with a finite scale an infinity or NaN in one element leaves its finite neighbours alone, while a NaN scale affects every lane. Finite scaling uses exact rational arithmetic, so it still means something beyond binary32's range. These quantization and decoding contracts describe the six logical block formats and say nothing about a physical memory layout.

## MX dot products with one final rounding

The standard MX operations `dot` and `dotGeneral` turn those decoded lanes into a binary32 result. Their operands may use different element profiles, which covers all 36 pairs of the six profiles. `dot` takes one 32-lane block from each operand, and `dotGeneral` takes equally many blocks on each side, with each operand keeping its own profile and each block its own scale. The MX specification leaves internal accumulation precision and the order of operations to the implementation, and we went with exact rational products and sums, followed by one nearest-even binary32 rounding. For decoded lanes $a_{j,i}$ and $b_{j,i}$, FloatLib computes

$$
S=\sum_{j=0}^{n-1}\sum_{i=0}^{31}a_{j,i}b_{j,i},
\qquad
\text{result}=\operatorname{round}_{\mathrm{binary32}}(S).
$$

No product or partial block sum is rounded, and here's a case where that matters. Take an E2M1 block with scale $2^{127}$ and element values $1,-1,0,\ldots,0$, and pair it with a block at the same scale holding $1,1,0,\ldots,0$. The first two products are $2^{254}$ and $-2^{254}$. Round each product to binary32 and you get opposite infinities, whose sum is NaN, but exact accumulation cancels them and returns positive zero. Splitting the cancelling terms across blocks gives the same result, because `dotGeneral` also postpones rounding past the block boundary.

In the [dot-product proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/DotProduct/Proof.lean) we prove the shared-scale formula, `dotExact_eq_scaled_sum`, and the multi-block exact sum, `dotGeneralExact_finite`. When the decoded lanes and the final binary32 result are finite, `toReal_dotGeneral_eq_roundAt` identifies the packed result with one real rounding of $S$, and `abs_toReal_dotGeneral_sub_le` then bounds the absolute error by half an ulp at $S$, gradual underflow included. There's no accumulation-error term at all. The bound starts from the decoded operands, though, so it leaves out any error from quantizing earlier real-valued inputs into MX blocks. The [configured dot-product proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/Configured/DotProduct/Proof.lean) carries the same result over to `ExecFloat.OCP.MX.Standard.dotGeneral`, because packing into the executable binary32 carrier adds no further rounding. Exact-zero sums return positive zero, and an empty dot is one of them, while a negative nonzero sum that underflows keeps its negative sign. NaN scales propagate NaN, and zero times infinity or addition of opposite infinities is invalid. This API is value-only, so it returns no NaN payloads and no status flags.

## Conditions on the error bounds

Scalar arithmetic has exact dyadic semantics, but its real-number error theorems reach less far. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] connects executable rounding to the rounded-real grid [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]], and it carries the hypothesis `fmt.isIEEE = true`, as do the arithmetic theorems built on it. So they cover bfloat16, TF32 and E5M2, but not E4M3FN, the FNUZ formats or the fully finite element formats. The MX results above bound quantization at a selected scale and the single binary32 rounding of an exact dot. They don't carry the IEEE half-ulp arithmetic bounds of [chapter 07](#/chapter/the-mathematics-of-rounding) over to operations rounded into those element formats.

A sequential mixed-precision dot product also rounds its intermediate results. `dotSequential` takes a `SitePolicy` that names the storage, product, accumulator and output formats, and the policy-aware `mulAddFinite?` can run, for example, an E4M3FN times E4M3FN product accumulated into bfloat16 or binary32. Both work on any descriptor. For the error budget, though, [[FloatLib.Floats.Formats.BinaryInterchange.Model.dotSequential_abs_error_le_budget]] needs all four formats to be IEEE and every intermediate to be finite. None of those intermediate rounding steps happen in the exact MX dot.

Directed and stochastic policies over the non-IEEE scalar formats have executable semantics and an agreement theorem for the IEEE directions, but no real error theorems. Our standard MX quantizer rounds to nearest-even under its stated scale and overflow policies, and its contracts describe the scale and accumulation precision FloatLib chose. They say nothing about how an H100 or MI300 behaves.

## Affine integer quantization

Integer inference often uses an affine quantizer. A stored code $k$ reconstructs as $s(k-z)$ for scale $s>0$ and zero point $z$, as in [Jacob and colleagues' 2018 inference scheme, §2.1](https://openaccess.thecvf.com/content_cvpr_2018/html/Jacob_Quantization_and_Training_CVPR_2018_paper.html). [Chapter 14's affine quantization example](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled/affine-quantization) follows a value through division by the scale, nearest-even rounding, adding the zero point, clipping, and reconstruction. It derives the half-step error bound, shows why clipping breaks that bound, and connects FloatLib's exact rational implementation to its real specification.
