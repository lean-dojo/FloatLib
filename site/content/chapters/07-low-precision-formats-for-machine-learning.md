---
number: "07"
slug: low-precision-formats-for-machine-learning
title: Small formats for machine learning
summary: "How FloatLib describes, rounds and proves things about the 16-, 8-, 6- and 4-bit floats of machine learning, from bfloat16 and FP8 to MX blocks and the IEEE P3109 family."
phases: [ml-formats, p3109]
---

Why would anyone store a number in four bits? A neural network is mostly a huge collection of weights, the numbers it learns, multiplied and added over and over. A binary32 float, the usual kind, takes 32 bits. In 16 bits, or 8, or 4, the same memory holds two, four or eight times as many numbers, with that much less data to move. If names like FP8 are new to you, that's fine. This chapter explains each one as it comes up.

The catch is the budget. Eight bits give only 256 bit patterns, or codes. Every code spent on infinity or NaN ("not a number", the code for an undefined result) is a number the format can't write, and every bit moved from the exponent, which sets a number's size, to the fraction, which holds its digits, brings the numbers closer together and narrows their range. So different groups made different choices.

## What does "FP8" mean?

The name is short for "floating point, eight bits", a float in one byte with a sign bit, an exponent and a fraction. For a normal value the exponent picks a power of two and the fraction picks a point between that power and the next. The names count the bits after the sign, E for exponent and M for mantissa, an older word for the fraction: E5M2 has five exponent bits and two fraction bits, E4M3 four and three. A file of FP8 weights is just bytes, and the formats disagree about them. The byte `0x7c` (the `0x` marks hexadecimal, one digit for every four bits) is positive infinity in E5M2 and 384 in E4M3FN, a variant of E4M3 we'll meet shortly.

## What is a format family?

These formats share four parts: an exponent width, a fraction width, a bias (subtracted from the stored exponent so that exponents can be negative) and an encoding saying which codes are infinities, NaNs and zeros. FloatLib writes them in one record, a descriptor, of type [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]], with an [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.Encoding]] for the last part. Think of it as a recipe, and a format family as everything such a recipe produces as you turn its knobs.

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

TF32 is a format you never store. Since the Ampere generation, the tensor cores in NVIDIA GPUs, units built for matrix multiplication, have a TensorFloat-32 mode that multiplies binary32 inputs using the sign, eight exponent bits and ten fraction bits, and accumulates in binary32 [@nvidiaTf32]. Our [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.tf32]], `FloatFormat.ieee 8 10`, describes the multiplication's precision, not how hardware stores the operands, and like binary16 it has eleven significant bits, so one tenth rounds the same way:

```lean
example : FloatFormat.tf32 = FloatFormat.ieee 8 10 := rfl
example : FloatFormat.tf32.bitWidth = 19 := by decide

#eval Model.toDyadic? (Model.roundRat FloatFormat.tf32 false 1 10)
-- some { negative := false, significand := 1638, exponent := -14 }
```

`rfl` confirms the definition, and one tenth rounds as in binary16.

## What are the FP8 formats?

In 2022 NVIDIA's H100 brought hardware for two eight-bit formats [@micikevicius2022fp8], which the Open Compute Project standardized as OFP8 [@ocpOfp8]. E5M2 keeps the IEEE encoding and binary16's exponent range, so [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]] is `FloatFormat.ieee 5 2`. E4M3 has only eighteen binades (a binade runs from one power of two to the next), and an IEEE top exponent for infinity and NaN would cost one of them. In E4M3FN ("finite with NaN") the all-ones exponent is ordinary, there's no infinity, and the only NaN has every exponent and fraction bit set, in either sign. The largest finite value is

$$\left(1 + \tfrac{6}{8}\right) \cdot 2^{15 - 7} = 1.75 \cdot 256 = 448,$$

encoded as `0x7e`, with NaN at `0x7f`. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteMaxNaN]] builds a descriptor with the conventional bias and this non-IEEE encoding, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fn]] is `finiteMaxNaN 4 3`.

Now we can decode our byte, $0\,1111\,100$ in bits. E5M2 reads exponent $11111_2 = 31$ and fraction $00_2$, which is $+\infty$. E4M3FN reads exponent $1111_2 = 15$ and fraction $100_2 = 4$, which is $1.5 \cdot 2^{8} = 384$. `Model.ofNatBits` reads a byte in the format you name:

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

Lean agrees, and the last two lines show E4M3FN's 448 and NaN. Try it yourself with other bytes.

## What are the FNUZ formats?

AMD's accelerators use two formats, E4M3FNUZ and E5M2FNUZ, from the float8 definitions of ONNX, a common file format for trained networks [@onnxFloat8]. UZ stands for "unsigned zero". The would-be negative zero `0x80` is the one NaN, `0x00` the only zero, and there's no infinity. ONNX also raises the bias by one, to 8 and 16, moving the extra binade from the top of the range to the bottom, so E4M3FNUZ tops out at 240 instead of 448, while E5M2FNUZ, whose all-ones exponent row is finite, keeps 57344. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.finiteUnsignedZero]] builds [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2fnuz]]. Here are the biases and the special bytes:

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

You get biases 7, 8 and 16, NaN at `0x80`, and the two maxima at `0x7f`.

IEEE formats and E4M3FN flip the sign of zero, but FNUZ negation returns the single zero, as the [finite-format negation proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Arithmetic/FiniteSemantics.lean) specify. Three encoding rules are theorems: [[FloatLib.Floats.Formats.BinaryInterchange.Model.isInf_eq_false_of_encoding_ne_ieee]] (no pattern is infinite in a non-IEEE encoding), [[FloatLib.Floats.Formats.BinaryInterchange.Model.isZero_eq_true_iff_of_encoding_finiteUnsignedZero]] (an FNUZ value is zero exactly when all its bits are) and `signMask_isNaN_of_encoding_finiteUnsignedZero` (the would-be negative zero is NaN). Here they are in use:

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

In each, `by decide` or `rfl` proves the format has the right encoding.

## What are FP6 and FP4?

The element formats of the OCP Microscaling (MX) specification [@ocpMx], FP6 as E2M3 or E3M2 and FP4 as E2M1, drop infinities and NaNs and keep both zeros. An element is one number in an MX block, which we'll meet later. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e2m1]], `e2m3` and `e3m2` use the `finite` encoding, and by [[FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN_eq_false_of_encoding_finite]] and `isFinite_eq_true_of_encoding_finite` every word is finite and none is NaN. FP4's sixteen codes denote

$$0,\ \pm\tfrac{1}{2},\ \pm 1,\ \pm\tfrac{3}{2},\ \pm 2,\ \pm 3,\ \pm 4,\ \pm 6,$$

fifteen distinct values (the two zeros are equal), a very coarse ruler. Lean can list them, and each format's largest finite value:

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
  (Model.toDyadic? (Model.maxFinite fmt (negative := false))).map FloatLib.Numerics.Dyadic.toRat
-- [some 6, some (15 / 2), some 28, some 448, some 240, some 57344, some 57344]
```

Codes 8 through 15 are 0 through 7 negated, and the maxima run from 6 in FP4 to 57344. An overflow in FP6 or FP4, a result too large to hold, has only the largest finite magnitude left, so our native rule, `nativeOverflow`, saturates (clamps) there. [Figure 7.1](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-element-values) puts all seven formats on one logarithmic scale.

![Seven low-precision formats on the same logarithmic value scale, with tall blue ticks for normals and short orange ticks for subnormals; labels give total bit widths, smallest and largest positive finite values, and counts](assets/ch13-element-values.png "Positive finite values of seven low-precision formats on a common logarithmic scale.")

## What happens when a result doesn't fit?

An encoding says what the bits mean, not what an operation does when its exact result doesn't fit, and the specifications leave that to the implementation. In CUDA, NVIDIA's GPU toolkit, `__NV_SATFINITE` clamps E4M3 overflow to 448 and `__NV_NOSAT` returns NaN, and hardware that flushes subnormals to zero splits underflow the same way. So each operation takes a [[FloatLib.Numerics.QuantizationPolicy]] (quantizing turns an exact value into a code) of three choices, a [[FloatLib.Numerics.RoundingMode]], an `OverflowMode` and an `UnderflowMode`:

| Choice | Options |
| --- | --- |
| Rounding | `nearest` (ties to even), `nearestAway`, `towardZero`, `up`, `down`, `away`, `stochastic` |
| Overflow | native or saturate |
| Underflow | gradual or flush to zero |

If nearest-even rounding carries $x$ past $M_F$, the largest finite magnitude of $F$, then

$$Q_F^{\text{sat}}(x) = M_F, \qquad Q_F^{\text{native}}(x) = \begin{cases} +\infty & F \text{ is IEEE} \\ \text{NaN} & F \text{ is FN or FNUZ} \\ M_F & F \text{ is fully finite,} \end{cases}$$

and within $\pm M_F$ the two agree. A theorem about one isn't about the other, so the policy is an argument to [[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]], not a global setting. If you start with 500 and round it in E4M3FN under two policies, then in E2M1, you get:

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

Native overflow gives 127, the NaN word, and saturation 126, which is 448, while E2M1 has no NaN and saturates either way, to 6. The `0` is entropy, random input for stochastic rounding, which picks a neighbour at random. It is unbiased per step when the entropy is uniform modulo the denominator of the discarded fraction, but not over a whole quantization with saturation or flush to zero, since those only move results toward zero. Flush to zero sends a result that rounds to a subnormal to the zero of the same sign. Here's the smallest E4M3FN subnormal both ways:

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

Nearest keeps code 1, flush to zero gives code 0, and the theorem says the nearest policy is `Model.roundDyadic` whatever the entropy. So the default policy is the canonical [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]] for every descriptor, and its theorems apply. Directed rounding, with native overflow and gradual underflow, runs on a separate engine, and `roundDyadicGeneral_toRoundingMode` proves the two agree on the packed word for every descriptor, all six `IEEERoundingMode` directions, both signs and every exact dyadic.

<a id="using-the-low-precision-types"></a>

## How to compute with the one-byte types

In a program you use the one-byte types in `FloatLib.Floats`, one per named small format, such as `E4M3FN`, `E5M2`, `E2M1` and `E4M3FNUZ`. They're distinct types, so mixing E5M2 and E5M2FNUZ takes a conversion. At eight bits or fewer, addition, subtraction, multiplication, division and square root are exhaustive lookup tables, like a times table, each a [[FloatLib.Floats.ExecFloat.Backend.TinyTable.CertifiedBinary]] or its unary cousin with a proof that it equals the reference specification. An FMA (fused multiply-add) table would need 16,777,216 entries, so the FP8 and FNUZ types use the proved generic single-rounding kernel, the general arithmetic code. Here are a few operations on bytes:

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

In E4M3FN, 1 plus 2 is 3 and 448 plus itself is NaN, code 127. E5M2 overflows to infinity, E4M3FNUZ to its NaN, and negating FNUZ zero gives zero, since there's no other zero to give :) [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] says the `+` on any static-byte family, the kind behind each one-byte type, equals [[FloatLib.Floats.ExecFloat.Spec.add]], the exact dyadic sum rounded once in the family's descriptor, and matching theorems cover subtraction, multiplication, division, square root and FMA. The [ONNX comparison](#/chapter/external-validation) checks the model's decoding against an independent implementation of the specification, which doesn't settle how hardware converts values or how block arithmetic behaves.

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

Applying a scale is exact, since it just adds exponents. [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeBlock?]] decodes and scales a whole array, failing if the scale or any element isn't finite, and a [[FloatLib.Floats.Formats.OCP.MX.BlockCode]] keeps a scale with its elements for `decode?`. If you start with scale $2^{-2}$, E2M1's nonnegative values become

$$
0,\quad \tfrac18,\quad \tfrac14,\quad \tfrac38,\quad
\tfrac12,\quad \tfrac34,\quad 1,\quad \tfrac32.
$$

Decoding only applies the scale it's given, so changing a stored scale without requantizing, rounding again for the new scale, changes every nonzero value in the block.

### How to take the dot product of two blocks

A dot product multiplies two blocks lane by lane, position by position, and adds the products. Here four E2M1 weights share the scale $2^{-2}$ and four activations, values the network computes, share $2^{1}$, and we sum in exact dyadic arithmetic, so the only rounding is the final sum into the output format. The code also rounds the result two ways:

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

The exact dot product is $1 + \tfrac34 - 3 - 3 = -\tfrac{17}{4}$, which bfloat16 holds exactly. E4M3FN gives $-4$, because its spacing there is $\tfrac12$ and the tie goes to the even neighbour. A NaN scale makes the decoder return `none`, so the last line prints `false`. [Figure 7.2](#/chapter/low-precision-formats-for-machine-learning/figure-ch13-mx-block) draws the computation.

![Two E2M1 blocks scaled by their E8M0 codes, followed by lane products and the exact sum -17/4; separate branches round that sum to -4.25 in bfloat16 and -4 in E4M3FN](assets/ch13-mx-block.png "Each output rounds the same exact dot product once.")

Our `blockDot?` trusted `decode?`, so that's what the proofs pin down. `blockSystem_represents_iff` says a block represents an array in the [numerical system interface](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled) exactly when its decoder returns it. For represented inputs, [[FloatLib.Floats.Formats.OCP.MX.BlockCode.decode_refines]] proves that decoding succeeds with the array, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines]] and [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines]] that scaling succeeds with the exact product of scale and value. Here's the first:

```lean
example (block : BlockCode FloatFormat.e2m1) (values : Array FloatLib.Numerics.Dyadic) :
    (blockSystem FloatFormat.e2m1).Represents block values ↔ block.decode? = some values :=
  blockSystem_represents_iff block values
```

Read `↔` as "exactly when".

<a id="choosing-a-scale-for-32-lanes"></a>

## How is a block's scale chosen?

The [standard MX implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/OCP/MX/Standard) fixes a block at an E8M0 scale plus a `Vector` of exactly 32 elements, in six profiles: E5M2, E4M3 (finite-max-NaN), E3M2, E2M3, E2M1, and INT8, a signed coefficient divided by 64. Our [quantizer](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/Runtime.lean) follows the recommended rule of Section 6.3 of the MX specification: the scale is $2^e$, where $e$ is the binary exponent of the largest absolute input minus the element format's largest power-of-two exponent, and each input is divided by the scale and rounded to the nearest element, ties to even, saturating by default.

The rule can clip. Take 32 E4M3 lanes all holding $15/8$. Their binade starts at $2^0$ and E4M3's largest power of two is $2^8$, so the scale is $2^{-8}$ and each lane asks to store

$$
\frac{15/8}{2^{-8}}=480.
$$

E4M3 ends at 448, so saturation reconstructs $448\cdot2^{-8}=7/4$, an error of $1/8$, where $2^{-7}$ would have kept $15/8$ exactly :) So our error theorem fixes the scale first. We prove the block follows the selected scale and element policy, and at a finite selected scale `quantizeFinite_error_le` proves each saturated lane has the smallest absolute reconstruction error among all finite element words **at that scale**. The [scale-selection proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/ScaleProof.lean) give the binade and scale bounds, and the element proofs give exactness for representable inputs and the even choice on ties.

Beyond that, the choices are ours:

| Situation | What our quantizer does |
| --- | --- |
| All-zero block | Scale one |
| Requested exponent below $-127$ | Clamped |
| Requested exponent above 127, or a nonfinite input lane | NaN block |
| FP8 elements overflow | Saturate by default, or `(overflow := .native)` |
| FP4, FP6 and INT8 elements overflow | Always saturate |

Under a finite scale an infinite or NaN element keeps its class and leaves its neighbours alone, but a NaN scale takes out every lane. Finite scaling is exact rational arithmetic and keeps its meaning beyond binary32's range. These contracts are about the six logical block formats, not how a block sits in memory.

## How do MX dot products round?

The specification doesn't fix an MX dot product's accumulation precision or order. The standard `dot` takes one 32-lane block from each side and `dotGeneral` equally many blocks per side, each with its own scale, and both return binary32 for any of the 36 pairs of profiles. We keep products and sums exact and round once to nearest-even binary32, the way you'd keep every line of a long bill exact and round only the total to the cent:

$$
S=\sum_{j=0}^{n-1}\sum_{i=0}^{31}a_{j,i}b_{j,i},
\qquad
\text{result}=\operatorname{round}_{\mathrm{binary32}}(S).
$$

So at scale $2^{127}$, blocks holding $1,-1,0,\ldots,0$ and $1,1,0,\ldots,0$ give positive zero, even across blocks in `dotGeneral`, where rounding the products $\pm 2^{254}$ to binary32 would give opposite infinities and a NaN sum.

The [dot-product proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/DotProduct/Proof.lean) establish the exact-sum formulas. When the decoded lanes and the final binary32 result are finite, they prove the result is one real rounding of $S$, with absolute error at most half an ulp at $S$, gradual underflow included, and no accumulation term, so rounding the products and partial sums adds no error. The half-ulp bound itself still grows with the size of the exact sum. The bound starts from decoded operands, so it leaves out the error of quantizing real inputs into MX blocks. The [configured dot-product proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/Standard/Configured/DotProduct/Proof.lean) carries it to `ExecFloat.OCP.MX.Standard.dotGeneral`, since packing into the binary32 carrier adds no rounding. The API is value-only, with no NaN payloads or status flags:

| Case | Result |
| --- | --- |
| Exact-zero sum, the empty dot among them | Positive zero |
| Negative sum that underflows | Keeps its sign |
| NaN scale | NaN |
| Zero times infinity, or adding opposite infinities | Invalid |

## Which error bounds hold for which formats?

Here's the promised catch. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] connects executable rounding to the rounded-real grid [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] and carries the hypothesis `fmt.isIEEE = true`, as do the arithmetic theorems built on it. So they don't cover E4M3FN, FNUZ or the fully finite formats, and our MX results don't carry the IEEE half-ulp bounds of the [Rounding](#/chapter/the-mathematics-of-rounding) chapter over to operations rounded into those element formats. Directed and stochastic policies over non-IEEE scalar formats have executable semantics and an agreement theorem for the IEEE directions, but no real error theorems.

A sequential mixed-precision dot product rounds as it goes. `dotSequential` takes a `SitePolicy` naming the storage, product, accumulator and output formats, so the policy-aware `mulAddFinite?` can accumulate E4M3FN products into bfloat16 or binary32. Its error budget, [[FloatLib.Floats.Formats.BinaryInterchange.Model.dotSequential_abs_error_le_budget]], needs IEEE product, accumulator and output formats and a finite value at every step. The standard MX contracts write down our choices, and they don't tell you how an H100 or an MI300 behaves.

Integer inference often uses an affine quantizer instead, where code $k$ means $s(k-z)$ for a scale $s>0$ and zero point $z$ ([Jacob and colleagues' 2018 inference scheme, §2.1](https://openaccess.thecvf.com/content_cvpr_2018/html/Jacob_Quantization_and_Training_CVPR_2018_paper.html)), and the [affine quantization example](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled/what-is-affine-quantization) derives its half-step error bound and shows why clipping breaks it.

## What is IEEE P3109?

Every format so far hands out its zero, infinity and NaN codes its own way. The IEEE P3109 working group does it once, for a family. We follow version 4.0.3 of the *IEEE Working Group P3109 Interim Report on Arithmetic Formats for Machine Learning* [@p3109InterimReport]. It's a working-group report and hasn't been approved as an IEEE standard, and section numbers below refer to it.

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

![Complete 256-code binary8p4se strip with a class key, plus comparisons for b8p4sf, b8p8uf, and b6p1sf; the precision-one format has no subnormals and its nonzero finite values are signed powers of two](assets/ch15-code-space.png "One complete P3109 code space, with three comparisons of reserved codes and finite values.")

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

`convert` also hands back status flags, our own, since the report defines none, like a receipt. The record is shared with the [beginners' chapter](#/chapter/using-the-library):

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

`ExecFloat.P3109.add`, `sub`, `mul`, `div` and `fma` take `(target := ...)`, by default the operands' format, plus `mode` and `saturation`. Each forms the exact rational result before projecting, with division's finite quotient rule needing a nonzero denominator. The exceptional cases follow the P3109 model and are proved too: opposite infinities in addition, zero times infinity, and every division by zero give the single NaN, with no IEEE signaling metadata or status flags. `square` provably equals multiplication for every target and policy. A literal such as `(1.5 : B8P4SE)` rounds once by the default policy, and `==` is numerical, so NaN is unequal to itself.

### How do square roots round?

$\sqrt{2}$ isn't rational, but rounding it needs only squares of rational boundaries. In `binary8p4se` the candidates are $11/8$ and $12/8$, with midpoint $23/16$, and

$$
2 = \frac{512}{256} < \left(\frac{23}{16}\right)^2 = \frac{529}{256},
$$

so nearest-even returns $11/8$. The [square-root kernel](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/Sqrt/Runtime.lean) decides this way for `sqrt`, `rsqrt` and `hypot`, which forms $x^2+y^2$ exactly first, and rounds before saturating. We prove it agrees with the reference rounder on the exact real square root, through encoding and for all nine modes, and the stochastic tests follow the report's formulas through the exact root's fractional part, with no approximate square root. Negative square-root and nonpositive reciprocal-square-root inputs give NaN. The catch is that exact rational intermediates can get large in formats with a wide exponent range.

## How to mix P3109 formats with other formats

Section 4.5 of the report [@p3109InterimReport] spells out minimum operation specializations over three sets of formats, and we supply them, taking all three formats the report allows for the external set, the formats from outside P3109.

| Set | Formats |
| --- | --- |
| `F4` | Binary4p2sf |
| `F8` | Binary8p4se and Binary8p3se |
| `FX` | binary16, binary32, and BFloat16 |

The [mixed-format API](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/P3109/Arithmetic/Mixed) gives each operand its own type and lets a `Destination` argument pick the final projection, for conversions, reciprocals, the basic operations, and fused multiply-add and add-add, under the default policy unless `mode` and `saturation` say otherwise. `Mixed.faa` keeps all three terms until it knows the destination. With `binary8p4se` inputs 16 and 1 and a binary32 accumulator of $-16$, the exact expression is

$$
(16+1)+(-16)=1.
$$

Rounding the first sum into `binary8p4se` would lose the one, since 17 is our tie and goes to 16, but `Mixed.faa` sends the exact 1 to binary32, as `faa_eq_project_finite` states, and `fma_eq_project_finite` states the same for the fused product. An external destination keeps its own precision, bias and endpoints, and the [external-destination theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/External/Proof.lean) proves that encoding preserves the rounded and saturated datum's finite value, infinity sign, or prescribed exceptional representation, with no second rounding. Following the report, external negative zero enters as the single zero, zero results are written as positive zero, and NaN diagnostics collapse to the one NaN, written in the canonical quiet encoding. Ordinary binary arithmetic keeps its IEEE signed-zero and NaN rules.

### How do scaled operations work?

Binary8p1uf, the required instance for block scales, goes with `F4` or `F8` elements and an `F8` or external result in the minimum scaled operations. `Mixed.scaledAdd`, `scaledSub` and `scaledMul` form $sx+ty$, $sx-ty$ and $(sx)(ty)$ exactly and project once, with an implicit result scale of one, as their theorems state. A zero scale times an infinite element is NaN, and a NaN scale propagates over a zero element, so scaling isn't a bit shift.

## How to compare values and find the next one

Comparisons are unordered at NaN, even NaN with itself, so NaN never compares as less, equal or greater. `minimum` propagates NaN, `minimumNumber` can return the other operand and `minimumFinite` prefers a finite operand even over an infinity, and the [extrema proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/P3109/Arithmetic/Extrema/Proof.lean) cover them and their maximum twins, and the magnitude variants settle equal magnitudes by numerical order. At precision one, with no nonzero subnormals, `maxSubnormalOf` provably returns NaN. `nextGreaterThan` and `nextLessThan` step to a strictly greater or lesser datum, so above 224 in `binary8p4se` comes positive infinity, then NaN, because no greater datum exists. The proofs connect consecutive finite codes to numerical order with no value in between. Every operation in this section has decoding, projection, ordering and classification proofs, but they don't show compliance with every requirement of the interim report.

## How to inspect a P3109 type

`#float_info` shows what a P3109 type means, and `#float_info!` adds its contracts' conditions and special values:

```lean
#float_info B8P4SE
-- Float information: B8P4SE
--   family: P3109 binary floating-point format
--   standard: IEEE P3109 Interim Report v4.0.3, revision 34f5964 (working-group report)
--
-- Format:
--   storage: BitVec 8
--   total bits (K): 8
--   precision (P): 4
--   signed: yes
--   datum set: extended
```

It names the report it follows and the format's knobs.

## How is P3109 different from the OCP formats?

It starts with that one unit of bias. E4M3FN has bias 7, NaN at `0x7f` and `0xff`, and negative zero at `0x80`, while `binary8p4se` has bias 8, NaN at `0x80`, and infinities at `0x7f` and `0xff`. E4M3FNUZ makes the signed finite P3109 choices, which `sameByteValues` checks on every code:

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

#eval sameByteValues binary8p4se FloatFormat.e4m3fn
-- false

#eval sameByteValues binary8p3se FloatFormat.e5m2
-- false
```

The first two print `true`, so [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fnuz]] matches the signed finite descriptor with $K = 8$, $P = 4$ on all 256 codes, and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2fnuz]] the one with $P = 3$. That's an evaluation, not a theorem, and says only that the value sets coincide, not that arithmetic agrees. [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e4m3fn]] and [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat.e5m2]] aren't P3109 formats under any descriptor. Their bias is one less, E5M2 spends eight codes on infinities and NaNs where P3109 spends three, and both keep a negative zero. Let's end with the bytes we started with:

```lean
#eval (FloatFormat.e4m3fn.exponentBias, binary8p4se.exponentBias)
-- (7, 8)

#eval Model.toDyadic? (Model.ofNatBits (fmt := FloatFormat.e4m3fn) 0x7e)
-- some { negative := false, significand := 14, exponent := 5 }

#eval binary8p4se.decode 0x7e
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 14, exponent := 4 }

#eval Model.isInf (Model.ofNatBits (fmt := FloatFormat.e5m2) 0x7c)
-- true

#eval binary8p3se.decode 0x7c
-- FloatLib.Numerics.NumericalValue.finite { negative := false, significand := 4, exponent := 13 }
```

Byte `0x7e` is 448 in E4M3FN and 224 in P3109, because of that one unit of bias. And `0x7c`, E5M2's infinity, is $2^{15}$ in the matching P3109 format. `FloatFormat` doesn't admit unsigned formats, $P = 1$ or $P = K$, so P3109 has a decoder of its own. Binary-interchange real-number proofs assume the IEEE reading of the reserved patterns, while P3109 evaluates the closed expression and then applies its policy, even into a binary destination, so a matching value table doesn't make the APIs interchangeable.
