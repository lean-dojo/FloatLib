---
number: "14"
slug: fixed-point-logarithmic-codebook-and-block-scaled
title: Fixed point, logarithmic numbers, and quantization
summary: Fixed point, logarithmic numbers, codebooks, and shared scales use common numerical contracts to describe exact arithmetic, rounding, and overflow.
phases: [exact-and-quantized, numerical-models]
---

A price of $1.25$ stored in cents has integer coefficient 125. Multiply it by a quantity of $2.50$, also stored with two decimal places, and the integer multiplication gives $125\cdot250=31250$. Now the denominator is $100\cdot100=10000$, so the product is $3.125$. Nothing has rounded, but the product needs a different scale from either input.

FloatLib puts that scale in the type: addition at two fractional digits stays at two, while this multiplication returns a value at four. Returning to cents would require a rounding decision. Keeping all four fractional digits lets the multiplication theorem state an exact rational equality.

## Exact fixed point: scaled integers

A fixed-point number is an integer with an agreed denominator. [[FloatLib.Floats.Formats.FixedPoint.Code]] at radix $\beta$ with $d$ fractional digits stores one field, `coefficient : Int`, and [[FloatLib.Floats.Formats.FixedPoint.Code.toRat]] divides it by `scale`, which is $\beta^d$. For the radix we use a [[FloatLib.Numerics.Radix]], a natural base with a proof that it is at least two, and the library comes with two of them, [[FloatLib.Numerics.decimalRadix]] and `binaryRadix`. So the value set is

$$\left\{ \frac{m}{\beta^d} : m \in \mathbb{Z} \right\},$$

an evenly spaced grid with no exponent, no signed zero, no infinity, and no NaN. Because the coefficient is a Lean `Int`, this unbounded family can't overflow. Its proofs use $\mathbb{Q}$ and not $\mathbb{R}$, since every value on the grid is rational and the decoder is an ordinary executable function. That means Lean can settle concrete goals about decoded values by computation. Here are the integer calculations for our price and quantity. Their sum keeps two fractional digits, and their product has four:

```lean
open FloatLib.Numerics
open FloatLib.Floats.Formats

def price : FixedPoint.Code decimalRadix 2 := { coefficient := 125 }
def quantity : FixedPoint.Code decimalRadix 2 := { coefficient := 250 }

#eval FixedPoint.Code.add price quantity
-- { coefficient := 375 }
#eval FixedPoint.Code.toRat (FixedPoint.Code.add price quantity)
-- 15 / 4
#eval FixedPoint.Code.mul price quantity
-- { coefficient := 31250 }
#eval FixedPoint.Code.toRat (FixedPoint.Code.mul price quantity)
-- 25 / 8
```

Adding the coefficients gives $125+250=375$, which represents $3.75$. Any two integers add to another integer, which is why the fixed-point grid is closed under addition, and nothing in this operation rounds. [[FloatLib.Floats.Formats.FixedPoint.add_refines]] states the contract with the same system three times and rational addition as the specification.

Multiplication is exact too, but it changes the scale. The product of $m/\beta^p$ and $n/\beta^q$ is $mn/\beta^{p+q}$, so `mul` takes codes at scales $p$ and $q$ and returns one at scale $p + q$. In our example, coefficient 31250 at scale four is $3.125$, and getting back to either input scale would take a rescaling operation of its own, with its own rounding policy and proof. You can see the scales in both theorem types. Addition uses the same system for both inputs and the output, and multiplication uses scales $p$, $q$, and $p+q$:

```lean
#check @FixedPoint.add_refines
-- @FixedPoint.add_refines : ∀ {radix : Radix} {fractionalDigits : ℕ},
--   Operation.Finite2 (FixedPoint.numericalSystem radix fractionalDigits)
--     (FixedPoint.numericalSystem radix fractionalDigits) (FixedPoint.numericalSystem radix fractionalDigits)
--     FixedPoint.Code.add fun left right => left + right
#check @FixedPoint.mul_refines
-- @FixedPoint.mul_refines : ∀ {radix : Radix} {p q : ℕ},
--   Operation.Finite2 (FixedPoint.numericalSystem radix p) (FixedPoint.numericalSystem radix q)
--     (FixedPoint.numericalSystem radix (p + q)) FixedPoint.Code.mul fun left right => left * right
```

Most of the proof work is in the decoding equations, `toRat_add` and [[FloatLib.Floats.Formats.FixedPoint.Code.toRat_mul]], where the second one uses $\beta^{p+q} = \beta^p \beta^q$. With those in hand, the contracts [[FloatLib.Floats.Formats.FixedPoint.add_refines]], `neg_refines`, `sub_refines`, and `mul_refines` take one line each. All of them are registered with the `numerics` automation, which computes the answer for concrete codes and picks the contract we need for symbolic represented values.

```lean
example : FixedPoint.Code.toRat (FixedPoint.Code.mul price quantity) = 25 / 8 := by
  unfold price quantity
  numerics

example {a b : ℚ}
    (x : FixedPoint.AtFinite decimalRadix 2 a)
    (y : FixedPoint.AtFinite decimalRadix 2 b) :
    FixedPoint.AtFinite decimalRadix 2 (a + b) :=
  numerics_refine (FixedPoint.Code.add x.1 y.1)

example {a b : ℚ}
    (x : FixedPoint.AtFinite decimalRadix 2 a)
    (y : FixedPoint.AtFinite decimalRadix 3 b) :
    FixedPoint.AtFinite decimalRadix (2 + 3) (a * b) :=
  numerics_refine (FixedPoint.Code.mul x.1 y.1)
```

The third example multiplies values at different scales, and the `2 + 3` in its result type records the sum of their fractional digit counts. Division, square root, fused multiply-add, and transcendental functions can produce values off the grid, so they'd need a rounding policy, and the exact family provides none of them.

## Fixed-point operators and literals

`FixedPoint` makes the same codes available through the `ExecFloat` interface. Ordinary `+` and `-` use the usual `ExecFloat.Add` and `ExecFloat.Sub` instances, and unary minus is a `Neg` instance straight on the integer kernel. For addition and subtraction the integer kernels above double as the reference definitions, so their certificates, such as `addCertified`, are immediate, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] connects the public operation to its specification. Multiplication skips `ExecFloat.Mul`, and you call `mul` itself, with the composed scale in its result type. Even with exact addition, literals need a rounding rule. A natural literal is embedded exactly by multiplying by the scale. A decimal literal such as `1.25` starts as the exact rational the parser produces, and then `roundRat` rounds it once to the nearest grid coefficient with ties to even, using [[FloatLib.Numerics.roundRatEven]]. At no point does it pass through a host floating-point value. Here are a few literals in cents:

```lean
open FloatLib.Floats

abbrev Cents := ExecFloat.FixedPoint decimalRadix 2

def a : Cents := 1.25
def b : Cents := 2.5

#eval ExecFloat.FixedPoint.toRat (a + b)
-- 15 / 4
#eval ExecFloat.FixedPoint.coefficient (0.125 : Cents)
-- 12
#eval ExecFloat.FixedPoint.coefficient (0.375 : Cents)
-- 38

example : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b
```

At two decimal digits, $0.125$ is $12.5$ hundredths. That's a tie, so it rounds to the even coefficient 12. The other literal, $0.375$, is $37.5$ hundredths and rounds to the even neighbour 38. Away from a midpoint, rounding selects the closer coefficient. Converting from another system follows the same rule. There `run` rounds a finite rational once and reports whether the result was inexact, and it rejects an infinity or an exceptional value, because the grid has no code for either (`run_infinity`).

## Bounded fixed point and overflow

If the coefficient has to fit a fixed-width word, [[FloatLib.Floats.Formats.FixedPoint.Bounded.Code]] takes a third parameter, a width, and stores its coefficient in [[FloatLib.Numerics.Representations.FixedInt]], a signed two's-complement word of that many bits. Its Lean type keeps the radix and scale, while the runtime value is just `FixedInt width`. At width $w$ the value set is

$$\left\{ \frac{m}{\beta^d} : -2^{w-1} \le m \le 2^{w-1} - 1 \right\},$$

so a coefficient sum outside this interval needs an overflow policy. The same sum below is wrapped, rejected, or saturated:

```lean
open FloatLib.Numerics.Representations

abbrev Q8 := FixedPoint.Bounded.Code decimalRadix 2 8

def big : Q8 := FixedInt.ofInt 120
def small : Q8 := FixedInt.ofInt 16

#eval FixedPoint.Bounded.toRat decimalRadix 2 (FixedPoint.Bounded.wrapAdd big small)
-- -6 / 5
#eval FixedPoint.Bounded.checkedAdd big small
-- none
#eval FixedPoint.Bounded.toRat decimalRadix 2 (FixedPoint.Bounded.saturatingAdd big small)
-- 127 / 100
#eval FixedPoint.Bounded.toRat decimalRadix 4 (FixedPoint.Bounded.wrapMul 16 big small)
-- 24 / 125
#eval FixedPoint.Bounded.checkedMul 8 big small
-- none
```

In exact arithmetic the coefficient sum is 136, which doesn't fit in eight signed bits. `wrapAdd` is `BitVec` addition, so the coefficient is reduced into $[-128, 127]$ and becomes $-120$, the value $-1.20$. Two positive numbers just added up to a negative one, which is exactly what wrapping means :) Meanwhile `checkedAdd` returns `none`, and `saturatingAdd` clamps to 127, the value $1.27$. Three correctness statements describe these different results. `wrapAdd_refines` is a total `Finite2` contract against `wrapAddValue`, a function that adds the recovered coefficients and applies the centered remainder `Int.bmod` modulo $2^w$. `checkedAdd_refines` is a `Checked2On` contract whose specification is plain rational addition and whose precondition is [[FloatLib.Numerics.Representations.FixedInt.InRange]] on the exact coefficient sum. `saturatingAdd_refines` is against exact coefficient addition followed by `clamp`. Every checked and saturating contract carries a hypothesis that the width is positive, which the three wrapping contracts don't need.

Multiplication takes the destination width as an argument. A product can need the sum of the operand widths, but you get to choose how many bits to store. `wrapMul` sign-extends or truncates both operands to that width and multiplies them as bit vectors. In the [bounded arithmetic definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Bounded/Core.lean) we describe this as exact multiplication followed by centered reduction, and `wrapMul_refines` proves it against `wrapMulValue` at the composed scale. In the example, $120 \times 16 = 1920$ fits sixteen bits, so the wrapped product at scale four is $0.1920$ with nothing lost, while `checkedMul` into eight bits returns `none`. Checked and saturating multiplication compute the exact `Int` product and then test or clamp it, and their contracts are `checkedMul_refines` and `saturatingMul_refines`.

```lean
example {a b : ℚ}
    (x : FixedPoint.Bounded.AtFinite decimalRadix 2 8 a)
    (y : FixedPoint.Bounded.AtFinite decimalRadix 2 8 b) :
    FixedPoint.Bounded.AtFinite decimalRadix 2 8
      (FixedPoint.Bounded.saturatingAddValue decimalRadix 2 8 a b) :=
  numerics_refine (FixedPoint.Bounded.saturatingAdd x.1 y.1)

example {a b : ℚ}
    (h : FixedInt.InRange 8
      (FixedPoint.Bounded.coefficientOf decimalRadix 2 a +
        FixedPoint.Bounded.coefficientOf decimalRadix 2 b))
    (x : FixedPoint.Bounded.AtFinite decimalRadix 2 8 a)
    (y : FixedPoint.Bounded.AtFinite decimalRadix 2 8 b) :
    (FixedPoint.Bounded.numericalSystem decimalRadix 2 8).At (.finite (a + b)) :=
  Operation.Checked2On.applyAt (FixedPoint.Bounded.checkedAdd_refines (by decide)) h x y
```

`At (.finite v)` is the general form of `AtFinite v`, a code together with a proof that it denotes `v`. To use a checked contract, you give `applyAt` the precondition and two represented inputs, and it returns the represented output, since under those hypotheses the contract rules out `none`.

In the second example, `coefficientOf` recovers the integer coefficient of a rational at a given scale, and by `coefficientOf_toRat` this recovery is exact on every stored value. So the hypothesis `h` is a statement about the scalars $a$ and $b$, and `(by decide)` proves that width 8 is positive. Under `h` the checked sum denotes $a + b$. Without it, you can handle `none` or pick the wrapping or saturating operation and its specification. Converting into a bounded grid runs into the same choice, so [[FloatLib.Floats.ExecFloat.BoundedFixedPoint.OverflowPolicy]] names the three options `reject`, `wrap`, and `saturate`. On the configured type `ExecFloat.BoundedFixedPoint` it's the `(overflow := ...)` option of `ofRat`, `add`, `sub`, and `mul`. By default you get `reject`, which returns an `Option` that's empty when the coefficient doesn't fit. All three policies round to nearest with ties to even first and differ only in what they do with a coefficient that doesn't fit. Let's convert five into the same eight-bit grid under each policy:

```lean
#eval (ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix)
    (fractionalDigits := 2) (width := 8) 5).map ExecFloat.BoundedFixedPoint.coefficient
-- none
#eval ExecFloat.BoundedFixedPoint.coefficient
  (ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix)
    (fractionalDigits := 2) (width := 8) 5 (overflow := .saturate))
-- 127
#eval ExecFloat.BoundedFixedPoint.coefficient
  (ExecFloat.BoundedFixedPoint.ofRat (radix := decimalRadix)
    (fractionalDigits := 2) (width := 8) 5 (overflow := .wrap))
-- -12
```

Five is 500 hundredths, and 500 reduced into eight signed bits is $-12$. We made the default conversion reject overflow so that picking a type alias can't silently change how overflow is handled, and the [bounded-conversion implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Bounded/Configured/Conversion/Runtime.lean) explains this choice. The conversion status tells `overflow`, `saturated`, and `wrapped` apart. If you want the exact-grid theorems on a bounded value, `toUnbounded` removes the width restriction and `toUnbounded_toRat` proves that its value is unchanged.

## Logarithmic numbers: multiplication becomes addition

A logarithmic number system stores the exponent of a value in place of its significand, so multiplying means adding exponents. The idea goes back to the sign/logarithm number system of Swartzlander and Alexopoulos [@swartzlanderAlexopoulos1975], which the [logarithmic-format introduction](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Logarithmic.lean) cites. At radix $\beta$, [[FloatLib.Floats.Formats.Logarithmic.Code]] is an inductive type with two constructors, `zero` and `value negative exponent`, where the second has a sign and an unbounded integer exponent and denotes $\pm\beta^e$. Zero gets its own constructor because it has no logarithm. `mul` follows the exponent law. Zero absorbs, the signs combine by exclusive or, and the exponents add,

$$(\pm\beta^{a})(\pm\beta^{b}) = \pm\beta^{a+b},$$

with no rounding and no overflow, because the exponent is an `Int`. Let's multiply, say, eight by minus one half. Eight is $2^3$ and minus one half is $-2^{-1}$, so their product is $-2^2$, which prints as `value true 2`.

```lean
def eight : Logarithmic.Code binaryRadix := .value false 3
def minusHalf : Logarithmic.Code binaryRadix := .value true (-1)

#eval Logarithmic.Code.mul eight minusHalf
-- FloatLib.Floats.Formats.Logarithmic.Code.value true 2
#eval Logarithmic.Code.toRat (Logarithmic.Code.mul eight minusHalf)
-- -4
#eval Logarithmic.Code.toRat (Logarithmic.Code.mul eight .zero)
-- 0

example : Logarithmic.Code.mul eight minusHalf = .value true 2 := by
  numerics

example {a b : ℝ}
    (x : Logarithmic.AtFinite binaryRadix a)
    (y : Logarithmic.AtFinite binaryRadix b) :
    Logarithmic.AtFinite binaryRadix (a * b) :=
  numerics_refine (Logarithmic.Code.mul x.1 y.1)
```

Proofs for this family use $\mathbb{R}$, as they do for the binary formats, so a statement that mixes a logarithmic factor with a binary32 value needs no cast between scalar types. In proofs we decode with [[FloatLib.Floats.Formats.Logarithmic.Code.toReal]], which is noncomputable. For execution, `toRat` returns the exact rational that every value $\pm\beta^e$ has, and `cast_toRat` proves the two agree. For multiplication, [[FloatLib.Floats.Formats.Logarithmic.Code.toReal_mul]] is the decoding equation and `mul_refines` its `Finite2` contract, valid for every radix. Addition generally leaves this value set: $2^3+2^2=12$ isn't a power of two. Our exact logarithmic family therefore supplies multiplication but no addition. For same-sign operands with exponents $a\ge b$, logarithmic addition adds the correction $\log_\beta(1 + \beta^{b-a})$ to $a$, and opposite signs need a subtraction of magnitudes [@swartzlanderAlexopoulos1975]. Hardware can approximate that correction with a table or a polynomial. Supporting the operation means choosing an approximation, a tie rule, underflow behaviour, and an exponent bound. The configured carrier `Logarithmic` installs `*` through `ExecFloat.Mul`, and [[FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]] ties it to the specification. It also has a source decoder, `exactDecoder`, so you can convert values out. Converting in is another matter. It would need nearest-power, tie, underflow, and bounded-exponent policies, so there's no destination quantizer. Our exact core uses an unbounded integer exponent, and a bounded hardware encoding or a fractional logarithm field would need a further representation with its own rounding rules.

## Codebooks: assigning a value to each word

A codebook gives each bit pattern a value of its own. A one-bit table can represent $-1$ and $+1$, for example, and a two-bit table can represent $-1$, $0$, and $+1$ with one word reserved. In FloatLib, [[FloatLib.Floats.Formats.Codebook]] stores the assignment in a single field mapping every `BitVec width` to a `NumericalValue α`. Every word means something, possibly something exceptional, and `numericalSystem` uses that table as its denotation. To define arithmetic, we have to show how an operation on the words relates to the values in the table, which the bit width alone can't tell us.

Two catalog tables ship with the library. `bipolar1` is the one-bit encoding with $0 \mapsto -1$ and $1 \mapsto +1$, and `ternary2` is the two-bit encoding with $00 \mapsto 0$, $01 \mapsto +1$, $10 \mapsto -1$, and $11$ reserved. The reserved word denotes an exceptional value that carries the pattern that was read. Here are two decoded ternary words and two products:

```lean
#eval Codebook.Catalog.ternary2.denote (BitVec.ofNat 2 2)
-- FloatLib.Numerics.NumericalValue.finite (-1)
#eval Codebook.Catalog.ternary2.denote (BitVec.ofNat 2 3)
-- FloatLib.Numerics.NumericalValue.exceptional (FloatLib.Numerics.ExceptionalValue.reserved (some 3))
#eval Codebook.Catalog.ternary2.mul? (BitVec.ofNat 2 2) (BitVec.ofNat 2 2)
-- some 1#2
#eval Codebook.Catalog.ternary2.mul? (BitVec.ofNat 2 2) (BitVec.ofNat 2 3)
-- none
```

`1#2` is Lean's notation for the two-bit word 01, so the product of two $-1$ codes is the code for $+1$, and a reserved operand makes the product `none`. Since $\{-1, +1\}$ is closed under negation and multiplication, the bipolar `neg` and `mul` are total, and the bipolar `mul_refines` is a `Finite2` contract against integer multiplication. Ternary has a reserved word, so its `neg?` and `mul?` return an `Option`. Its `mul_refines` is a `Checked2` contract, which says that on two finite inputs the kernel succeeds and the result denotes the integer product. Neither table has addition, because $1 + 1$ is in neither set. For these two tables the proofs can check every word and every pair. Bipolar has two words and ternary has four, so a binary contract splits into four cases for one and sixteen for the other. Enumeration in the [codebook arithmetic proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Codebook/Arithmetic/Proof.lean) proves facts about these two tables only, and the general codebook type has no small-width restriction.

```lean
example {a b : ℤ}
    (x : Codebook.AtFinite Codebook.Catalog.bipolar1 a)
    (y : Codebook.AtFinite Codebook.Catalog.bipolar1 b) :
    Codebook.AtFinite Codebook.Catalog.bipolar1 (a * b) :=
  numerics_refine (Codebook.Catalog.bipolar1.mul x.1 y.1)

example {a b : ℤ}
    (x : Codebook.AtFinite Codebook.Catalog.ternary2 a)
    (y : Codebook.AtFinite Codebook.Catalog.ternary2 b) :
    Codebook.At Codebook.Catalog.ternary2 (.finite (a * b)) :=
  Operation.Checked2.applyAt Codebook.Catalog.ternary2.mul_refines x y
```

To quantize, the codebook looks at every finite word and picks the closest. `nearestCode` scans words in ascending order without building an intermediate list and keeps the best distance for the next comparison. It replaces the current best only on a strict improvement in $|x - c|$, so a tie goes to the lower word. If you want to inspect the table, `finiteEntries` lists the same finite words and their values. [[FloatLib.Floats.Formats.Codebook.nearestCode_spec]] proves that the selected word is finite and at least as close to $x$ as every finite word in the table. A second theorem, `nearestCode_isSome_of_denote_finite`, proves the search succeeds whenever the table has a finite word. All the scalar type needs is subtraction, negation, and a linear order, so one quantizer serves integer, rational, and real tables.

```lean
#eval Codebook.finiteEntries Codebook.Catalog.ternary2
-- [(0#2, 0), (1#2, 1), (2#2, -1)]
#eval Codebook.nearestCode Codebook.Catalog.ternary2 (5 : ℤ)
-- some 1#2
#eval Codebook.nearestCode Codebook.Catalog.bipolar1 (0 : ℤ)
-- some 0#1
```

In the last quantization, zero is equidistant from $-1$ and $+1$. The lower-word tie rule chooses the code for $-1$, so nearest-word quantization needn't preserve zero when the table has no zero entry. On the configured carrier `Codebook`, the selected table is part of the type, so two tables of the same width are never interchangeable. It exposes `decode` and named values such as `negativeOne`, and you get the nearest-word quantizer as `nearest?`. A generic conversion instance would also need an application policy for reserved words and ties, so callers choose `nearest?` explicitly.

## Affine quantization

[[FloatLib.Numerics.Quantization.AffineQuantizer]] implements the scale-and-zero-point scheme used for integer neural network inference, described by [Jacob and colleagues (2018), §2.1](https://openaccess.thecvf.com/content_cvpr_2018/html/Jacob_Quantization_and_Training_CVPR_2018_paper.html). It has a positive rational `scale`, an integer `zeroPoint`, and a nonempty code interval from `qmin` to `qmax`. To quantize an exact rational $x$, it computes $\operatorname{roundEven}(x / s) + z$ with [[FloatLib.Numerics.roundRatEven]] and then clamps the result into the code interval with the shared saturating clamp. Dequantizing a code $k$ returns $s\,(k - z)$. With exact rational parameters, what a code means doesn't depend on host floating-point arithmetic, and a tensor library can apply the same scalar operation pointwise. With scale $s=\tfrac14$, zero point $z=3$, and codes 0 through 7, we can work through the quantization exactly. Reconstruction assigns these codes the values

$$
-\tfrac34,\quad -\tfrac12,\quad -\tfrac14,\quad 0,\quad
\tfrac14,\quad \tfrac12,\quad \tfrac34,\quad 1.
$$

Code 3 represents zero, which leaves three steps below it and four above. Move the zero point and you reallocate the codes between negative and positive values, while the scale still fixes the distance between neighbours. Say we quantize $\tfrac58$. Dividing by the scale gives $\tfrac52$, ties to even rounds that to 2, and adding the zero point gives code 5. Reconstruction subtracts 3 again and multiplies by $\tfrac14$, which gives $\tfrac12$.

| Input | Input divided by scale | Nearest-even integer | Code before clamp | Stored code | Reconstruction |
| --- | --- | --- | --- | --- | --- |
| $\tfrac58$ | $\tfrac52$ | 2 | 5 | 5 | $\tfrac12$ |
| $\tfrac78$ | $\tfrac72$ | 4 | 7 | 7 | 1 |
| 2 | 8 | 8 | 11 | 7 | 1 |

Both of the first two reconstructions are off by $\tfrac18$, exactly half the step. Their stored codes are odd because the zero point is odd, and if you moved the zero-point addition inside the rounding, these ties would change. As `rawCode` specifies, nearest-even applies to the coefficient before the offset. To derive the error bound, write the rounded integer as $r=\operatorname{roundEven}(x/s)$. When the clamp leaves the code alone, reconstruction gives

$$
s\bigl((r+z)-z\bigr)-x
=s\left(r-\frac{x}{s}\right),
\qquad
\left|s\left(r-\frac{x}{s}\right)\right|\le\frac{s}{2}.
$$

The offset cancels, and because the scale is positive, the integer half-step bound passes through the multiplication. The table's last row shows why the theorem checks the *raw* code against the interval. Input 2 rounds exactly to integer 8, but code 11 is outside the interval and clamps to 7. So its reconstructed value is 1, an error of 1, even though there was no rounding error before the clamp, and the half-step conclusion no longer holds. Going the other way, the round-trip theorem starts from a stored code. For code 6, reconstruction gives $\tfrac34$, dividing by the scale recovers the integer 3 exactly, and adding the zero point gets back to 6. In general the recovered coefficient is $k-z$, already an integer, so rounding changes nothing, and the in-range hypothesis prevents clipping. All the descriptor itself requires is a positive scale and an ordered code interval. Its zero point doesn't have to lie inside that interval, and `dequantize_zeroPoint` is an algebraic identity even when that code can't be stored.

`quantize_mem` says every quantized code lies in the interval, and `dequantize_zeroPoint` says the zero point means exactly zero. By `quantize_dequantize`, every in-range code survives a round trip. When the clamp is inactive, `dequantize_quantize_error_le` puts the reconstructed value within half a step, $s / 2$, of the input, and that error bound comes from the half bound on `roundRatEven`.

Each quantizer is also a numerical system, `AffineQuantizer.numericalSystem`, whose codes denote their exact reconstruction, and there `numericalSystem_quantize_error_le` states the same half-step bound using `Represents`. By definition the executable quantizer satisfies the `QuantizerOn` contract onto its own reconstructed value, so the generic quantization automation can use it. It has no configured `ExecFloat` carrier and no arithmetic on its codes. It's a conversion, and whatever arithmetic comes next belongs to the integer system that receives the codes. [[FloatLib.Numerics.Quantization.RealAffineQuantizer]] also accepts irrational scales and inputs, and it takes its integer rounder as an argument. Its order theorem needs a monotone rounder and its code round-trip theorem needs one that fixes integers, and with a nearest rounder the same $s/2$ bound holds when clipping is inactive. For every rational input, clipped or not, [[FloatLib.Floats.Formats.Flocq.affine_toReal_quantize]] proves that the rational implementation agrees with the real nearest-even specification. The block below is a whole file, so you can paste it into a fresh Lean file and try it:

```lean standalone
import FloatLib

open FloatLib.Numerics.Quantization
open FloatLib.Floats.Formats.Flocq

def offsetGrid : AffineQuantizer where
  scale := 1 / 4
  zeroPoint := 3
  qmin := 0
  qmax := 7
  scale_pos := by norm_num
  codeRange := by norm_num

#eval ([5 / 8, 7 / 8, 2] : List Rat).map offsetGrid.quantize
-- [5, 7, 7]

example (x : ℚ) :
    offsetGrid.toReal.quantize nearestEven (x : ℝ) = offsetGrid.quantize x :=
  affine_toReal_quantize offsetGrid x
```

## One exponent for a block of values

In a block-scaled format, several stored integers share one exponent, and you need that exponent to recover the value of each entry. A [[FloatLib.Floats.Formats.Block.SharedScaleCode]] with `lanes` entries holds one `exponent : Int` and a `Vector Int lanes` of significands. From these, `decode` produces a `Vector Rat lanes` whose lane $i$ is

$$s_i \cdot 2^{e},$$

with `scale` supplying the power of two. As far as `NumericalSystem` is concerned, the decoded "scalar" is the whole rational vector, because each lane depends on the shared exponent stored beside it. We follow the layout of the OCP microscaling specification [@ocpMx], which the [shared-scale definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/SharedScale/Core.lean) cites, but our version stays independent of any element width or scale-selection policy. Quantizing a block starts with choosing its shared exponent. [[FloatLib.Floats.Formats.Block.quantizeAt]] takes that exponent as an argument and rounds each lane to the nearest integer multiple of $2^e$ with ties to even, using the same [[FloatLib.Numerics.roundRatEven]] as the fixed-point literals. For a nonempty block, decoding and quantization compute the shared scale once and reuse it across the lanes. Let's quantize, say, the vector $[1/3,5/4,-7/8,100]$ twice. Exponent $-2$ gives a spacing of $1/4$, and changing only the exponent to 3 makes the spacing eight:

```lean
def lanes : Vector Rat 4 := #v[1/3, 5/4, -7/8, 100]
def block : Block.SharedScaleCode 4 := Block.quantizeAt (-2) lanes

#eval block.significands.toArray
-- #[1, 5, -4, 400]
#eval (Block.decode block).toArray
-- #[1 / 4, 5 / 4, -1, 100]
#eval (Block.decode (Block.quantizeAt 3 lanes)).toArray
-- #[0, 0, 0, 96]

example : Block.QuantizesAt (-2) lanes block :=
  Block.quantizesAt_quantizeAt (-2) lanes
```

With exponent $-2$ the step is a quarter. One third is $4/3$ quarters and rounds to 1, five quarters is exactly 5, and minus seven eighths is $-3.5$ quarters, which rounds to the even value $-4$. The lane holding 100 is 400 quarters. With exponent 3 the step is eight, so the three small lanes round to zero, and 100 is $12.5$ eights, which rounds to 12 and decodes to 96. The kernel accepts both. You supply the exponent and the representation never chooses one for you, which is what lets the [configured block implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Configured/Runtime.lean) support different calibration methods. Whichever exponent you pick, the theorems in the [configured block proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Configured/Proof.lean) hold. In the finer grid, the lane holding 100 needs an unbounded coefficient. At a quarter-step it needs coefficient 400, which wouldn't fit an eight-bit signed lane whose maximum is 127, but this family stores an `Int`, so it keeps 400 exactly. At step eight the rounded coefficient is only 12, but the three smaller values all disappear. In the spacing figure, the three shared-scale rows show the same expansion of the grid, and every lane moves to the coarser grid together, including lanes that needed the finer spacing. For bounded elements, the [standard MX quantizer](#/chapter/low-precision-formats-for-machine-learning/choosing-a-scale-for-32-lanes) makes the scale choice and proves a nearest-error property at the scale it selects.

`QuantizesAt` states the result. It says the stored exponent is the one supplied and every lane is the ties-to-even rounding of the input divided by the scale. Then `quantizesAt_quantizeAt` proves the kernel satisfies this rule. [[FloatLib.Floats.Formats.Block.quantizeAt_refines]] exposes the same relation through the common quantization interface, and `decode_quantizeAt_get` gives each decoded lane in closed form. For any format, the `BlockScaled` contract says you recover a block's values by applying its scale to each stored lane. `blockScaled_sharedScale` proves this for the shared-scale family, decoding a stored significand as $s \cdot 2^e$. With the configured carrier `SharedScale`, you pass the shared exponent as the conversion instance's context. There's no default shared exponent, and the [block-conversion implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Configured/Conversion/Runtime.lean) requires it as an argument. Converting an infinity or an exceptional value fails, because the block has no code for either.

In the concrete OCP MX formats of [chapter 11](#/chapter/low-precision-formats-for-machine-learning), both the scale and the elements are bounded. In the [scale encoding](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/E8M0/Core.lean), E8M0 codes 0 through 254 denote $2^{c-127}$ and code 255 is NaN, and element words can be nonfinite too. The array API supplies checked finite decoders. Both [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines]] and [[FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines]] are `Checked2` contracts, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeBlock?]] extends them to an array. The standard 32-lane API also decodes each lane with its exceptional class, so a finite scale can sit next to a NaN element and finite neighbours. In both APIs a finite power-of-two scale is exact exponent arithmetic and adds no rounding of its own.

## Stating the arithmetic guarantees

For the fixed-point sum above, correctness means that decoding coefficient 375 at scale two gives $1.25 + 2.50$. For ternary multiplication, it means that the word returned for $(-1)\times(-1)$ decodes to $+1$, and that a reserved input is rejected. With the common definitions from [chapter 06](#/chapter/the-numerical-models) we can state both results without prescribing how either family stores its values. A [[FloatLib.Numerics.NumericalSystem]] specifies the stored type and its decoder, and a decoded value can be finite, infinite, or exceptional. [[FloatLib.Numerics.NumericalSystem.Represents]] says that a stored value decodes to a particular finite scalar, and [[FloatLib.Numerics.NumericalSystem.AtFinite]] packages the stored value with a proof of that fact. Lean erases this proof when it compiles the program. The operation specifications differ in when they guarantee a result:

- [[FloatLib.Numerics.Operation.Finite2]] covers a total operation on finite inputs. Fixed-point addition and logarithmic multiplication satisfy it.
- [[FloatLib.Numerics.Operation.Checked2]] covers an operation returning an `Option`. It guarantees success on finite inputs, as with ternary multiplication, where neither input can be the reserved word.
- [[FloatLib.Numerics.Operation.Checked2On]] also requires a hypothesis about the decoded inputs. Bounded checked addition needs the exact coefficient sum to fit the destination width. Under that hypothesis it returns a value representing the rational sum.

Each specification names separate systems for the two operands and the result, which is how fixed-point multiplication can take scales $p$ and $q$ and return scale $p+q$. Mixed-format multiply-add uses the same definition, and there the operands and accumulator may have different formats. Here are all the grids we've used, drawn together. Fixed point has uniform spacing, and the logarithmic row shows a finite window of powers, which continue toward zero beyond the displayed exponents. Changing a shared exponent moves every lane onto a different grid. Bipolar and ternary have only the few values listed in their definitions.

![Value grids from -8 to 8 for fixed point with two fractional bits, E2M3, a logarithmic window with exponents -4 to 3, shared scales at exponents -2, 0 and 2, ternary with one reserved code, and bipolar; the logarithmic grid continues towards zero](assets/ch16-spacing.png "Value spacing on a common linear axis; the logarithmic row shows a finite window.")

<a id="finding-these-representations-in-the-source"></a>

## Using the proofs and inspecting operations

Our [fixed-point](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Automation.lean), [logarithmic](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Logarithmic/Automation.lean), and [codebook](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Codebook/Automation.lean) automation modules register decoding equations in `numerics_simps` and register contracts as safe rules in the shared `Numerics` Aesop rule set. Those rules are what the examples' `numerics` and `numerics_refine` calls run on. For the block family you apply the theorems by hand. `#float_info` lists the available operations and guarantees, including fixed-point multiplication's change of scale. You'll find the main results in the [theorem index](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md), and their correctness rests on kernel-checked proofs. These families haven't had independent external comparisons like the ones [chapter 19](#/chapter/external-validation) reports for binary formats and posits.
