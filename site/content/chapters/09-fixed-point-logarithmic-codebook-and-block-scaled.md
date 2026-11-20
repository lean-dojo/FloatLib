---
number: "09"
slug: fixed-point-logarithmic-codebook-and-block-scaled
title: Fixed point, logarithmic and other formats
summary: How to use fixed point, logarithmic numbers, codebooks, affine quantization and block-scaled formats in Lean, and what FloatLib proves about each one.
phases: [exact-and-quantized, numerical-models]
---

A fixed-point program that multiplies $1.25$ by $2.50$ has to choose a scale for the result. With two decimal places the operand coefficients are $125$ and $250$. Their product is $31250$ at a scale of $10^{-4}$, exactly $3.125$. Keeping the original scale would require rounding.

FloatLib records that choice in the type of the operation. Fixed-point multiplication can return a result with four decimal places. Logarithmic formats, codebooks and block-scaled formats have different rules for decoding a stored value, so each has its own theorem connecting arithmetic on codes to arithmetic on their values.

## What is a fixed-point number?

A fixed-point number is an integer with an agreed denominator. [[FloatLib.Floats.Formats.FixedPoint.Code]] takes a radix $\beta$, the number base, and a count $d$ of fractional digits, and it stores one integer field, `coefficient : Int`. [[FloatLib.Floats.Formats.FixedPoint.Code.toRat]] divides it by `scale`, which is $\beta^d$. So the value set is

$$\left\{ \frac{m}{\beta^d} : m \in \mathbb{Z} \right\},$$

an evenly spaced grid, with no exponent, signed zero, infinity or NaN (not a number). The radix is a [[FloatLib.Numerics.Radix]], a natural base of at least two, such as [[FloatLib.Numerics.decimalRadix]] or `binaryRadix`. The coefficient is a Lean `Int`, which grows as needed, so it can't overflow. The proofs work in $\mathbb{Q}$, the rationals, where Lean can settle a goal about a particular value by computing it.

## How to add and multiply fixed-point numbers

Let's look at the price and the quantity as codes, added and multiplied:

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

Adding the coefficients gives $125+250=375$, which is $3.75$, and nothing rounds. Multiplication is exact too, but it moves the scale: $m/\beta^p$ times $n/\beta^q$ is $mn/\beta^{p+q}$, so `mul` returns scale $p + q$, and rescaling back to cents would need its own rounding policy. You can see the scales in the theorem types:

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

[[FloatLib.Floats.Formats.FixedPoint.add_refines]] is the addition contract, the theorem that says what its result means. Both inputs and the output live in one system, and the specification is plain rational addition. `Finite2`, as its name says, marks a two-input operation that always succeeds on finite inputs.

## How to prove facts about fixed-point results

The proof work is in the decoding equations `toRat_add` and [[FloatLib.Floats.Formats.FixedPoint.Code.toRat_mul]], which give the decoded sum and product, and each contract follows in a line. For a specific code the `numerics` tactic computes the answer, and for a symbolic value it picks the contract. A value of type `FixedPoint.AtFinite decimalRadix 2 a` is a code together with a proof that it means $a$, and `numerics_refine` builds one from a code you computed. Here are some examples:

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

Look at the `2 + 3` in the third example's result type. It's the sum of the two scales, so the type does the bookkeeping. Division, square root, fused multiply-add ($a \cdot b + c$ in one step) and transcendental functions are another matter. They can land off the grid and would need a rounding policy, so this exact family, where nothing rounds, doesn't provide them.

## How to write sums and decimal literals

To write plain `a + b` and `1.25`, use `ExecFloat.FixedPoint`, one of FloatLib's *configured* types, the ones you compute with. It puts the same codes behind `ExecFloat`, FloatLib's common interface for such numbers, so `+`, `-` and unary minus work, and [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] connects the public operation to its specification. Multiplication skips `ExecFloat.Mul`, so you call `mul` itself, with the composed scale in its result type.

Literals are where rounding comes in. A natural-number literal goes in exactly. A decimal literal such as `1.25` is parsed as an exact rational, and `ofRat` rounds it once to the nearest coefficient, ties to even, with [[FloatLib.Numerics.roundRatEven]], never through a host floating-point value. Here's a type of cents and a few literals:

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
#eval ExecFloat.FixedPoint.coefficient (.ofRat (1 / 3) : Cents)
-- 33

example : a + b = ExecFloat.Spec.add a b :=
  ExecFloat.Proof.add_eq_spec a b
```

$0.125$ is $12.5$ hundredths, a tie, so it goes to the even coefficient 12. $0.375$ goes to its even neighbour 38, and one third is 33 cents. Conversion from another numerical system follows the same rule: `run` rounds a finite rational once, reports whether the result was inexact, and rejects an infinity or an exceptional value such as NaN, which the grid has no code for (`run_infinity`). We'll come back to these systems at the end.

## What happens when a fixed-point number overflows?

When the coefficient has to fit a machine word, [[FloatLib.Floats.Formats.FixedPoint.Bounded.Code]] takes a width and stores the coefficient in a [[FloatLib.Numerics.Representations.FixedInt]], a signed two's-complement word of that many bits. Two's complement is the usual way computers store signed integers. At width $w$ the value set is

$$\left\{ \frac{m}{\beta^d} : -2^{w-1} \le m \le 2^{w-1} - 1 \right\},$$

so a sum outside this interval needs an overflow policy. Let's look at one sum done three ways, wrapped, rejected and saturated, then two products:

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

The exact coefficient sum is $136$, outside the range of an eight-bit signed integer. `wrapAdd` uses `BitVec` addition modulo $256$, so the stored coefficient represents $-120$, giving the value $-1.20$. `checkedAdd` returns `none` because the exact coefficient is out of range. `saturatingAdd` returns the largest coefficient, $127$. Multiplication also takes a destination width: $120\times16=1920$ fits in sixteen bits and denotes $0.1920$ at scale four, while `checkedMul` into eight bits returns `none`.

## What does each overflow policy promise?

Wrapping has a total `Finite2` contract against the exact coefficient sum reduced by `Int.bmod` modulo $2^w$, using signed representatives centred on zero. Checked addition has a `Checked2On` contract against rational addition, with [[FloatLib.Numerics.Representations.FixedInt.InRange]] on the exact coefficient sum as its precondition. The theorem `checkedAdd_refines` guarantees success on finite inputs satisfying this condition. Saturating addition has a contract against exact addition followed by `clamp`. These contracts, and the wrapping contracts for subtraction and multiplication, hold at every width, including zero.

The [bounded arithmetic definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Bounded/Core.lean) makes `wrapMul` exact multiplication followed by centered reduction, and `wrapMul_refines` proves it against `wrapMulValue` at the composed scale. Checked and saturating multiplication test or clamp the exact `Int` product, each with its own contract. Here are the saturating and checked addition contracts at work:

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
  Operation.Checked2On.applyAt FixedPoint.Bounded.checkedAdd_refines h x y
```

In the second example, `At (.finite v)` is the general form of `AtFinite v`. Hand `applyAt` the precondition and two represented inputs and you get the represented output. `coefficientOf` recovers a rational's coefficient, and `coefficientOf_toRat` says the recovery is exact on stored values, so `h` is about the scalars $a$ and $b$.

## How to choose an overflow policy

The configured type `ExecFloat.BoundedFixedPoint` leaves the choice to you. An [[FloatLib.Floats.ExecFloat.BoundedFixedPoint.OverflowPolicy]] is one of `reject`, `wrap` or `saturate`, and you pass it as the `(overflow := ...)` option of `ofRat`, `add`, `sub` and `mul`. All three policies first round to nearest, ties to even. The default, `reject`, returns `none` when the coefficient doesn't fit:

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

Five is 500 hundredths, and 500 wrapped into eight signed bits is $-12$. Ask for five and get minus twelve cents. That's why the default rejects overflow: picking a type alias can't quietly change how overflow is handled. The status from the [bounded-conversion implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Bounded/Configured/Conversion/Runtime.lean) tells `overflow`, `saturated` and `wrapped` apart, and `toUnbounded` drops the width, with `toUnbounded_toRat` proving the value unchanged.

## How does this follow Embedded C?

Embedded C (ISO/IEC TR 18037) is the standard for fixed-point types in C: `_Fract` and `_Accum`, with saturating and rounding operations. FloatLib follows the committee draft WG14 N1169 [@wg14N1169], and has one family for it, `FixedPoint.Embedded`, with the layout (signedness, integer and fractional widths), the rounding choice and the overflow policy as parameters. It covers the usual conversions and operators, the `stdfix.h` functions and limits, shifts, constants and the text conversions. Here are the four arithmetic operators on the greatest `short fract` value, $127/128$, and the least positive one, $1/128$, at a layout with 8-bit `short fract`:

```lean
section EmbeddedC

open FloatLib.Floats.Formats.FixedPoint.Embedded FloatLib.Floats.Formats.FixedPoint.Embedded.Examples

-- the sum and the quotient overflow, the difference is 63/64, the product rounds to 1/128
example :
    [(Binary.«+» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Binary.«-» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Binary.«*» Layout.example environment shortFract shortFract top unit).map Format.decode,
      (Binary.«/» Layout.example environment shortFract shortFract top unit).map Format.decode] =
      [none, some (63 / 64), some (1 / 128), none] := by
  decide +kernel

end EmbeddedC
```

| Clause of N1169 | Operations | In FloatLib |
| --- | --- | --- |
| 4.1.1, 4.1.2 | the types `_Fract`, `_Accum` and `_Sat` | `Embedded.CType`, `Embedded.Layout` |
| 4.1.3, 4.1.4 | rounding, overflow and saturation of a conversion | `Embedded.Rounding`, `Embedded.Overflow`, `Embedded.convert`, `Embedded.toInteger` |
| 4.1.5 | constants | `Embedded.Constant.parse` |
| 4.1.6.1 | `++`, `--`, unary `+`, `-` and `!` | `Embedded.Prefix`, `Postfix`, `Unary` |
| 4.1.6.2 | `+`, `-`, `*`, `/`, `<<`, `>>`, the comparisons, and `mulifx`, `divifx`, `fxdivi`, `idivfx` | `Embedded.Binary`, `IntegerLeft`, `Compare`, and `mulir`, `divir`, `rdivi`, `idivr` with their siblings |
| 4.1.6.3 | assignment and compound assignment | `Embedded.Assignment` |
| 4.1.7 | `absfx`, `roundfx`, `countlsfx`, `bitsfx`, `fxbits` | the same names with their type suffixes, such as `abshr` and `roundhr` |
| C 7.18a.2, 7.18a.3 | the `stdfix.h` limits | `SFRACT_FBIT`, `SFRACT_MAX` and their siblings |
| C 7.18a.6.8 | `strtofxfx` | `strtofxhr` and its siblings |
| 4.1.9 | the fixed-point conversions of `fprintf` and `fscanf` | `Embedded.Formatted.fprintf`, `fscanf` |

Take two fractional bits, so that a signed fractional type has spacing $1/4$ and the range $[-1, 3/4]$. With nearest-even rounding, converting $7/8$ first rounds to $1$, and only then does the result need an overflow decision. Clipping the exact input before rounding would hide that step, and it can change what an unsaturated conversion is allowed to do. So here too rounding comes before overflow, as the document's revision notes require.

Text conversion has a boundary of its own. `1e+` isn't a complete number, but it can become one: append `0` and you get `1e+0`. Formatted input has to tell such a prefix from characters that can't begin a number. Our grammar proof does it for decimal and hexadecimal input of any length: a completing suffix exists exactly when the prefix is already accepted or appending one `0` makes it accepted. What stays outside the model is C itself: whole format strings and streams, the ABI, memory, and locales other than the C locale.

## What is a logarithmic number?

A logarithmic number system stores an exponent instead of a significand. Nonzero values have the form $\pm\beta^e$, so multiplication adds exponents and combines signs. Addition generally requires a separate approximation. [[FloatLib.Floats.Formats.Logarithmic.Code]] has two constructors: `zero` and `value negative exponent`, with a sign flag and an unbounded integer exponent. The operation `mul` returns zero if either operand is zero; otherwise it combines the signs by exclusive or and adds the exponents,

$$(\pm\beta^{a})(\pm\beta^{b}) = \pm\beta^{a+b},$$

with no rounding and no overflow. Let's try it: eight is $2^3$ and minus one half is $-2^{-1}$, so their product is $-2^2$, which prints as `value true 2`.

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

These proofs work in $\mathbb{R}$, the real numbers, like the binary formats' proofs, so mixing a logarithmic factor with a binary32 value (a 32-bit float) needs no cast. Proofs decode with the noncomputable [[FloatLib.Floats.Formats.Logarithmic.Code.toReal]], which Lean can reason about but not run. Execution uses the exact `toRat`, and `cast_toRat` proves the two agree. The decoding equation [[FloatLib.Floats.Formats.Logarithmic.Code.toReal_mul]] and the `Finite2` contract `mul_refines` hold for every radix.

## Why can't logarithmic numbers add?

Because $2^3+2^2=12$ isn't a power of two. In the sign/logarithm system of Swartzlander and Alexopoulos [@swartzlanderAlexopoulos1975], same-sign addition adds the correction $\log_\beta(1 + \beta^{b-a})$ to the larger exponent $a$. Supporting that means choosing an approximation, a tie rule, underflow behaviour and an exponent bound, so our exact family has no addition, and for the same reason the configured `Logarithmic` has no quantizer to bring values in. It does give you `*` through `ExecFloat.Mul`, tied to its specification by [[FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]], and `exactDecoder` to get values out. A bounded hardware encoding or a fractional logarithm field would need its own representation and rounding rules.

## What is a codebook?

Sometimes you want a list of values instead of a formula, a table giving the value of each bit pattern. That's a codebook. [[FloatLib.Floats.Formats.Codebook]] maps every `BitVec width`, a word of `width` bits, to a `NumericalValue α`, the word's value. Arithmetic is defined table by table, since the width alone can't say how an operation on words relates to the values. The catalog ships `bipolar1`, with $0 \mapsto -1$ and $1 \mapsto +1$, and `ternary2`, with $00 \mapsto 0$, $01 \mapsto +1$, $10 \mapsto -1$, and $11$ reserved, an exceptional value carrying the pattern that was read:

```lean
#eval Codebook.Catalog.ternary2.denote (BitVec.ofNat 2 2)
-- FloatLib.Numerics.NumericalValue.finite (-1)
#eval Codebook.Catalog.ternary2.denote (BitVec.ofNat 2 3)
-- FloatLib.Numerics.NumericalValue.exceptional (.reserved (payload := some 3))
#eval Codebook.Catalog.ternary2.mul? (BitVec.ofNat 2 2) (BitVec.ofNat 2 2)
-- some 1#2
#eval Codebook.Catalog.ternary2.mul? (BitVec.ofNat 2 2) (BitVec.ofNat 2 3)
-- none
```

Here `BitVec.ofNat 2 2` is the two-bit word 10 and `1#2` is the word 01 (value 1, width 2). Two $-1$ codes multiply to the code for $+1$, and a reserved operand gives `none`. The bipolar values $\{-1, +1\}$, the poles in its name, are closed under negation and multiplication (the results stay in the set), so bipolar `neg` and `mul` are total and its `mul_refines` is a `Finite2` contract against integer multiplication. With its reserved word, ternary's `mul_refines` is a `Checked2` contract, promising that on finite inputs the multiplication succeeds and denotes the integer product. Neither table has addition, since $1 + 1$ is in neither set. The [codebook arithmetic proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Codebook/Arithmetic/Proof.lean) enumerates every case, so it covers these two tables only, though the general type has no small-width restriction. Here are both contracts in use:

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

## How to find the nearest code

Going the other way, from a number to a code, is called quantizing, and for a codebook it's a search. `nearestCode` walks the words in ascending order, keeping the best so far, and replaces it only when the distance $|x - c|$ strictly improves, so a tie goes to the lower word. [[FloatLib.Floats.Formats.Codebook.nearestCode_spec]] proves the result is finite and at least as close to $x$ as every finite word, and another theorem proves the search succeeds when the table has a finite word. Any scalar type with subtraction, negation and a linear order works. Let's try it on both tables:

```lean
#eval Codebook.finiteEntries Codebook.Catalog.ternary2
-- [(0#2, 0), (1#2, 1), (2#2, -1)]
#eval Codebook.nearestCode Codebook.Catalog.ternary2 (5 : ℤ)
-- some 1#2
#eval Codebook.nearestCode Codebook.Catalog.bipolar1 (0 : ℤ)
-- some 0#1
```

In the last line zero sits exactly between $-1$ and $+1$, and the lower-word rule picks $-1$, so zero quantizes to minus one. On the configured `Codebook` the table is part of the type, so same-width tables never mix, and you call `nearest?` yourself, because a generic conversion would need a policy for reserved words and ties.

## What is affine quantization?

When the codes stand for evenly spaced values, [[FloatLib.Numerics.Quantization.AffineQuantizer]] computes the code with a formula in place of a table (affine means a scaling plus a shift). It implements the scale-and-zero-point scheme of integer neural network inference, described by [Jacob and colleagues (2018), §2.1](https://openaccess.thecvf.com/content_cvpr_2018/html/Jacob_Quantization_and_Training_CVPR_2018_paper.html). The `scale` determines the spacing between decoded values, and the integer `zeroPoint` is the code that decodes to zero.

Writing $s$ for the scale and $z$ for the zero point, quantizing an exact rational $x$ computes $\operatorname{roundEven}(x / s) + z$ with [[FloatLib.Numerics.roundRatEven]] and clamps it into the code interval from `qmin` to `qmax`. Dequantizing a code $k$ back to a number returns $s\,(k - z)$, so a code's meaning never depends on host floating point. With $s=\tfrac14$, $z=3$ and codes 0 through 7, the codes reconstruct to

$$
-\tfrac34,\quad -\tfrac12,\quad -\tfrac14,\quad 0,\quad
\tfrac14,\quad \tfrac12,\quad \tfrac34,\quad 1.
$$

Let's quantize $\tfrac58$ by hand. Divide by the scale to get $\tfrac52$, round to the even 2, and add the zero point: code 5, which reconstructs to $\tfrac12$. Here are three inputs taken through every step:

| Input | Input divided by scale | Nearest-even integer | Code before clamp | Stored code | Reconstruction |
| --- | --- | --- | --- | --- | --- |
| $\tfrac58$ | $\tfrac52$ | 2 | 5 | 5 | $\tfrac12$ |
| $\tfrac78$ | $\tfrac72$ | 4 | 7 | 7 | 1 |
| 2 | 8 | 8 | 11 | 7 | 1 |

**Note:** The order matters. As `rawCode` specifies, nearest-even applies before the offset, and rounding $\tfrac52 + 3$ would give 6.

## How big is the quantization error?

The first two rows are off by $\tfrac18$, half a step. With $r=\operatorname{roundEven}(x/s)$ and the clamp inactive, reconstruction gives

$$
s\bigl((r+z)-z\bigr)-x
=s\left(r-\frac{x}{s}\right),
\qquad
\left|s\left(r-\frac{x}{s}\right)\right|\le\frac{s}{2}.
$$

The offset cancels, and since the scale is positive, the integer half-step bound survives the multiplication. That needs the clamp to do nothing, so the theorem checks the *raw* code, before clamping. In the last row input 2 divides to exactly 8, but code 11 clamps to 7, an error of 1.

The descriptor, the structure holding $s$, $z$ and the code interval, asks only for a positive scale and an ordered code interval, and `dequantize_zeroPoint` holds even when the zero point lies outside it. `quantize_mem` puts every quantized code in the interval, `quantize_dequantize` brings every in-range code back from a round trip, and when the clamp is inactive, `dequantize_quantize_error_le` puts the reconstruction within $s / 2$ of the input. Each quantizer is also a numerical system whose codes denote their reconstruction, and it satisfies `QuantizerOn` by definition. But it's a conversion only, with no configured `ExecFloat` type and no arithmetic on codes.

## Can the scale be irrational?

Yes. [[FloatLib.Numerics.Quantization.RealAffineQuantizer]] accepts irrational scales and inputs and takes its integer rounder as an argument. Its order theorem (larger inputs never get smaller codes) needs a monotone rounder, its round-trip theorem one that leaves integers unchanged, and with a nearest rounder the $s/2$ bound holds when clipping is inactive. On the same grid, for every rational input, clipped or not, [[FloatLib.Floats.Formats.Flocq.affine_toReal_quantize]] proves the rational implementation matches the real nearest-even specification, as this complete Lean file shows:

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
  code_range := by norm_num

#eval ([5 / 8, 7 / 8, 2] : List Rat).map offsetGrid.quantize
-- [5, 7, 7]

example (x : ℚ) :
    offsetGrid.toReal.quantize nearestEven (x : ℝ) = offsetGrid.quantize x :=
  affine_toReal_quantize offsetGrid x
```

## What is a block-scaled format?

A financial report often says "all figures in thousands" once, at the top. Block-scaled formats do the same: a block of small numbers shares one scale, stored once. That scale moves the whole block's range and adds no precision to its elements.

FloatLib has one definition for all of them. A [[FloatLib.Floats.Formats.Block.CodedFormat]] names an element codec and a list of scale levels, each with its groups of positions and its scale codec. A [[FloatLib.Floats.Formats.Block.Tensor]] of that format stores one element code per position and one scale code per group, and position $i$ decodes to

$$e_i \cdot s_{g(i)},$$

its element times the scale of its group, times the scales of any outer levels. How a scale is chosen isn't part of the format. That is a policy, and the quantizer takes it as an argument.

The simplest instance is [[FloatLib.Floats.Formats.Block.sharedScale]]: unbounded integer elements and one power-of-two scale for the block. With the policy [[FloatLib.Floats.Formats.Block.sharedExponent]], which stores the exponent you supply, each lane is rounded to the nearest multiple of $2^e$, ties to even:

```lean
def lanes : Vector Rat 4 := #v[1/3, 5/4, -7/8, 100]
def block : Block.Tensor (Block.sharedScale (Fin 4)) :=
  (Block.sharedScale (Fin 4)).quantize (Block.sharedExponent (Fin 4) (-2)) fun lane =>
    SignedRat.ofRat lanes[lane]

#eval Array.ofFn block.elements
-- #[1, 5, -4, 400]
#eval Array.ofFn block.value
-- #[1 / 4, 5 / 4, -1, 100]
#eval Array.ofFn ((Block.sharedScale (Fin 4)).quantize (Block.sharedExponent (Fin 4) 3) fun lane =>
    SignedRat.ofRat lanes[lane]).value
-- #[0, 0, 0, 96]

example (lane : Fin 4) :
    block.elements lane = roundRatEven (lanes[lane] / (2 : ℚ) ^ (-2 : ℤ)) :=
  Block.sharedScale_elements (-2) _ lane
```

With exponent $-2$ the step is a quarter: one third rounds to 1, five quarters is exactly 5, minus seven eighths is $-3.5$ quarters and rounds to the even $-4$, and 100 is 400 quarters. With exponent 3 the step is eight, the small lanes round to zero, and 100, which is $12.5$ eights, rounds to 12 and decodes to 96.

## What is proved about a block?

Every theorem here holds for every element codec, scale codec, level structure and policy. [[FloatLib.Floats.Formats.Block.CodedFormat.value_quantize]] proves that the stored values are those of the value theory, where each element is one rounding of its input in the element format scaled by its total scale ([[FloatLib.Floats.Formats.Block.Format.reconstruct_eq]]). For a positive total scale, the element format supplies two useful bounds.

- An element's error is the element format's error budget, with the absolute part multiplied by the scale ([[FloatLib.Floats.Formats.Block.Format.abs_reconstruct_sub_le]]).
- An element is flushed to zero when its magnitude is at most the element format's zero threshold times the scale. Under a policy that chooses the scale from the largest magnitude in the block, one large element can therefore make smaller ones round to zero.

With the configured type `ExecFloat.Block` you pass the policy as the conversion context, and converting an infinity or another exceptional value into a block fails.

The named formats are instances. OCP MX has a power-of-two scale stored as E8M0, a byte that is all exponent, and its six element profiles (E5M2, E4M3, E3M2, E2M3, E2M1 and INT8) are in [the machine-learning chapter](#/chapter/low-precision-formats-for-machine-learning). Four Over Six and a fixed-point format with power-of-two scales are in the same [catalog](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Catalog.lean).

## What does a second scale add?

NVIDIA's NVFP4 (arXiv:2509.25149) stores four-bit E2M1 elements, one E4M3 scale for every block of 16, and one binary32 scale for the tensor. In the general format that is a second level in the list, with its own groups and its own codec. Its policy maps the largest magnitude of the tensor to $6 \cdot 448$ and the largest magnitude of each block to 6, the largest values of E4M3 and E2M1:

```lean
def weights : Fin 16 → ℚ := fun i => (#[21/8, -21/16, 21/64, 1/10] : Array ℚ).getD i.val 0
def stored :=
  (Block.nvfp4Stored (fun _ : Fin 16 => ()) (fun _ => ())).quantize
    (Block.nvfp4Policy (fun _ => ()) (fun _ => ())) fun i => SignedRat.ofRat (weights i)

#eval (stored.scales.2.1 ()).toNat
-- 126
#eval (List.finRange 4).map fun i : Fin 4 => stored.value ⟨i.val, by omega⟩
-- [21 / 8, -21 / 16, 7 / 16, 0]
```

The tensor scale is $2^{-10}$ and the block scale is E4M3's code 126, the value 448, so one element step is $7/16$. That makes the first two values 6 and $-3$ steps, the third three quarters of a step, a tie between a half and one that goes to the even one, and the fourth less than a quarter of a step, which is stored as zero.

That last rule is a theorem: [[FloatLib.Floats.Formats.Block.nvfp4_reconstruct_eq_zero_iff]] reads the flush rule for NVFP4 as a magnitude of at most a quarter of the block scale. Who shares a block, and so who gets flushed, is decided by the block shape. On a $16 \times 16$ tile holding the value 42 among entries of $3/4$, $1 \times 16$ blocks flush the 15 other entries of one row, and one $16 \times 16$ tile flushes all 255. Those two counts are single examples, checked in Lean's kernel. Square tiles have one property the row blocks lack: [[FloatLib.Floats.Formats.Block.nvfp4_reconstruct_transpose]] proves that quantizing the transpose is the transpose of quantizing.

Are these theorems about the real formats or about the stored codes? Both, and that took a proof. [[FloatLib.Floats.Formats.OCP.MX.Standard.Profile.codec_round_eq_real]] proves that the element codec of each OCP MX profile is, on every rational, the real rounding of its format. With it, the stored OCP MX and NVFP4 tensors with their standard selections have the values of the real formats on every tensor of finite binary32 values. Four Over Six and calibrated outer scales aren't covered by those results, though the element bounds hold for every policy.

Import `FloatLib.Floats.Formats.Block.Roundoff` and the `roundoff` commands of [Intervals and roundoff bounds](#/chapter/proving-numerical-bounds) use these budgets for a quantized element, a dot product of quantized tensors, and accumulation in a narrow accumulator that is promoted to a wide one. The [NVFP4 dot-product example](https://github.com/lean-dojo/FloatLib/blob/main/tests/FloatLibTests/Tactic/Roundoff/Block.lean#L252) shows the generated error bound.

### How exact is NVFP4's scale?

NVFP4 isn't a numerical standard. Our reference is NVIDIA's description, Appendix B of arXiv:2509.25149 included, and it leaves one thing open that matters: the working precision of the scale selection. An exact-rational formula and a sequence of binary32 operations can choose different scales or element codes near a boundary. We measured it against torchao 0.18.0: with the same scale floor, the two computations differ in 18 one-level observations and 368 two-level ones. We prove both. For the exact policy we prove the stored codes and their decoding. For the binary32 computation, `Block.nvfp4Working` is the quantizer on binary32 encodings in torchao's order: two quotients and a clamp for the scale, one reciprocal per block, one product per element. For every finite block and every finite positive outer scale, `nvfp4Working_toReal_scale` says that the stored scale is the E4M3 rounding of the two binary32 quotients clamped to $[2^{-6}, 448]$, and `nvfp4Working_toReal_element` that a stored element is the E2M1 rounding of the binary32 product. Neither needs a premise about overflow: when a quotient or a product overflows, the machine clamps an infinity and the formula clamps a number beyond the largest binary32 value, and they land on the same code. `nvfp4Working_abs_element_sub_le` is the error of an element with the binary32 unit roundoff in it. The quantizer agrees with torchao on that corpus, and with the processor's binary32 arithmetic on 271,932 words. One case has no theorem: a zero element under a reciprocal that overflowed is $0 \cdot \infty$, a NaN.

## What do all these contracts have in common?

Every contract in this chapter uses the common definitions from [Executable arithmetic and its proofs](#/chapter/the-numerical-models), which don't prescribe storage. A [[FloatLib.Numerics.NumericalSystem]] gives the stored type and a decoder to finite, infinite or exceptional values, [[FloatLib.Numerics.NumericalSystem.Represents]] says a stored value decodes to a given finite scalar, and [[FloatLib.Numerics.NumericalSystem.AtFinite]] packages the value with that proof, which compilation erases. The operation specifications differ in when they promise a result:

- [[FloatLib.Numerics.Operation.Finite2]] covers a total operation on finite inputs, such as fixed-point addition and logarithmic multiplication.
- [[FloatLib.Numerics.Operation.Checked2]] covers an operation that returns an `Option` and succeeds on finite inputs, such as ternary multiplication.
- [[FloatLib.Numerics.Operation.Checked2On]] also requires a hypothesis about the decoded inputs (the *On* in its name), such as bounded checked addition, which needs the exact coefficient sum to fit.

Each specification names its own systems for the operands and the result, so fixed-point multiplication can put its result at scale $p + q$. [Figure 9.1](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled/figure-ch16-spacing) puts every grid from this chapter on one axis, with the logarithmic row a window of powers that carries on toward zero.

![Eight rows of marks on one linear axis from −8 to 8. Fixed point with step 1/4 is an even comb. The marks of the floating-point format E2M3 are dense near zero and thin out toward −7.5 and 7.5. The logarithmic row has zero and the powers of two from 1/16 to 8 with both signs. Three shared-scale rows are even combs with steps 1/4, 1 and 4. The ternary row has −1, 0 and 1, and the bipolar row has −1 and 1](assets/ch16-spacing.png "The values between −8 and 8 that each number system of this chapter can represent, on one linear axis. The logarithmic row draws the exponents −4 to 3 only, and its values go on toward zero. The ternary codebook has a fourth code, which is reserved.")

## Where to find the proofs

The `numerics` and `numerics_refine` automation runs on rules from our [fixed-point](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Automation.lean), [logarithmic](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Logarithmic/Automation.lean) and [codebook](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Codebook/Automation.lean) automation modules, and for the block family `roundoff` has the rules above, while exact statements about codes are applied by hand. `#float_info` lists the available operations and guarantees, including fixed-point multiplication's change of scale, and the main results are in the [theorem index](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md). The block formats are compared bit for bit with torchao, microxcaling and PyTorch's FP8 casts, as the [external validation guide](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md#block-scaled-formats) records. For Embedded C fixed point we compared arithmetic, conversions and text handling with independent rational and grammar references, and checked fixed-point operations against Clang. The [test report](https://github.com/lean-dojo/FloatLib/blob/main/tests/EXTERNAL.md#the-standards-operations-and-the-complex-functions) lists 1,196,256 interface cases.
