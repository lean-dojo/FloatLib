---
number: "12"
slug: fixed-point-logarithmic-codebook-and-block-scaled
title: Fixed point, logarithmic numbers, and quantization
summary: Fixed point, logarithmic numbers, codebooks, and shared scales use common numerical contracts to describe exact arithmetic, rounding, and overflow.
phases: [exact-and-quantized, numerical-models]
---

When we keep a bank balance in cents, we are using an integer with an agreed position for the
decimal point. A one-bit weight in a neural network means minus one or plus one. The cents add
exactly, and the bit multiplies exactly but its codebook cannot represent every sum. In each
case, a stored code denotes a number. What we need from an arithmetic theorem is a connection
between the operation on codes and the operation on those numbers.

Fixed-point, logarithmic, codebook, and shared-scale representations give codes different meanings and support different operations. They use the contracts from [chapter 06](#/chapter/the-numerical-models) to state which operations are exact, which can fail, and which need a range hypothesis. Fixed-width integers supply the stored coefficients for bounded fixed point; affine quantization connects integer codes to values through a scale and a zero point. FloatLib also includes Booleans among its non-floating-point systems.

<a id="one-contract-several-carriers"></a>

## Connecting stored codes to numbers

A [[FloatLib.Numerics.NumericalSystem]] connects a type of stored codes to a type of scalars used in proofs. Its denotation assigns every code a finite scalar, an infinity, or an exceptional value. The code type is also called the *carrier* in [chapter 14](#/chapter/backends-and-the-planner): it is what a program stores at runtime.

[[FloatLib.Numerics.NumericalSystem.Represents]] says that a code denotes a given finite scalar. [[FloatLib.Numerics.NumericalSystem.AtFinite]] pairs the code with a proof of that fact. Lean erases the proof at compile time, leaving just the code.

The operation contracts are stated over systems rather than bit layouts. [[FloatLib.Numerics.Operation.Finite2]] says that when two inputs represent finite scalars, the output represents the specified function of them. [[FloatLib.Numerics.Operation.Checked2]] says the same for a kernel returning an `Option`: on finite inputs it succeeds and the result denotes the specified value. [[FloatLib.Numerics.Operation.Checked2On]] adds an explicit precondition on the scalars, which is how a hypothesis like "the sum fits in eight bits" enters a theorem instead of being assumed silently.

The three systems in a `Finite2` statement may differ. Fixed-point multiplication needs this because its inputs use two scales and its output a third. The binary formats use the same contract for mixed-format multiply-add, `mulAddFinite_refines`, with two storage-format operands and an accumulator-format result. The contracts do not require any particular bit layout: a code can be an unbounded integer, an inductive type, a two-bit vector, or a whole vector of integers.

Defining a system gives codes a meaning; each family still needs algorithms and proofs for its operations. A logarithmic number can be multiplied exactly, but its value set is not closed under addition, so the library provides multiplication without addition. A generic codebook supplies only a table of values; arithmetic requires a kernel justified by that table, with an explicit rounding policy for results outside it. Compare the spacing in [Figure 12.1](#/chapter/fixed-point-logarithmic-codebook-and-block-scaled/figure-ch16-spacing): it puts these value sets on one number line, at toy parameters and with a small binary float alongside.

![Every representable value between -8 and 8 under fixed point at binary radix with two fractional digits, the E2M3 float, the binary logarithmic system with exponents from -4 to 3, three shared-scale blocks with exponents -2, 0 and 2, and the two catalog codebooks](assets/ch16-spacing.png "Representable values between -8 and 8 under several numerical representations. A block’s common scale changes the values of all its elements together.")

## Exact fixed point: scaled integers

A fixed-point number is an integer with an agreed denominator. [[FloatLib.Floats.Formats.FixedPoint.Code]] at radix $\beta$ with $d$ fractional digits stores one field, `coefficient : Int`, and [[FloatLib.Floats.Formats.FixedPoint.Code.toRat]] divides it by `scale`, which is $\beta^d$. The radix is a [[FloatLib.Numerics.Radix]], a natural base with a proof that it is at least two; [[FloatLib.Numerics.decimalRadix]] and `binaryRadix` are provided. The value set is

$$\left\{ \frac{m}{\beta^d} : m \in \mathbb{Z} \right\},$$

an evenly spaced grid with no exponent, no signed zero, no infinity, and no NaN. The coefficient is a Lean `Int`, so this unbounded family cannot overflow. Its proofs use $\mathbb{Q}$ rather than $\mathbb{R}$: every value on the grid is rational, and the decoder is an ordinary executable function. Lean can therefore settle concrete goals about decoded values by computation.

For two values kept to two decimal digits, 1.25 and 2.50, we can compute the sum and product
as follows. Keep an eye on the product's scale: retaining the exact result takes more fractional
digits than either input.

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

Addition is exact: the coefficients add, and because both operands sit on the same grid, so does the sum. Among these four families, fixed point alone provides addition. Its exact addition has no rounding step or error term. [[FloatLib.Floats.Formats.FixedPoint.add_refines]] states the contract with the same system three times and rational addition as the specification. The fixed-point grid is closed under addition; the floating-point grid of [chapter 07](#/chapter/the-mathematics-of-rounding) is not.

Multiplication is exact too, but it changes the scale. The product of $m/\beta^p$ and $n/\beta^q$ is $mn/\beta^{p+q}$, so `mul` takes codes at scales $p$ and $q$ and returns one at scale $p + q$. Above, the coefficient 31250 at scale four is $3.125$. Returning to either input scale would require a separate rescaling operation with its own rounding policy and proof.

We can see the scale change in the contracts themselves. The addition contract repeats one system
three times; the multiplication contract carries the scales $p$, $q$, and $p + q$ in its three
positions.

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

The decoding equations do most of the proof work: `toRat_add` and
[[FloatLib.Floats.Formats.FixedPoint.Code.toRat_mul]], the second using
$\beta^{p+q} = \beta^p \beta^q$. Once we have them, the contracts
[[FloatLib.Floats.Formats.FixedPoint.add_refines]], `neg_refines`, `sub_refines`, and `mul_refines`
take one line each. All are registered with the `numerics` automation. For concrete codes, it
computes the answer; for symbolic represented values, it selects the contract we need.

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

The third example multiplies values at different scales. The `2 + 3` in its result type records the sum of their fractional digit counts. Division, square root, fused multiply-add, and transcendental functions can produce values outside the grid and need a rounding policy. The exact family provides none of these operations.

<a id="fixed-point-through-execfloat-operators-and-literals"></a>

## Fixed-point operators and literals

`FixedPoint` makes the same codes available through the `ExecFloat` interface. Ordinary `+` and `-` use the usual `ExecFloat.Add` and `ExecFloat.Sub` instances; unary minus is a direct `Neg` instance on the integer kernel. For addition and subtraction, the integer kernels above are also the reference definitions, so their certificates, such as `addCertified`, are immediate. [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]] connects the public operation to its specification. Multiplication uses the explicit `mul` with the composed scale in its result type, rather than `ExecFloat.Mul`.

Literals need a rounding rule even when addition is exact. A natural literal is embedded exactly by multiplying by the scale. A decimal literal such as `1.25` is rounded once, from the exact rational the parser produces, to the nearest grid coefficient with ties to even, by `roundRat` using [[FloatLib.Numerics.roundRatEven]]. It never passes through a host floating-point value.

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

The value $0.125$ at two decimal digits is $12.5$ hundredths, a tie, and rounds to the even coefficient 12; $0.375$ is $37.5$ hundredths and rounds to 38.
Try nudging the literals in the two coefficient `#eval` calls to either side of the tie and
watching which coefficient we get :)

Conversion from another system follows the same rule: `run` rounds a finite rational once and reports whether the result was inexact, and rejects an infinity or an exceptional value because the grid has no code for either (`run_infinity`).

<a id="bounded-fixed-point-three-answers-to-overflow"></a>

## Bounded fixed point and overflow

When the coefficient must fit a fixed-width word, [[FloatLib.Floats.Formats.FixedPoint.Bounded.Code]] takes a third parameter, a width, and stores its coefficient in [[FloatLib.Numerics.Representations.FixedInt]], a signed two's-complement word of exactly that many bits. Its definition is reducible but deliberately not an abbreviation: Lean keeps the radix and scale in the type, even though neither needs storage at runtime. The runtime value is exactly `FixedInt width`. The value set at width $w$ is

$$\left\{ \frac{m}{\beta^d} : -2^{w-1} \le m \le 2^{w-1} - 1 \right\},$$

and now we have to decide what an operation should do when a coefficient leaves that range.
The named kernels provide wrapping, checked, and saturating arithmetic. We can compare all
three choices on the same operands:

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

The exact coefficient sum is 136, which does not fit in eight signed bits. `wrapAdd` is `BitVec` addition, so the coefficient is reduced into $[-128, 127]$ and becomes $-120$, the value $-1.20$. `checkedAdd` returns `none`. `saturatingAdd` clamps to 127, the value $1.27$.

We need different contracts for these choices, because they promise different answers.
`wrapAdd_refines` is a total `Finite2` contract against `wrapAddValue`, which adds the recovered
coefficients and applies the centered remainder `Int.bmod` modulo $2^w$. `checkedAdd_refines` is a
`Checked2On` contract whose specification is plain rational addition and whose precondition is
[[FloatLib.Numerics.Representations.FixedInt.InRange]] on the exact coefficient sum.
`saturatingAdd_refines` is against exact coefficient addition followed by `clamp`. Every checked
and saturating contract carries a hypothesis that the width is positive; the three wrapping
contracts do not need it.

Multiplication takes the destination width as an argument. A product can need the sum of the operand widths, but the caller chooses how many bits to store. `wrapMul` sign-extends or truncates both operands to that width and multiplies them as bit vectors. The [bounded arithmetic definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Bounded/Core.lean) describes this as exact multiplication followed by centered reduction, and `wrapMul_refines` proves it against `wrapMulValue` at the composed scale.

Above, $120 \times 16 = 1920$ fits sixteen bits, so the wrapped product at scale four is exactly $0.1920$, while `checkedMul` into eight bits returns `none`. Checked and saturating multiplication compute the exact `Int` product and then test or clamp it, with `checkedMul_refines` and `saturatingMul_refines` as contracts.

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

`At (.finite v)` is the general form of `AtFinite v`: a code together with a proof that it denotes `v`. To use a checked contract, `applyAt` takes the precondition and two represented inputs, then returns the represented output. The contract rules out `none` under those hypotheses.

In the second example, `coefficientOf` recovers the integer coefficient of a rational at a given scale, and `coefficientOf_toRat` proves this recovery exact on every stored value. The hypothesis `h` is therefore a statement about the scalars $a$ and $b$; `(by decide)` proves that width 8 is positive. Under `h` the checked sum denotes exactly $a + b$. Without it, a caller can handle `none` or choose the wrapping or saturating operation and its specification.

Conversion into a bounded grid faces the same choice, so [[FloatLib.Floats.ExecFloat.BoundedFixedPoint.Conversion.OverflowPolicy]] names it: `reject`, `wrap`, or `saturate`. The constructors `ofRat?`, `ofRatWrapping`, and `ofRatSaturating` all round to nearest with ties to even first and differ only in what they do with a coefficient that does not fit.

```lean
#eval (ExecFloat.BoundedFixedPoint.ofRat? (radix := decimalRadix)
    (fractionalDigits := 2) (width := 8) 5).map ExecFloat.BoundedFixedPoint.coefficient
-- none
#eval ExecFloat.BoundedFixedPoint.coefficient
  (ExecFloat.BoundedFixedPoint.ofRatSaturating (radix := decimalRadix)
    (fractionalDigits := 2) (width := 8) 5)
-- 127
#eval ExecFloat.BoundedFixedPoint.coefficient
  (ExecFloat.BoundedFixedPoint.ofRatWrapping (radix := decimalRadix)
    (fractionalDigits := 2) (width := 8) 5)
-- -12
```

Five is 500 hundredths, and 500 reduced into eight signed bits is $-12$. The default conversion is checked, so choosing a type alias cannot silently change how overflow is handled; the [bounded-conversion implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Bounded/Configured/Conversion/Runtime.lean) explains this choice. The conversion status reports `overflow`, `saturated`, and `wrapped` separately. To use the exact-grid theorems on a bounded value, `toUnbounded` removes the width restriction and `toUnbounded_toRat` proves that its value is unchanged.

## Logarithmic numbers: multiplication becomes addition

A logarithmic number system stores the exponent of a value instead of its significand. Multiplication then requires adding exponents. The idea goes back to the sign/logarithm number system of Swartzlander and Alexopoulos [@swartzlanderAlexopoulos1975], cited in the [logarithmic-format introduction](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Logarithmic.lean). [[FloatLib.Floats.Formats.Logarithmic.Code]] at radix $\beta$ is an inductive type with two constructors: `zero`, and `value negative exponent` with a sign and an unbounded integer exponent, denoting $\pm\beta^e$. Zero has its own constructor because it has no logarithm.

`mul` follows the exponent law: zero absorbs, the signs combine by exclusive or, and the exponents add,

$$(\pm\beta^{a})(\pm\beta^{b}) = \pm\beta^{a+b},$$

with no rounding and no overflow because the exponent is an `Int`. Eight is $2^3$ and minus one half is $-2^{-1}$; their product is $-2^2$, which prints as `value true 2`.

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

The proofs for this family use $\mathbb{R}$, as they do for the binary formats, so a statement mixing a logarithmic factor with a binary32 value needs no cast between scalar types. The real decoder [[FloatLib.Floats.Formats.Logarithmic.Code.toReal]] is noncomputable and used in proofs. The executable decoder `toRat` returns the exact rational that every value $\pm\beta^e$ has, and `cast_toRat` proves the two agree. [[FloatLib.Floats.Formats.Logarithmic.Code.toReal_mul]] is the decoding equation and `mul_refines` its `Finite2` contract, valid for every radix.

Multiplication is the only arithmetic operation: the sum of two powers of $\beta$ is in general not a power of $\beta$. A hardware logarithmic unit adds by evaluating $\log_\beta(1 + \beta^{b-a})$ from a table or a polynomial and rounding. Supporting that operation requires choices of approximation, tie rule, underflow behaviour, and exponent bound.

The configured carrier `Logarithmic` installs `*` through `ExecFloat.Mul`, with [[FloatLib.Floats.ExecFloat.Proof.mul_eq_spec]] tying it to the specification, and a source decoder (`exactDecoder`) so values can be converted out. Converting into logarithmic codes would require choices of nearest-power, tie, underflow, and bounded-exponent policies; there is no destination quantizer. The exact core uses an unbounded integer exponent. A bounded hardware encoding or a fractional logarithm field would need a further representation and its own rounding rules.

<a id="codebooks-the-table-is-the-format"></a>

## Codebooks: assigning a value to each word

A codebook assigns a value directly to each bit pattern. Examples include a one-bit weight, a two-bit ternary value with a spare pattern, and a four-bit table tuned to a weight distribution. [[FloatLib.Floats.Formats.Codebook]] stores this assignment in a single field mapping every `BitVec width` to a `NumericalValue α`. Every word has a meaning, possibly an exceptional one, and `numericalSystem` uses that table as its denotation. To define arithmetic, we must show how an operation on the words relates to the values in the table. The bit width alone cannot tell us.

Two catalog tables ship with the library. `bipolar1` is the one-bit encoding with $0 \mapsto -1$ and $1 \mapsto +1$. `ternary2` is the two-bit encoding with $00 \mapsto 0$, $01 \mapsto +1$, $10 \mapsto -1$, and $11$ reserved; the reserved word denotes an exceptional value carrying the pattern that was read.

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

`1#2` is Lean's notation for the two-bit word 01, so the product of two $-1$ codes is the code for $+1$, and a reserved operand makes the product `none`. The set $\{-1, +1\}$ is closed under negation and multiplication, so `neg` and `mul` are total, and `mul_refines` is a `Finite2` contract against integer multiplication. The ternary table has a reserved word, so `neg?` and `mul?` return an `Option`, and `mul_refines` is a `Checked2` contract: on two finite inputs the kernel succeeds and the result denotes the integer product. Neither table has addition, because $1 + 1$ is in neither set.

The proofs check every word and every pair. There are two words for the bipolar table and four for the ternary one, so a binary contract splits into four and sixteen cases respectively. The [codebook arithmetic proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Codebook/Arithmetic/Proof.lean) uses enumeration to prove facts about these particular tables; the general codebook type has no small-width restriction.

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

The codebook quantizer examines every finite word and picks the closest. `finiteEntries` lists the finite words with their values in ascending order of the unsigned pattern, and `nearestCode` folds over that list, replacing the current best only on a strict improvement in $|x - c|$, so a tie goes to the lower word. [[FloatLib.Floats.Formats.Codebook.nearestCode_spec]] proves that the selected word is finite and at least as close to $x$ as every finite word in the table, and `nearestCode_isSome_of_denote_finite` proves the search succeeds whenever the table has a finite word. The scalar type needs only subtraction, negation, and a linear order, so the same quantizer serves integer, rational, and real tables.

```lean
#eval Codebook.finiteEntries Codebook.Catalog.ternary2
-- [(0#2, 0), (1#2, 1), (2#2, -1)]
#eval Codebook.nearestCode Codebook.Catalog.ternary2 (5 : ℤ)
-- some 1#2
#eval Codebook.nearestCode Codebook.Catalog.bipolar1 (0 : ℤ)
-- some 0#1
```

The last line is the tie rule in action: zero is equidistant from $-1$ and $+1$, the lower word wins, and the answer is the code for $-1$. The configured carrier `Codebook` keeps the selected table in the type, so two tables of the same width are never interchangeable, and exposes `decode` and named values such as `negativeOne`. The nearest-word quantizer is available as `nearest?`. It is not installed as the generic conversion instance: that would also require a policy for reserved words and ties in the application.

<a id="affine-quantization-a-scale-a-zero-point-and-a-code-range"></a>

## Affine quantization

[[FloatLib.Numerics.Quantization.AffineQuantizer]] is the integer quantizer that neural network runtimes use for inference: a positive rational `scale`, an integer `zeroPoint`, and a nonempty code interval from `qmin` to `qmax`. Quantizing an exact rational $x$ computes $\operatorname{roundEven}(x / s) + z$ with [[FloatLib.Numerics.roundRatEven]] and clamps the result into the code interval with the shared saturating clamp; dequantizing a code $k$ returns $s\,(k - z)$. Exact rational parameters make the meaning of a code independent of host floating-point arithmetic. A tensor library can apply the same scalar operation pointwise.

`quantize_mem` says every quantized code lies in the interval, `dequantize_zeroPoint` that the zero point means exactly zero, `quantize_dequantize` that every in-range code survives a round trip, and `dequantize_quantize_error_le` that when the clamp is inactive the reconstructed value is within half a step, $s / 2$, of the input. The error bound is inherited from the half bound on `roundRatEven`.

For a concrete calculation, we'll use scale $s=\tfrac14$, zero point $z=3$, and codes 0 through 7. The reconstruction formula assigns these codes the values

$$
-\tfrac34,\quad -\tfrac12,\quad -\tfrac14,\quad 0,\quad
\tfrac14,\quad \tfrac12,\quad \tfrac34,\quad 1.
$$

Code 3 represents zero, leaving three steps below it and four above. Moving the zero point reallocates the available codes between negative and positive values; the scale still fixes the distance between neighbours. To quantize $\tfrac58$, first divide by the scale to get $\tfrac52$. Ties to even rounds that to 2, then adding the zero point gives code 5. Reconstruction subtracts 3 again and multiplies by $\tfrac14$, producing $\tfrac12$.

| Input | Input divided by scale | Nearest-even integer | Code before clamp | Stored code | Reconstruction |
| --- | --- | --- | --- | --- | --- |
| $\tfrac58$ | $\tfrac52$ | 2 | 5 | 5 | $\tfrac12$ |
| $\tfrac78$ | $\tfrac72$ | 4 | 7 | 7 | 1 |
| 2 | 8 | 8 | 11 | 7 | 1 |

The first two reconstructions each differ from the input by $\tfrac18$, exactly half the step. Their stored codes are odd because the zero point is odd. Moving the addition of the zero point inside the rounding operation would change these ties: nearest-even is applied to the coefficient before the offset, as `rawCode` specifies.

We can derive the error bound by writing the rounded integer as $r=\operatorname{roundEven}(x/s)$. When the clamp leaves the code alone, reconstruction gives

$$
s\bigl((r+z)-z\bigr)-x
=s\left(r-\frac{x}{s}\right),
\qquad
\left|s\left(r-\frac{x}{s}\right)\right|\le\frac{s}{2}.
$$

The offset cancels, and positivity of the scale lets the integer half-step bound pass through multiplication. The last row shows why the theorem checks the *raw* code against the interval. Input 2 rounds exactly to integer 8, but code 11 is outside the interval and clamps to 7. Its reconstructed value is 1, an error of 1; there was no rounding error before the clamp, and the half-step conclusion no longer holds.

The round-trip theorem starts with a stored code instead of an arbitrary input. For code 6, reconstruction gives $\tfrac34$; division by the scale recovers the integer 3 exactly, then adding the zero point recovers 6. In general the recovered coefficient is $k-z$, already an integer, so rounding changes nothing and the in-range hypothesis prevents clipping. The descriptor itself requires only a positive scale and an ordered code interval. It does not require the zero point to lie inside that interval; `dequantize_zeroPoint` is an algebraic identity even when that code cannot be stored.

The quantizer is also a numerical system, `AffineQuantizer.numericalSystem`, whose codes denote their exact reconstruction. `numericalSystem_quantize_error_le` restates the half-step bound in the `Represents` vocabulary of the contracts above. The executable quantizer satisfies the `QuantizerOn` contract onto its own reconstructed value by definition, allowing the generic quantization automation to use it. There is no configured `ExecFloat` carrier for it and no arithmetic on its codes: it is a conversion, and subsequent arithmetic belongs to the integer system receiving the codes.

<a id="shared-scale-blocks-a-code-that-is-a-whole-vector"></a>

## One exponent for a block of values

In a block-scaled format, several stored integers share one exponent. We need that exponent to recover the value of each entry. [[FloatLib.Floats.Formats.Block.SharedScaleCode]] with `lanes` entries holds one `exponent : Int` and a `Vector Int lanes` of significands, and `decode` produces a `Vector Rat lanes` whose lane $i$ is

$$s_i \cdot 2^{e},$$

with `scale` supplying the power of two. For `NumericalSystem`, the decoded "scalar" is the whole rational vector: each lane depends on the shared exponent stored beside it. The organization follows the OCP microscaling specification [@ocpMx], which the [shared-scale definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/SharedScale/Core.lean) cites, while staying independent of any element width or scale-selection policy.

To quantize a block, we first choose its shared exponent. [[FloatLib.Floats.Formats.Block.quantizeAt]] takes that exponent as an argument and rounds each lane to the nearest integer multiple of $2^e$ with ties to even, using the same [[FloatLib.Numerics.roundRatEven]] as the fixed-point literals.

We'll keep the input vector fixed and change only the exponent. Watch the large entry and
the smaller entries separately as the spacing changes.

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

With exponent $-2$ the step is a quarter: one third is $4/3$ quarters and rounds to 1, five quarters is exactly 5, minus seven eighths is $-3.5$ quarters and rounds to the even value $-4$, and 100 is 400 quarters. With exponent 3 the step is eight, the three small lanes round to zero, and 100 is $12.5$ eights, which rounds to 12 and decodes to 96. Both choices are accepted by the kernel. You supply the exponent; the representation does not choose it. This lets the [configured block implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Configured/Runtime.lean) support different calibration methods, and the theorems in the [configured block proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Configured/Proof.lean) hold for whichever exponent you choose.

The lane holding 100 explains why the unbounded integer matters. At a quarter-step it needs coefficient 400, which would not fit an eight-bit signed lane whose maximum is 127. This family stores an `Int`, so it keeps 400 exactly. At step eight the rounded coefficient is only 12, but the smaller three values all disappear. The three shared-scale rows in the spacing figure show this same expansion of the grid. Every lane moves to the coarser grid together, including lanes that needed the finer spacing. This kernel accepts a supplied exponent. The [standard MX quantizer](#/chapter/low-precision-formats-for-machine-learning/choosing-a-scale-for-32-lanes) makes the scale choice for bounded elements and proves a nearest-error property at that selected scale.

`QuantizesAt` states the result precisely: the stored exponent is the one supplied, and every lane is the ties-to-even rounding of the input divided by the scale. `quantizesAt_quantizeAt` proves the kernel satisfies this rule, [[FloatLib.Floats.Formats.Block.quantizeAt_refines]] exposes the same relation through the common quantization interface, and `decode_quantizeAt_get` gives each decoded lane in closed form. The format-independent `BlockScaled` contract says that we recover a block's values by applying its scale to each stored lane. `blockScaled_sharedScale` proves this for the shared-scale family, using $s \cdot 2^e$ to decode a stored significand.

With the configured carrier `SharedScale`, we pass the shared exponent as the conversion
instance's context. There is deliberately no default context:
the [block-conversion implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Block/Configured/Conversion/Runtime.lean) keeps that choice explicit, so a global default cannot
silently choose the grid for us. Conversion of an infinity or an exceptional value fails, because
the block has no code for either.

The concrete OCP MX formats in [chapter 09](#/chapter/low-precision-formats-for-machine-learning) bound both the scale and the elements. E8M0 codes 0 through 254 denote $2^{c-127}$, and code 255 is NaN ([scale encoding](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/OCP/MX/E8M0/Core.lean)); element words may also be nonfinite. The array API supplies checked finite decoders: [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeElement_refines]] and [[FloatLib.Floats.Formats.OCP.MX.E8M0.scaleDyadic_refines]] are `Checked2` contracts, and [[FloatLib.Floats.Formats.OCP.MX.E8M0.decodeBlock?]] extends them to an array. The standard 32-lane API additionally decodes each lane with its exceptional class, so a finite scale can coexist with a NaN element and finite neighbours. In both APIs, applying a finite power-of-two scale is exact exponent arithmetic and contributes no rounding of its own.

<a id="automation-inspection-and-conformance"></a>

## Using the proofs and inspecting operations

To apply an operation's contract, we need proofs that its inputs are finite. For `Finite2` and `Checked2`, that is enough; for `Checked2On`, we also need its side condition, such as the coefficient range bound for checked fixed-point addition. Proof automation uses these same assumptions.

The [fixed-point](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/FixedPoint/Automation.lean), [logarithmic](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Logarithmic/Automation.lean), and [codebook](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Codebook/Automation.lean) automation modules register their decoding equations as `numerics_simps` and their contracts as safe rules in the shared `Numerics` Aesop rule set. This supplies the rules used by the `numerics` and `numerics_refine` calls from [chapter 06](#/chapter/the-numerical-models) and [chapter 01](#/chapter/using-the-library) in the examples above. The block family's theorems are applied directly.

`#float_info` lists each family's available operations and their guarantees. For fixed point, for instance, it makes the scale-changing behaviour of multiplication explicit.

The families store their values as an `Int`, a `FixedInt`, an inductive type, a `BitVec`, or a structure holding a vector. Their kernels operate directly on those values. The common contracts require no extra runtime dictionary and do not change the storage.

The [theorem index](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/THEOREMS.md) collects the families' main results. Their correctness rests on kernel-checked proofs; these families have not had independent external comparisons like those for binary formats and posits in [chapter 16](#/chapter/external-validation).

Possible extensions include a bounded logarithmic encoding with a rounding policy, and fixed-point division and rescaling under named policies. Each would need new kernels and contracts, stated with the same three contract forms. The concrete MX family now provides a bounded block example: six element profiles, a reserved NaN scale, and exactly 32 lanes, with scale-selection and quantization proofs described in [chapter 09](#/chapter/low-precision-formats-for-machine-learning/choosing-a-scale-for-32-lanes).

## Finding these representations in the source

The four families have separate implementations for [fixed point](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint), [logarithmic numbers](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Logarithmic), [codebooks](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Codebook), and [blocks](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/Block). For exact multiplication, start with [[FloatLib.Floats.Formats.FixedPoint.Code.toRat_mul]], which combines the two scales and gives the exact rational product, or [[FloatLib.Floats.Formats.Logarithmic.Code.toReal_mul]], which proves multiplication of logarithmic codes is exact real multiplication.

For quantization, [[FloatLib.Floats.Formats.Codebook.nearestCode_spec]] says the chosen codeword is finite and minimizes the distance to the input, with ties going to the lower word. [[FloatLib.Floats.Formats.Block.quantizeAt_refines]] says quantizing a block at a supplied exponent rounds every lane at that exponent.
