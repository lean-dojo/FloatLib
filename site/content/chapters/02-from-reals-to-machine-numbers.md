---
number: "02"
slug: from-reals-to-machine-numbers
title: How floating-point numbers work
summary: "What a floating-point number is, why 0.1 can't be stored exactly, how rounding picks the value you get, and why arithmetic built on rounding is hard to get right and to prove right."
phases: [numerical-models, binary-format]
---

A floating-point number is how a computer keeps a real number such as 0.1 or $\pi$ in a fixed number of bits, much like scientific notation in base two: a sign, a fixed number of significant digits, and an exponent that says where the point goes. In this chapter we'll take one apart, see why `0.1` can't be stored exactly and how rounding picks the value you get, and then see why arithmetic built on rounding is hard to get right and to prove right. For the full mathematics, see the handbook of Muller and his coauthors [@mullerHandbook].

## What is a floating-point number?

A float, short for floating-point number, approximates a real number. In a Lean theorem $\sqrt{2}$ is the exact nonnegative real whose square is two, and its floating-point approximation is a different number, one whose square needn't be two.

A computer stores a number in a word, a fixed group of bits. A 32-bit word has $2^{32}$ possible patterns, about 4.3 billion, and no number of bits will represent every real number. Even the exact sum of two stored values can be missing, so a format also needs a rounding rule.

Fixed point, named for a binary point that never moves, spends those patterns on one ruler with evenly spaced ticks. With $k$ bits after the binary point, rounding to nearest within range is off by at most $2^{-k-1}$ at every magnitude, so relative error, the error as a fraction of the value, grows near zero.

Floating point fixes the number $p$ of significant bits, the precision, and stores an exponent with each value. A normal value is $\pm m \cdot 2^e$ with $2^{p-1} \le m < 2^p$. Picture one ruler, always with the same number of ticks, for each stretch between consecutive powers of two, called a binade. Notice that the exponent changes jobs here: it labels the binade $[2^e, 2^{e+1})$, whose spacing is $2^{e-p+1}$. The gaps grow with the numbers, so relative error stays roughly constant across the normal range.

## Why can't 0.1 be stored exactly?

One third has decimal digits that never end, and one tenth has the same trouble in binary. Let's see why. In base two, $0.1101_2$ means $\tfrac{1}{2} + \tfrac{1}{4} + \tfrac{1}{16} = \tfrac{13}{16}$. A binary fraction that stops is an integer over a power of two, $m / 2^k$, called a dyadic rational, and every finite value of a binary floating-point format in this library is one. One tenth isn't, since $F / 2^n = 1/10$ would give $10F = 2^n$, so $5$ would divide a power of $2$. Long division in base two, doubling the fractional part, gives $0.2, 0.4, 0.8, 1.6, 1.2, 0.4, \ldots$, and the integer parts are the digits:

$$
  \tfrac{1}{10} = 0.0\overline{0011}_2 = 0.000110011001100110011\ldots_2.
$$

The other direction is safe, since $10 = 2 \cdot 5$ gives every binary fraction a finite decimal expansion. Goldberg's survey [@goldberg1991] is the classic short account of what this does to arithmetic.

Binary32, the standard 32-bit format, has 24 significant bits, and the literal `0.1` becomes the nearest value it can store. [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns the exact rational value of a finite word. If you start with this

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval ExecFloat.Binary.toRat? (0.1 : Binary32)
-- some (13421773 / 134217728)

#eval toString (0.1 : Binary32)
-- "0.1"
```

you get $13421773 \cdot 2^{-27}$, which is exactly

$$
  0.100000001490116119384765625,
$$

about $1.49 \times 10^{-9}$ above one tenth. The `some` means the word was finite. `toString` prints `0.1` because that's the shortest decimal that reads back as this word.

The type [[FloatLib.Numerics.Dyadic]] holds $\pm m \cdot 2^e$ as sign, significand (the integer of significant digits) and exponent, [[FloatLib.Numerics.Dyadic.toRat]] gives its value, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] reads it off a finite word. We'll build $13421773 \cdot 2^{-27}$ by hand, then read it off the stored `0.1`:

```lean
open FloatLib.Numerics in
#eval (Dyadic.mk false 13421773 (-27)).toRat
-- 13421773 / 134217728

#eval Model.toDyadic? (ExecFloat.Binary.toModel (0.1 : Binary32))
-- some { negative := false, significand := 13421773, exponent := -27 }
```

Both lines give $13421773 \cdot 2^{-27}$, once built by hand and once read off the stored word.

The Lean proof that one tenth isn't dyadic is the cross-multiplication from above:

```lean
theorem tenth_not_dyadic (F n : ℕ) : (F : ℚ) / 2 ^ n ≠ 1 / 10 := by
  intro h
  have h10 : (F : ℚ) * 10 = 2 ^ n := by
    field_simp at h
    linarith
  have hnat : F * 10 = 2 ^ n := by exact_mod_cast h10
  have h5 : 5 ∣ 2 ^ n := ⟨F * 2, by omega⟩
  have := Nat.prime_five.dvd_of_dvd_pow h5
  omega
```

`intro h` assumes the fraction is one tenth. Clearing denominators leads to `h5`, which says $5$ divides a power of $2$. Five is prime, so it would divide 2, which `omega` rules out.

## How does a word store a number?

Think of a word as recording a sign, which ruler and which tick. From the most significant end it holds a sign bit $s$, an exponent field $E$ of $w_e$ bits and a fraction field $F$ of $w_f$ bits. In the library a format is a [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] record of those widths, a bias and an encoding policy for the special values. We'll call it a format descriptor.

A normal significand always starts with a $1$, so this hidden bit isn't stored, and binary32 keeps 23 fraction bits for 24 bits of precision. The exponent field is unsigned, so it holds $E = e + b$, the exponent shifted up by a bias $b = 2^{w_e - 1} - 1$. `ieeeBias` computes the conventional bias, $127$ for eight exponent bits and $1023$ for eleven. A normal word stands for

$$
  (-1)^s \cdot \left(1 + \frac{F}{2^{w_f}}\right) \cdot 2^{E - b}
  = (-1)^s (2^{w_f} + F) \cdot 2^{E - b - w_f}.
$$

For binary32 the number one has $E = 127$ and $F = 0$. Let's ask Lean for a few words. `toBits32` returns a word's 32 bits as one integer:

```lean
#eval ExecFloat.Binary.toBits32 (1 : Binary32)
-- 1065353216

#eval ExecFloat.Binary.toBits32 (2 : Binary32)
-- 1073741824

#eval ExecFloat.Binary.toBits32 (-2.5 : Binary32)
-- 3223322624

#eval FloatFormat.ieeeBias 8
-- 127
```

In hexadecimal those are `0x3f800000`, `0x40000000` and `0xc0200000`. The last has the sign bit set, $E = 128$ and $F = 2^{21}$, so it's $-(1 + 1/4) \cdot 2 = -2.5$. [Figure 2.1](#/chapter/from-reals-to-machine-numbers/figure-ch01-binary32-layout) reads it and the word for `0.1` bit by bit, and [Chapter 05](#/chapter/ieee-binary-formats) decodes every class of word.

![Binary32's sign, exponent, and fraction fields, with the stored words for 0.1 and -2.5](assets/ch01-binary32-layout.png "Binary32 uses one sign bit, eight exponent bits, and twenty-three stored fraction bits. The two normal values illustrate how those fields encode a number.")

For `0.1` the exponent field is $123$, because one tenth lies between $2^{-4}$ and $2^{-3}$, where values are integer multiples of $2^{-27}$. In those units one tenth is

$$
  \frac{1/10}{2^{-27}} = 13421772 + \frac45,
$$

so nearest rounding picks 13421773, a fifth of a step up, and the stored tenth is a little too big. Its fraction field, $13421773 - 2^{23} = 5033165$, gives `0x3dcccccd`.

## What are subnormals, signed zeros, infinities and NaN?

In the IEEE encodings, the all-zeros and all-ones exponent fields hold the other kinds of word. Near zero, the all-zeros field means $(-1)^s \cdot F \cdot 2^{1 - b - w_f}$ with no hidden bit. These subnormal numbers carry the grid below the smallest normal with the same spacing, down to zero. They keep $x - y = 0$ exactly when $x = y$ for finite operands. Underflowing onto this grid instead of to zero is called gradual underflow, and it was a contested part of the 1985 standard, as Kahan's account [@kahan1997] and [the history at the end of this chapter](#/chapter/from-reals-to-machine-numbers/a-short-history-of-floating-point) describe.

`nextUp` steps to the next value up, and `isSubnormal` tests for a subnormal. A literal like `1e-39`, below the smallest normal $2^{-126}$, lands on this grid:

```lean
#eval ExecFloat.Binary.toRat?
  (ExecFloat.Binary.nextUp (0 : Binary32))
-- some (1 / 713623846352979940529142984724747568191373312)

#eval ExecFloat.Binary.isSubnormal
  (ExecFloat.Binary.nextUp (0 : Binary32))
-- true

#eval (1e-39 : Binary32)
-- 1e-39
```

The first line is the smallest positive value, $2^{-149}$, and the second confirms it's subnormal. `1e-39` is stored as $713624 \cdot 2^{-149}$, not flushed to zero. In the toy format of [Figure 2.2](#/chapter/from-reals-to-machine-numbers/figure-ch01-toy-grid), the subnormals $1/16$, $2/16$ and $3/16$ run into the first normal, $4/16$, with no change of spacing.

![Nonnegative values of a toy IEEE format with three exponent bits and two fraction bits. Squares mark zero and subnormals; circles mark normal values. Normal spacing doubles at each power of two, while subnormals keep the first normal spacing of 1/16.](assets/ch01-toy-grid.png "A toy format with three exponent bits and two fraction bits. Normal spacing doubles at each binade, while subnormal spacing stays at 1/16 down to zero.")

The all-zeros word with the sign bit set is $-0$. The two zeros compare equal, but $1 / (-0) = -\infty$, so a zero from underflow remembers which side the exact result was on. Branch cuts of complex functions, the lines where their values jump, depend on that.

[[FloatLib.Floats.ExecFloat.Binary.decode]] returns a [[FloatLib.Numerics.NumericalValue]] whose finite case carries a [[FloatLib.Numerics.SignedRat]], a rational paired with the stored sign bit. Here's $-0$ decoded, and one divided by it:

```lean
#eval ExecFloat.Binary.decode (-(0 : Binary32))
-- FloatLib.Numerics.NumericalValue.finite -0

#eval (1 : Binary32) / (-(0 : Binary32))
-- -inf
```

You get a finite `-0`, sign intact, and one over it is `-inf`.

Here are some more examples. Under nearest-even, $(-0) + (-0) = -0$ but $(-0) + 0 = +0$:

```lean
#eval ExecFloat.Binary.decode ((-(0 : Binary32)) + (-(0 : Binary32)))
-- FloatLib.Numerics.NumericalValue.finite -0

#eval ExecFloat.Binary.decode ((-(0 : Binary32)) + 0)
-- FloatLib.Numerics.NumericalValue.finite 0

#eval ExecFloat.Binary.toRat? (-(0 : Binary32))
-- some 0
```

The sums come out as promised, but `toRat?` gives a plain `some 0`.

**Note:** A `Rat` has no negative zero, so `toRat?` reports $-0$ as `0`, and a cast that lost the sign would pass any test that compared the zeros with `==`. FloatLib keeps the sign where it matters. `negative_add_of_eq_zero` says an exact zero sum of `SignedRat` values, added with the nearest-even sign rule, is negative exactly when both operands are. [[FloatLib.Floats.ExecFloat.Binary.Conversion.run_default_negZero_value?]] says converting an exact $-0$ into a binary format gives its negative zero, or its only zero in formats that have just one, such as FNUZ (the UZ stands for "unsigned zero").

Infinities have the all-ones exponent field and a zero fraction. Dividing a finite nonzero value by zero makes one, and depending on the rounding direction, so does overflow. For nearest-even the binary32 threshold is the midpoint between the largest finite value, about $3.4028235 \times 10^{38}$, and $2^{128}$:

```lean
#eval (1 : Binary32) / 0
-- inf

#eval ExecFloat.Binary.toRat? (3.4028235e38 : Binary32)
-- some 340282346638528859811704183484516925440

#eval (3.5e38 : Binary32)
-- inf
```

One over zero is `inf`, and `3.5e38`, past the threshold, overflows to `inf`.

In the IEEE encodings, a nonzero fraction under the all-ones field is a NaN, short for "not a number", the answer to invalid operations such as $0/0$, $\infty - \infty$, $0 \cdot \infty$ or $\sqrt{-1}$. Arithmetic passes it along, and its fraction can carry a payload of extra information. Binary32 has $2^{24} - 2$ NaN words, a lot of ways to say "not a number" :) They all print the same:

```lean
#eval (0 : Binary32) / 0
-- nan
```

Zero over zero gives `nan`.

With these, every operation has an answer for every input. For those who like precise definitions, the format is closed and every operation is a total function on words. [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] records a word's complete meaning: a finite dyadic with its sign of zero, a signed infinity, or a NaN with its sign, signaling class and payload.

## How does rounding work?

Say you add two finite binary32 values and the exact sum needs more than 24 significant bits, or exceeds the range. Correct rounding means the format computes the exact result, at least conceptually, and rounds it once by the chosen rule [@ieee754_2019]. Overflow and exceptional operands get fixed answers at the word level. The inputs and the mode then decide the output, so a correctness theorem can name the one right answer instead of bounding its distance from the exact result.

IEEE 754 requires four rounding directions for binary formats. Nearest-even picks the nearer neighbour and, at a midpoint, the one with an even significand. Toward zero picks the smaller magnitude, and up or down the neighbour on that side. [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] adds ties away from zero, which the 2008 revision [@ieee754_2008] requires for decimal formats, and MPFR's rounding away from zero. `roundToIntegral` rounds to a whole number. Let's try it on `2.5`, `3.5` and `-2.5`, each halfway between two integers:

```lean
#eval ExecFloat.Binary.roundToIntegral (2.5 : Binary32) (mode := .nearest)
-- 2

#eval ExecFloat.Binary.roundToIntegral (3.5 : Binary32) (mode := .nearest)
-- 4

#eval ExecFloat.Binary.roundToIntegral (2.5 : Binary32) (mode := .towardZero)
-- 2

#eval ExecFloat.Binary.roundToIntegral (2.5 : Binary32) (mode := .up)
-- 3

#eval ExecFloat.Binary.roundToIntegral (-2.5 : Binary32) (mode := .down)
-- -3
```

Nearest-even sends `2.5` down to 2 and `3.5` up to 4, the even neighbours. Toward zero gives 2, up gives 3 and down gives -3. [Figure 2.3](#/chapter/from-reals-to-machine-numbers/figure-ch01-rounding-directions) draws them.

Each has a theorem, such as [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundToIntegral_nearest]], saying that the decoded result is the nearest-even integer, the truncation, the ceiling $\lceil x \rceil$ or the floor $\lfloor x \rfloor$ of the decoded input. They cover finite inputs in a conventional IEEE format, and all but truncation also need `(fmt.fracWidth : Int) ≤ fmt.maxNormalExponent`, which keeps the rounded integer representable. Every standard IEEE interchange format satisfies it, but a custom descriptor needs its own proof.

![The four required directions of IEEERoundingMode on the midpoints -2.5, 2.5 and 3.5, with arrows to the chosen integers](assets/ch01-rounding-directions.png "Four rounding directions on an integer grid. At a midpoint, nearest-even chooses by the parity of the destination integer.")

Arithmetic rounds the same way. Let's add `1e-9` to one, rounding to nearest and then up:

```lean
#eval ExecFloat.Binary.add (1 : Binary32) 1e-9 (mode := .nearest)
-- 1

#eval ExecFloat.Binary.add (1 : Binary32) 1e-9 (mode := .up)
-- 1.0000001

#eval ExecFloat.Binary.toRat?
  (ExecFloat.Binary.nextUp (1 : Binary32))
-- some (8388609 / 8388608)
```

$1 + 10^{-9}$ sits only about $0.0084$ of the way from $1$ to its binary32 upper neighbour, so nearest rounding returns $1$ and rounding up returns that neighbour. The last line shows that neighbour exactly, $1 + 2^{-23}$.

## Where is the exact result kept?

In code, the exact result of adding two finite binary values is a dyadic. Addition's reference definition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add]], decodes both finite operands with `toDyadic?`, adds them exactly with integers that grow as needed, and rounds once to nearest-even with [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]]. Multiplication and fused multiply-add work the same way. Division and square root are harder, because their exact results need not be dyadic, but rounding only needs to know which side of a midpoint the true result is on.

Our [finite binary64 divider](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Division/Proof.lean) is a loop on `UInt64` machine words doing long division in base two, with an integer quotient and an exact remainder. Dividing 13 by 7, after $j$ binary digits the divider keeps

$$
  13\cdot 2^j = 7q_j + r_j, \qquad 0 \le r_j < 7,
$$

and each step doubles the remainder and subtracts 7 when it can:

| Digits generated | Scaled numerator | Quotient | Remainder |
| --- | ---: | ---: | ---: |
| 0 | 13 | 1 | 6 |
| 1 | 26 | 3 | 5 |
| 2 | 52 | 7 | 3 |
| 3 | 104 | 14 | 6 |

At three fractional bits the remainder 6 is more than half of 7, so nearest rounding bumps 14 to 15 and returns $15/8$. The proof also shows that the doubled quotient and remainder fit in the machine words ([Chapter 03](#/chapter/the-numerical-models)).

For proofs, [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] rounds to nearest-even on a real grid with a format's precision and subnormal spacing and no upper exponent limit, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] reads a finite word as its real value.

**Note:** By convention `toReal` gives zero for infinities and NaNs, so a theorem that uses it to describe arithmetic has to keep exceptional words out.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] says that for a format with the IEEE encoding and conventional bias, whenever the executable rounder returns a finite word, its real value is `roundAt` of the real value of the exact input. For addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] gives

$$
  \operatorname{toReal}(\operatorname{add}(x, y))
  = \operatorname{roundAt}_{f}(\operatorname{toReal}(x) + \operatorname{toReal}(y))
$$

under the IEEE encoding, the conventional bias and a finite computed sum. That last hypothesis forces finite operands and excludes overflow, which finite inputs alone don't. [Chapter 03](#/chapter/the-numerical-models) proves one case on concrete words and [shows how to prove the result is finite](#/chapter/the-numerical-models/how-to-prove-a-result-is-finite). This real-valued view, on a grid in the style of the Coq library Flocq [@boldoMelquiond2011], sits next to the word-level [[FloatLib.Floats.ExecFloat.Proof.add_eq_spec]]: the implementation and its specification return the same complete output on every input, including ties and exceptional values, and the selected implementation supplies the proof.

## How big can a rounding error be?

Rounding to nearest is off by at most half the gap between neighbours. That gap is the unit in the last place, $\operatorname{ulp}(x)$, which is $2^{e-p+1}$ for $2^e \le |x| < 2^{e+1}$, so binary32 has $\operatorname{ulp}(1) = 2^{-23}$. [[FloatLib.Floats.Formats.BinaryInterchange.Model.ulpAt]] is the ulp function for a format's grid, flat subnormal spacing included, [[FloatLib.Floats.Formats.BinaryInterchange.Model.halfUlpAt]] is half of it, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] proves

$$
  |\operatorname{round}(x) - x| \le \tfrac{1}{2}\operatorname{ulp}(x)
$$

for every real $x$ and every binary format. The `roundAt` grid can't overflow, so applying the bound to a stored result needs the finiteness hypotheses above. Here's the binary32 case as a Lean `example`, a theorem without a name:

```lean
example (x : ℝ) :
    |Model.roundAt FloatFormat.binary32 x - x| ≤
      Model.halfUlpAt FloatFormat.binary32 x :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 x
```

It needs no hypotheses about `x`.

The relative yardstick is the unit roundoff $u = 2^{-p}$, which is $2^{-24} \approx 5.96 \times 10^{-8}$ for binary32 and $2^{-53} \approx 1.11 \times 10^{-16}$ for binary64. In the normal range $\operatorname{round}(x) = x(1 + \delta)$ with $|\delta| \le u$, which [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] proves for nonzero $x$ with $|x|$ at least the smallest normal magnitude. It follows from dividing the absolute bound by $|x|$:

$$
  \frac{|\operatorname{round}(x)-x|}{|x|}
  \le \frac{2^{e-p}}{|x|}
  \le \frac{2^{e-p}}{2^e}
  = 2^{-p}.
$$

For subnormals the relative bound breaks. The binary32 midpoint $2^{-150}$ rounds to zero under nearest-even, a relative error of one, and only the absolute bound holds. [Chapter 04](#/chapter/the-mathematics-of-rounding) develops both bounds for arbitrary formats.

## Why is 0.1 + 0.2 not 0.3?

Now for the question from the last chapter. In binary32, `0.1 + 0.2` gives the same word as the literal `0.3`, but in binary64, the 64-bit format, the sum is the next value up:

```lean
#eval (0.1 : Binary64) + 0.2
-- 0.30000000000000004

#eval (0.3 : Binary64)
-- 0.3

#eval ExecFloat.Binary.nextUp (0.3 : Binary64)
-- 0.30000000000000004
```

The sum and `nextUp` of the stored `0.3` print the same digits.

Every rounding here obeyed nearest-even. In binary64 `0.1` is stored as $0.1000000000000000055511\ldots$ and `0.2` as twice that. Their exact sum, $10808639105689191 \cdot 2^{-55}$, lands on the midpoint between the word for `0.3` and its upper neighbour, and ties to even picks the upper one, $0.3000000000000000444\ldots$, while the stored `0.3` is $0.2999999999999999888\ldots$.

## Why is floating point hard to get right?

Correct rounding is a promise about one operation. Programs chain operations, so moving parentheses moves where rounding happens, and changing an intermediate format can change which side of a midpoint the next operation sees. One correctly rounded operation is easy to specify, and a chain of them is hard to prove. An implementation also has to get its shifts, table lookups and exceptional branches right for every input. On the way we'll meet five real failures with five different causes ([Figure 2.4](#/chapter/from-reals-to-machine-numbers/figure-ch03-incident-timeline)).

![Five incidents, each marked by the kind of numerical failure described in its primary sources. Sleipner concerns the physical model.](assets/ch03-incident-timeline.png "Five failures with different causes, from arithmetic and conversion errors to an inadequate physical model. Correct rounding alone would not resolve all five.")

### Why can't you test every input?

Let's count. A binary64 addition has $2^{128}$ input pairs. At a billion tests per second, running them all takes about $10^{22}$ years, and binary32's $2^{64}$ pairs still take a few hundred. An eight-bit format has $2^{16} = 65{,}536$ ([Figure 2.5](#/chapter/from-reals-to-machine-numbers/figure-ch02-state-space)).

![Ordered input pairs of one binary operation at 8, 16, 32 and 64 bits, read also as the time to run them all at a billion tests per second; binary32 and binary64 are impractical to enumerate at this rate](assets/ch02-state-space.png "Ordered pairs for one binary operation, on a logarithmic scale. The time scale assumes one billion checks per second and is illustrative, not a measured test run.")

So for formats of eight bits or fewer, the table backends evaluate the reference operation once at every pair and store the answers, like a times table. [[FloatLib.Floats.Formats.BinaryInterchange.Configured.ByteTable.runBinary_eq_lift]] states that calling the table gives the same result as the configured model operation, and corresponding theorems cover operations with one or three operands. For the 16-bit formats binary16 and bfloat16 we ran every pair through addition, subtraction, multiplication and division in all four rounding directions IEEE 754 requires, against SoftFloat [@hauserSoftFloat] and MPFR [@fousseMpfr2007] respectively, and every value and flag agreed ([Chapter 14](#/chapter/external-validation)). For binary32 and binary64, tests can only hunt for hard cases, while a proof's variables stand for any input word.

Hardware can miss hard cases. In June 1994 Thomas Nicely noticed inconsistent results on his new Pentium [@coePentium1995]. Its division table should have had 1066 populated cells, and five were missing. Divisions that hit them had relative errors of up to about $6 \times 10^{-5}$ [@coePentium1995] [@edelman1997], and Intel took a 475 million dollar pretax charge [@intelAnnualReport1994]. For $4195835 / 3145727 = 1.333820449136241002\ldots$ the flawed chips returned $1.333739068902037589$. Correctly rounded binary64 agrees with the exact quotient to seventeen significant digits:

```lean
#eval (4195835 : Binary64) / 3145727
-- 1.333820449136241

#eval (6006993277709123 * 10 ^ 18) / 4503599627370496
-- 1333820449136241093

#eval (4195835 * 10 ^ 18) / 3145727
-- 1333820449136241002
```

The integer lines print nineteen digits without another floating-point conversion, the second for the stored binary64 quotient and the third for the exact one. One quotient isn't a proof, but [[FloatLib.Floats.ExecFloat.Proof.div_eq_spec]] covers every pair of stored operands, exceptional cases included, and under finite-divisor and finite-result hypotheses [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_div_eq_roundAt]] identifies the rounded quotient ([Chapter 03](#/chapter/the-numerical-models)). These are proofs about Lean definitions, not about your processor's divider.

### Why does moving parentheses change the answer?

Rearranging an expression changes which intermediate results get rounded, so rounding breaks associativity and distributivity, the rules for regrouping and multiplying out. Let's add $2^{-24}$, half the spacing at one in binary32, to one twice, building it from its bit pattern so no decimal conversion sneaks in:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

def halfUlp : Binary32 :=
  ExecFloat.Binary.ofBits32 0x33800000

#eval ExecFloat.Binary.toRat? halfUlp
-- some (1 / 16777216)

#eval ((1 : Binary32) + halfUlp) + halfUlp
-- 1

#eval (1 : Binary32) + (halfUlp + halfUlp)
-- 1.0000001
```

`halfUlp` is $2^{-24}$, and the two groupings give `1` and `1.0000001`. In the first grouping each addition lands on a tie that goes to one, whose significand is even. In the second the small terms add exactly to $2^{-23}$. Both groupings obeyed the rounding rule but saw different exact sums.

$x + y = x$ doesn't imply $y = 0$ either. [[FloatLib.Floats.ExecFloat.Binary.add]] with `(status := true)` also returns the five IEEE status flags, which record events such as an inexact result, and the direction of rounding:

```lean
#eval (16777216 : Binary32) + 1
-- 16777216

#eval (ExecFloat.Binary.add (16777216 : Binary32) 1 (status := true)).status
-- { inexact := true }
```

You get $2^{24}$ back, with only `inexact` raised. Above $2^{24}$ the binary32 integers are two apart, so adding one is a tie that goes to even, the original value. The `inexact` flag says the addition wasn't exact, not how much was lost, and a counter that adds one gets stuck at $2^{24}$ :)

Sterbenz's lemma [@sterbenz1974] says nearby floating-point values subtract exactly, and an exact difference can still be a poor answer. Try adding $10^{-6}$ to one and then subtracting one:

```lean
#eval ((1 : Binary32) + 1e-6) - 1
-- 9.536743e-7
```

We wanted $10^{-6}$ and got $2^{-20}$, almost five percent off from an exact subtraction. The addition rounded $1 + 10^{-6}$ to a multiple of $2^{-23}$, and subtracting one kept that absolute error while shrinking the result a millionfold. Our lemma, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz_of_same_sign]], says that for finite values of the same sign whose magnitudes are within a factor of two of each other, the decoded difference is the exact real difference. At binary32, `by decide` settles the hypothesis that the format is a conventional IEEE one:

```lean
example (x y : Model FloatFormat.binary32)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hsign : 0 ≤ Model.toReal x * Model.toReal y)
    (hxy : |Model.toReal x| ≤ 2 * |Model.toReal y|)
    (hyx : |Model.toReal y| ≤ 2 * |Model.toReal x|) :
    Model.toReal (Model.sub x y) = Model.toReal x - Model.toReal y :=
  Model.toReal_sub_eq_of_sterbenz_of_same_sign (by decide) hx hy hsign hxy hyx
```

`hx` and `hy` say both values are finite, `hsign` that they have the same sign, and `hxy` and `hyx` that each magnitude is at most twice the other. [Chapter 04](#/chapter/the-mathematics-of-rounding) develops the grid form, [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]].

### Why do small errors add up?

In January 1982 the Vancouver Stock Exchange launched an index at 1000.000. Twenty-two months later it closed at 524.811, and after three weeks of recomputing it reopened at 1098.892 [@lilley1983]. It had been updated close to 3000 times on a busy day, each result truncated, cut off instead of rounded, to three decimal places [@quinn1983], so every error went downward. Rounding to nearest allows errors of both signs, but nothing promises that they cancel. Here is a binary32 loop, unrelated to the exchange's decimal arithmetic, that adds `0.1` ten thousand times. `accumulate` adds `step` to a running total `steps` times:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Numerics
open FloatLib.Numerics.Representations

#eval ExecFloat.Binary.toRat? (0.1 : Binary32)
-- some (13421773 / 134217728)

#eval 10000 * (13421773 / 134217728 : Rat)
-- 8388608125 / 8388608

def accumulate (steps : Nat) (step : Binary32)
    (rounding : Model.IEEERoundingMode) : Binary32 :=
  (List.range steps).foldl
    (fun total _ => ExecFloat.Binary.add total step (mode := rounding)) 0

#eval accumulate 10000 0.1 .nearest
-- 999.9029

#eval accumulate 10000 0.1 .towardZero
-- 999.8049

#eval (ExecFloat.Binary.add (1000 : Binary32) 0.1 (mode := .towardZero) (status := true)).status
-- { inexact := true }
```

Ten thousand exact copies of the stored tenth come to just over 1000, yet both totals come out short, `999.9029` to nearest and `999.8049` toward zero. Inside a binade, away from ties, a fixed step makes the same rounding error at every addition until the total reaches the next binade, which gives the straight stretches and bends in [Figure 2.6](#/chapter/from-reals-to-machine-numbers/figure-ch03-binary32-accumulation).

![Ten thousand binary32 additions of 0.1 under nearest-even and toward-zero rounding, as the running total minus k/10, with the points where the total reaches a new binade marked](assets/ch03-binary32-accumulation.png "Accumulated error after repeated binary32 additions of 0.1, measured against the exact decimal total. Rounding direction changes the drift, and each binade changes the step size.")

The last line's addition raises `inexact`. [[FloatLib.Numerics.IEEEStatus.union]] combines flags across a loop with logical OR. Think of a check-engine light that stays on: one inexact addition looks the same as ten thousand. Only a rounding analysis bounds the error.

### What happens when you chop instead of round?

One tenth turns up again in a clock. On 25 February 1991 the Patriot battery at Dhahran failed to track an incoming Scud, which hit an Army barracks and killed 28 American soldiers. The battery had run for over 100 hours, counting time in tenths of a second and converting the count to seconds in 24-bit registers [@gaoPatriot1992]. As Robert Skeel worked out [@skeel1992], one tenth chopped (truncated) to 23 fraction bits is

$$
\frac{\lfloor 2^{23}/10 \rfloor}{2^{23}} = \frac{838860}{8388608} = \frac{1}{10}\left(1 - 2^{-20}\right),
$$

about one part in a million short. After 100 hours, $3{,}600{,}000$ ticks, that's about $0.3433$ seconds, the figure the US General Accounting Office (GAO) itself reports, and a shift of 687 meters in the range gate, which predicts where the target will appear next. Worse, a more accurate conversion added during deployment was called from only some of the places that needed it. Tracking subtracts the times $T$ and $T+\Delta$ of two radar pulses, and with $\varepsilon = 2^{-20}$, chopping both leaves an error proportional to the short interval, while the better conversion, treated as exact and used for the later time only, puts the whole uptime into the error:

$$
  (1-\varepsilon)(T+\Delta) - (1-\varepsilon)T = (1-\varepsilon)\Delta,
  \qquad
  (T+\Delta) - (1-\varepsilon)T = \Delta + \varepsilon T.
$$

A corrected version reached Dhahran on 26 February, the day after the barracks was hit.

`ClockGrid` below is the [fixed-point family](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/Formats/FixedPoint) with 23 fraction bits. It reproduces the rounding grid but not the register's finite storage, because its coefficient, the integer it stores, is unbounded, and [[FloatLib.Floats.ExecFloat.FixedPoint.toRat]] reads it as an exact rational. We'll chop one tenth, measure the loss, and scale it to 100 hours:

```lean
/-- Binary fixed point with 23 fractional bits: the grid of the Patriot's clock conversion. -/
abbrev ClockGrid := ExecFloat.FixedPoint binaryRadix 23

/-- The first 23 fraction bits of one tenth, with everything after them discarded. -/
def choppedTenth : ClockGrid :=
  ExecFloat.FixedPoint.ofCoefficient (2 ^ 23 / 10)

#eval ExecFloat.FixedPoint.coefficient choppedTenth
-- 838860

#eval (1 / 10 : Rat) - ExecFloat.FixedPoint.toRat choppedTenth
-- 1 / 10485760

#eval (3600000 : Rat) * ((1 / 10 : Rat) - ExecFloat.FixedPoint.toRat choppedTenth)
-- 5625 / 16384

#eval ExecFloat.FixedPoint.coefficient (0.1 : ClockGrid)
-- 838861
```

The coefficient matches Skeel's formula, and the loss per tick times $3{,}600{,}000$ ticks is $5625 / 16384$, the GAO's 0.3433 seconds as an exact fraction. The last line is the literal `0.1 : ClockGrid`, which rounds to nearest and stores 838861, a quarter of the chopping error with the opposite sign. That's better, but only consistency, the same conversion for both times, lets nearby errors cancel.

### What happens when you round twice?

In decimal, 1.46 rounds to 1.5 and then to 2, but straight to a whole number it's 1. In binary, take $x = 1 + 2^{-24} + 2^{-53}$. Straight to binary32 it rounds up, being just above the midpoint between $1$ and $1 + 2^{-23}$. Rounded to binary64 first it's a tie, since $2^{-53}$ is half the binary64 spacing at one. Nearest-even gives $1 + 2^{-24}$, a binary32 midpoint, and the second rounding returns $1$. [Figure 2.7](#/chapter/from-reals-to-machine-numbers/figure-ch02-double-rounding) draws this on smaller grids.

![The chapter's double rounding on grids small enough to draw: with three binary digits as the target and five as the intermediate, x = 1 + 2^-3 + 2^-5 rounds once to 1.25 and twice, through the five-digit grid, to 1](assets/ch02-double-rounding.png "The intermediate rounding lands exactly on a target-grid midpoint. Rounding again therefore returns a different value from rounding the original input once.")

[[FloatLib.Floats.Formats.BinaryInterchange.Model.Policy.roundDyadic]] rounds an exact dyadic into a format under a [[FloatLib.Numerics.QuantizationPolicy]]. Its third argument is entropy, the random input for stochastic rounding, which rounds up or down at random. Nearest-even ignores it, so we pass 0. Here `justAboveMidpoint` is $x$, rounded once straight to binary32 and once through binary64:

```lean
open FloatLib.Numerics (QuantizationPolicy)

def justAboveMidpoint : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 2^53 + 2^29 + 1, exponent := -53 }

def direct32 : Model FloatFormat.binary32 :=
  Model.Policy.roundDyadic FloatFormat.binary32
    QuantizationPolicy.nearest 0 justAboveMidpoint

def via64 : Model FloatFormat.binary64 :=
  Model.Policy.roundDyadic FloatFormat.binary64
    QuantizationPolicy.nearest 0 justAboveMidpoint

#eval Model.toDyadic? direct32
-- some { negative := false, significand := 8388609, exponent := -23 }

#eval Model.toDyadic? via64
-- some { negative := false, significand := 4503599895805952, exponent := -52 }

#eval Model.toDyadic?
  (Model.cast FloatFormat.binary64 FloatFormat.binary32 via64)
-- some { negative := false, significand := 8388608, exponent := -23 }
```

Significand $8388609$ at exponent $-23$ is $1 + 2^{-23}$. The binary64 result in the middle line is $1 + 2^{-24}$, the binary32 midpoint, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast]] takes it to significand $8388608$, which is $1$, one ulp lower. On x87 hardware a computation rounds first in an 80-bit register and again when it's stored to a 64-bit memory slot, so a register spill to memory can change later results. [Chapter 04](#/chapter/the-mathematics-of-rounding) proves double-rounding identities under specific hypotheses, including directed modes (up, down and toward zero) and round to odd followed by nearest even on a fixed grid. For nearest-even, the example shows why no general identity can hold.

Fused multiply-add, or FMA, rounds $xy + z$ once. Take $a = 1 + 2^{-12}$, so $a^2 - 1 = 2^{-11} + 2^{-24}$ exactly. You can compute it fused and unfused:

```lean
def a : Binary32 :=
  ExecFloat.Binary.ofBits32 0x3f800800

#eval ExecFloat.Binary.toRat? a
-- some (4097 / 4096)

#eval ExecFloat.Binary.toRat? (ExecFloat.fma a a (-1))
-- some (8193 / 16777216)

#eval ExecFloat.Binary.toRat? (a * a - 1)
-- some (1 / 2048)
```

The first line confirms `a`, and in the second [[FloatLib.Floats.ExecFloat.fma]] returns the exact answer. The unfused product needs 25 significant bits, one more than binary32 has, so it rounds to $1 + 2^{-11}$ and the subtraction returns $2^{-11}$, the third line. A compiler allowed to contract, or fuse, `a * a - 1` into an FMA changes the answer. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] specifies the fused operation as one rounding of the exact expression.

### How do NaNs and infinities behave?

An infinity swallows every finite addend, so $x + \infty = \infty$ says nothing about $x$. A NaN isn't equal to itself under IEEE comparison, but it is under Lean's structural equality on stored words:

```lean
#eval ((0 : Binary32) / 0) == ((0 : Binary32) / 0)
-- false

#eval ((0 : Binary32) / 0) = ((0 : Binary32) / 0)
-- true
```

`==` says `false` and `=` says `true`. `==` is the IEEE comparison installed for `ExecFloat` types and `=` compares bit patterns, so a theorem can say two computations return the same NaN word without claiming IEEE equality.

Every IEEE ordered comparison with a NaN operand returns false, so a clamp, code that caps a value, written as `if x < bound then x else bound` quietly turns a NaN into the finite `bound`. NaNs are quiet or signaling, and arithmetic can pass a quiet NaN along without raising `invalid` again. You can check each claim:

```lean
def nan32 : Binary32 := (0 : Binary32) / 0
def inf32 : Binary32 := (1 : Binary32) / 0

#eval nan32 < 1
-- false

#eval (1 : Binary32) < nan32
-- false

#eval if nan32 < 1 then nan32 else (1 : Binary32)
-- 1

#eval inf32 + (-1000000) == inf32
-- true

#eval (ExecFloat.Binary.sub inf32 inf32 (status := true)).status
-- { invalid := true }

#eval (2 : Binary32) * (nan32 + 1)
-- nan

#eval (ExecFloat.Binary.add nan32 1 (status := true)).status
-- {}
```

Both comparisons give `false`, so the `if` returns `1`. The infinity swallows `-1000000`, and the NaN passes through arithmetic. The subtraction that created the NaN set `invalid` and the addition that propagated it didn't, so the flags needn't say where a NaN came from.

Dividing by zero and dividing zero by zero raise different flags of [[FloatLib.Numerics.IEEEStatus]]:

```lean
#eval (ExecFloat.Binary.div (1 : Binary32) 0 (status := true)).status
-- { divideByZero := true }

#eval (ExecFloat.Binary.div (0 : Binary32) 0 (status := true)).status
-- { invalid := true }
```

One over zero raises `divideByZero`, and zero over zero raises `invalid`. We hand the flags back with each result, like a receipt. [[FloatLib.Floats.Formats.BinaryInterchange.Model.div_divideByZero]] says the divide-by-zero flag is set exactly when a finite nonzero operand is divided by a zero, and `div_invalid` does the same for `invalid`, including signaling NaN operands and infinity over infinity. None of this survives decoding the result to a real number.

### What happens when a number doesn't fit?

Say you convert the exact value 500 to E4M3FN, an 8-bit machine-learning format with four exponent bits and three fraction bits, the E4 and M3 of its name. FN means "finite with NaN": it has no infinity, so a positive result too large to round back to its largest finite value, $448$, becomes either a NaN word or $448$, both in the same encoding. You pick with a [[FloatLib.Numerics.QuantizationPolicy]] argument. `toNatBits` shows the stored bits as an integer:

```lean
def exact500 : FloatLib.Numerics.Dyadic :=
  { negative := false, significand := 500, exponent := 0 }

#eval Model.toNatBits <| Model.Policy.roundDyadic FloatFormat.e4m3fn
  QuantizationPolicy.nearest 0 exact500
-- 127

#eval Model.toNatBits <| Model.Policy.roundDyadic FloatFormat.e4m3fn
  QuantizationPolicy.saturating 0 exact500
-- 126
```

`nearest` gives 127, which is `0x7f`, the NaN code, and `saturating` gives 126, or `0x7e`, which encodes $448$. A proof under one policy doesn't carry over to the other ([Chapter 07](#/chapter/low-precision-formats-for-machine-learning)).

A number that didn't fit ended the Ariane 5 rocket's maiden flight on 4 June 1996, in less than a minute. The inquiry board chaired by Jacques-Louis Lions traced the loss of guidance [@lions1996] to "a data conversion from 64-bit floating point to 16-bit signed integer value". BH, the horizontal bias, exceeded 32767, the largest signed integer that fits. In IEEE 754 terms that's the invalid-operation case of conversion to an integer format, clause 5.8 of [@ieee754_2019], and rounding played no part. BH's bound came from Ariane 4, and the tests left out Ariane 5's early trajectory, with its much higher horizontal velocity. The board recommended: "Identify all implicit assumptions made by the code and its justification documents on the values of quantities provided by the equipment."

In FloatLib a [16-bit signed destination](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Core.lean) is [[FloatLib.Numerics.Representations.FixedInt]] at width 16, and the decidable [[FloatLib.Numerics.Representations.FixedInt.InRange]] says which values fit. The board didn't publish BH's value, so we'll make one up, 40000. We check whether it fits, then try three casts from binary64:

```lean
#eval decide (FixedInt.InRange 16 40000)
-- false

#eval (FixedInt.ofInt 40000 : FixedInt 16).toInt
-- -25536

/-- Sixteen-bit two's complement integers, seen as a fixed-point grid with no fraction digits. -/
abbrev Int16Grid := ExecFloat.BoundedFixedPoint binaryRadix 0 16

open FloatLib.Floats.ExecFloat.BoundedFixedPoint (OverflowPolicy)

def horizontalBias : Binary64 := 40000

#eval ExecFloat.cast (target := Int16Grid) horizontalBias
-- .failure .outOfRange

#eval horizontalBias.cast (target := Int16Grid) (context := OverflowPolicy.wrap)
-- .success (-25536) { inexact := true, overflow := true, wrapped := true }

#eval horizontalBias.cast (target := Int16Grid) (context := OverflowPolicy.saturate)
-- .success 32767 { inexact := true, overflow := true, saturated := true }
```

40000 doesn't fit, and `ofInt` wraps it around to `-25536`. By default the cast returns `outOfRange` for the caller to handle. Wrapping rolls over like an odometer and saturation pins the value at $32767$, both raising `overflow` and `inexact`. The [round-trip theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Representations/FixedInt/Semantics/Basic.lean) `toInt_ofInt_eq_self` assumes that the value fits:

```lean
example (value : Int) (h : FixedInt.InRange 16 value) :
    (FixedInt.ofInt value : FixedInt 16).toInt = value :=
  FixedInt.toInt_ofInt_eq_self h
```

It says a value in range comes back unchanged from `ofInt` and `toInt`. Proving it doesn't establish `InRange 16 BH` for a trajectory, which takes evidence about what the guidance system produces. It puts the range assumption in plain sight, as a hypothesis every use has to supply.

### Why isn't an error bound enough?

Higham [@higham2002] and Goldberg [@goldberg1991] use the model $\mathrm{fl}(x \circ y) = (x \circ y)(1 + \delta)$ with $|\delta| \le u$, where fl is the computed result and the circle any basic operation. Under its range assumptions the model bounds an operation's error without knowing the rounded result. Subnormal results need an absolute-error treatment, and overflow its own handling. And meeting the bound doesn't prove correct rounding. At the binary32 tie $1 + 2^{-24}$, both one and $1 + 2^{-23}$ pass it, and nearest-even wants one. A bit-level specification fixes one output word for each input and rounding mode, so its proof needs enough about the exact intermediate to pick that word, including ties and exceptional cases. Error bounds then follow from the equality, and the layers in [chapter 03](#/chapter/the-numerical-models) keep both.

### What does a proof not cover?

A proof about source code is only as good as the execution rules it assumes, and Monniaux [@monniaux2008] documents how those rules depend on the environment. Where it's permitted, a compiler may contract multiplication and addition into an FMA, keep an intermediate in an 80-bit register or reassociate a sum under a fast-math option, which trades exactness for speed, and a processor may flush subnormal results to zero or inherit a rounding mode that earlier code set. A theorem about Lean definitions says nothing about the processor's `addss` instruction until some argument connects the two. Certified `ExecFloat` arithmetic is software compiled from the definitions in the proofs, so you're trusting the Lean compiler to implement integer and bit-vector operations correctly, including any substitutions it makes for faster execution. [Chapter 03](#/chapter/the-numerical-models) explains how these execution assumptions differ from the axioms listed by `#print axioms`. The optional host operations, such as `Unchecked.add32`, also trust the host's arithmetic, under guards and execution conditions that [Chapter 13](#/chapter/lean-native-floats/how-to-use-the-processors-own-arithmetic) describes. They live in the [unchecked host-arithmetic module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Configured/NativeFPU/Unchecked.lean), outside the default `import FloatLib` path.

Our refinement theorems prove agreement with the formal reference, not that the reference says what the standard says, so a mistake shared by the implementation and its specification is invisible to the proof. Comparing with independent implementations can expose it, and [Chapter 14](#/chapter/external-validation) compares with TestFloat, MPFR, published value tables and host arithmetic. Some failures sit outside arithmetic altogether. In 1991 the concrete base of the Sleipner A platform sank, a loss of about 700 million dollars, after a finite element analysis, which models a structure as a mesh of small pieces, underestimated shear stresses by about 47 percent [@jakobsenRosendahl1994] [@selbyVecchioCollins1997] [@arnoldDisasters], and correct rounding says nothing about whether a mesh is good enough. Like [the other failures here](#/chapter/from-reals-to-machine-numbers/why-is-floating-point-hard-to-get-right), it rests on assumptions outside any single operation, so your application still has to establish its own input bounds and error budget.

## A short history of floating point

Before IEEE 754, a program could give three different answers on a VAX, an IBM System/360 and a CDC machine, none of them because of the algorithm. [Figure 2.8](#/chapter/from-reals-to-machine-numbers/figure-ch04-standards-timeline) places the formats along the history that followed.

![Five milestones in floating-point formats, from an early computer design to low-precision standards](assets/ch04-standards-timeline.png "Selected milestones in floating-point representation and standardization. The P3109 entry refers to an interim report.")

Special values are older than any standard. In Raúl Rojas's [reconstruction based on Zuse's 1941 patent application](https://www.inf.fu-berlin.de/inst/ag-ki/rojas_home/documents/1996/Konrad_Zuses_Legacy.pdf), Konrad Zuse's Z3 encodes zero and infinity in the exponent and stops on $0/0$ with an exception lamp. Later, the IBM System/360 normalized its [hexadecimal formats](https://bitsavers.org/pdf/ibm/360/princOps/A22-6821-6_360PrincOpsJan67.pdf) four bits at a time (so a 32-bit float could keep as few as 21 significant binary digits), the CDC 6600 had [separate rounded and unrounded instructions](https://bitsavers.org/pdf/cdc/cyber/cyber_70/60045000_6600_Computer_System_RefMan_Aug63.pdf), DEC's VAX had no infinity or NaN, only [reserved operands](https://bitsavers.org/pdf/dec/vax/archSpec/EY-3459E-DP_VAX_Architecture_Reference_Manual_1987.pdf) that fault, and the Cray-1 [flushed vector underflow to zero](https://bitsavers.org/pdf/cray/CRAY-1/HR-0004-CRAY_1_Hardware_Reference_Manual-PRELIMINARY-1975.OCR.pdf).

William Kahan was one of the main voices for a common standard with reproducible results, specified exceptional cases and correct rounding ([Chapter 03](#/chapter/the-numerical-models/what-does-the-addition-theorem-say-about-real-numbers)). Intel's 8087 coprocessor of 1980 already rounded correctly and had subnormals, infinities, NaNs and an 80-bit extended format. After five more years of argument, among other things over the cost of gradual underflow, IEEE 754-1985 was ratified [@ieee754_1985]. Kahan received the Turing Award in 1989, and his lecture notes on the contested choices [@kahan1997] are still marked "work in progress".

**Note:** The 8087's extended format stores its integer bit, the leading one, while [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] assumes an implicit leading one, so a descriptor with 15 exponent bits and 63 fraction bits has its normal values in different bit patterns.

Machine-checked proofs of hardware arithmetic followed the Pentium bug, such as Moore, Lynch, and Kaufmann's ACL2 proof of the AMD5K86 division microcode [@mooreLynchKaufmann1998], Russinoff's for AMD-K7 multiplication, division and square root [@russinoff1998], and Harrison's HOL Light theory of floating point [@harrison1999], which Intel used. Boldo and Melquiond's Coq library Flocq [@boldoMelquiond2011] treats a float as a real number on a grid fixed by a radix and an exponent function, and FloatLib's rounded-real layer follows the same design ([chapter 04](#/chapter/the-mathematics-of-rounding)). [Chapter 14](#/chapter/external-validation/how-floatlib-compares-with-flocq-and-mpfr) checks that FloatLib and an independent proved implementation extracted from Flocq agree on complete input and output values at matching precision and exponent bounds.

IEEE 854 [@ieee854_1987] restated the rules for radix 2 or 10, and the 2008 revision [@ieee754_2008] merged the two, adding decimal formats ([the decimal chapter](#/chapter/decimal-arithmetic/how-decimal-numbers-are-stored-in-bits)) and requiring fused multiply-add. IEEE 754-1985 hadn't covered transcendental functions at all, and the revision also recommends correctly rounded $\exp$ and $\log$, whose values near a rounding midpoint may need far more digits than the destination stores, the table maker's dilemma [@deDinechinLog2007].

Deep learning revived narrow formats, from binary16 in mixed-precision training [@micikevicius2018mixed] and [bfloat16 on Google's TPU v2 and v3](https://cloud.google.com/blog/products/ai-machine-learning/bfloat16-the-secret-to-high-performance-on-cloud-tpus) to the 8-bit E5M2 and E4M3 [@micikevicius2022fp8] of OCP's OFP8 [@ocpOfp8], with FNUZ variants in ONNX [@onnxFloat8] and block scales, one scale shared by a block of numbers, in OCP's Microscaling [@ocpMx]. [Chapter 07](#/chapter/low-precision-formats-for-machine-learning) covers them, and we met their [overflow policies](#/chapter/from-reals-to-machine-numbers/what-happens-when-a-number-doesnt-fit) above. Posits [@gustafsonYonemoto2017], standardized in 2022 [@positStandard2022], spend their bits differently and add the quire, an accumulator that sums products exactly until its range runs out, though one accuracy comparison tells you nothing about a calculation spanning a wide range [@deDinechinPosits2019] ([Chapter 08](#/chapter/posits-and-the-quire)). An interim report of the IEEE P3109 working group [@p3109InterimReport], not an approved standard, proposes a recipe for many low-precision formats, and [Chapter 07](#/chapter/low-precision-formats-for-machine-learning/what-is-ieee-p3109) has our proofs against it. [Chapter 14](#/chapter/external-validation) compares posit arithmetic with an independent implementation and checks our P3109 decoding against the group's value tables, which test how a word is read and not arithmetic, exceptions or hardware.
