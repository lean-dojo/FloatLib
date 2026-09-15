---
number: "02"
slug: from-reals-to-machine-numbers
title: Representing real numbers in binary
summary: Binary encodings and rounding explain which numbers a format can store and how much precision a calculation can lose.
phases: [numerical-models, binary-format]
---

When we write `0.1` in a binary32 program, we store a number slightly larger than one tenth. The discrepancy begins with the representation: one tenth has a repeating binary expansion, and binary32 retains only 24 significant bits. Decoding the stored word gives an exact fraction; rounding is needed when choosing that word, not when reading its value back.

To understand that discrepancy, we'll follow two operations separately: interpreting the bits as a number, then choosing a representable number when an exact result falls between grid points. The handbook of Muller and his coauthors [@mullerHandbook] develops the mathematics behind both.

## What a real number is

The real numbers complete the rational number line. A sequence of rational approximations such as $3, 3.1, 3.14, 3.141, \ldots$ approaches a limit even though that limit need not be rational. Completeness requires that every Cauchy sequence, whose terms eventually stay arbitrarily close to one another, has a limit on the line. The real line includes numbers such as $\sqrt{2}$ and $\pi$, and lets us reason about limits in calculus without leaving the number system.

There are more real numbers than finite descriptions of them. Descriptions written in a finite alphabet are countable: list those with one symbol, then those with two, and continue by length. Cantor's uncountability result says that such a list cannot cover the real line. In fact, the countable set of finitely describable reals has measure zero, so almost every real has no finite formula or program that names it. Particular irrational numbers can still have short symbolic descriptions. The limitation of a fixed-width numeric type is stronger: it has room for only finitely many values, however those values are described.

<a id="why-a-machine-holds-finitely-many-values"></a>

## A fixed word stores finitely many values

A word of $n$ bits has exactly $2^n$ states. A 32-bit word has $2^{32}$ of them, and any interpretation of those states supplies at most $2^{32}$ distinct meanings. A numeric format specifies that interpretation: which number each pattern denotes, and which patterns represent exceptional results. A 64-bit word increases the available states to $2^{64}$, still a finite set. More bits can make the represented values closer together or extend their range, but cannot represent every real number.

A computation can leave this finite set even when both inputs belong to it. The format therefore needs both a set of representable values and a rounding rule that chooses an output when the exact result is missing.

## Binary fractions and dyadic rationals

Digits after the point in base two work like digits after the point in base ten. The pattern $0.1101_2$ means $\tfrac{1}{2} + \tfrac{1}{4} + \tfrac{1}{16} = \tfrac{13}{16}$. Any terminating binary fraction with $k$ digits after the point is an integer over $2^k$, and any integer over a power of two has a terminating binary expansion. The numbers of the form $m / 2^k$ are called dyadic rationals, and they are the values represented by finite binary significands and integer exponents. Every finite value of a binary floating-point format in this library is a dyadic.

The denominator tells us which rational numbers are dyadic. A fraction $p/q$ in lowest terms has a terminating binary expansion exactly when $q$ is a power of two. One tenth fails that test: if $F / 2^n = 1/10$ for integers $F$ and $n$, then $10F = 2^n$, so $5$ divides a power of $2$, which is impossible. Long division in base two shows what one tenth has instead. Doubling the fractional part repeatedly gives $0.2, 0.4, 0.8, 1.6, 1.2, 0.4, \ldots$, and the integer parts $0, 0, 0, 1, 1, 0, \ldots$ are the binary digits, so

$$
  \tfrac{1}{10} = 0.0\overline{0011}_2 = 0.000110011001100110011\ldots_2,
$$

a repeating block of four digits that never ends. Storing this expansion at a fixed precision requires choosing a nearby terminating expansion. Discarding the remaining digits and rounding to the nearest value are different choices.

A binary fraction $m / 2^k$ always has a terminating decimal expansion, because $10 = 2 \cdot 5$ is divisible by $2$. The converse holds only when the decimal's denominator in lowest terms is a power of two: $0.5$, $0.25$ and $0.375$ qualify; $0.1$, $0.2$ and $0.3$ do not. Reading a decimal literal into a binary format therefore includes a conversion: the stored value can differ from the rational number denoted by the text. Goldberg's survey [@goldberg1991] is the classic short account of the consequences for floating-point arithmetic.

We can find out exactly how far the stored value is from the decimal we typed. `Binary32` here is the 8-exponent-bit, 23-fraction-bit member of the [[FloatLib.Floats.ExecFloat.Binary]] family, and [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns the exact rational value of a finite word:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

#eval ExecFloat.Binary.toRat? (0.1 : Binary32)
-- some (13421773 / 134217728)

#eval toString (0.1 : Binary32)
-- "13421773 * 2^-27"
```

The stored value is $13421773 \cdot 2^{-27}$, which is exactly

$$
  0.100000001490116119384765625,
$$

about $1.49 \times 10^{-9}$ above one tenth. Its decimal expansion terminates because it is a binary fraction. Nothing was approximated in reading it back: `toRat?` is exact, and the only approximation happened when the literal was rounded to 24 significant bits.

The type for a number $\pm m \cdot 2^e$, with $m$ a natural number and $e$ an integer, is [[FloatLib.Numerics.Dyadic]]. It is a record of three fields, a sign, a significand and an exponent, and [[FloatLib.Numerics.Dyadic.toRat]] gives its rational value. The decoder [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]] takes a finite word to that record:

```lean
open FloatLib.Numerics in
#eval (Dyadic.mk false 13421773 (-27)).toRat
-- 13421773 / 134217728

#eval Model.toDyadic? (ExecFloat.Binary.toModel (0.1 : Binary32))
-- some { negative := false, significand := 13421773, exponent := -27 }
```

The impossibility argument for one tenth is short enough for us to follow in Lean as well. If the proof syntax is unfamiliar, start with the equations: cross-multiplying gives $10F = 2^n$ in the natural numbers, and then $5$ would divide a power of two:

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

## Fixed point or floating point

Fixed-point and floating-point formats allocate their bits differently. Fixed point chooses one exponent for all values. Floating point stores an exponent with each value and reserves a fixed amount of space for its significant digits.

A fixed-point format with $k$ fractional bits stores an integer $n$ and denotes $n \cdot 2^{-k}$. Its values form a uniform grid with spacing $2^{-k}$, so nearest rounding within range has absolute error at most $2^{-k-1}$, and adding two values is exact when the sum fits. With a fixed word width, finer spacing leaves less room for large values. A $w$-bit signed word covers only $[-2^{w-k-1}, 2^{w-k-1})$, so the absolute error bound is independent of magnitude, while the relative error becomes larger for values close to zero. Fixed point suits quantities whose scale is known in advance: currency, sensor readings, the coefficients of a digital filter. The [Patriot clock conversion](#/chapter/a-short-history-of-floating-point/what-imprecision-has-cost) used a fixed-point approximation to one tenth; its error affected tracking when timestamps converted by different rules were subtracted.

A floating-point format instead fixes the precision $p$ and lets the exponent vary. A normal value is $\pm m \cdot 2^e$ with $2^{p-1} \le m < 2^p$. This is scientific notation in base two. Within a binade $[2^e, 2^{e+1})$ the spacing is $2^{e-p+1}$; here the exponent labels the binade's lower endpoint, rather than the scale attached to the integer significand above. Moving to the next binade doubles both the values and the spacing. The absolute rounding error can grow with magnitude while the relative error stays roughly constant in the normal range. Addition can require rounding because aligning the operands may produce more significant bits than the format can store. A small addend can lie between the grid points available at the scale of a larger one. Floating point suits quantities whose scale is unknown or varies over many orders of magnitude, which describes most of scientific computing.

<a id="sign-exponent-width-fraction-width"></a>

## The sign, exponent, and fraction fields

A binary floating-point word has three fields, packed from the most significant end: a sign bit $s$, an exponent field $E$ of $w_e$ bits, and a fraction field $F$ of $w_f$ bits. The total width is $1 + w_e + w_f$. In the library a format is a [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] record holding those two widths, a bias and an encoding policy, and [[FloatLib.Floats.ExecFloat.Binary]] takes the two widths as parameters and derives the storage width from them, so the layout can never disagree with the parameters. For a normal value, normalization determines the significand and a bias determines how to read the exponent.

Normalization removes the redundant representations of a value. A nonzero value $m \cdot 2^e$ has many representations, since $m \cdot 2^e = 2m \cdot 2^{e-1}$. Choosing the one with $2^{p-1} \le m < 2^p$ makes it unique and puts the leading $1$ of $m$ in a fixed position.

In a normal binary value, the leading bit is always $1$, so decoding can supply it without storing it. The fraction field holds the $p - 1 = w_f$ bits after the leading one, and the significand is $1 + F / 2^{w_f}$. Binary32 stores 23 fraction bits and has 24 bits of precision. Counting this implicit bit explains why the precision is one greater than the number of stored fraction bits.

The bias allows an unsigned exponent field to encode negative as well as positive exponents. Storing $E = e + b$ with $b = 2^{w_e - 1} - 1$ avoids a sign bit inside the exponent field, and makes the word order agree with numerical order for positive finite values. A larger exponent field means a larger value, and among equal exponent fields a larger fraction means a larger value, so two positive words compare as unsigned integers. Hardware comparison relies on this. The library computes the conventional bias with `ieeeBias`, which is $127$ for eight exponent bits and $1023$ for eleven.

With these three fields, a normal word denotes

$$
  (-1)^s \cdot \left(1 + \frac{F}{2^{w_f}}\right) \cdot 2^{E - b},
$$

which is exactly the dyadic $(-1)^s (2^{w_f} + F) \cdot 2^{E - b - w_f}$. For binary32, $b = 127$, so the number one has $E = 127$ and $F = 0$, two has $E = 128$, and $-2.5$ uses all three fields, with the sign bit set and a nonzero fraction:

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

In hexadecimal the three words are `0x3f800000`, `0x40000000` and `0xc0200000`. The last has the sign bit set, $E = 128$, and $F = 2^{21}$, so it denotes $-(1 + 1/4) \cdot 2 = -2.5$. [Figure 2.1](#/chapter/from-reals-to-machine-numbers/figure-ch01-binary32-layout) lays the three fields out and reads that word, and the word for `0.1`, bit by bit; [Chapter 08](#/chapter/ieee-binary-formats) decodes every class of word in this detail and derives the constants for other widths from $w_e$ and $w_f$.

![The bit layout of binary32 and the stored words for 0.1 and -2.5, each bit tinted by its field, with the decoding rules for a normal word, a subnormal word and the reserved exponent field](assets/ch01-binary32-layout.png "Binary32 uses one sign bit, eight exponent bits, and twenty-three stored fraction bits. The exponent class determines how the word is decoded.")

We can now work backwards from the word for `0.1` in the figure. One tenth lies between $2^{-4}$ and $2^{-3}$, so its normal exponent is $-4$ and its stored exponent field is $123$. With 24 significant bits, the available values in this binade are integer multiples of $2^{-27}$. Expressing the exact tenth in those units gives

$$
  \frac{1/10}{2^{-27}} = 13421772 + \frac45.
$$

The upper integer, 13421773, is only one fifth of a grid step away; the lower is four fifths away. Nearest rounding therefore selects the significand printed earlier. Subtracting its implicit leading bit leaves the stored fraction field $F = 13421773 - 2^{23} = 5033165$. Together with the exponent field, that gives `0x3dcccccd`. The repeating binary expansion, the exact rational returned by `toRat?`, and the coloured bits in the figure are three ways to read this same choice.

## Subnormals, signed zeros, infinities, NaN

The formula above applies to normal values. IEEE formats reserve the all-zeros and all-ones exponent fields for subnormals, zeros, infinities, and NaNs. These encodings provide outputs for results outside the normal range and for invalid operations. Gradual underflow, which uses the all-zeros field, was a contested part of the 1985 standard; Kahan's account [@kahan1997] describes the debate, also covered in [chapter 03](#/chapter/a-short-history-of-floating-point).

Without the reserved zero field, the smallest positive normal value $2^{1-b}$ would have zero as its lower neighbour, a gap of $2^{1-b}$ against a gap of $2^{1-b-w_f}$ on its upper side. The all-zeros exponent field instead denotes $(-1)^s \cdot F \cdot 2^{1 - b - w_f}$ with no hidden bit: the grid continues below the smallest normal with the same spacing it had just above, all the way to zero. These are the subnormals, and the behaviour is called gradual underflow. For finite operands, this preserves the numerical equality property that $x - y = 0$ exactly when $x = y$. Distinct values cannot acquire a zero difference merely because that difference is smaller than the normal range. As the result approaches zero, it loses significant bits gradually while the absolute spacing stays fixed. The smallest positive binary32 value is $2^{-149}$, and a literal like `1e-39`, which is below the smallest normal $2^{-126}$, lands on this grid rather than collapsing to zero:

```lean
#eval ExecFloat.Binary.toRat?
  (ExecFloat.Binary.nextUp (0 : Binary32))
-- some (1 / 713623846352979940529142984724747568191373312)

#eval ExecFloat.Binary.isSubnormal
  (ExecFloat.Binary.nextUp (0 : Binary32))
-- true

#eval (1e-39 : Binary32)
-- 89203 * 2^-146
```

The first line is $2^{-149}$, the smallest step of the grid, and the second confirms it is a subnormal word. The printer strips trailing zero bits from the significand, so `89203 * 2^-146` is $713624 \cdot 2^{-149}$, a whole number of those steps: the literal was rounded onto the subnormal grid rather than flushed to zero.

Binary32 has far too many values to draw. In [Figure 2.2](#/chapter/from-reals-to-machine-numbers/figure-ch01-toy-grid), we use a toy format with three exponent bits and two fraction bits so we can see every positive finite value. The spacing doubles at each power of two, and the words with the all-zeros exponent field continue the spacing of the first normal binade down to zero.

![The positive values of a toy IEEE-style format with 3 exponent bits and 2 fraction bits, built with FloatFormat.ieee 3 2: the spacing doubles at each power of two, and the subnormal words below 1/4 keep the 1/16 spacing of the first normal binade all the way to zero, with the lower panel enlarging 0 to 1](assets/ch01-toy-grid.png "A toy format with three exponent bits and two fraction bits. Normal spacing doubles at each binade; subnormal spacing stays at 1/16 down to zero.")

In the enlarged lower panel, the three positive subnormals are $1/16$, $2/16$, and $3/16$. The first normal is $4/16$, followed by $5/16$, $6/16$, and $7/16$. Nothing happens to the spacing at the change from open squares to filled circles. The significand coefficient advances from 3 to 4; encoding 4 supplies its leading one implicitly and resets the fraction field to zero. At $1/2$, however, the exponent increases. The next value is $5/8$, so the gap has doubled to $1/8$. This is the point of keeping the exponent fixed for subnormals: they extend the finest normal grid towards zero, although fewer of their stored fraction bits remain significant.

With a sign bit and an all-zeros payload, the pattern with the sign set is available, and the standard uses it for $-0$. The two zeros compare equal, but they are not interchangeable: $1 / (+0) = +\infty$ while $1 / (-0) = -\infty$, so the sign of a zero that arose from underflow records which side of zero the exact result was on. Branch cuts of complex functions depend on this. We keep both zeros in every IEEE format, and this is why our full decoder does not return a plain rational. `toRat?`, which we used above, does return one and so reports $-0$ as `0`. [[FloatLib.Floats.ExecFloat.Binary.decode]] instead returns a [[FloatLib.Numerics.NumericalValue]] whose finite case carries a [[FloatLib.Numerics.SignedRat]], a rational paired with the sign bit the format would store, because a `Rat` has no negative zero and converting through one would silently turn $-0$ into $+0$:

```lean
#eval ExecFloat.Binary.decode (-(0 : Binary32))
-- FloatLib.Numerics.NumericalValue.finite -0

#eval (1 : Binary32) / (-(0 : Binary32))
-- -inf
```

The `finite -0` on the first line is that signed rational; a plain `Rat` would have printed `0`, and the division returns the negative infinity specified for a positive numerator and a negative zero denominator.

The all-ones exponent field with a zero fraction denotes $\pm\infty$. A finite nonzero value divided by zero produces a signed infinity. Overflow can also produce infinity, depending on the rounding direction. The arithmetic rules give $x + \infty = \infty$ for every finite $x$, and finite divided by infinity is zero. The largest finite binary32 value is $(2 - 2^{-23}) \cdot 2^{127}$, about $3.4028235 \times 10^{38}$.

A literal slightly above this largest finite value still rounds down to it. The overflow threshold for nearest-even is the midpoint between that value and the first value of the next binade, if the exponent range extended that far. At that midpoint, and above it, nearest-even returns infinity:

```lean
#eval (1 : Binary32) / 0
-- inf

#eval ExecFloat.Binary.toRat? (3.4028235e38 : Binary32)
-- some 340282346638528859811704183484516925440

#eval (3.5e38 : Binary32)
-- inf
```

The first literal is above the largest finite value by less than half a unit in the last place, so it rounds down to it; `3.5e38` is far past the threshold and becomes `inf`.

The all-ones exponent field with a nonzero fraction denotes Not a Number. It represents invalid real arithmetic such as $0/0$, $\infty - \infty$, $0 \cdot \infty$, $\sqrt{-1}$. Basic arithmetic propagates NaNs according to its exceptional-value rules, and the fraction field can carry a payload. Binary32 has $2^{24} - 2$ NaN words, two signs times $2^{23} - 1$ nonzero fractions, although the printer displays them with the same label:

```lean
#eval (0 : Binary32) / 0
-- nan
```

With subnormals, signed zeros, infinities and NaN added to the normal numbers, the format is closed: every arithmetic operation on a pair of words yields a word. We can therefore define these operations as total functions, including their exceptional cases. [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] records the complete meaning of a word: a finite dyadic with its sign of zero intact, a signed infinity, or a NaN with its sign, signaling class and payload. Later operations can distinguish those encodings when their rules require it.

<a id="rounding-is-not-optional"></a>

## Correct rounding

The exact sum of two finite binary32 values is a dyadic, but it may need more than 24 significant bits or exceed the format's range. Correct rounding specifies which result to return: compute the exact result conceptually, then apply the chosen rounding rule once [@ieee754_2019]. For inputs in the finite range, that rule selects a grid point from an exact value in $\mathbb{R}$. The word-level operation also specifies overflow and exceptional operands. This makes the output determined by the inputs and rounding mode, so a correctness theorem can state an equality with a rounding function rather than merely bound the error.

IEEE 754 requires four rounding directions for binary formats, represented by [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. Round to nearest, ties to even, chooses the nearer representable neighbour and, at an exact midpoint, the one with an even significand. Toward zero chooses the neighbour with smaller magnitude. Toward positive infinity and toward negative infinity choose the neighbour on the named side.

The 2008 revision [@ieee754_2008] also requires ties away from zero for decimal formats. That rule sends each midpoint away from zero; ties to even can send one up and another down. Neither rule guarantees that the errors in a sequence of operations cancel. The error bounds in [chapter 07](#/chapter/the-mathematics-of-rounding) depend on the rule used for each operation and on the values being rounded.

We can get a feel for the four directions by rounding familiar numbers to integers. Before reading the answers, choose which integer each mode should return:

```lean
#eval ExecFloat.Binary.roundToIntegral (2.5 : Binary32)
  .nearestEven
-- 2

#eval ExecFloat.Binary.roundToIntegral (3.5 : Binary32)
  .nearestEven
-- 4

#eval ExecFloat.Binary.roundToIntegral (2.5 : Binary32)
  .towardZero
-- 2

#eval ExecFloat.Binary.roundToIntegral (2.5 : Binary32)
  .towardPositiveInfinity
-- 3

#eval ExecFloat.Binary.roundToIntegral (-2.5 : Binary32)
  .towardNegativeInfinity
-- -3
```

Both $2.5$ and $3.5$ are midpoints, and ties to even sends the first down and the second up. The theorems [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundToIntegral_nearestEven]], `toReal_roundToIntegral_towardZero`, `toReal_roundToIntegral_towardPositiveInfinity` and `toReal_roundToIntegral_towardNegativeInfinity` state that, for finite inputs in a conventional IEEE format satisfying the range condition below, the decoded result is the nearest-even integer, the truncation, $\lceil x \rceil$ or $\lfloor x \rfloor$ of the decoded input.

The additional condition is `(fmt.fracWidth : Int) ≤ fmt.maxNormalExponent`, which ensures that the rounded integer remains representable. The standard IEEE interchange formats satisfy it; a custom descriptor needs its own proof.

To compare the four rules, follow the arrows in [Figure 2.3](#/chapter/from-reals-to-machine-numbers/figure-ch01-rounding-directions): the same three inputs appear on the integer line, one row per direction.

![The four directions of IEEERoundingMode on the midpoints -2.5, 2.5 and 3.5 when the representable values are the integers, one row per direction, with an arrow from each input to the integer that direction chooses](assets/ch01-rounding-directions.png "Four rounding directions on an integer grid. At a midpoint, nearest-even chooses by the parity of the destination integer.")

The same directions apply to arithmetic. In binary32 the exact sum of $1$ and $10^{-9}$ lies between $1$ and the next representable value $1 + 2^{-23}$, and much closer to $1$: the excess is about $0.0084$ of the gap. Nearest rounding returns $1$. Rounding toward positive infinity returns the upper neighbour, which is the value `nextUp` produces:

```lean
#eval ExecFloat.Binary.add (1 : Binary32) 1e-9
  (rounding := .nearestEven)
-- 1

#eval ExecFloat.Binary.add (1 : Binary32) 1e-9
  (rounding := .towardPositiveInfinity)
-- 8388609 * 2^-23

#eval ExecFloat.Binary.toRat?
  (ExecFloat.Binary.nextUp (1 : Binary32))
-- some (8388609 / 8388608)
```

The directed modes are what make the library's interval arithmetic possible: round the lower endpoint down and the upper endpoint up, and the exact result is enclosed.

<a id="why-the-exact-value-is-a-dyadic-and-the-rounded-value-is-a-contract-on-the-reals"></a>

## Exact intermediates and real-valued rounding

An executable addition needs a finite representation of its exact intermediate. An error bound needs a way to compare the rounded result with the number that was intended. Dyadics provide the first, and a rounding function on the real numbers provides the second.

The reference definition of addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add]], does three things in order. It decodes both finite operands to `Dyadic` records with `toDyadic?`, adds the records exactly with integer arithmetic on significands and exponents, and applies [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]] to the exact sum. That final step rounds once, to nearest with ties to even, into the destination format. Multiplication and fused multiply-add follow the same pattern; the fused operation rounds only after adding the third operand to the exact product. The final rounding is the only approximation in this calculation.

We can follow the addition by hand with the dyadics $3 \cdot 2^{-1}$ and $1 \cdot 2^{-2}$, representing 1.5 and 0.25. Aligning them at exponent $-2$ shifts the first significand left by one bit:

$$
  3 \cdot 2^{-1} + 1 \cdot 2^{-2}
  = (6 + 1) \cdot 2^{-2}
  = 7 \cdot 2^{-2}.
$$

The integer addition produces 7, and the rounder returns 1.75 unchanged because it fits. The reference uses the same alignment when the exact significand is too long to store; its integers can grow to retain the bits that the final rounding decision needs.

Sums and products of dyadics are dyadics. Their exact intermediates can therefore be represented by integer fields, and rounding can inspect the significand, exponent, and discarded bits directly. No fraction normalization is needed. The sign field also preserves a negative zero that a plain `Rat` would lose.

Division and square root need more information because their exact results need not be dyadic. Division can compare an exact rational quotient with the candidate grid points. Square root can use an integer square root and its remainder to determine which side of a rounding midpoint contains the true result. Rounding needs that comparison; it does not require writing every digit of an infinite expansion.

For instance, consider rounding $\sqrt{2}$ to a three-bit significand. Its two neighbours are $5/4$ and $3/2$, with midpoint $11/8$. The root and midpoint are positive, so comparing them is equivalent to comparing their squares. Since $(11/8)^2 = 121/64 < 2$, the root is above the midpoint and rounds to $3/2$. We have decided the result using integers, without approximating the decimal expansion of the root. The integer-square-root calculation in the implementation supplies the candidate and remainder needed for this kind of comparison.

Error analysis compares these finite computations with real arithmetic. Higham's textbook [@higham2002], for example, states rounding bounds on a real-valued grid. The function [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] describes nearest-even rounding on the grid with a format's precision and subnormal spacing. Unlike a stored format, this mathematical grid has no upper exponent limit.

The corresponding reading of a word is [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]]. It returns the dyadic's real value for finite words and zero by convention for infinities and NaNs, which have no real value. Consequently, a theorem that uses `toReal` to describe arithmetic must exclude exceptional words or handle them separately.

The theorem [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] relates the two rounding functions: for a format with the IEEE encoding and conventional bias, whenever the executable rounder returns a finite word, the real value of that word is `roundAt` applied to the real value of the exact input. We can then state an operation's rounding rule as an equation over $\mathbb{R}$. The theorem for addition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]], says exactly what correct rounding promises:

$$
  \operatorname{toReal}(\operatorname{add}(x, y))
  = \operatorname{roundAt}_{f}(\operatorname{toReal}(x) + \operatorname{toReal}(y)).
$$

The hypotheses are that the format uses the IEEE encoding and conventional bias and that $x$, $y$ and the computed sum are finite; the last excludes overflow, and it is there because a sum of two finite words can be infinite while a sum of two reals cannot. The equation allows the error bounds over $\mathbb{R}$ to be applied to the decoded executable result once those finiteness conditions have been established. [Chapter 06](#/chapter/the-numerical-models) proves an instance of it on concrete words, shows how the finiteness hypotheses are discharged, and gives the relational form the rest of the library shares.

## The unit in the last place

Two quantities measure the grid, one absolute and one relative. The unit in the last place at $x$, written $\operatorname{ulp}(x)$, is the spacing of representable values in the binade of $x$: for $2^e \le |x| < 2^{e+1}$ and precision $p$, it is $2^{e-p+1}$. At one, binary32 has $\operatorname{ulp}(1) = 2^{-23}$, the gap between $1$ and the value `nextUp` returned above. The library's [[FloatLib.Floats.Formats.BinaryInterchange.Model.ulpAt]] is this function for a format's grid, including the flat spacing in the subnormal range, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.epsilonAt]] is half of it. Correct rounding to nearest guarantees

$$
  |\operatorname{round}(x) - x| \le \tfrac{1}{2}\operatorname{ulp}(x),
$$

and [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] proves this for every real $x$ and every binary format. The grid used by `roundAt` has no largest element, so it cannot overflow. To apply the bound to a stored result, we need the finiteness hypotheses from the previous section:

```lean
example (x : ℝ) :
    |Model.roundAt FloatFormat.binary32 x - x| ≤
      Model.epsilonAt FloatFormat.binary32 x :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 x
```

Relative error is measured using the unit roundoff $u = 2^{-p}$, half the ulp at one, so $u = 2^{-24} \approx 5.96 \times 10^{-8}$ for binary32 and $u = 2^{-53} \approx 1.11 \times 10^{-16}$ for binary64. In the normal range the half-ulp bound turns into a relative bound, $\operatorname{round}(x) = x(1 + \delta)$ with $|\delta| \le u$, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] proves it under the hypotheses that $x$ is nonzero, so that the relative error is defined, and that $|x|$ is at least the smallest normal magnitude.

In the subnormal range the spacing stops shrinking with magnitude. The relative bound need not hold there, so we use the absolute half-ulp bound. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops both bounds for arbitrary formats.

To get the relative bound, we divide the absolute bound by the input magnitude and use the lower endpoint of its normal binade. For $2^e \le |x| < 2^{e+1}$,

$$
  \frac{|\operatorname{round}(x)-x|}{|x|}
  \le \frac{2^{e-p}}{|x|}
  \le \frac{2^{e-p}}{2^e}
  = 2^{-p}.
$$

In the subnormal range the numerator stops shrinking with the denominator. At the binary32 midpoint $x = 2^{-150}$, halfway between zero and the smallest positive subnormal, nearest-even returns zero. The absolute error is still half a grid step, but the relative error is one: the entire input has been lost. An analysis of very small values must therefore keep an absolute error allowance even when a relative bound works elsewhere.

The sum `0.1 + 0.2` shows how rounding the inputs interacts with rounding an operation. In binary32 it happens to give the same word as the literal `0.3`. In binary64 the sum is the next representable value above that literal:

```lean
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

#eval (0.1 : Binary64) + 0.2
-- 1351079888211149 * 2^-52

#eval (0.3 : Binary64)
-- 5404319552844595 * 2^-54

#eval ExecFloat.Binary.nextUp (0.3 : Binary64)
-- 1351079888211149 * 2^-52
```

We can now account for the mismatch. Three roundings happened in computing the sum, one for each input literal and one for the addition, and each was correct. The binary64 value of `0.1` is $0.1000000000000000055511\ldots$, the value of `0.2` is twice that, and their exact sum is $10808639105689191 \cdot 2^{-55}$, which sits precisely at the midpoint between the binary64 word for `0.3` and its upper neighbour. Ties to even picks the neighbour with the even significand, which is the upper one, and that word is `nextUp` of the binary64 `0.3`. The sum is $0.3000000000000000444\ldots$ and the stored `0.3` is $0.2999999999999999888\ldots$. The sum's own rounding moved the exact value by $2^{-55}$, exactly half a unit in the last place at $0.3$, and the two words end up one unit apart.
