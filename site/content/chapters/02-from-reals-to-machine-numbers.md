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

For our literal, the exact reference is $1/10$, so a rational number is enough. Square roots and transcendental functions can return irrational values, so for general statements we use the reals. In a Lean theorem, $\sqrt{2}$ denotes the exact nonnegative real number whose square is two. A floating-point approximation to it is a different number, and squaring that approximation need not give two exactly. To state its error, we need both values, the stored approximation and the real number it approximates.

The real numbers complete the rational number line. A sequence of rational approximations such as $3, 3.1, 3.14, 3.141, \ldots$ approaches a limit, even though that limit need not be rational. Completeness says that every Cauchy sequence has a limit on the line, where a Cauchy sequence is one whose terms eventually stay arbitrarily close to one another. This includes numbers such as $\sqrt{2}$ and $\pi$, and lets calculus reason about limits without leaving the number system.

## A fixed word stores finitely many values

An $n$-bit word has $2^n$ states. A 32-bit word has $2^{32}$ of them, so any interpretation of those states can give at most $2^{32}$ distinct meanings. A numeric format specifies that interpretation, saying which number each pattern denotes and which patterns stand for exceptional results. A 64-bit word raises the count to $2^{64}$, but that's still a finite set. More bits can put the represented values closer together or stretch their range, but no number of bits will represent every real number.

An operation on two members of this finite set can have an exact result outside it. So a format needs a set of representable values and a rounding rule, which picks an output when the exact result is missing.

## Binary fractions and dyadic rationals

The binary pattern $0.1101_2$ means $\tfrac{1}{2} + \tfrac{1}{4} + \tfrac{1}{16} = \tfrac{13}{16}$, because digits after the point work the same way in base two as in base ten. A terminating binary fraction with $k$ digits after the point is an integer over $2^k$, and any integer over a power of two has a terminating binary expansion. Numbers of the form $m / 2^k$ are called dyadic rationals. They're the values that finite binary significands and integer exponents can represent, and every finite value of a binary floating-point format in this library is one of them.

You can tell from the denominator whether a rational number is dyadic. A fraction $p/q$ in lowest terms has a terminating binary expansion exactly when $q$ is a power of two, and one tenth fails that test. If $F / 2^n = 1/10$ for integers $F$ and $n$, then $10F = 2^n$, so $5$ divides a power of $2$, which is impossible.

Long division in base two shows what happens instead. Doubling the fractional part again and again gives $0.2, 0.4, 0.8, 1.6, 1.2, 0.4, \ldots$, and the integer parts $0, 0, 0, 1, 1, 0, \ldots$ are the binary digits, so

$$
  \tfrac{1}{10} = 0.0\overline{0011}_2 = 0.000110011001100110011\ldots_2,
$$

a block of four digits that repeats forever. Storing this expansion at a fixed precision means picking a nearby terminating expansion, and simply chopping off the remaining digits is a different choice from rounding to the nearest value.

A binary fraction $m / 2^k$ has a terminating decimal expansion, because $10 = 2 \cdot 5$ is divisible by $2$. The converse only holds when the decimal's denominator in lowest terms is a power of two, so $0.5$, $0.25$ and $0.375$ qualify, while $0.1$, $0.2$ and $0.3$ don't. Reading a decimal literal into a binary format is therefore a conversion, and the stored value can differ from the rational number the text denotes. Goldberg's survey [@goldberg1991] is the classic short account of what that does to floating-point arithmetic.

We can measure the rounding of our tenth without estimating any digits. Here `Binary32` is the 8-exponent-bit, 23-fraction-bit member of the [[FloatLib.Floats.ExecFloat.Binary]] family. [[FloatLib.Floats.ExecFloat.Binary.toRat?]] returns the exact rational value of a finite word:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

#eval ExecFloat.Binary.toRat? (0.1 : Binary32)
-- some (13421773 / 134217728)

#eval toString (0.1 : Binary32)
-- "0.1"
```

So the stored value is $13421773 \cdot 2^{-27}$, which is exactly

$$
  0.100000001490116119384765625,
$$

about $1.49 \times 10^{-9}$ above one tenth. Its decimal expansion terminates because it's a binary fraction. Since `toRat?` is exact, the only approximation happened when the literal was rounded to 24 significant bits.

In the library, a number $\pm m \cdot 2^e$ with $m$ a natural number and $e$ an integer has the type [[FloatLib.Numerics.Dyadic]]. It's a record with three fields, for the sign, the significand and the exponent, and [[FloatLib.Numerics.Dyadic.toRat]] gives its rational value. To get that record from a finite word, use the decoder [[FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?]]:

```lean
open FloatLib.Numerics in
#eval (Dyadic.mk false 13421773 (-27)).toRat
-- 13421773 / 134217728

#eval Model.toDyadic? (ExecFloat.Binary.toModel (0.1 : Binary32))
-- some { negative := false, significand := 13421773, exponent := -27 }
```

The Lean proof of the impossibility follows the same arithmetic. Cross-multiplying gives $10F = 2^n$ in the natural numbers, and then $5$ would divide a power of two:

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

Fixed-point and floating-point formats spend their bits differently. Fixed point picks one exponent for all values, while floating point stores an exponent with each value and keeps a fixed amount of space for its significant digits.

A fixed-point format with $k$ fractional bits stores an integer $n$ and denotes $n \cdot 2^{-k}$, so its values sit on a uniform grid with spacing $2^{-k}$. Nearest rounding within range has absolute error at most $2^{-k-1}$, and adding two values is exact when the sum fits. But with a fixed word width, finer spacing leaves less room for large values, and a $w$-bit signed word covers only $[-2^{w-k-1}, 2^{w-k-1})$. Its absolute error bound is the same at every magnitude, while the relative error gets larger for values close to zero. Fixed point suits quantities whose scale you know in advance, like currency, sensor readings, or the coefficients of a digital filter. The [Patriot clock conversion](#/chapter/a-short-history-of-floating-point/what-imprecision-has-cost) used a fixed-point approximation to one tenth, and its error affected tracking when timestamps converted by different rules were subtracted.

A floating-point format fixes the precision $p$ and lets the exponent vary. A normal value is $\pm m \cdot 2^e$ with $2^{p-1} \le m < 2^p$, which is scientific notation in base two. Within a binade $[2^e, 2^{e+1})$ the spacing is $2^{e-p+1}$. Here the exponent labels the binade's lower endpoint, and that isn't the same as the scale attached to the integer significand above. Each move to the next binade doubles both the values and the spacing, so the absolute rounding error can grow with magnitude, while the relative error stays roughly constant in the normal range. Addition can need rounding, because aligning the operands may produce more significant bits than the format can store. A small addend can also fall between the grid points available at the scale of a larger one. Floating point suits quantities whose scale is unknown or varies over many orders of magnitude, which describes most of scientific computing.

## The sign, exponent, and fraction fields

A binary floating-point word has three fields, packed from the most significant end. First comes a sign bit $s$, then an exponent field $E$ of $w_e$ bits, then a fraction field $F$ of $w_f$ bits. The total width is $1 + w_e + w_f$. In the library a format is a [[FloatLib.Floats.Formats.BinaryInterchange.FloatFormat]] record holding those two widths, a bias and an encoding policy. [[FloatLib.Floats.ExecFloat.Binary]] takes the two widths as parameters and derives the storage width from them, so the layout can never disagree with the parameters. For a normal value, normalization fixes the significand and a bias says how to read the exponent.

Normalization gets rid of redundant representations. A nonzero value $m \cdot 2^e$ has many of them, since $m \cdot 2^e = 2m \cdot 2^{e-1}$. Choosing the one with $2^{p-1} \le m < 2^p$ makes it unique and puts the leading $1$ of $m$ in a fixed position.

In a normal binary value the leading bit is therefore always $1$, so decoding can supply it and the word doesn't have to store it. The fraction field holds the $p - 1 = w_f$ bits after the leading one, and the significand is $1 + F / 2^{w_f}$. That implicit bit is why the precision is one greater than the number of stored fraction bits. Binary32 stores 23 fraction bits and has 24 bits of precision.

A bias lets an unsigned exponent field encode negative exponents as well as positive ones. Storing $E = e + b$ with $b = 2^{w_e - 1} - 1$ avoids a sign bit inside the exponent field. It also makes the word order agree with numerical order for positive finite values. A larger exponent field means a larger value, and among equal exponent fields a larger fraction means a larger value, so two positive words compare as unsigned integers. Hardware comparison relies on this. In the library, `ieeeBias` computes the conventional bias, which is $127$ for eight exponent bits and $1023$ for eleven. With these three fields, a normal word denotes

$$
  (-1)^s \cdot \left(1 + \frac{F}{2^{w_f}}\right) \cdot 2^{E - b},
$$

which is the dyadic $(-1)^s (2^{w_f} + F) \cdot 2^{E - b - w_f}$. For binary32, $b = 127$, so the number one has $E = 127$ and $F = 0$, and two has $E = 128$. Let's ask Lean for those two words and for $-2.5$, which uses all three fields, with the sign bit set and a nonzero fraction:

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

In hexadecimal the three words are `0x3f800000`, `0x40000000` and `0xc0200000`. That last word has the sign bit set, $E = 128$, and $F = 2^{21}$, so it denotes $-(1 + 1/4) \cdot 2 = -2.5$. [Figure 2.1](#/chapter/from-reals-to-machine-numbers/figure-ch01-binary32-layout) lays out the three fields and reads that word bit by bit, along with the word for `0.1`. [Chapter 08](#/chapter/ieee-binary-formats) decodes every class of word at this level of detail, and it also derives the constants for other widths from $w_e$ and $w_f$.

![Binary32's sign, exponent, and fraction fields, with the stored words for 0.1 and -2.5](assets/ch01-binary32-layout.png "Binary32 uses one sign bit, eight exponent bits, and twenty-three stored fraction bits. The two normal values illustrate how those fields encode a number.")

Now we can work backwards from the word for `0.1` in the figure. One tenth lies between $2^{-4}$ and $2^{-3}$, so its normal exponent is $-4$ and its stored exponent field is $123$. With 24 significant bits, the values available in this binade are integer multiples of $2^{-27}$, and in those units the exact tenth is

$$
  \frac{1/10}{2^{-27}} = 13421772 + \frac45.
$$

The upper integer, 13421773, is only one fifth of a grid step away, and the lower one is four fifths away, so nearest rounding picks the significand we printed earlier. Subtract its implicit leading bit and you're left with the stored fraction field $F = 13421773 - 2^{23} = 5033165$. Together with the exponent field, that gives `0x3dcccccd`. You can read the same choice in the repeating binary expansion, in the exact rational that `toRat?` returns, and in the coloured bits of the figure.

## Subnormals, signed zeros, infinities, NaN

IEEE formats reserve the all-zeros and all-ones exponent fields for subnormals, zeros, infinities, and NaNs, which provide outputs for results outside the normal range and for invalid operations. Gradual underflow uses the all-zeros field, and it was a contested part of the 1985 standard. Kahan's account [@kahan1997] describes the debate, and [chapter 03](#/chapter/a-short-history-of-floating-point) covers it too.

Without the reserved zero field, the smallest positive normal value $2^{1-b}$ would have zero as its lower neighbour. That gap would be $2^{1-b}$, against a gap of $2^{1-b-w_f}$ on its upper side. Instead, the all-zeros exponent field denotes $(-1)^s \cdot F \cdot 2^{1 - b - w_f}$ with no hidden bit. So the grid continues below the smallest normal with the same spacing it had just above, all the way down to zero. These are the subnormals, and the behaviour is called gradual underflow. For finite operands it preserves the numerical equality property that $x - y = 0$ exactly when $x = y$. Distinct values can't end up with a zero difference just because that difference is smaller than the normal range. As a result approaches zero it loses significant bits gradually, while the absolute spacing stays fixed. The smallest positive binary32 value is $2^{-149}$. A literal like `1e-39` is below the smallest normal $2^{-126}$, and it lands on this grid instead of collapsing to zero:

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

The first line gives $2^{-149}$, the smallest step of the grid, and the second confirms that it's a subnormal word. The literal prints back as `1e-39`, the shortest decimal that reads back as its stored value $713624 \cdot 2^{-149}$. That's a whole number of those steps, so the literal was rounded onto the subnormal grid and wasn't flushed to zero. Binary32 has far too many values to draw, so [Figure 2.2](#/chapter/from-reals-to-machine-numbers/figure-ch01-toy-grid) uses a toy format with three exponent bits and two fraction bits. It's small enough that we can see every positive finite value. Spacing doubles at each power of two, and the words with the all-zeros exponent field carry the spacing of the first normal binade down to zero.

![Nonnegative values of a toy IEEE format with three exponent bits and two fraction bits. Squares mark zero and subnormals; circles mark normal values. Normal spacing doubles at each power of two, while subnormals keep the first normal spacing of 1/16.](assets/ch01-toy-grid.png "A toy format with three exponent bits and two fraction bits. Normal spacing doubles at each binade; subnormal spacing stays at 1/16 down to zero.")

There are three positive subnormals, $1/16$, $2/16$, and $3/16$. Then comes the first normal, $4/16$, followed by $5/16$, $6/16$, and $7/16$. Nothing happens to the spacing where open squares change to filled circles. The significand coefficient goes from 3 to 4. Encoding 4 supplies its leading one implicitly and resets the fraction field to zero. At $1/2$, though, the exponent goes up. The next value is $5/8$, so the gap has doubled to $1/8$. That's the point of keeping the exponent fixed for subnormals. They extend the finest normal grid towards zero, even though fewer of their stored fraction bits stay significant.

Because the sign is its own bit, the all-zeros payload can also appear with the sign set, and the standard uses that pattern for $-0$. The two zeros compare equal, but you can't swap one for the other. In division, $1 / (+0) = +\infty$ while $1 / (-0) = -\infty$, so the sign of a zero that came from underflow records which side of zero the exact result was on. Branch cuts of complex functions depend on this.

We keep both zeros in every IEEE format, and that's why our full decoder doesn't return a plain rational. `toRat?`, which we used above, does return one, so it reports $-0$ as `0`. [[FloatLib.Floats.ExecFloat.Binary.decode]] returns a [[FloatLib.Numerics.NumericalValue]] instead. Its finite case carries a [[FloatLib.Numerics.SignedRat]], which is a rational paired with the sign bit the format would store. The sign is there because a `Rat` has no negative zero and converting through one would silently turn $-0$ into $+0$:

```lean
#eval ExecFloat.Binary.decode (-(0 : Binary32))
-- FloatLib.Numerics.NumericalValue.finite -0

#eval (1 : Binary32) / (-(0 : Binary32))
-- -inf
```

That `finite -0` on the first line is the signed rational, where a plain `Rat` would have printed `0`. The division returns the negative infinity specified for a positive numerator and a negative zero denominator.

Infinities have their own encoding. An all-ones exponent field with a zero fraction denotes $\pm\infty$. Dividing a finite nonzero value by zero produces a signed infinity, and overflow can also produce one, depending on the rounding direction. The arithmetic rules give $x + \infty = \infty$ for every finite $x$, and a finite value divided by infinity is zero.

The largest finite binary32 value is $(2 - 2^{-23}) \cdot 2^{127}$, about $3.4028235 \times 10^{38}$. A literal slightly above that largest finite value still rounds down to it. For nearest-even, the overflow threshold is the midpoint between that value and the first value of the next binade, if the exponent range extended that far. At the midpoint and above it, nearest-even returns infinity:

```lean
#eval (1 : Binary32) / 0
-- inf

#eval ExecFloat.Binary.toRat? (3.4028235e38 : Binary32)
-- some 340282346638528859811704183484516925440

#eval (3.5e38 : Binary32)
-- inf
```

The first literal is less than half a unit in the last place above the largest finite value, so it rounds down to it, while `3.5e38` is far past the threshold and becomes `inf`.

With a nonzero fraction, the all-ones exponent field denotes Not a Number. A NaN stands for invalid real arithmetic such as $0/0$, $\infty - \infty$, $0 \cdot \infty$, $\sqrt{-1}$. Basic arithmetic propagates NaNs according to its exceptional-value rules, and the fraction field can carry a payload. Binary32 has $2^{24} - 2$ NaN words, two signs times $2^{23} - 1$ nonzero fractions, which is a lot of ways to say "not a number" :) The printer shows them all with the same label:

```lean
#eval (0 : Binary32) / 0
-- nan
```

Add subnormals, signed zeros, infinities and NaN to the normal numbers and the format is closed, so every arithmetic operation on a pair of words gives back a word. That means we can define these operations as total functions, exceptional cases included. [[FloatLib.Floats.Formats.BinaryInterchange.Model.exactValue]] records the complete meaning of a word. That meaning is a finite dyadic with its sign of zero intact, a signed infinity, or a NaN with its sign, signaling class and payload. Later operations can tell those encodings apart when their rules require it.

## Correct rounding

Add two finite binary32 values and the exact sum is a dyadic, but it may need more than 24 significant bits, or exceed the format's range. Correct rounding says which result to return. Compute the exact result conceptually, then apply the chosen rounding rule once [@ieee754_2019]. For inputs in the finite range, that rule picks a grid point given an exact value in $\mathbb{R}$, and the word-level operation also specifies overflow and exceptional operands. The inputs and rounding mode determine the output, so a correctness theorem can identify the required rounded answer rather than merely bound its distance from the exact result.

IEEE 754 requires four rounding directions for binary formats. [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]] represents them, along with ties away from zero and MPFR's rounding away from zero. Round to nearest, ties to even, picks the nearer representable neighbour, and at an exact midpoint it picks the one with an even significand. Toward zero picks the neighbour with smaller magnitude. Toward positive infinity and toward negative infinity pick the neighbour on the named side.

For decimal formats, the 2008 revision [@ieee754_2008] also requires ties away from zero. That rule sends every midpoint away from zero, while ties to even can send one up and another down. Neither rule guarantees that the errors in a sequence of operations cancel, and the error bounds in [chapter 07](#/chapter/the-mathematics-of-rounding) depend on the rule used for each operation and on the values being rounded. Let's try the four directions on the midpoints $2.5$ and $3.5$, and on the negative input $-2.5$:

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

Both $2.5$ and $3.5$ are midpoints, and ties to even sends the first down and the second up. The theorems [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundToIntegral_nearest]], `toReal_roundToIntegral_towardZero`, `toReal_roundToIntegral_up` and `toReal_roundToIntegral_down` cover finite inputs in a conventional IEEE format that satisfies the range condition below. They state that the decoded result is the nearest-even integer, the truncation, $\lceil x \rceil$ or $\lfloor x \rfloor$ of the decoded input. That range condition is `(fmt.fracWidth : Int) ≤ fmt.maxNormalExponent`, and it keeps the rounded integer representable. The standard IEEE interchange formats satisfy it, but a custom descriptor needs its own proof. To compare the four rules, follow the arrows in [Figure 2.3](#/chapter/from-reals-to-machine-numbers/figure-ch01-rounding-directions), where each rule maps the same three inputs to integers.

![The four required directions of IEEERoundingMode on the midpoints -2.5, 2.5 and 3.5, with arrows to the chosen integers](assets/ch01-rounding-directions.png "Four rounding directions on an integer grid. At a midpoint, nearest-even chooses by the parity of the destination integer.")

Arithmetic uses the same directions. In binary32 the exact sum of $1$ and $10^{-9}$ lies between $1$ and the next representable value $1 + 2^{-23}$. It's much closer to $1$, since the excess is only about $0.0084$ of the gap, so nearest rounding returns $1$. Rounding toward positive infinity returns the upper neighbour, which is the value `nextUp` produces:

```lean
#eval ExecFloat.Binary.add (1 : Binary32) 1e-9 (mode := .nearest)
-- 1

#eval ExecFloat.Binary.add (1 : Binary32) 1e-9 (mode := .up)
-- 1.0000001

#eval ExecFloat.Binary.toRat?
  (ExecFloat.Binary.nextUp (1 : Binary32))
-- some (8388609 / 8388608)
```

Directed modes are what make the library's interval arithmetic possible, and they're what we used to enclose one third in the first chapter. Round the lower endpoint down and the upper endpoint up, and the exact result is enclosed.

## Exact intermediates and real-valued rounding

An executable addition needs a finite representation of its exact intermediate, and an error bound needs a way to compare the rounded result with the number that was intended. Dyadics give us the first, and a rounding function on the real numbers gives us the second.

Addition's reference definition, [[FloatLib.Floats.Formats.BinaryInterchange.Model.Spec.add]], does three things in order. It decodes both finite operands to `Dyadic` records with `toDyadic?`, adds the records exactly with integer arithmetic on significands and exponents, and then applies [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundDyadic]] to the exact sum. That last step rounds once, to nearest with ties to even, into the destination format, and it's the only approximation in the whole calculation. Multiplication and fused multiply-add follow the same pattern. The fused operation doesn't round until it has added the third operand to the exact product.

You can follow the addition by hand with the dyadics $3 \cdot 2^{-1}$ and $1 \cdot 2^{-2}$, which represent 1.5 and 0.25. Aligning them at exponent $-2$ shifts the first significand left by one bit:

$$
  3 \cdot 2^{-1} + 1 \cdot 2^{-2}
  = (6 + 1) \cdot 2^{-2}
  = 7 \cdot 2^{-2}.
$$

Integer addition produces 7, and the rounder returns 1.75 unchanged because it fits. When the exact significand is too long to store, the reference uses the same alignment, and its integers can grow to keep the bits that the final rounding decision needs. That works because sums and products of dyadics are dyadics. Their exact intermediates fit in integer fields, and rounding can look at the significand, exponent, and discarded bits as they are, with no fraction normalization. The sign field also keeps a negative zero that a plain `Rat` would lose.

Division and square root need more information, because their exact results need not be dyadic. Division can compare an exact rational quotient with the candidate grid points. Square root can use an integer square root and its remainder to work out which side of a rounding midpoint the true result is on. Rounding needs that comparison, and it never has to write out every digit of an infinite expansion.

For example, round $\sqrt{2}$ to a three-bit significand. Its two neighbours are $5/4$ and $3/2$, with midpoint $11/8$. Both the root and the midpoint are positive, so comparing them is the same as comparing their squares. Since $(11/8)^2 = 121/64 < 2$, the root is above the midpoint and rounds to $3/2$. We decided that with integers, without approximating the decimal expansion of the root. In the implementation, the integer-square-root calculation supplies the candidate and remainder that this kind of comparison needs.

Error analysis compares these finite computations with real arithmetic. Higham's textbook [@higham2002], for example, states rounding bounds on a real-valued grid. In the library, [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] describes nearest-even rounding on the grid with a format's precision and subnormal spacing. This mathematical grid has no upper exponent limit, though every stored format has one.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal]] is the matching way to read a word. It returns the dyadic's real value for finite words, and since infinities and NaNs have no real value, it returns zero for them by convention. So a theorem that uses `toReal` to describe arithmetic has to exclude exceptional words or deal with them on their own.

[[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_roundDyadic_eq_roundAt]] connects the two rounding functions. Take a format with the IEEE encoding and conventional bias. Whenever the executable rounder returns a finite word, the real value of that word is `roundAt` applied to the real value of the exact input. That lets us state an operation's rounding rule as an equation over $\mathbb{R}$. For addition the theorem is [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]], and it says what correct rounding promises:

$$
  \operatorname{toReal}(\operatorname{add}(x, y))
  = \operatorname{roundAt}_{f}(\operatorname{toReal}(x) + \operatorname{toReal}(y)).
$$

Its hypotheses are that the format uses the IEEE encoding and conventional bias, and that $x$, $y$ and the computed sum are finite. That last one excludes overflow, and it's there because a sum of two finite words can be infinite, while a sum of two reals can't. Once you've established those finiteness conditions, the equation lets you apply the error bounds over $\mathbb{R}$ to the decoded executable result. [Chapter 06](#/chapter/the-numerical-models) proves an instance of it on concrete words and shows how the finiteness hypotheses are discharged, and it also gives the relational form the rest of the library shares.

## The unit in the last place

Two quantities measure the grid, one absolute and one relative. The unit in the last place at $x$, written $\operatorname{ulp}(x)$, is the spacing of representable values in the binade of $x$. For $2^e \le |x| < 2^{e+1}$ and precision $p$ it's $2^{e-p+1}$. At one, binary32 has $\operatorname{ulp}(1) = 2^{-23}$, the gap between $1$ and the value `nextUp` returned above. In the library, [[FloatLib.Floats.Formats.BinaryInterchange.Model.ulpAt]] is this function for a format's grid, including the flat spacing in the subnormal range, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.epsilonAt]] is half of it. Correct rounding to nearest guarantees

$$
  |\operatorname{round}(x) - x| \le \tfrac{1}{2}\operatorname{ulp}(x),
$$

and [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] proves this for every real $x$ and every binary format. Because the grid that `roundAt` uses has no largest element, it can't overflow. So to apply the bound to a stored result, we need the finiteness hypotheses from the previous section:

```lean
example (x : ℝ) :
    |Model.roundAt FloatFormat.binary32 x - x| ≤
      Model.epsilonAt FloatFormat.binary32 x :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 x
```

Relative error is measured with the unit roundoff $u = 2^{-p}$, which is half the ulp at one. That makes $u = 2^{-24} \approx 5.96 \times 10^{-8}$ for binary32 and $u = 2^{-53} \approx 1.11 \times 10^{-16}$ for binary64. In the normal range the half-ulp bound turns into a relative bound, $\operatorname{round}(x) = x(1 + \delta)$ with $|\delta| \le u$. [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] proves it under two hypotheses. One is that $x$ is nonzero, so that the relative error is defined, and the other is that $|x|$ is at least the smallest normal magnitude. The relative bound need not hold in the subnormal range, so there we use the absolute half-ulp bound. [Chapter 07](#/chapter/the-mathematics-of-rounding) develops both bounds for arbitrary formats.

To get the relative bound, divide the absolute bound by the input magnitude and use the lower endpoint of its normal binade. For $2^e \le |x| < 2^{e+1}$,

$$
  \frac{|\operatorname{round}(x)-x|}{|x|}
  \le \frac{2^{e-p}}{|x|}
  \le \frac{2^{e-p}}{2^e}
  = 2^{-p}.
$$

This derivation breaks in the subnormal range, where the numerator stops shrinking with the denominator. Take the binary32 midpoint $x = 2^{-150}$, halfway between zero and the smallest positive subnormal. Nearest-even returns zero. The absolute error is still half a grid step, but the relative error is one, because the entire input has been lost. So an analysis of very small values has to keep an absolute error allowance, even when a relative bound works elsewhere.

Back to `0.1 + 0.2`, which shows how rounding the inputs interacts with rounding an operation. In binary32 it happens to give the same word as the literal `0.3`, but in binary64 the sum is the next representable value above that literal:

```lean
#eval (0.1 : Binary64) + 0.2
-- 0.30000000000000004

#eval (0.3 : Binary64)
-- 0.3

#eval ExecFloat.Binary.nextUp (0.3 : Binary64)
-- 0.30000000000000004
```

The mismatch comes from three roundings, one for each input literal and one for the addition. Each obeyed nearest-even. The binary64 value of `0.1` is $0.1000000000000000055511\ldots$, and the value of `0.2` is twice that. Their exact sum is $10808639105689191 \cdot 2^{-55}$, which lands right on the midpoint between the binary64 word for `0.3` and its upper neighbour. Ties to even picks the neighbour with the even significand, which here is the upper one, and that word is `nextUp` of the binary64 `0.3`. So the sum is $0.3000000000000000444\ldots$ while the stored `0.3` is $0.2999999999999999888\ldots$. The sum's own rounding moved the exact value by $2^{-55}$, exactly half a unit in the last place at $0.3$, and the two words end up one unit apart.