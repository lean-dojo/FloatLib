---
number: "15"
slug: kernels-fixed-word-algorithms
title: "Kernels: arithmetic on words and limb arrays"
summary: Machine-word and limb-array algorithms compute significands, with proofs relating each result to natural-number arithmetic.
phases: [kernels]
---

An exact floating-point reference operation decodes its operands into arbitrary-precision integers, combines them, and rounds once. This handles every format, but even a small operation can allocate heap objects for values that fit in registers. The [shared kernels](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) replace those steps with machine-word arithmetic and prove which natural numbers the returned words denote. A backend applies the theorem to justify the replacement, keeping the reference operation as its specification.

Binary64 multiplication shows why the intermediate representation matters. Each significand has at most 53 bits and fits in a `UInt64`, but the exact product can need 106 bits. A single word multiplication would throw away the high bits before rounding. Returning two words keeps the whole product, and its theorem identifies their combined value with the natural-number product. At larger widths, limb kernels also avoid constructing bits that cannot affect rounding, and integer square root increases its working precision as the estimate improves.

## What we mean by a kernel

A kernel is an integer algorithm together with a theorem about its result. It may store a value in a `UInt64`, a pair of words represented by [[FloatLib.Numerics.FixedWord.UInt128]], four words in a `UInt256`, or an `Array UInt32` of limbs. A `toNat` function reads those words as a natural number, and the theorem says what number the algorithm computes. Shared arbitrary-precision helpers can also work on `Nat` itself, as the integer square root below does.

For multiplication, the theorem says the returned words denote the product. For rounding, they denote what the arbitrary-precision [[FloatLib.Numerics.roundShiftRightEven]] returns. Division uses the Euclidean identity to relate its quotient and remainder to the numerator. These contracts let a backend use a kernel without repeating its arithmetic proof. They also let us check an answer found by an unproved search: if a proposed quotient and remainder satisfy the identity and the remainder bound, they are the right answer.

Kernel interfaces know nothing about a format's bit layout, and you won't find field widths, a bias, or a NaN or infinity encoding anywhere in the [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels). Signs enter only as a boolean on a magnitude, as in the [signed-magnitude implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/SignedMagnitude/Runtime.lean). Exponents enter as integers used for alignment and comparison, as in the [dyadic comparison implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/DyadicCompare/Runtime.lean) and `finiteScale`. Decoding the fields and packing the result are the backend's job, and its refinement proof uses the kernel theorems as lemmas.

Every kernel keeps its executable definitions in a `Runtime.lean` module and its theorems in proof modules of their own, a `Proof.lean` that is sometimes split further. A program can import the runtime alone, and a proof imports the same definitions together with their theorems. Declarations keep the `FloatLib.Numerics.FixedWord` and `FloatLib.Numerics.LimbArray` namespaces because, as the [fixed-word module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord.lean) explains, they operate on the numerical layer's primitive representations.

## One word, two words, four words

A binary64 significand has 53 bits and fits a `UInt64`, but its square doesn't. A 53-by-53-bit product can require 106 bits, and a binary128 significand product can require 226. A pair of native words holds up to 128 bits, with the value

$$\mathrm{toNat}(\langle hi, lo\rangle) = lo + hi \cdot 2^{64},$$

and the four-limb `UInt256` in the [word-product implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Product/Runtime.lean) is the same idea twice.

Everything starts from [[FloatLib.Numerics.FixedWord.mul64]], the exact product of two 64-bit words as a `UInt128`. Native multiplication wraps, so the algorithm splits each operand into 32-bit halves, combines the four partial products, and propagates the carries by hand, a decomposition the docstring credits to Hacker's Delight [@warrenHackersDelight2013]. Its certificate, [[FloatLib.Numerics.FixedWord.mul64_toNat]], says the two words denote `x.toNat * y.toNat`. One level up, `mul128` forms a 256-bit product from four `mul64` calls, and `mul128_toNat` states the same equation. Addition hands back its carry instead of losing it, and its theorem `add128_toNat` says value plus carry times $2^{128}$ equals the sum. Comparison is `UInt128.less`. Subtraction is `UInt128.sub`, which wraps modulo $2^{128}$, and a [subtraction proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Difference/Proof.lean) says when the wrapped result is the ordinary difference. If a theorem identifies wrapped word arithmetic with an unbounded result, it needs bounds that rule out overflow. When the operation also returns the carry, its theorem can account for the carry in the result.

Let's try multiplication and addition on the largest values there are. Multiplying two maximal words keeps the high half of the product, while adding one to a maximal two-word value wraps both words and returns a separate carry:

```lean
section
open FloatLib.Numerics.FixedWord

#eval mul64 0xffffffffffffffff 0xffffffffffffffff
-- { hi := 18446744073709551614, lo := 1 }

example (x y : UInt64) : (mul64 x y).toNat = x.toNat * y.toNat :=
  mul64_toNat x y

#eval add128 ⟨0xffffffffffffffff, 0xffffffffffffffff⟩ ⟨0, 1⟩
-- { value := { hi := 0, lo := 0 }, carry := 1 }
end
```

Here's what happens inside that multiplication. Splitting into half-words is ordinary multiplication in base $B=2^{32}$, so if you write $x=x_0+Bx_1$ and $y=y_0+By_1$ you get

$$
xy=x_0y_0+B(x_1y_0+x_0y_1)+B^2x_1y_1.
$$

Each partial product fits in 64 bits, but adding the two middle products in one word could lose a carry. So the implementation combines them in stages, keeping the low half of each completed column and passing its high half into the next. `mul64_toNat` accounts for those carries in the reconstructed integer. Since the returned high word is part of the product, a large high word is a valid result and not an overflow flag.

For the maximal inputs in the first evaluation, $(2^{64}-1)^2 = 2^{128} - 2^{65} + 1$, so the high word is $2^{64} - 2$ and the low word is 1. A backend proof applies `mul64_toNat` to recover this product without repeating the half-word arithmetic. The last result is $2^{128} - 1$ plus one. Both words wrap to zero, and the carry field records the $2^{128}$ that a plain addition would have lost, which is the term `add128_toNat` accounts for.

## Guard bits and sticky bits

Once a backend has an exact significand, it may need to shorten it to the destination precision, and that's where rounding comes in. Say we want to round $v$ to nearest even after discarding $s$ low bits. We compare the discarded remainder $r = v \bmod 2^s$ with the halfway value $2^{s-1}$. Below it we keep the quotient, above it we add one, and right at it we pick whichever of the two neighbours is even. The one-word kernel `roundShiftRightEven` does just this. It has its own branches for a shift of 64 and beyond, because Lean's `UInt64` shifts reduce their count modulo 64 and a naive `1 <<< 64` would be `1` :) Its certificate, `roundShiftRightEven_toNat`, says the word it returns denotes `Numerics.roundShiftRightEven value.toNat shift` for every value and every shift.

In a word, building $2^{s-1}$ is cheap, but for a limb array it can mean a large allocation. You can decide the same comparison by looking at bits of the value already stored, and [[FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky]] states that for $s > 0$,

$$\mathrm{round}(v, s) = \lfloor v / 2^s \rfloor + \begin{cases} 1 & \text{if } g \wedge (t \vee p) \\ 0 & \text{otherwise,} \end{cases}$$

where the guard bit $g$ is bit $s-1$ of $v$, the sticky bit $t$ records whether any bit below the guard is set, and the parity bit $p$ is bit $s$, the low bit of the quotient. A clear guard means the discarded remainder is below halfway, and guard and sticky both set means it's above halfway. A set guard with a clear sticky is an exact tie, and then the low bit of the quotient decides whether to increment, because incrementing an odd quotient makes the answer even. All three tests read the stored limbs, so the remainder never has to be built as a large integer of its own.

The sticky bit also lets us truncate early. `shiftRightJam` shifts right by $j$ bits and ors a one into the low bit whenever a nonzero bit was discarded. [[FloatLib.Numerics.roundShiftRightEven_shiftRightJam]] proves that if $j + 2 \le s$, rounding the jammed value by the remaining $s - j$ bits equals rounding the original by $s$. Those two bits of separation keep the jammed low bit below the guard used by the final rounding, so the jam records discarded information without replacing the guard itself.

Wide addition uses three extra low positions, a guard bit, one more bit, and a sticky bit. It also needs alignment conditions that keep this information valid through the addition or subtraction. In fixed words the forms are `UInt256.shiftRightJam128`, which reduces a four-limb value to two limbs while jamming, and `UInt256.roundShiftRightEven128`. The two-word product kernels call the second with a shift of 112 or 113 for binary128.

We prove the guard-and-sticky identity in the [shared shift-rounding module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/Quantization/Deterministic/ShiftRight.lean) and preservation under jamming in the [shift-right-jam proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/ShiftRightJam/Proof.lean), and limb-array proofs reuse both through the arrays' natural-number values.

Let's try it on a few small numbers. Dividing 21, 20, and 28 by eight gives an above-midpoint case and two ties with different quotient parity. The last evaluation shifts 100 right and records its discarded suffix in the low bit:

```lean
section
open FloatLib.Numerics.FixedWord

-- 21 / 8 = 2.625: guard set and sticky set, so round up.
#eval roundShiftRightEven 0b10101 3
-- 3

-- 20 / 8 = 2.5: a tie, and the quotient 2 is even, so keep it.
#eval roundShiftRightEven 0b10100 3
-- 2

-- 28 / 8 = 3.5: a tie, and the quotient 3 is odd, so round up.
#eval roundShiftRightEven 0b11100 3
-- 4

-- 100 / 16 = 6.25: the jam records the discarded 0.25 as a low one bit.
#eval UInt256.shiftRightJam128 ⟨0, 0, 0, 0b1100100⟩ 4
-- { hi := 0, lo := 7 }

example (value : UInt64) (shift : Nat) :
    (roundShiftRightEven value shift).toNat =
      FloatLib.Numerics.roundShiftRightEven value.toNat shift :=
  roundShiftRightEven_toNat value shift
end
```

The jammed result is seven, although the exact quotient is $6.25$ and its nearest integer is six. Its low one bit records that something nonzero was lost, so a later rounding decision can see it. With a final shift of six the theorem applies. Rounding the original $100/64=1.5625$ gives two, and rounding the jammed $7/4=1.75$ also gives two, so the fractional distances changed and the final rounding decision survived.

A final shift of five leaves only one bit after the jam and violates the separation hypothesis. Rounding $100/32=3.125$ gives three, but rounding $7/2=3.5$ to even gives four, because the jam has reached the final guard position and created a tie. We like this example because the same stored value also gives a counterexample once you drop the theorem's two-bit separation hypothesis.

### Bounded alignment in generic addition

Say we add a huge number to a tiny one. The exponent gap doesn't have to become a correspondingly wide integer. The generic IEEE addition, subtraction, and FMA path uses [`FiniteScaleAdd.roundAligned`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Generic/ScaleAdd/Runtime.lean) to combine a high-scale magnitude $H$ and a low-scale magnitude $L$. At their common scale the exact magnitude is $H2^d+L$ or $H2^d-L$, where $d$ is the scale gap. With fraction width $f$, the bounded branch keeps $k=f+3$ extra positions below $H$. It applies only when $d>2k$, $\operatorname{log2}(L)+1<d$, and $H\ne0$. Those checks make sure $H$ determines the sign and that subtraction can't cancel the leading bits the rounding proof needs. With the stricter gap threshold, moderate gaps stay on complete alignment, which skips the extra jamming work when the full intermediate is already short. The same rounding proof applies.

Set $j=d-k$, $U=H2^k$, and $Q=\lfloor L/2^j\rfloor$. If the discarded suffix is zero, the shortened magnitude is just $U+Q$ or $U-Q$. Otherwise addition jams the low bit of $U+Q$, and subtraction first borrows one and then jams the low bit of $U-Q-1$. Take $4096-5=4091$, which has quotient 63 when shifted right by six. Subtracting the shortened operands alone would give $64-0=64$, and the borrow is what accounts for the nonzero discarded part. To detect that part, the implementation compares $L$ with $(L\mathbin{\gg}j)\mathbin{\ll}j$ and never constructs a $2^j$ mask.

Round the shortened magnitude to nearest even at a scale increased by $j$ and you get the same encoding. The proof [`FiniteProductRound.round_shiftRightJam`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Generic/ProductRound/Proof.lean) requires $j+f+2\le\operatorname{log2}(M)$ for the exact combined magnitude $M$. The alignment checks establish that even after the borrow, and the proof covers normal and subnormal rounding. `FiniteScaleAdd.roundAligned_eq` then identifies the bounded branch with complete alignment, and `roundSum_eq` connects it to exact dyadic addition followed by one rounding.

When the checks fail, complete alignment is still there for close exponents and cancellation. On the bounded branch, storage grows with the source significands and the destination precision, and the exponent gap doesn't enter into it. FMA still forms the exact product first, and only its alignment with the addend is shortened, so nothing here adds an intermediate floating-point rounding.

## Restoring division

Restoring division produces the quotient one bit at a time. Each step doubles the remainder, and if that's still below the divisor, the next quotient bit is zero. Otherwise the step subtracts the divisor and appends a one, and subtracting the divisor from the remainder and adding one to the quotient keep the represented numerator the same. We copied the natural-number recurrence below from the [restoring-division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Proof.lean), and the `rfl` check fails if this copy ever stops being definitionally equal to the library definition.

```lean
open FloatLib.Numerics.FixedWord.RestoringQuotient in
def natQuotientStep (den : Nat) (state : QuotientState Nat) :
    QuotientState Nat :=
  let doubledRemainder := 2 * state.remainder
  if doubledRemainder < den then
    { quotient := 2 * state.quotient
      remainder := doubledRemainder }
  else
    { quotient := 2 * state.quotient + 1
      remainder := doubledRemainder - den }

example :
    natQuotientStep =
      FloatLib.Numerics.FixedWord.RestoringQuotient.natQuotientStep := rfl
```

`QuotientState` can hold `Nat`, `UInt64`, or `UInt128` pairs. Its invariant is `natQuotientSteps_spec`: after $n$ steps from a state with remainder below the divisor,

$$q' \cdot d + r' = (q \cdot d + r) \cdot 2^n, \qquad r' < d, \qquad q \le q'.$$

That equation is the division identity scaled by $2^n$. Doubling a remainder that's below the divisor gives a value below twice the divisor, so at most one subtraction restores the strict remainder bound, and that bound makes the quotient the true floor. The last inequality says the quotient prefix never shrinks, and the word-level proof uses it to bound every intermediate quotient. Uniqueness of Euclidean quotient and remainder then gives `natQuotientSteps_div_mod`, which says the state is the quotient and remainder of the scaled numerator.

On machine words, the loop `quotientStep` runs the same recurrence, with each doubling written as `x + x`. Its proof applies the natural-number result under the capacity hypotheses in its docstring, which ask for a divisor and a quotient prefix below $2^{63}$ so that neither addition wraps.

Let's follow the first two steps of the example below, which go through both branches. We start with $4=1\cdot3+1$. Doubling the remainder gives two, which is below the divisor three, so the new state is quotient two and remainder two, representing eight. Doubling again gives remainder four, so we subtract three and set the next quotient bit, which leaves quotient five and remainder one, representing sixteen. In general the subtraction branch preserves the scaled numerator because

$$
(2q+1)d+(2r-d)=2(qd+r).
$$

The guard tells us the subtraction is nonnegative, and the old bound $r<d$ tells us the new remainder is below $d$. So the identity tracks the represented value, and the inequalities make that value's quotient unique and let us do the updates in bounded words.

To round a quotient, the one-word rounder `roundQuotientEven` compares the remainder with the divisor minus the remainder, which decides $2r$ against $d$ inside one word with no bound on the divisor. It's the kernel that `Numerics.roundQuotientEven` compiles to, as the section on `csimp` below explains. The restoring loop gets away with a simpler comparison. Its state rounder `roundQuotientState` doubles the remainder and compares it with the divisor, and the doubling is safe because the same capacity hypothesis keeps the divisor below $2^{63}$. `roundScaledQuotient` does the whole calculation from scaled numerator to nearest-even quotient, and [[FloatLib.Numerics.FixedWord.RestoringQuotient.roundScaledQuotient_toNat]] proves it correct.

When `0 < den < 2^63` and `shift < 64`, compiled scaled-quotient calls first try a floating-point candidate and its immediate neighbours. An exact two-word product and remainder check accepts a candidate only if it's the floor quotient, and if all three are rejected, the restoring loop runs. The [`roundScaledQuotient_eq_internal` compiler equation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Compiler.lean) proves equality with the logical rounder without assuming anything about how accurate the floating-point proposal is, so the floating-point guess is allowed to be as wrong as it likes.

```lean
section
open FloatLib.Numerics.FixedWord.RestoringQuotient

-- Start from 4 = 1 * 3 + 1 and generate four more quotient bits:
-- 4 * 2^4 = 64 = 21 * 3 + 1.
#eval quotientSteps 3 4 { quotient := 1, remainder := 1 }
-- { quotient := 21, remainder := 1 }

-- (1 / 3) * 2^52 rounded to nearest even, in native words ...
#eval roundScaledQuotient 1 3 52
-- 1501199875790165

-- ... and by the arbitrary-precision definition it refines.
#eval FloatLib.Numerics.roundQuotientEven (1 <<< 52) 3
-- 1501199875790165

example (den n : Nat) (state : QuotientState Nat) (h : state.remainder < den) :
    (natQuotientSteps den n state).quotient =
      ((state.quotient * den + state.remainder) * 2 ^ n) / den :=
  (natQuotientSteps_div_mod den n state h).1
end
```

[Figure 15.1](#/chapter/kernels-fixed-word-algorithms/figure-ch08-restoring-division) follows the first of those `#eval`s one step at a time. Each step doubles the remainder, compares it with the divisor, and appends the quotient bit. You can check the invariant after each step from the displayed new quotient and remainder, and the hatched segment marks the divisor removed on a subtraction.

![Restoring division of 4 by 3: four steps double the remainder and compare it with 3, keeping it and appending 0 or subtracting 3 and appending 1, to reach quotient 21 and remainder 1](assets/ch08-restoring-division.png "Each step appends one quotient bit and preserves the exact quotient-and-remainder identity.")

The two-limb loop [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128]] has the same shape, with the certificate `quotientSteps128_div_mod` in the [two-word restoring-division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Restoring128Proof.lean), and its compiler replacement keeps the state in scalar accumulators, as described under `csimp` below.

## Restoring square root

Square root has the same shape with two-bit digits, because $(2r + b)^2 = 4r^2 + 4rb + b^2$ lets us extend a root by one bit while consuming two bits of radicand. Here's the two-limb step from the [restoring-square-root implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/RestoringSqrt/Runtime.lean). It shifts the remainder left by two, appends the next base-four digit, forms the trial value $4r + 1$, and subtracts it if it fits.

```lean
open FloatLib.Numerics.FixedWord in
def rootStep (digit : UInt64)
    (state : RestoringRootState UInt128) : RestoringRootState UInt128 :=
  let expandedBase := RestoringSquareRoot.shiftLeftTwo state.remainder
  let expanded : UInt128 := { expandedBase with lo := expandedBase.lo ||| digit }
  let trialBase := RestoringSquareRoot.shiftLeftTwo state.root
  let trial : UInt128 := trialBase.setLowBit
  let doubledRoot := RestoringSquareRoot.shiftLeftOne state.root
  if UInt128.less expanded trial then
    { root := doubledRoot, remainder := expanded }
  else
    { root := doubledRoot.setLowBit, remainder := UInt128.sub expanded trial }

example : rootStep = FloatLib.Numerics.FixedWord.RestoringSquareRoot.rootStep := rfl
```

Its invariant is `Represents`. A state represents a value $x$ when $r^2 + m = x$ and $m \le 2r$, where $r$ is the root and $m$ the remainder. Because the remainder is nonnegative, the square of $r$ is at or below the radicand, and the upper bound on the remainder puts the next integer square strictly above it. So $r$ is $\lfloor\sqrt{x}\rfloor$, which is `sqrt_spec`. Once all digits are consumed, [[FloatLib.Numerics.FixedWord.RestoringSquareRoot.rootAndRemainder_spec]] says the root is `Nat.sqrt` of the radicand and the remainder is the radicand minus the root squared. That holds for any digit count from 64 to 125 and any radicand below $2^{2 \cdot \mathrm{steps}}$. The binary128 backend uses 113 digits, one more than its fraction width, and it declines fractions wider than 124 bits, where a doubled remainder would no longer fit the two-word state.

You can read the trial value in `rootStep` straight off this invariant. If the consumed prefix is $x=r^2+m$ and the next base-four digit is $d$, the enlarged prefix is

$$
4x+d=(2r)^2+(4m+d).
$$

So the candidate root $2r$ has remainder $4m+d$. Raising the root to $2r+1$ costs $(2r+1)^2-(2r)^2=4r+1$, which is the trial the code subtracts. The old remainder bound and $0\le d\le3$ put the enlarged prefix below $(2r+2)^2$, so these are the only two possible floor roots. Appending `digit` with bitwise OR implements the addition, because a two-bit left shift leaves two zero bits and the digit occupies only those positions. The word-level proof also has to show that the shifts don't discard high bits, and that's where the digit-count capacity bounds come in.

The remainder also tells us how to round the root. A square root of a nonnegative $p$-bit binary input can't land exactly on a midpoint at the same precision. A midpoint between adjacent $p$-bit values has an odd significand of $p+1$ bits, so its square would have an odd significand of $2p+1$ or $2p+2$ bits, which no $p$-bit input can have. For the integer radicand of the restoring kernel, we round up exactly when $x > (r + \tfrac12)^2 = r^2 + r + \tfrac14$, that is when $m > r + \tfrac14$. Since both are integers, this is just $m > r$. `roundRoot` increments the root when the remainder exceeds it, and `roundRoot_toNat` proves that this gives the nearest integer root under the same digit-count hypotheses. Here are two radicands on either side of that boundary:

```lean
section
open FloatLib.Numerics.FixedWord.RestoringSquareRoot

-- 1000 = 31^2 + 39
#eval rootAndRemainder ⟨0, 0, 0, 1000⟩ 64
-- { root := { hi := 0, lo := 31 }, remainder := { hi := 0, lo := 39 } }

-- 39 > 31, so the nearest integer root is 32 (sqrt 1000 = 31.62...).
#eval roundRoot (rootAndRemainder ⟨0, 0, 0, 1000⟩ 64)
-- { hi := 0, lo := 32 }

-- 980 = 31^2 + 19 and 19 <= 31, so it stays at 31 (sqrt 980 = 31.30...).
#eval roundRoot (rootAndRemainder ⟨0, 0, 0, 980⟩ 64)
-- { hi := 0, lo := 31 }
end
```

For binary64 the root and remainder fit in a one-word state, because the root has at most 53 bits and the remainder is at most twice the root. In the [binary64 square-root implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Sqrt/Runtime.lean), the kernel scales the significand to a 105- or 106-bit radicand held in two words. It first tries a checked Newton candidate, whose square and remainder must satisfy the exact floor-root inequalities. If the candidate is rejected, the original 53-step restoring loop runs, and `rootAndRemainderChecked_eq` proves that both paths return the same state. The binary64 `sqrt` covers every input bit pattern, NaN, infinities, signed zeros, and negatives included.

On the binary128 path, the [checked square-root kernel](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/CheckedSqrt/Runtime.lean) also checks proposed roots against exact four-word squares, and its compiler certificate proves equality with the restoring algorithm. Floating-point seeds and corrections guide the search, but whether their answer gets accepted is up to the integer check.

### Increasing precision for arbitrary-precision square root

The shared [`IntegerSquareRoot.sqrtNat`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Runtime.lean) handles radicands of any width. Below $2^{64}$ its logical case uses a `UInt64` Newton iteration that starts above the floor root. Native-word calls compiled with `IntegerSquareRoot.Compiler` available use `sqrtChecked` in its place. That one tries a hardware square-root candidate and its immediate neighbours and accepts one only if it passes an exact floor-root check, with Newton iteration staying as the fallback, and `sqrtChecked_toNat` proves this alternative correct. Larger inputs use `approxRoot`, which recursively discards low pairs of radicand bits until a word-sized seed is enough and then does one Newton refinement at each increasing precision. For a 1,024-bit radicand, its precision parameter goes down through 511, 255, 127, 63, and 31 before the word step. Coming back up through those levels increases the working width, so the early divisions never use the complete radicand. We follow [CPython 3.13's integer-square-root algorithm](https://github.com/python/cpython/blob/v3.13.0/Modules/mathmodule.c#L1494) for this refinement.

Every candidate has to pass an exact check. For a proposed root $a$, `checkRoot?` computes $a^2$ once, and if $a^2\le n$, it accepts exactly when $n-a^2\le2a$. Together those inequalities say $a^2\le n<(a+1)^2$. A guess that's too high can be corrected downward by one, using $(a-1)^2=a^2-(2a-1)$. A rejected guess falls back to a full-precision Newton iteration from a valid upper bound. [`checkRoot?_eq` and `sqrtRem_eq`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Proof.lean) prove that the returned pair is $(\lfloor\sqrt n\rfloor,\ n-\lfloor\sqrt n\rfloor^2)$. So correctness doesn't depend on any unproved assumption about how accurate the candidate is, or on the check always accepting. With the remainder in hand, a floating-point caller can tell a perfect square from a positive tail before rounding.

Above the word bound, `sqrtNat` projects the root from this pair, and the compiler equation `natSqrt_eq_sqrtNat` applies to large inputs as well as words. The generic binary square-root path calls this shared helper, so it doesn't need a new planner candidate. Its fallback calls `Nat.sqrt.iter` by name, which keeps the compiler replacement acyclic. The fixed-capacity restoring kernels above keep their own routes.

## Checking a division result

At two limbs the restoring loop runs 112 or 113 iterations for binary128, one bit each, after the initial state has supplied the leading quotient bit. Knuth's Algorithm D [@knuth1997] uses long division in radix $2^{32}$ to produce a 128-bit quotient in four digit steps. Each step estimates a quotient digit, corrects it at most twice, and repairs a negative partial remainder by adding the divisor back. We haven't proved the Algorithm D search itself. Its correctness comes from the independent check of the proposed quotient and remainder, with the restoring loop as the fallback. [[FloatLib.Numerics.FixedWord.CertifiedDivision.candidate]] runs Algorithm D and returns a candidate quotient and remainder, and [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate]] checks them independently with three tests, shown here with namespaces shortened:

```
sum.carry == 0 &&
  sum.value == UInt256.ofUInt128ShiftedLeft num (shift.toNat precision) &&
  UInt128.less remainder den
```

Here `precision` is $p$ for significands of $p + 1$ bits, so it counts the fraction bits and leaves out the leading bit. The annoying part is that the square-root argument above counted every significand bit in its precision. Binary128 passes 112 for its 113-bit significands. The `shift` picks one of two scalings of the numerator. `.exact` scales by $2^p$ when the numerator is at least the denominator, and `.extra` scales by $2^{p+1}$ otherwise, so the quotient has exactly $p + 1$ bits. In 256 bits, `sum` is `mul128 quotient den` plus the widened remainder.

So the three tests check that this addition has no carry, that the result equals the scaled numerator, and that the remainder is below the divisor. Together they establish Euclidean division. [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate_sound]] concludes that a candidate passing the check is the unique correct quotient and remainder, however it was produced.

A proposed quotient can fail the certificate check, so the backend has a proved fallback. [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate]] computes the candidate and checks it, and if the check fails it runs the restoring loop. `checkedCandidate_complete` proves that the loop's result passes the same check on every normalized input.

The backends use [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate_sound]]. It says the selected pair satisfies the exact quotient equation and the strict remainder bound for normalized significands of $p+1$ bits, with fraction-width parameter $65 \le p \le 126$ and the shift chosen as above. It holds whether the initial candidate passed or the restoring loop replaced it. In the final step, `roundQuotient` rounds to nearest even by doubling the remainder in 128 bits and keeping the carry, and `roundQuotient_toNat` connects it to the arbitrary-precision quotient rounder. Let's divide, say, one by one and a half in binary128:

```lean
section
open FloatLib.Numerics.FixedWord
open FloatLib.Numerics.FixedWord.CertifiedDivision

-- binary128 significands have 113 bits: 1.0 divided by 1.5.
-- The numerator is smaller, so the extra shift scales it by 2^113.
#eval (checkedCandidate 112 (UInt128.ofNat (2 ^ 112)) (UInt128.ofNat (3 * 2 ^ 111)) .extra).quotient.toNat
-- 6923062478046436838040661772293461

#eval (2 ^ 225 : Nat) / (3 * 2 ^ 111)
-- 6923062478046436838040661772293461

-- The certificate accepts the true quotient and rejects its predecessor.
#eval certificate 112 (UInt128.ofNat (2 ^ 112)) (UInt128.ofNat (3 * 2 ^ 111)) .extra
  (UInt128.ofNat 6923062478046436838040661772293461) (UInt128.ofNat (2 ^ 111))
-- true

#eval certificate 112 (UInt128.ofNat (2 ^ 112)) (UInt128.ofNat (3 * 2 ^ 111)) .extra
  (UInt128.ofNat 6923062478046436838040661772293460) (UInt128.ofNat (2 ^ 111))
-- false
end
```

You get the large quotient by cancelling the common power of two in $2^{225}/(3\cdot2^{111})$, which leaves $2^{114}/3$. Since $2^{114}$ leaves remainder one on division by three, the floor quotient is $(2^{114}-1)/3$. Multiply it back by the original denominator and the remainder is $2^{111}$, the same remainder we gave the certificate. Lower the quotient by one without changing the remainder and the product-plus-remainder equality breaks, while raising the remainder by the divisor would repair that equality but violate the strict remainder bound. Between them, the two tests rule out both ways of presenting the wrong quotient.

The carry test is what makes the equality an equality of natural numbers. Ignore the carry and equal low 256 bits would only give a congruence modulo $2^{256}$. Here `mul128_toNat` gives the full product, and the zero carry on its addition to the remainder lets `certificate_sound` recover the unbounded Euclidean identity. Any search strategy that produces a candidate will do, because the accepted answer has to satisfy that identity and the bound.

So we can change the Algorithm D search in the [certified-division implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/CertifiedDivision/Runtime.lean) and leave the soundness argument for an accepted result alone, since that proof depends on the certificate check.

## Reusing a kernel proof across formats

Once the word arithmetic is proved, we can reuse it across formats. Each kernel theorem spells out its capacity bounds and value invariants. For each format, all that's left is to show that its decoded operands satisfy those bounds and that it packs the result correctly.

Our certificates are stated over natural numbers and parametrized by capacity, never by format. [[FloatLib.Numerics.FixedWord.RestoringQuotient.roundScaledQuotient_toNat]] takes any numerator, divisor, and shift satisfying its two bounds. The binary64 backend in the [binary64 division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Division/Proof.lean) discharges those bounds from its own field widths and then uses the theorem unchanged. So does the small-word backend in the [small-word division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Div/Proof.lean). [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate_sound]] takes the fraction width $p=f$ as its parameter, with $64 < p \le 126$, and requires normalized $p+1$-bit significands. That one theorem serves binary128 and every custom `ExecFloat.Binary e f` with $65 \le f$ and $e + f \le 127$ that the pair backend accepts.

Invariants are stated over an abstract carrier. `RestoringRootState α` holds a root and a remainder of any type, and `Represents` takes the `toNat` function as an argument. In the [shared word proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Proof/Word.lean), `loop_represents` proves the whole induction over base-four digits once, for any step function that preserves `Represents` on one digit. The binary64 square-root proof instantiates it with `UInt64.toNat` and the two-limb proof with `UInt128.toNat`, and neither repeats the induction. Each backend still proves what's specific to it. Its decoding has to produce the radicand it claims, its exponent arithmetic has to be right, and its packing has to be inverse to its decoding.

Definitions are shared too. The [signed-magnitude implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/SignedMagnitude/Runtime.lean) combines two signed magnitudes in one word, and the [dyadic comparison implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/DyadicCompare/Runtime.lean) compares word significands at unbounded exponents. So binary interchange and posit backends use the same definitions of cancellation and ordering.

<a id="finding-the-kernel-implementations"></a>
<a id="reading-a-compiler-certificate"></a>

## Compiler replacements with csimp

The word algorithms are useful even when a caller is written against a simpler `Nat` definition. A `@[csimp]` equation, introduced in [chapter 05](#/chapter/why-execution-and-proofs-are-separate), proves that the two functions are equal. Lean's kernel checks `f = g`, and the compiler uses it to rewrite calls to `f` into calls to `g`. The [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) supplies these equations for shift rounding and for the restoring division and square-root loops.

Consider right-shift rounding. Its logical definition is [[FloatLib.Numerics.roundShiftRightEven]] over `Nat`, and its fast counterpart is `roundShiftRightEvenNat`, quoted below as a checked copy. If the value fits one word, it runs the native kernel and converts back. Wider inputs use the same guard-and-sticky algorithm as the shared definition. They first shift to a retained prefix containing the guard bit and quotient, the prefix's lowest byte supplies the guard bit and quotient parity, and one more one-bit shift gives the quotient.

```lean
def roundShiftRightEvenNat (value shift : Nat) : Nat :=
  if _hvalue : value < 2 ^ 64 then
    (FloatLib.Numerics.FixedWord.roundShiftRightEven (UInt64.ofNat value) shift).toNat
  else if shift == 0 then
    value
  else
    let amount := shift - 1
    let retained := Nat.shiftRight value amount
    let quotient := Nat.shiftRight retained 1
    let lowByte := UInt8.ofNat retained
    if (lowByte &&& 1) != 0 then
      if ((lowByte >>> 1) &&& 1) != 0 || Nat.shiftLeft retained amount != value then
        quotient + 1
      else
        quotient
    else
      quotient

example :
    roundShiftRightEvenNat =
      FloatLib.Numerics.FixedWord.roundShiftRightEvenNat := rfl

example :
    FloatLib.Numerics.roundShiftRightEven =
      FloatLib.Numerics.FixedWord.roundShiftRightEvenNat :=
  FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat

#eval FloatLib.Numerics.roundShiftRightEven 0b10101 3
-- 3
```

The second `example` states [[FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat]], which carries `@[csimp]`. Its proof is `funext` followed by the lemma `roundShiftRightEvenNat_eq_roundShiftRightEven`, which applies the certificate `roundShiftRightEven_toNat` on the native branch, and the wide branch closes by `rfl` because it matches the shared guard-and-sticky definition. After you import that module, calls in newly compiled definitions and `#eval` expressions use `roundShiftRightEvenNat`, as in the example above. An import doesn't go back and rewrite functions that were already compiled, so their modules need the theorem available when those callers are compiled. Since the logical definition hasn't changed, its theorems still apply.

The arbitrary-precision branch never allocates the halfway marker $2^{s-1}$. A clear guard returns the quotient right away, and a set guard with an odd quotient increments it right away. Only a set guard with an even quotient needs a sticky test, and that test reuses the prefix. Shifted back, the prefix differs from the input exactly when a discarded bit was set, so no remainder is ever built. The branch also stays away from `Numerics.roundShiftRightEven` itself, because the compiler would rewrite that call back to the replacement and create a cycle.

Compiler equations also cover `roundQuotientEven` in the [rounding proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Proof/Rounding.lean). The [integer-square-root proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Proof.lean) routes `Nat.sqrt` through the native-word or checked increasing-precision implementation described above, and that one reaches outside the library. Any program importing `FloatLib.Kernels` compiles its own `Nat.sqrt` calls through [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]]. Limb-array `toNat` has a Horner-loop replacement too, which we get to below.

<details>
<summary>The two compiler-certificate signatures</summary>

On the left is the logical definition, and on the right the executable dispatcher:

```lean
#check @FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat
-- FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat : FloatLib.Numerics.roundShiftRightEven =
--   FloatLib.Numerics.FixedWord.roundShiftRightEvenNat

#check @FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat
-- FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat : Nat.sqrt =
--   FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat
```

</details>

All of these equalities are about Lean's logical operations. `mul64_toNat`, for example, relates the `UInt64` operations in Lean's model to natural-number multiplication. Running the proved algorithms also relies on the compiler applying the substitutions correctly, and on the compiler, runtime, and CPU implementing those word operations correctly.

To normalize a significand you also have to find its highest set bit. In the [word implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Runtime.lean), `log2Word` returns right away for zero and one and uses a packed lookup for values from 2 to 15. Other values below 256 need only the 4-bit stage before the lookup, and larger words go through the 32-, 16-, 8-, and 4-bit stages. Its [proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Proof/Word.lean) covers every machine word and supplies the compiler equation `uint64_log2_eq_log2Word`, and through `UInt64.log2` the same helper serves both binary and posit arithmetic.

Our [division compiler proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Compiler.lean) replaces the one-word `quotientSteps` and the two-limb [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128]] by `Internal.quotientSteps` and `Internal.quotientSteps128`, where quotient and remainder travel as two or four `UInt64` scalar accumulators. Likewise the [restoring-square-root compiler proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/RestoringSqrt/Compiler.lean) replaces `rootLoop` by `Internal.rootLoop`, which reads the same `UInt256` radicand and keeps the root and remainder in four `UInt64` accumulators.

These loops build the returned state once, after the final digit, so there's no fresh state allocation at every digit. `quotientSteps_eq_internal`, [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128_eq_internal]], and `rootLoop_eq_internal` follow by induction over the loop count. They hold for every divisor or radicand, initial state, and digit count, even on inputs where the word arithmetic wraps. Reading a result as a natural-number quotient or square root still needs the same capacity bounds as before. We keep these equalities in compiler modules of their own, so executable clients can enable the rewrites without importing the numerical proofs.

Those modules also certify the wrappers, with `roundScaledQuotient_eq_internal` and `rootAndRemainder_eq_internal`. For square root, the replacement calls straight into `rootLoopWords`. Division is different. Under the guard described above, its replacement first tries the floating-point candidate and its neighbours, checks each with exact integer arithmetic, and falls back to `quotientStepsWords` when none passes or the guard fails. These wrapper equations matter because an equation for the inner loop alone need not change an inline wrapper whose body was compiled before that equation was available. If the wrapper equations are imported when a consumer is compiled, the compiler can replace the wrapper itself and reach the scalar loop.

<a id="kernels-fixed-word-algorithms-and-limb-arrays"></a>

## Limb arrays: 32-bit limbs updated in place

For binary128's intermediate arithmetic the fixed-word kernels use up to four 64-bit limbs, and whether a backend supports a particular layout also depends on its field widths and the kernel's capacity bounds. Wider formats can use [[FloatLib.Numerics.LimbArray]] from the [limb-array implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/LimbArray). It stores a natural number as a little-endian `Array UInt32`, with limb $i$ carrying weight $2^{32 i}$. Reading beyond the stored limbs is defined to give zero, so appending zero limbs doesn't change the value. [[FloatLib.Numerics.LimbArray.toNat]] reads that value, and as everywhere in the kernels, each operation is specified by its effect on it. Addition has [[FloatLib.Numerics.LimbArray.toNat_add]], subtraction has `toNat_sub`, and multiplication has [[FloatLib.Numerics.LimbArray.toNat_mul]]. The shift theorems are `toNat_shiftLeft` and `toNat_shiftRight`, and rounding has [[FloatLib.Numerics.LimbArray.toNat_roundShiftRightEven]].

On a 64-bit platform, 32-bit limbs avoid boxing allocations in Lean's runtime. An `Array` holds `lean_object` pointers, and this repository pins the toolchain `leanprover/lean4:v4.35.0`. In its [runtime header](https://github.com/leanprover/lean4/blob/v4.35.0/src/include/lean/lean.h), `lean_box_uint64` allocates a constructor cell with `lean_alloc_ctor` for every value. On a 64-bit platform `lean_box_uint32` calls `lean_box`, which encodes the number in a tagged pointer with no allocation. So writing a `UInt64` array element needs a boxed value, and a `UInt32` element fits the tagged representation on that platform. A smaller limb also leaves room for a product and carries in the arithmetic register. A limb product plus two addends fits exactly,

$$(2^{32}-1)^2 + 2(2^{32}-1) = 2^{64} - 1,$$

so every intermediate of the schoolbook multiplication stays in a `UInt64`, and a limb sum with two carries stays there with room to spare.

Whether writing those elements also copies the array depends on ownership. When the array's reference count is one, Lean updates it destructively, so `Array.setIfInBounds` on a loop-owned accumulator is an in-place store. The result buffer still has to be allocated, but the owned loop avoids a new boxed object or array copy on every limb update.

`carryLoop` adds a word at a limb position and propagates the carry upward, stopping as soon as it vanishes, so the common case touches one limb. It's the primitive behind `addAt`, which adds $w \cdot 2^k$ for a bit position $k$, and behind the increment that rounding needs. `add` produces one limb more than the wider operand, which is why `toNat_add` has no side condition. `sub` assumes its result is nonnegative, and `toNat_sub` states that contract.

[[FloatLib.Numerics.LimbArray.mul]] is the schoolbook product in `a.size + b.size` limbs, one row per limb of the left operand. Shifts build each result limb from at most two source limbs with `Array.ofFn`, so no intermediate array is written twice. Every loop is structural recursion over a limb count, which makes its invariant in the [limb-arithmetic proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/LimbArray/Arithmetic/Proof.lean) an induction on that count. The processed segment changed by the intended amount, and every limb outside it didn't.

Limb rounding uses the guard-and-sticky form, so it never needs a large halfway integer. [[FloatLib.Numerics.LimbArray.roundShiftRightEven]] reads the guard and parity bits with `testBit` and the sticky bit with `anyBelow`, and then it increments the shifted quotient with one carry-propagating `addAt`. At no point does it form $2^{s-1}$.

```lean
open FloatLib.Numerics in
def roundShiftRightEven (v : LimbArray) (shift : Nat) : LimbArray :=
  if shift == 0 then
    v
  else
    let quotient := v.shiftRight shift
    if v.testBit (shift - 1) && (v.anyBelow (shift - 1) || v.testBit shift) then
      quotient.addAt 0 1
    else
      quotient

example : roundShiftRightEven = FloatLib.Numerics.LimbArray.roundShiftRightEven := rfl
```

Its certificate `toNat_roundShiftRightEven` is the guard-and-sticky theorem applied to the value of the array, with `testBit_eq` and `anyBelow_eq` turning the three bit reads into facts about `toNat`. For arrays the sticky jam is `orLowBit`, and `toNat_orLowBit` says it ors a one into the value of a nonempty array.

Here they are on actual numbers. The printed arrays list limbs from least to most significant, the product and sum below both reserve an extra limb, and the last calls test and record discarded bits.

```lean
section
open FloatLib.Numerics

#eval LimbArray.ofNat (2 ^ 70 + 5) 3
-- { limbs := #[5, 0, 64] }

-- Three limbs times two limbs gives five, and the value is the product.
#eval LimbArray.mul (LimbArray.ofNat (2 ^ 70 + 5) 3) (LimbArray.ofNat (2 ^ 40 + 1) 2)
-- { limbs := #[5, 1280, 64, 16384, 0] }

#eval (LimbArray.mul (LimbArray.ofNat (2 ^ 70 + 5) 3) (LimbArray.ofNat (2 ^ 40 + 1) 2)).toNat ==
  (2 ^ 70 + 5) * (2 ^ 40 + 1)
-- true

-- The sum gets one limb more than the wider operand, so the carry has somewhere to go.
#eval LimbArray.add (LimbArray.ofNat (2 ^ 96 - 1) 3) (LimbArray.ofNat 1 1)
-- { limbs := #[0, 0, 0, 1] }

-- 100 = 0b1100100: nothing below bit 2, something below bit 4.
#eval (LimbArray.ofNat 100 1).anyBelow 2
-- false
#eval (LimbArray.ofNat 100 1).anyBelow 4
-- true

-- Shift right by four and jam the discarded bits into the low bit: 6 becomes 7.
#eval ((LimbArray.ofNat 100 1).shiftRight 4).orLowBit true
-- { limbs := #[7] }

example (a b : LimbArray) : (LimbArray.mul a b).toNat = a.toNat * b.toNat :=
  LimbArray.toNat_mul a b

example (v : LimbArray) (shift : Nat) :
    (LimbArray.roundShiftRightEven v shift).toNat =
      FloatLib.Numerics.roundShiftRightEven v.toNat shift :=
  LimbArray.toNat_roundShiftRightEven v shift
end
```

You can check the product's five output limbs by expanding it:

$$
(2^{70}+5)(2^{40}+1)=2^{110}+2^{70}+5\cdot2^{40}+5.
$$

Five goes in limb zero. Since $5\cdot2^{40}$ is $1280\cdot2^{32}$, limb one is 1280. Then $2^{70}=64\cdot2^{64}$ supplies limb two, and $2^{110}=16384\cdot2^{96}$ supplies limb three. Limb four is zero, and it's there at all because multiplication reserves the sum of the operand lengths even when a particular answer needs fewer limbs. The value theorem allows that leading zero, so a printed array doesn't have to be the shortest representation of its integer.

Back at the top of the example, the first result splits $2^{70} + 5$ into three limbs. [Figure 15.2](#/chapter/kernels-fixed-word-algorithms/figure-ch08-limb-arrays) follows the fourth, a carry through three saturated limbs into the fourth limb that `add` reserves. Limb zero receives the added 1, and the later 1s are carries.

![Adding 1 to 2^96 - 1 in base 2^32: each of three saturated limbs stores zero and passes a carry of one, producing four limbs (0, 0, 0, 1), lowest limb first](assets/ch08-limb-arrays.png "The final carry occupies the extra limb reserved by addition.")

For this conversion the compiler certificate is [[FloatLib.Numerics.LimbArray.toNat_eq_internal]]. In proofs, `toNat` starts with the first limb and adds the radix times the value of the rest. That form makes the invariants easy to state, but it isn't tail recursive, so the compiled form uses a Horner loop from the top limb down. `hornerFrom_eq` proves the two forms equal, and `csimp` tells the compiler to use the loop.

These kernels serve the [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb), which handles IEEE layouts wider than 128 bits with an exponent field of at most 32 bits, using the limb storage named by `ExecFloat.BinaryLimbs`. Public arithmetic on this type goes through the automatic certified planner, so `+` on `ExecFloat.BinaryLimbs 19 236`, for example, selects wide-limb addition under the default policy.

Its addition core `alignOrdered?` is the sticky-bit argument put to work. Suppose the scale difference $d$ is at least three. Suppose also that after alignment the operand at the larger scale keeps its leading bit at least two positions above the other's, so the leading bit of the result is known. Then it shifts the operand at the smaller scale right by $d - 3$ bits and records `anyBelow` of the discarded part as the sticky bit. It shifts the larger operand left by three, adds or subtracts in limbs, jams the sticky bit with `orLowBit`, and rounds. Those three extra bits are the guard bit, one more bit, and the sticky position that `roundShiftRightEven_shiftRightJam` requires. On this accepted addition path the significand is never converted to a `Nat`, and only limb indices and shift counts are. Addition, subtraction, multiplication, and fused multiply-add have limb fast paths for accepted normal operands with normal results, and any declined call uses the exact baseline. Those dyadic fallback operations use bulk integer rounding at every width, because the [dyadic specification](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Spec/Dyadic.lean) imports the compiler proof before defining them.

### Division and square root from limb storage

Wide-limb division and square root read the stored fields themselves and then work with arbitrary-precision integers. [Division](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Division/Runtime.lean) handles finite operands, zeros and subnormals included, through the shared [quotient rounder](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Generic/QuotientRound/Runtime.lean). For nearest-even rounding, one integer division computes an extra quotient bit, and that bit and the retained result's parity settle most rounding decisions. The remaining case checks whether the quotient times the denominator equals the scaled numerator. If their low machine words differ, the result is inexact, and if the low words match, we still have to compare the full integers. Either way there's no second division to compute the remainder.

For normal operands with fraction width $f$, both significands $n,d$ lie in $[2^f,2^{f+1})$, so their ratio is strictly between $1/2$ and $2$. Its binary exponent is $0$ when $d\le n$, and $-1$ otherwise, and the shared theorem `floorLog2_eq_of_normal` justifies passing this exponent to the rounder. On its wide normal branch the generic finite kernel uses the same comparison and skips two integer logarithms. Its `divRuntime_eq` proof preserves the reference result, including the existing fallbacks for small widths, zero exponent fields, and exponent boundaries.

[Square root](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Sqrt/Runtime.lean) accepts positive normal operands. For fraction width $f$, it scales the integer significand by $f$ or $f+1$ bits depending on exponent parity, and the shared `sqrtRem` returns $s,r$ with $n=s^2+r$ and $0\le r\le2s$. Rounding picks $s$ when $r\le s$ and $s+1$ otherwise, because the midpoint square is $s^2+s+\tfrac14$, which no integer radicand can equal. Neither integer kernel has a fixed significand-width limit. Division sends non-finite operands to the reference operation, and square root sends zeros, subnormals, negative values, and exceptional values there. The proofs [`toModel_div`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Division/Proof.lean) and [`toModel_sqrt`](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/WideLimb/Sqrt/Proof.lean) cover the complete operations, fallback branches included.

<a id="capacity-bounds-and-compiler-assumptions"></a>

## Capacity bounds and backend dispatch

Several numerical certificates need capacity hypotheses. The word division loop needs a divisor below $2^{63}$, and the two-word square root at 113 digits needs a radicand below $2^{226}$. Certified division needs a fraction-width parameter between 65 and 126. That range corresponds to normalized significands of 66 to 127 bits. Before applying the theorem, a backend has to prove these from its field widths. Outside those bounds the kernel still returns words, but the theorem says nothing about what they mean, and even there the accumulator equalities preserve those word results.

[Chapter 16](#/chapter/backends-and-the-planner) follows an ordinary arithmetic call through format eligibility, cost comparison, and execution, and the dispatcher selected there uses these certificates where their hypotheses hold and a proved fallback everywhere else.
