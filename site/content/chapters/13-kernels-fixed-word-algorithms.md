---
number: "13"
slug: kernels-fixed-word-algorithms
title: "Kernels: arithmetic on words and limb arrays"
summary: Machine-word and limb-array algorithms compute significands, with proofs relating each result to natural-number arithmetic.
phases: [kernels]
---

An exact floating-point reference operation decodes its operands into arbitrary-precision
integers, combines them, and rounds once. This handles every format, but even a small operation
can allocate heap objects for values that fit in registers. When the values fit, we'd like to
avoid that allocation. The algorithms in the [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) compute with machine words and
prove which natural numbers those words denote. A backend applies that theorem to justify
replacing an arbitrary-precision step with a word operation. The reference operation remains
its specification.

## What we mean by a kernel

A kernel combines an algorithm over machine words with a theorem about its result. It may store a value in a `UInt64`, a pair of words represented by [[FloatLib.Numerics.FixedWord.UInt128]], four words in a `UInt256`, or an `Array UInt32` of limbs. A `toNat` function interprets those words as a natural number, and the theorem states what number the algorithm computes.

For multiplication, the theorem says the returned words denote the product. For rounding, they denote what the arbitrary-precision [[FloatLib.Numerics.roundShiftRightEven]] returns. For division, the quotient and remainder satisfy the Euclidean identity. A backend uses these theorems to justify calling a kernel. For the division algorithm described below, the proof instead justifies a check that every proposed result must pass.

The kernel interfaces are independent of a format's bit layout: no field widths, bias, or NaN or infinity encoding appears in the [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels). Signs enter only as a boolean on a magnitude ([signed-magnitude implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/SignedMagnitude/Runtime.lean)), and exponents as integers used for alignment and comparison ([dyadic comparison implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/DyadicCompare/Runtime.lean), `finiteScale`). The backends described in [chapter 14](#/chapter/backends-and-the-planner) decode a format's fields, call a kernel, and pack the result. Their refinement proofs use the kernel theorems as lemmas.

Every kernel keeps executable definitions in a `Runtime.lean` module and theorems in separate proof modules (`Proof.lean`, sometimes split further). A program can import the runtime alone; a proof imports the same definitions together with their theorems.

## One word, two words, four words

A binary64 significand has 53 bits and fits a `UInt64`. Its square does not: a 53 by 53 bit product has 106 bits, and a 113 by 113 bit binary128 product has 226. A pair of native words represents up to 128 bits, with the value

$$\mathrm{toNat}(\langle hi, lo\rangle) = lo + hi \cdot 2^{64},$$

and the four-limb `UInt256` in the [word-product implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Product/Runtime.lean) is the same idea twice.

The primitive product is [[FloatLib.Numerics.FixedWord.mul64]], the exact product of two 64-bit words as a `UInt128`. Native multiplication wraps, so the algorithm splits each operand into 32-bit halves and combines the four partial products with explicit carries, the decomposition the docstring credits to Hacker's Delight [@warrenHackersDelight2013]. Its certificate, [[FloatLib.Numerics.FixedWord.mul64_toNat]], says the two words denote exactly `x.toNat * y.toNat`. One level up, `mul128` forms a 256-bit product from four `mul64` calls and `mul128_toNat` states the same equation. Addition returns its carry rather than losing it (`add128_toNat` says value plus carry times $2^{128}$ equals the sum), comparison is `UInt128.less`, and `UInt128.sub` wraps modulo $2^{128}$ with a [subtraction proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Difference/Proof.lean) of when the wrapped result is the ordinary difference. A theorem that identifies wrapped word arithmetic with an unbounded result needs bounds that rule out overflow; a theorem that also returns the carry can account for it directly.

We can make the carry visible by filling both words before adding. Compare the two outputs
below: the multiplication keeps its high word as part of the product, while the addition
returns a separate carry.

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

The half-word split is ordinary multiplication in base $B=2^{32}$. Writing $x=x_0+Bx_1$ and $y=y_0+By_1$ gives

$$
xy=x_0y_0+B(x_1y_0+x_0y_1)+B^2x_1y_1.
$$

Each partial product fits in 64 bits, but simply adding the two middle products in one word could lose a carry. The implementation combines them in stages: it keeps the low half of each completed column and passes its high half into the next column. `mul64_toNat` accounts for those carries in the reconstructed integer. The returned high word is part of the product, so a large high word is a valid result rather than an overflow flag.

The first result is $(2^{64}-1)^2 = 2^{128} - 2^{65} + 1$, whose high word is $2^{64} - 2$ and whose low word is 1; the theorem is what lets a backend proof replace the two words by that number without inspecting the half-word arithmetic. The last result is $2^{128} - 1$ plus one: both words wrap to zero and the carry field records the $2^{128}$ that a plain addition would have lost, which is exactly the term `add128_toNat` accounts for.

## Guard bits and sticky bits

After computing an exact significand, a backend may need to shorten it to the destination precision. This is where rounding enters. Rounding $v$ to nearest even after discarding $s$ low bits means comparing the discarded remainder $r = v \bmod 2^s$ against the halfway value $2^{s-1}$: below it keep the quotient, above it add one, and exactly at it pick whichever of the two neighbours is even. The one-word kernel `roundShiftRightEven` does exactly this. It has explicit branches for a shift of 64 and beyond, because Lean's `UInt64` shifts reduce their count modulo 64 and a naive `1 <<< 64` would be `1`. Its certificate, `roundShiftRightEven_toNat`, says the word it returns denotes `Numerics.roundShiftRightEven value.toNat shift` for every value and every shift.

Building $2^{s-1}$ is cheap in a word but can require a large allocation for a limb array. The same comparison can be decided by inspecting bits in the value already stored. [[FloatLib.Numerics.roundShiftRightEven_eq_guard_sticky]] states that for $s > 0$,

$$\mathrm{round}(v, s) = \lfloor v / 2^s \rfloor + \begin{cases} 1 & \text{if } g \wedge (t \vee p) \\ 0 & \text{otherwise,} \end{cases}$$

where the guard bit $g$ is bit $s-1$ of $v$, the sticky bit $t$ records whether any bit below the guard is set, and the parity bit $p$ is bit $s$, the low bit of the quotient. If the guard is clear, the discarded remainder is below halfway. If both guard and sticky are set, it is above halfway. A set guard with a clear sticky is an exact tie, so the low bit of the quotient decides whether to increment: incrementing an odd quotient makes the answer even. These tests use the stored limbs without constructing the remainder as a separate large integer.

The sticky bit also justifies truncating early. `shiftRightJam` shifts right by $j$ bits and ors a one into the low bit whenever a nonzero bit was discarded, and [[FloatLib.Numerics.roundShiftRightEven_shiftRightJam]] proves that if $j + 2 \le s$ then rounding the jammed value by the remaining $s - j$ bits equals rounding the original by $s$. The two-bit separation keeps the jammed low bit below the guard used by the final rounding, so the jam records discarded information without replacing the guard itself. Wide addition uses three extra low positions, a guard bit, one more bit, and a sticky bit, together with alignment conditions that keep this information valid through the addition or subtraction. The fixed-word forms are `UInt256.shiftRightJam128`, which reduces a four-limb value to two limbs while jamming, and `UInt256.roundShiftRightEven128`, which the two-word product kernels call with a shift of 112 or 113 for binary128.

Both rounding theorems share the [shift-right-jam proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Numerics/ShiftRightJam/Proof.lean); the limb-array proofs reuse them through the arrays' natural-number values.

Before running these three rounding cases on five-bit values, mark the guard bit and check
whether anything below it is set. Then compare the even and odd ties. The last call gives us
a jammed value, which we'll interpret separately.

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

The jammed value seven deserves a closer look. It is neither the exact quotient $6.25$ nor that quotient rounded to the nearest integer. Its low one bit records that something nonzero was lost, for a later rounding decision. With a final shift of six, the theorem applies: rounding the original $100/64=1.5625$ gives two, and rounding the jammed $7/4=1.75$ also gives two. The fractional distances have changed, but the final rounding decision has survived.

If we instead tried to finish with a shift of five, only one bit would remain after the jam. Rounding $100/32=3.125$ gives three, while rounding $7/2=3.5$ to even gives four. The jam has reached the final guard position and created a tie. This is a counterexample to dropping the theorem's two-bit separation hypothesis, using the very same stored value as the example.

## Restoring division

Restoring division generates the quotient one bit at a time. Each step doubles the remainder; if it is still below the divisor, the next quotient bit is zero. Otherwise the step subtracts the divisor and appends a one. Subtracting the divisor from the remainder and adding one to the quotient preserve the same represented numerator. The natural-number recurrence below is copied from the [restoring-division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Proof.lean); the `rfl` check requires this copy to remain definitionally equal to the library definition.

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

The type `QuotientState` can hold `Nat`, `UInt64`, or `UInt128` pairs. The invariant is `natQuotientSteps_spec`: after $n$ steps from a state with remainder below the divisor,

$$q' \cdot d + r' = (q \cdot d + r) \cdot 2^n, \qquad r' < d, \qquad q \le q'.$$

The equation is the division identity scaled by $2^n$. Doubling a remainder that is below the divisor gives a value below twice the divisor, so at most one subtraction restores the strict remainder bound. That bound makes the quotient the true floor. The last inequality says the quotient prefix never shrinks; the word-level proof uses this to bound every intermediate quotient. Uniqueness of Euclidean quotient and remainder then gives `natQuotientSteps_div_mod`: the state is exactly the quotient and remainder of the scaled numerator.

The word loop `quotientStep` uses the same recurrence, with each doubling written as `x + x`. Its proof applies the natural-number result under the capacity hypotheses stated in its docstring: a divisor and a quotient prefix below $2^{63}$, so that neither addition wraps.

We can follow both branches in the first two steps of the example below. Starting with $4=1\cdot3+1$, doubling the remainder gives two, below the divisor three, so the new state is quotient two and remainder two: it represents eight. Doubling again gives remainder four, so we subtract three and set the next quotient bit, obtaining quotient five and remainder one: it represents sixteen. In general the subtraction branch preserves the scaled numerator because

$$
(2q+1)d+(2r-d)=2(qd+r).
$$

The guard tells us the subtraction is nonnegative, while the old bound $r<d$ tells us the new remainder is below $d$. The identity tracks the represented value; the inequalities make that value's quotient unique and justify performing the updates in bounded words.

To round a quotient, the one-word rounder `roundQuotientEven` compares the remainder with the divisor minus the remainder. This decides $2r$ against $d$ within one word, without any bound on the divisor. It is the kernel that `Numerics.roundQuotientEven` compiles to, as the section on `csimp` below explains. The restoring loop can use a simpler comparison: its state rounder `roundQuotientState` doubles the remainder and compares it with the divisor. The same capacity hypothesis keeps the divisor below $2^{63}$, so the doubling is safe. The complete calculation from scaled numerator to nearest-even quotient is `roundScaledQuotient`, proved correct by [[FloatLib.Numerics.FixedWord.RestoringQuotient.roundScaledQuotient_toNat]].

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

We can follow the first of those `#eval`s one step at a time in [Figure 13.1](#/chapter/kernels-fixed-word-algorithms/figure-ch08-restoring-division): each row doubles the remainder, compares it with the divisor, and appends the quotient bit. Read the last column alongside the updates to check the invariant on every row.

![Restoring division of 4 by 3 through four more quotient bits, each step doubling the remainder, comparing it with the divisor, and either keeping it and appending a 0 or subtracting and appending a 1, until the state is quotient 21 and remainder 1](assets/ch08-restoring-division.png "Each restoring-division step appends one quotient bit while maintaining the exact quotient-and-remainder identity.")

The two-limb loop [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128]] has the same shape and the certificate `quotientSteps128_div_mod` in the [two-word restoring-division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Restoring128Proof.lean); its compiler replacement keeps the state in scalar accumulators, as described under `csimp` below.

## Restoring square root

Square root uses the same shape with two-bit digits, because $(2r + b)^2 = 4r^2 + 4rb + b^2$ lets us extend a root by one bit while consuming two bits of radicand. The two-limb step from the [restoring-square-root implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/RestoringSqrt/Runtime.lean) shifts the remainder left by two, appends the next base-four digit, forms the trial value $4r + 1$, and subtracts it when it fits.

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

The invariant is `Represents`: a state represents a value $x$ when $r^2 + m = x$ and $m \le 2r$, where $r$ is the root and $m$ the remainder. The nonnegative remainder puts the square of $r$ at or below the radicand. The upper bound on the remainder puts the next integer square strictly above it. Thus $r$ is $\lfloor\sqrt{x}\rfloor$, which is `sqrt_spec`. After all digits are consumed, [[FloatLib.Numerics.FixedWord.RestoringSquareRoot.rootAndRemainder_spec]] says the root is `Nat.sqrt` of the radicand and the remainder is the radicand minus the root squared, for any digit count from 64 to 125 and any radicand below $2^{2 \cdot \mathrm{steps}}$; the binary128 backend uses 113 digits, one more than its fraction width, and declines fractions wider than 124 bits, where a doubled remainder would leave the two-word state.

The trial value in `rootStep` follows directly from this invariant. If the consumed prefix is $x=r^2+m$ and the next base-four digit is $d$, the enlarged prefix is

$$
4x+d=(2r)^2+(4m+d).
$$

The candidate root $2r$ therefore has remainder $4m+d$. Raising the root to $2r+1$ costs exactly $(2r+1)^2-(2r)^2=4r+1$, which is the trial subtracted by the code. The old remainder bound and $0\le d\le3$ put the enlarged prefix below $(2r+2)^2$, so these are the only two possible floor roots. Appending `digit` with bitwise OR implements the addition because a two-bit left shift leaves two zero bits and the digit occupies only those positions. The word-level proof must also show that the shifts do not discard high bits; this is where the digit-count capacity bounds enter.

The remainder also determines how to round the root. The square root of a nonnegative $p$-bit binary input cannot land exactly on a midpoint at the same precision: a midpoint between adjacent $p$-bit values has an odd significand of $p+1$ bits, and its square would have an odd significand of $2p+1$ or $2p+2$ bits, which no $p$-bit input can have. For the integer radicand used by the restoring kernel, rounding up happens exactly when $x > (r + \tfrac12)^2 = r^2 + r + \tfrac14$, that is when $m > r + \tfrac14$, and since both are integers this is $m > r$. `roundRoot` increments the root when the remainder exceeds it, and `roundRoot_toNat` proves that this is the nearest integer root under the same digit-count hypotheses.

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

For binary64 the root and remainder fit in a one-word state. The kernel in the [binary64 square-root implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Sqrt/Runtime.lean) scales the significand to a 105- or 106-bit radicand held in two words, runs 53 steps of a `UInt64` version of the same step while reading the radicand two bits at a time, and packs. The state fits one word because the root has at most 53 bits and the remainder is at most twice the root. Its `sqrt` covers every input bit pattern, including NaN, infinities, signed zeros, and negatives.

<a id="certificates-check-the-answer-instead-of-trusting-the-search"></a>

## Checking a division result

At two limbs the restoring loop runs 112 or 113 iterations for binary128, one bit each, after the initial state has supplied the leading quotient bit. Knuth's Algorithm D [@knuth1997] uses long division in radix $2^{32}$ to produce a 128-bit quotient in four digit steps. Each step estimates a quotient digit, corrects it at most twice, and repairs a negative partial remainder by adding the divisor back. The correctness proof is attached to the check of the proposed quotient and remainder; the Algorithm D search itself is unproved. [[FloatLib.Numerics.FixedWord.CertifiedDivision.candidate]] runs Algorithm D and returns a candidate quotient and remainder; [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate]] checks them independently with three tests (namespaces shortened here):

```
sum.carry == 0 &&
  sum.value == UInt256.ofUInt128ShiftedLeft num (shift.toNat precision) &&
  UInt128.less remainder den
```

Here `precision` is $p$ for significands of $p + 1$ bits. The `shift` chooses one of two scalings of the numerator: `.exact` by $2^p$ when the numerator is at least the denominator, and `.extra` by $2^{p+1}$ otherwise. This gives a quotient of exactly $p + 1$ bits. The value `sum` is `mul128 quotient den` plus the widened remainder in 256 bits.

The tests check that this addition has no carry, that the result equals the scaled numerator, and that the remainder is below the divisor. Together these establish Euclidean division, so [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate_sound]] concludes that a candidate passing the check is the unique correct quotient and remainder, however it was produced.

A proposed quotient can fail the certificate check, so the backend includes a proved fallback. [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate]] computes the candidate and checks it. If the check fails, it runs the restoring loop, whose result `checkedCandidate_complete` proves will pass the same check on every normalized input.

The backends use [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate_sound]]: the selected pair satisfies the exact quotient equation and the strict remainder bound, for every precision from 65 to 126 bits. This holds whether the initial candidate passed or the restoring loop replaced it. The final step, `roundQuotient`, rounds to nearest even by doubling the remainder in 128 bits with an explicit carry, and `roundQuotient_toNat` connects it to the arbitrary-precision quotient rounder.

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

Let's check the large quotient by cancelling the common power of two in
$2^{225}/(3\cdot2^{111})$. This leaves $2^{114}/3$. Since $2^{114}$ leaves remainder one on
division by three, the floor quotient is $(2^{114}-1)/3$. Multiplying it back by the original
denominator leaves remainder $2^{111}$, exactly the remainder supplied to the certificate.
Decreasing the quotient by one without changing the remainder breaks the product-plus-remainder
equality. Increasing the remainder by the divisor would repair that equality, but would violate
the strict remainder bound. The two tests together exclude both ways of presenting the wrong
quotient.

The carry test makes the equality an equality of natural numbers. Without accounting for carry, equality of the low 256 bits would establish only a congruence modulo $2^{256}$. Here `mul128_toNat` gives the full product, and the zero carry on its addition to the remainder lets `certificate_sound` recover the unbounded Euclidean identity. The search can use any strategy that produces a candidate; the accepted answer must satisfy that identity and the bound.

We can change the Algorithm D search in the [certified-division implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/CertifiedDivision/Runtime.lean) without changing the
soundness argument for an accepted result: that proof depends on the certificate check.

<a id="proved-once-reused-everywhere"></a>

## Reusing a kernel proof across formats

Once we have proved the word arithmetic, we can reuse it across formats. The kernel theorems
state their capacity bounds and value invariants explicitly. For each format, we then need to
show that its decoded operands satisfy those bounds and that it packs the result correctly.

The certificates are stated over natural numbers and parametrized by capacity rather than by format. [[FloatLib.Numerics.FixedWord.RestoringQuotient.roundScaledQuotient_toNat]] takes any numerator, divisor, and shift satisfying its two bounds; the binary64 backend in the [binary64 division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Full/Division/Proof.lean) and the small-word backend in the [small-word division proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Backends/Word/Small/Div/Proof.lean) both discharge those bounds from their own field widths and then use the theorem unchanged. [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate_sound]] takes the precision as an argument with the bounds $64 < p \le 126$, so the same theorem serves binary128 and every custom `ExecFloat.Binary e f` with $65 \le f$ and $e + f \le 127$ that the pair backend accepts.

The invariants are stated over an abstract carrier. `RestoringRootState α` holds a root and a remainder of any type, `Represents` takes the `toNat` function as an argument, and `loop_represents` in the [shared word proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Proof/Word.lean) proves the entire induction over base-four digits once, for any step function that preserves `Represents` on one digit. The binary64 square-root proof instantiates it with `UInt64.toNat` and the two-limb proof with `UInt128.toNat`; neither repeats the induction. What each backend still proves is exactly what is specific to it: that its decoding produces the radicand it claims, that its exponent arithmetic is right, and that its packing is inverse to its decoding.

The definitions are shared too. The [signed-magnitude implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/SignedMagnitude/Runtime.lean) combines two signed magnitudes in one word, and the [dyadic comparison implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/DyadicCompare/Runtime.lean) compares word significands at unbounded exponents. Binary interchange and posit backends therefore use the same definitions of cancellation and ordering.

<a id="what-csimp-does-on-one-example"></a>

## Compiler replacements with csimp

A `@[csimp]` equation connects a logical definition to a compiler replacement, as described in [chapter 05](#/chapter/why-execution-and-proofs-are-separate). Lean's kernel checks the equation `f = g`, and the compiler uses it to rewrite calls to `f` into calls to `g`. The replacements in the [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels) include the proved two-limb quotient substitution described below.

For right-shift rounding, the logical definition is [[FloatLib.Numerics.roundShiftRightEven]] over `Nat`. The fast definition is `roundShiftRightEvenNat`, quoted below as a checked copy: it tests whether the value fits one word, and if so runs the native kernel and converts back.

```lean
def roundShiftRightEvenNat (value shift : Nat) : Nat :=
  if _hvalue : value < 2 ^ 64 then
    (FloatLib.Numerics.FixedWord.roundShiftRightEven (UInt64.ofNat value) shift).toNat
  else if shift == 0 then
    value
  else if value.log2 + 1 < shift then
    0
  else
    let quotient := Nat.shiftRight value shift
    let remainder := FloatLib.Numerics.shiftRightRemainder value shift
    let half := Nat.shiftLeft 1 (shift - 1)
    if remainder < half then
      quotient
    else if half < remainder then
      quotient + 1
    else if quotient % 2 == 0 then
      quotient
    else
      quotient + 1

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

The second `example` is the statement of [[FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat]], which carries `@[csimp]`. Its proof is `funext` followed by the lemma `roundShiftRightEvenNat_eq_roundShiftRightEven`, which applies the certificate `roundShiftRightEven_toNat` on the native branch and unfolds the definition on the other. Once we import that module, calls in newly compiled definitions and `#eval` expressions use `roundShiftRightEvenNat`, as in the example above. An import does not retroactively rewrite previously compiled functions; their modules need the theorem available when compiling those callers. The logical definition is unchanged, so its theorems still apply.

The arbitrary-precision branch repeats the body of the logical definition instead of calling it. If it called `Numerics.roundShiftRightEven`, the compiler would apply the same `csimp` rewrite to that call, and the compiled fallback would call itself. Repeating the body avoids this recursion, and the equation theorem proves that it computes the same result.

There are five `@[csimp]` theorems in the [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels). Two are the rounders in the [rounding proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Proof/Rounding.lean) (`roundShiftRightEven` and `roundQuotientEven`). The [integer-square-root proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/IntegerSquareRoot/Proof.lean) routes `Nat.sqrt` through a `UInt64` Newton iteration for inputs below $2^{64}$; this one reaches outside the library, since any program importing `FloatLib.Kernels` compiles its own `Nat.sqrt` calls through [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]], and the theorem's docstring says so. The [division compiler proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Quotient/Compiler.lean) replaces the two-limb loop [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128]], which allocates a fresh two-limb state at every generated bit, by `quotientSteps128Impl`, which keeps quotient and remainder in four `UInt64` accumulators and builds the state once at the end. The theorem [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128_eq_quotientSteps128Impl]] is a short induction, kept in its own module so that an executable client can enable the rewrite without importing the rational-arithmetic proofs. The fifth replaces limb-array `toNat` with a Horner loop.

## Limb arrays: 32-bit limbs updated in place

The fixed-word kernels use up to four 64-bit limbs for binary128's intermediate arithmetic. Whether a backend supports a particular layout also depends on the [field widths and capacity bounds](#/chapter/backends-and-the-planner/which-formats-a-kernel-supports). Wider formats can use [[FloatLib.Numerics.LimbArray]] in the [limb-array implementation](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/LimbArray): a natural number stored as a little-endian `Array UInt32`, limb $i$ carrying weight $2^{32 i}$, with reading beyond the stored limbs defined to give zero so that appending zero limbs does not change the value. [[FloatLib.Numerics.LimbArray.toNat]] is the value, and, as everywhere in the kernels, every operation is specified by its effect on it: [[FloatLib.Numerics.LimbArray.toNat_add]], `toNat_sub`, [[FloatLib.Numerics.LimbArray.toNat_mul]], `toNat_shiftLeft`, `toNat_shiftRight`, and [[FloatLib.Numerics.LimbArray.toNat_roundShiftRightEven]].

The 32-bit limb width avoids boxing allocations in Lean's runtime on a 64-bit platform. An `Array` holds `lean_object` pointers, and in the [runtime header](https://github.com/leanprover/lean4/blob/v4.33.1/src/include/lean/lean.h) of the toolchain this repository pins (`leanprover/lean4:v4.33.1`), `lean_box_uint64` allocates a constructor cell with `lean_alloc_ctor` for every value, while `lean_box_uint32` on a 64-bit platform calls `lean_box`, which encodes the number in a tagged pointer with no allocation. Writing a `UInt64` array element therefore requires a boxed value, while a `UInt32` element fits the tagged representation on that platform. The smaller limb width also leaves room for a product and carries in the arithmetic register. A limb product plus two addends fits exactly,

$$(2^{32}-1)^2 + 2(2^{32}-1) = 2^{64} - 1,$$

so every intermediate of the schoolbook multiplication stays in a `UInt64`, and a limb sum with two carries stays there with room to spare. Array ownership determines whether writing those elements also copies the array. When its reference count is one, Lean updates the array destructively, so `Array.setIfInBounds` on a loop-owned accumulator is an in-place store. The result buffer still needs allocation; the owned loop avoids a new boxed object or array copy for each limb update.

`carryLoop` adds a word at a limb position and propagates the carry upward, stopping as soon as it vanishes, so the common case touches one limb; it is the primitive behind `addAt`, which adds $w \cdot 2^k$ for a bit position $k$, and behind the increment that rounding needs. `add` produces one limb more than the wider operand, which is why `toNat_add` has no side condition. `sub` assumes its result is nonnegative and `toNat_sub` states that contract. [[FloatLib.Numerics.LimbArray.mul]] is the schoolbook product in `a.size + b.size` limbs, one row per limb of the left operand. The shifts build each result limb from at most two source limbs with `Array.ofFn`, so no intermediate array is written twice. Each loop is structural recursion over a limb count, so its invariant in the [limb-arithmetic proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/LimbArray/Arithmetic/Proof.lean) is an induction on that count: the processed segment changed by the intended amount and every limb outside it did not.

Limb rounding uses the guard-and-sticky form to avoid a large halfway integer. [[FloatLib.Numerics.LimbArray.roundShiftRightEven]] reads the guard and parity bits with `testBit` and the sticky bit with `anyBelow`, then increments the shifted quotient with one carry-propagating `addAt`. It never forms $2^{s-1}$.

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

Its certificate `toNat_roundShiftRightEven` is the guard-and-sticky theorem applied to the value of the array, with `testBit_eq` and `anyBelow_eq` translating the three bit reads into facts about `toNat`. `orLowBit` is the sticky jam for arrays, with `toNat_orLowBit` saying it ors a one into the value of a nonempty array.

Read these arrays from low limb to high limb. We start with the stored value, then follow
the product and the carry into their extra limbs; the last calls make the two sticky reads
used for rounding.

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

We can check the product's five output limbs ourselves by expanding it:

$$
(2^{70}+5)(2^{40}+1)=2^{110}+2^{70}+5\cdot2^{40}+5.
$$

The constant five goes in limb zero. The term $5\cdot2^{40}$ is $1280\cdot2^{32}$, so limb one is 1280; $2^{70}=64\cdot2^{64}$ supplies limb two, and $2^{110}=16384\cdot2^{96}$ supplies limb three. Limb four is zero. Multiplication reserves the sum of the operand lengths, even when the particular answer needs fewer limbs, and the value theorem permits that leading zero. This is why the printed array need not be a shortest representation of its integer.

For the first and the fourth of those results, follow the limb positions in [Figure 13.2](#/chapter/kernels-fixed-word-algorithms/figure-ch08-limb-arrays): the split of $2^{70} + 5$ into three limbs, and the carry that ripples through three saturated limbs into the fourth limb that `add` reserves.

![A limb array stores 2^70 + 5 as three 32-bit limbs, and adding 1 to 2^96 - 1 carries through all three limbs into the extra limb that add reserves](assets/ch08-limb-arrays.png "Little-endian 32-bit limbs represent a wide integer. The addition example shows why the output needs an extra limb for the final carry.")

The fifth `csimp` theorem is [[FloatLib.Numerics.LimbArray.toNat_eq_toNatImpl]]. The `toNat` definition used in proofs starts with the first limb and adds the radix times the value of the rest. This form makes the invariants easy to state, but is not tail recursive. The compiled form uses a Horner loop from the top limb down. `hornerFrom_eq` proves the two forms equal, and `csimp` tells the compiler to use the loop.

These kernels serve the [wide-limb backend](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Floats/ExecFloat/Backends/WideLimb), which handles IEEE layouts wider than 128 bits with an exponent field of at most 32 bits, using the limb storage named by `ExecFloat.BinaryLimbs`. Public arithmetic on this type uses the automatic certified planner: for example, `+` on `ExecFloat.BinaryLimbs 19 236` selects wide-limb addition under the default policy. [Chapter 14](#/chapter/backends-and-the-planner/choosing-the-limb-carrier) works through that call and its public specification theorem.

Its addition core `alignOrdered?` is the sticky-bit argument made concrete: when the scale difference $d$ is at least three and the operand at the larger scale keeps its leading bit at least two positions above the other's after alignment, so that the leading bit of the result is known, it shifts the operand at the smaller scale right by $d - 3$ bits, records `anyBelow` of the discarded part as the sticky bit, shifts the larger operand left by three, adds or subtracts in limbs, jams the sticky bit with `orLowBit`, and rounds. The three extra bits are the guard bit, one more bit, and the sticky position that `roundShiftRightEven_shiftRightJam` requires. On the accepted path the significand is never converted to a `Nat`; only limb indices and shift counts are. Addition, subtraction, multiplication, and fused multiply-add have limb fast paths for accepted normal operands with normal results; any declined call uses the exact baseline. These dyadic fallback operations use bulk integer rounding at every width: the [dyadic specification](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Spec/Dyadic.lean) imports the compiler proof before defining them. Division and square root above 128 bits run on the exact baseline throughout.

<a id="kernels-fixed-word-algorithms-and-limb-arrays"></a>

## Finding the kernel implementations

The [core word implementation](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord/Core/Runtime.lean) contains nearest-even shifts and quotients, two-word arithmetic, and restoring square-root state over `UInt64` and `UInt128`. The files live in the [kernel directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels); their declarations use the `FloatLib.Numerics.FixedWord` and `FloatLib.Numerics.LimbArray` namespaces because they operate on the numerical layer's primitive fixed-word representations. The [fixed-word module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/FixedWord.lean) documents that naming convention, and the [kernel module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels.lean) documents the import's effect on compiled `Nat.sqrt` calls.

Each subdirectory under the [fixed-word directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/FixedWord) pairs an algorithm with its proof. The [restoring divider](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/FixedWord/Quotient) implements restoring division, with [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128]] as the two-limb loop. The [certified divider](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/FixedWord/CertifiedDivision) implements the binary128 divider: a proposed quotient and remainder, the check justified by [[FloatLib.Numerics.FixedWord.CertifiedDivision.certificate_sound]], and the restoring fallback covered by [[FloatLib.Numerics.FixedWord.CertifiedDivision.checkedCandidate_sound]].

Beside the [fixed-word directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/FixedWord), the [limb-array directory](https://github.com/lean-dojo/FloatLib/tree/main/FloatLib/Kernels/LimbArray) handles formats wider than two words: [[FloatLib.Numerics.LimbArray]] stores a natural number as little-endian 32-bit limbs, and every kernel in it is specified by its effect on [[FloatLib.Numerics.LimbArray.toNat]]. The choice of `UInt32` avoids per-element boxing on a 64-bit platform, as explained in [this chapter](#/chapter/kernels-fixed-word-algorithms). The [limb-array definition](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels/LimbArray/Core/Runtime.lean) describes the representation and its accessors.

The proof style is uniform. A word-level function is related to its natural-number meaning by a `_toNat` lemma such as [[FloatLib.Numerics.FixedWord.mul64_toNat]] for the two-word product, and the specification is stated over `Nat`, so correctness is a theorem about naturals that the word version inherits. Five theorems here are also compiler certificates. A `@[csimp]` lemma tells the compiler to replace one Lean definition by another when compiling a caller with the theorem available; the five in this directory are [[FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat]], `roundQuotientEven_eq_roundQuotientEvenNat`, [[FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat]], [[FloatLib.Numerics.FixedWord.RestoringQuotient.quotientSteps128_eq_quotientSteps128Impl]], and [[FloatLib.Numerics.LimbArray.toNat_eq_toNatImpl]]. The square-root lemma applies to newly compiled `Nat.sqrt` calls in any importing module, including code outside FloatLib, which is why the [kernel module](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Kernels.lean) warns about it. The following two signatures put the logical definition on the left and the word-level implementation on the right:

```lean
#check @FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat
-- FloatLib.Numerics.FixedWord.roundShiftRightEven_eq_roundShiftRightEvenNat : FloatLib.Numerics.roundShiftRightEven =
--   FloatLib.Numerics.FixedWord.roundShiftRightEvenNat

#check @FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat
-- FloatLib.Numerics.FixedWord.IntegerSquareRoot.natSqrt_eq_sqrtNat : Nat.sqrt =
--   FloatLib.Numerics.FixedWord.IntegerSquareRoot.sqrtNat
```

Lean checks the equations that authorize these substitutions. The compiler must still apply them correctly, as it must correctly compile the rest of the program.

<a id="where-the-kernel-boundary-ends"></a>

## Capacity bounds and compiler assumptions

Several certificates require capacity hypotheses: a divisor below $2^{63}$ for the word division loop, a radicand below $2^{226}$ for the two-word square root at 113 digits, or a precision between 65 and 126 for certified division. A backend must prove these from its field widths before applying the theorem. Outside those bounds, the kernel still returns words, but the theorem does not establish their meaning. The dispatchers in [chapter 14](#/chapter/backends-and-the-planner) check eligibility and use a fallback when the specialized kernel cannot apply.

The refinement proofs are statements about Lean's definitions. `mul64_toNat` is a statement about `UInt64` operations as Lean's logic models them; whether the machine code the compiler emits for `mul64` multiplies correctly is a property of the compiler, the runtime, and the CPU. The refinement proofs cover the floating-point algorithms above those integer operations; they assume the toolchain and machine implement the operations correctly. [Chapter 15](#/chapter/performance/comparing-with-leans-native-floats) returns to it.
