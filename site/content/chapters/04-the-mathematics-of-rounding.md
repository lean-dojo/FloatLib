---
number: "04"
slug: the-mathematics-of-rounding
title: Rounding
summary: "What it means to round a number to a grid, how far rounding can move it, when a subtraction is exact, why rounding twice can go wrong, and how a sum can round only once."
phases: [rounding-theory, planner-and-configured, ieee-formats, binary-arithmetic]
---

A floating-point format can store only some numbers, so when the exact answer to a calculation falls between two of them, the format has to pick one. That pick is rounding, and the gap it leaves is rounding error. We'll round numbers by hand and in Lean, see how far rounding can move a number, and meet the two places where it surprises people most: subtractions that turn out exact, and roundings done twice.

Picturing a float as a real number with a little noise on it can't tell you when an operation adds no noise at all, or why computing in a wider format first can leave the narrower answer incorrectly rounded. A grid of points on the real line can. The grid needs no bit layout, so we study rounding on the real line alone, following Boldo and Melquiond's Flocq, a floating-point library for the Coq prover [@boldoMelquiond2011], in Lean on top of Mathlib [@leanMathlib2020]. Once the operations of a packed format, one stored as bits, are proved to agree with rounding on its grid, each grid theorem applies to that format under the theorem's own hypotheses, so one proof covers binary32, binary128 and custom IEEE-style descriptors (the records that give a format its field widths).

## What is rounding?

Let's start with a sum that surprises people. If you add one and a hundred-millionth in binary32, IEEE's single-precision format, and ask for the next binary32 number above one:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.Flocq

#eval (1 : Binary32) + 1e-8
-- 1

#eval ExecFloat.Binary.nextUp (1 : Binary32)
-- 1.0000001
```

you get one, and then $1 + 2^{-23}$. Picture the numbers a format can store as the ticks on a ruler. Just above one, binary32's ticks are $2^{-23}$ apart, and $10^{-8}$ is only about $0.084$ of that gap, well short of the midpoint. So rounding to nearest sends the true sum `1 + 1e-8` back to one, as we saw in [Chapter 03](#/chapter/the-numerical-models). In general a rounding function maps every real number onto the representable ones, the numbers the format can store, leaves each of those alone, and is monotone: a bigger input never gets a smaller output.

## How to round a number to a grid

Rounding to a format works like rounding a price to cents: multiply by 100, round to a whole number, divide by 100. But a format's scale depends on the size of the number. So we compute a canonical exponent $e$ from the magnitude of $x$ (we'll see how below), apply an integer rule to $x \cdot \beta^{-e}$, where the radix $\beta$ is the format's base, 2 for a binary format, and multiply back:

$$
\mathrm{round}_{\mathrm{rnd}}(x) \;=\; \mathrm{rnd}\!\left(x\,\beta^{-e}\right)\cdot \beta^{e}, \qquad e = \mathrm{cexp}(x).
$$

Let's try one. With a grid step of $1/4$, rounding $11/8$ scales it to $11/2 = 5.5$, a tie between 5 and 6. Nearest-even, which breaks ties toward the even integer, picks 6, and scaling back gives $6/4 = 3/2$. The step decided the candidates, $5/4$ and $3/2$, and the integer rule settled the tie. This construction is [[FloatLib.Floats.Formats.Flocq.round]], drawn in [Figure 4.1](#/chapter/the-mathematics-of-rounding/figure-ch07-rounding-staircase) as a staircase on a grid with three binary digits, whose steps double in width at each power of two.

![Round to nearest even on a grid with three binary digits, from 0.5 to 2.5: each step is the set of reals sent to one grid point, the steps double in width at 1 and at 2, and a filled end marks the neighbour a tie goes to](assets/ch07-rounding-staircase.png "Nearest-even rounding with three binary digits. Filled endpoints show the tie choice.")

An integer rule $\mathrm{rnd} : \mathbb{R} \to \mathbb{Z}$ is `ValidRnd`, a valid rounding rule, if it's monotone and leaves every integer alone, and `ValidRndToNearest` adds $|\mathrm{rnd}(x) - x| \le \tfrac12$. The six rules `floorRound`, `ceilRound`, `truncRound`, `awayRound`, [[FloatLib.Floats.Formats.Flocq.nearestEven]] and [[FloatLib.Floats.Formats.Flocq.oddRound]] are `ValidRnd`, and `nearestEven` and `nearestChoice`, for every tie rule (what it picks exactly halfway), are `ValidRndToNearest`.

## How to choose a rounding direction

The rounding directions you can ask for are the six constructors of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]], built from those integer rules. `oddRound` isn't one of them: it stays inside the grid theory. `down` uses `floorRound`, `up` uses `ceilRound`, `towardZero` uses `truncRound` and `away` uses `awayRound`. These four are called directed. The default, `nearest`, is `nearestEven`, and `nearestAway` is `nearestChoice` with ties sent to the larger magnitude. IEEE 754-2019, the floating-point standard, defines all but `away` [@ieee754_2019], and `away` is what the GNU MPFR library calls `MPFR_RNDA` [@mpfrManual].

[[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] takes the direction as `(mode := m)`, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_eq_round]] identifies each direction with Flocq's `round` under its integer rule [[FloatLib.Floats.Formats.Flocq.roundingFunction]]. That theorem is what carries the grid theorems over. Those that assume only `ValidRnd` hold in all six directions, and those that assume `ValidRndToNearest`, such as the half-ulp bound below, only for `nearest` and `nearestAway`. A directed mode can be off by almost a whole gap: $1 + 2^{-25}$ rounded up in binary32 is $1 + 2^{-23}$. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_neg]] says rounding $-x$ negates rounding $x$ in the direction `mode.negate`, which swaps `up` and `down` and leaves the rest alone.

### How do you know which way a result was rounded?

A rounded value doesn't remember which side of the exact result it fell on. The inexact flag says the result was rounded, and the ternary value, named for its three possible answers and returned by MPFR with every operation [@fousseMpfr2007], says which way: `Ordering.lt` when the delivered value is below the exact result, `Ordering.eq` when it's equal, `Ordering.gt` when it's above. With `(status := true)` an operation returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]] holding the value, the five IEEE status flags of [chapter 03](#/chapter/the-numerical-models/how-to-see-which-flags-an-operation-raised) and the ternary value, which comes from one exact comparison ([[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicTernary]] for operations that round an exact dyadic, a fraction with a power-of-two denominator). NaN, infinite, overflowed and saturated results follow fixed conventions, which the docstring of `IEEEOutcome.ternary` lists case by case.

The directions part ways at a tie, so let's add half a gap to one in binary32 in three modes:

```lean
def halfGap : Binary32 := ExecFloat.Binary.ofBits32 0x33800000

#eval ExecFloat.Binary.add 1 halfGap (status := true)
-- { value := 1, status := { inexact := true }, ternary := Ordering.lt }
#eval ExecFloat.Binary.add 1 halfGap (mode := .nearestAway) (status := true)
-- { value := 1.0000001, status := { inexact := true }, ternary := Ordering.gt }
#eval (ExecFloat.Binary.add 1 halfGap (mode := .towardZero) (status := true)).ternary
-- Ordering.lt
```

The word `0x33800000` holds $2^{-24}$, so the true sum $1 + 2^{-24}$ lies exactly halfway between $1$ and $1 + 2^{-23}$. Nearest-even keeps $1$, whose significand is even, below the exact sum, so the ternary value is `Ordering.lt`, and nearest-away goes up. Both calls raise only `inexact`, so it's the ternary value that tells you the side. Toward zero also returns $1$.

## How does a grid know its spacing?

The steps of that staircase doubled at each power of two, so a grid has to say how its spacing depends on the size of a number. It does that with a radix $\beta$ and a function $\mathrm{fexp} : \mathbb{Z} \to \mathbb{Z}$ giving the exponent for each magnitude. Think of $\mathrm{fexp}$ as the rule that hands out rulers: for numbers of each size, it says how far apart the ticks are. There are [three exponent families](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean), named as in Flocq:

- `fixExp` ($e \mapsto e_{\min}$) is fixed point, one spacing everywhere.
- [[FloatLib.Floats.Formats.Flocq.flxExp]] ($e \mapsto e - p$) gives the FLX grid, $p$ digits everywhere, and never underflows.
- [[FloatLib.Floats.Formats.Flocq.fltExp]] ($e \mapsto \max(e - p, e_{\min})$) gives the FLT grid, which adds the flat grid of gradual underflow, the subnormals with spacing $\beta^{e_{\min}}$, below the normal range.

Flush to zero, which drops the subnormals, has its own [abrupt underflow selector](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Special/FTZ.lean), `ftzExp`. So when is a number on the grid? A grid point [[FloatLib.Floats.Formats.Flocq.FloatRep]] is an integer mantissa $m$ and an exponent $e$, standing for $m\,\beta^{e}$ ([[FloatLib.Floats.Formats.Flocq.toReal]], [[FloatLib.Floats.Formats.Flocq.bpow]]). The `magnitude` of a nonzero $x$ satisfies $\beta^{\mathrm{mag}(x)-1} \le |x| < \beta^{\mathrm{mag}(x)}$, and applying $\mathrm{fexp}$ to it gives the canonical exponent [[FloatLib.Floats.Formats.Flocq.cexp]], the exponent of the grid spacing at $x$. Then $x$ is representable, which Flocq calls [[FloatLib.Floats.Formats.Flocq.genericFormat]], when its `scaledMantissa` $x\,\beta^{-\mathrm{cexp}(x)}$ is an integer.

Not every exponent function gives a sensible grid. The class [[FloatLib.Floats.Formats.Flocq.ValidExp]] carries Flocq's two conditions for neighbouring rulers to fit. Where $\mathrm{fexp}(k) < k$, so the format has genuine precision at magnitude $k$, the exponent one magnitude up is at most $k$, and the grid continues across the boundary. And once $\mathrm{fexp}$ reaches the magnitude, the spacing stays constant towards zero. We prove that FLX and FLT are valid exactly when the precision is positive, which is why callers check it with `FormatPrecision.ofInt?` first.

## What does rounding always guarantee?

Three facts about `round` carry most of the theory. It lands on the grid ([[FloatLib.Floats.Formats.Flocq.generic_format_round]]), leaves grid points alone (`round_preserves_generic`) and is monotone (`round_mono`, our [monotonicity proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Order.lean)), so a chain of operations stays inside the format. All three hold for any valid exponent function and integer rule, which the square-bracket arguments, filled in by instance search, ask for. In Lean they read:

```lean
example {β : FloatLib.Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (rnd : ℝ → ℤ) [ValidRnd rnd] (x : ℝ) :
    genericFormat β fexp (round (β := β) (fexp := fexp) rnd x) :=
  generic_format_round rnd x

example {β : FloatLib.Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x : ℝ} (hx : genericFormat β fexp x) :
    round (β := β) (fexp := fexp) rnd x = x :=
  round_preserves_generic rnd x hx

example {β : FloatLib.Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (rnd : ℝ → ℤ) [ValidRnd rnd] {x y : ℝ} (hxy : x ≤ y) :
    round (β := β) (fexp := fexp) rnd x ≤ round (β := β) (fexp := fexp) rnd y :=
  round_mono rnd hxy
```

Monotonicity also traps the integer rule between floor and ceiling. That gives the [neighbour-selection theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Properties.lean) `round_eq_floor_or_ceil`: every valid mode returns one of the two neighbours. The relational specifications `RoundDownPoint`, `RoundUpPoint` and `RoundNearestPoint`, which describe a correct rounding as a property of the result instead of a function that computes it, follow Flocq's `Rnd_DN_pt` and `Rnd_N_pt`, and we prove that the computed roundings meet them ([[FloatLib.Floats.Formats.Flocq.round_toNearest_point]] for nearest).

## What is a ulp?

Before we can bound an error we need a unit to measure it in, and the grid hands us one. A ulp, short for unit in the last place, is the grid spacing at a point, one tick's width on the ruler there, so at any nonzero $x$, [[FloatLib.Floats.Formats.Flocq.ulp]] is $\beta^{\mathrm{cexp}(x)}$. Following Flocq, the ulp of zero is the smallest subnormal, $\beta^{e_{\min}}$, for FLT, and for FLX, which has no smallest positive number, it's zero. Our [ulp proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Ulp.lean) and [neighbour proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Neighbors.lean) show that the directed roundings of a nonrepresentable $x$ are one ulp apart, and that `succ` and `pred` (successor and predecessor), the neighbouring grid points, land on the grid, even at a radix power.

For a packed binary format, [[FloatLib.Floats.Formats.BinaryInterchange.Model.fexpOf]] computes the exponent function from the descriptor of [chapter 03](#/chapter/the-numerical-models). It's `fltExp` at the minimum subnormal exponent, with precision one more than the fraction width. For binary32 that's $e_{\min} = -149$ and $p = 24$, and Lean will check both for you:

```lean
example : Model.fexpOf FloatFormat.binary32 = fltExp (-149) 24 := by
  rfl

#eval ExecFloat.Binary.nextUp (0 : Binary32)
-- 1e-45
```

The `rfl` proof has Lean compute both sides, and the `1e-45` is the predicted ulp of zero, $2^{-149}$. [[FloatLib.Floats.Formats.BinaryInterchange.Model.ulpAt]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.halfUlpAt]] are the format-level ulp and half ulp. The `1 + 1e-8` example falls out of `fexpOf` too: the canonical exponent is $\max(1-24,-149)=-23$ at one and $-22$ at two. At the least normal value, $2^{-126}$, it's $\max(-125-24,-149)=-149$, and the maximum keeps choosing $-149$ below that, so the subnormal spacing stays the same all the way to zero.

## How far can rounding move a number?

With the ulp as our unit, the answer is short. Nearest rounding lands within half a ulp of the exact value, and directed modes get one full ulp (`round_abs_error_le_ulp`), strictly less when the rounding was inexact. In the theory the nearest bound is [[FloatLib.Floats.Formats.Flocq.error_bound_ulp]], and since it asks only for `ValidRndToNearest`, it covers every tie policy:

$$
|\mathrm{round}_{\mathrm{rnd}}(x) - x| \;\le\; \frac{\mathrm{ulp}(x)}{2} \qquad \text{for every } \mathrm{rnd} \text{ with } |\mathrm{rnd}(t) - t| \le \tfrac12.
$$

That bound is absolute. Our [relative-error proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/Bounds.lean) also give the error as a fraction of $x$, in the form $\mathrm{fl}(x) = x(1 + \delta)$ for the rounded value $\mathrm{fl}(x)$. For FLX with $p$ digits, [[FloatLib.Floats.Formats.Flocq.round_relative_error_FLX]] proves $|\delta| \le \beta^{1-p}/2$, the unit roundoff $u$. The FLT version requires a normal-range input, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] applies it to packed formats with $u = 2^{-p}$, the $2^{-24}$ for binary32 that `#float_info [errors]` shows in [chapter 01](#/chapter/using-the-library). The sharper $u/(1+u)$ for FLX with at least two digits, from [Jeannerod and Rump (2018), Theorem 2.1](https://doi.org/10.1090/mcom/3234), we haven't proved :)

Here are the bounds in Lean: the two grid theorems, then the binary32 half-ulp bound and the binary32 relative bound, which needs a normal input. The second example writes `@round` with every argument given because its validity instance depends on `hprec`, the proof that the precision is positive.

```lean
example {β : FloatLib.Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    |round (β := β) (fexp := fexp) rnd x - x| ≤ ulp β fexp x / 2 :=
  error_bound_ulp rnd x

example {β : FloatLib.Numerics.Radix} (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    ∃ δ : ℝ, |δ| ≤ bpow β (1 - prec) / 2 ∧
      @round β (flxExp prec) (flxValidExp prec hprec) rnd x = x * (1 + δ) :=
  round_relative_error_FLX prec hprec rnd x

example (x : ℝ) :
    |Model.roundAt FloatFormat.binary32 x - x| ≤
      Model.halfUlpAt FloatFormat.binary32 x :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 x

example (x : ℝ) (hx : x ≠ 0)
    (hnormal : Model.minNormalAt FloatFormat.binary32 ≤ |x|) :
    ErrorBounds.relativeError x (Model.roundAt FloatFormat.binary32 x) hx ≤
      bpow FloatLib.Numerics.binaryRadix (1 - 24) / 2 :=
  Model.relativeError_roundAt_le_of_normal FloatFormat.binary32 x hx hnormal
```

### Why does the relative bound need a normal input?

[Figure 4.2](#/chapter/the-mathematics-of-rounding/figure-ch07-ulp) shows why for binary16, IEEE's half-precision format (`fltExp (-24) 11`). The absolute half-ulp bound is flat across the subnormal range and doubles at every power of two above it. Take a normal binade (the binary version of a decade), the stretch between two powers of the radix, with magnitude index $e$. There $|x| \ge \beta^{e-1}$ and half an ulp is $\beta^{e-p}/2$, so

$$
\frac{|\mathrm{round}(x)-x|}{|x|}
\le \frac{\beta^{e-p}}{2\,\beta^{e-1}}
= \frac{\beta^{1-p}}{2}.
$$

Error and value grow together through each binade, so their ratio forgets $e$. That's the whole trick, and it breaks down below the normal range, where the spacing stops shrinking. The real input $2^{-150}$, halfway between zero and the least binary32 subnormal, rounds to zero with relative error one. It's like rounding half a cent to whole cents: ties to even gives you zero cents, and the whole amount is gone. The half-ulp bound survives this and the relative one doesn't.

![Two binary16 panels for fltExp (-24) 11: Absolute spacing plots ulp and half ulp; Relative bound plots half ulp divided by x, between u/2 and u in the normal range and increasing as positive subnormal inputs approach zero](assets/ch07-ulp.png "Binary16 absolute and relative error bounds: the uniform relative bound requires a normal input.")

### How to drop the normal-range hypothesis

If you allow one more error term, the normal-range hypothesis can go. The standard model with gradual underflow of Higham [@higham2002] and [Demmel (1984)](https://doi.org/10.1137/0905062) writes $\mathrm{fl}(x) = x(1+\delta) + \eta$ with $|\delta| \le u$ and $|\eta| \le \eta_0$, at most one of the two nonzero, where $\eta_0 = 2^{e_{\min}-1}$ is half the subnormal spacing. Think of $\delta$ as the relative error of the normal range and $\eta$ as the absolute error the subnormals allow. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_standardModel]] proves it for every binary format with no hypothesis on $x$, and directed versions hold with both constants doubled. For binary32 it reads like this, with `δ * η = 0` saying at most one term is nonzero:

```lean
example (x : ℝ) :
    ∃ δ η : ℝ, Model.roundAt FloatFormat.binary32 x = x * (1 + δ) + η ∧
      |δ| ≤ Model.unitRoundoffAt FloatFormat.binary32 ∧
      |η| ≤ Model.underflowErrorAt FloatFormat.binary32 ∧ δ * η = 0 :=
  Model.roundAt_standardModel FloatFormat.binary32 x
```

Addition and subtraction are nicer. They need no $\eta$, because an exact sum below the normal range is a multiple of the subnormal spacing. For an IEEE descriptor, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_mul_one_add]] gives $\mathrm{fl}(a+b) = (a+b)(1+\delta)$ assuming only a finite result. To bound an executable operation, we rewrite it with its refinement equality, the theorem equating it with a rounding of the exact result, and the grid bound applies once that theorem's hypotheses hold. `abs_toReal_add_sub_le` does this for addition, the `*_standardModel` lemmas cover product, quotient, square root and fused multiply-add, and [Chapter 05](#/chapter/ieee-binary-formats/what-the-theorems-give-you) works through the hypotheses.

## When is subtraction exact?

Now for some good news: sometimes there's no error to bound at all. Sterbenz's lemma [@sterbenz1974] says that if $y \le x \le 2y$ and both are representable, then so is $x - y$, and the subtraction doesn't round. What we like about our [Sterbenz proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Sterbenz.lean) is that it never mentions rounding: both operands, and so their difference, are multiples of $\beta^{\mathrm{cexp}(y)}$, fine enough for the difference's grid because $0 \le x - y \le y$. [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]] is the order-symmetric form, which doesn't care which operand is larger, and its hypothesis is the shaded wedge in [Figure 4.3](#/chapter/the-mathematics-of-rounding/figure-ch07-sterbenz).

![Sterbenz's hypothesis y/2 ≤ x ≤ 2y as a wedge in the plane, with every pair of grid points with three binary digits between 1/2 and 4 marked by whether x - y is on the grid: inside the wedge all 97 pairs are, outside it 38 are and 34 are not](assets/ch07-sterbenz.png "Subtraction is exact throughout the factor-of-two region, and some pairs outside it also subtract exactly.")

On FLT grids a subnormal difference is representable for free, since every FLT value is a multiple of $\beta^{e_{\min}}$, and our [FLT proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/SterbenzFLT.lean) carries the FLX theorem over to a normal one. For executable values, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz_of_same_sign]] says that two finite values of the same sign whose magnitudes are within a factor of two subtract exactly, with no finiteness assumption on the result. Stating it with magnitudes covers negative operands and both signs of zero. Let's look at the theorem, and then at 1.5 minus the next binary32 number above one:

```lean
example {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hsign : 0 ≤ Model.toReal x * Model.toReal y)
    (hxy : |Model.toReal x| ≤ 2 * |Model.toReal y|)
    (hyx : |Model.toReal y| ≤ 2 * |Model.toReal x|) :
    Model.toReal (Model.sub x y) = Model.toReal x - Model.toReal y :=
  Model.toReal_sub_eq_of_sterbenz_of_same_sign hfmt hx hy hsign hxy hyx

def onePlusUlp : Binary32 := ExecFloat.Binary.nextUp 1

#eval (1.5 : Binary32) - onePlusUlp
-- 0.49999988

#eval (ExecFloat.Binary.sub (1.5 : Binary32) onePlusUlp (status := true)).status
-- {}
```

Here $x = 1.5$ and $y = 1 + 2^{-23}$, the difference $\tfrac12 - 2^{-23}$ comes back exactly, and the empty status says nothing was inexact. Counted in units of $2^{-23}$, the operands have integer significands $12582912$ and $8388609$, and their difference $4194303$, the significand of the printed `0.49999988`, has fewer significant bits than either. Cancellation, the subtraction of close numbers, made the answer smaller, but it didn't throw away a single nonzero bit.

### Is the error of an addition on the grid?

The error of a nearest-rounded addition is representable too. For representable $x$ and $y$, [[FloatLib.Floats.Formats.Flocq.add_round_exact_error]] writes $x + y = \mathrm{round}(x+y) + e$ with $e$ in the format. That's the mathematical content of the TwoSum and FastTwoSum error-free transformations, short floating-point programs that recover the error of a sum ([Møller's 1965 paper on addition](https://doi.org/10.1007/BF01975722), Knuth [@knuth1997], Dekker [@dekker1971]). It needs nearest rounding and a monotone exponent function. With three binary digits and directed rounding, $x = 1$ and $y = -2^{-10}$ show why: rounding the sum down gives $7/8$, and the error $2^{-3} - 2^{-10} = 127 \cdot 2^{-10}$ needs seven digits, more than the format has. What we prove is that the error value exists, not that TwoSum's sequence of floating-point operations computes it. On packed values, `genericFormat_toReal_add_sub` needs a finite output, so that its real value denotes the rounded sum:

```lean
example {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf fmt)
      (Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)) :=
  Model.genericFormat_toReal_add_sub x y hfmt hout
```

<details>
<summary>Residual theorems for multiplication, division, and square root</summary>

A residual measures what rounding left out. Companion [product-residual proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/Multiplication.lean) and [division and square-root residual proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/DivisionSqrt.lean) show that the residual of a rounded FLX product (`mul_round_error_FLX`) and the division residual $x - qy$ (`div_round_residual_FLX`) are representable for any valid mode, and the square-root residual $x - q^2$ (`sqrt_round_residual_FLX`) for nearest-even rounding and precision above one.

</details>

## Why rounding twice can go wrong

Say you compute in binary64, the double-precision format, and store the result as binary32. Is that the same as rounding straight to binary32? Not always. Rounding twice to the same format changes nothing, since a second rounding leaves a grid point alone, but rounding to a fine format and then a coarse one may differ from rounding straight to the coarse one. Downward is the easy case. If every coarse point is a fine one, the fine result lies between the coarse result and $x$, so rounding it down again lands on the same point.

Our [double-rounding theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Double.lean) state this for any two formats, given as predicates, where one contains the other, and [[FloatLib.Floats.Formats.Flocq.round_floor_double_FLX]] and `round_ceil_double_FLX` instantiate them for FLX, below with the 53 and 24 binary digits of binary64 and binary32. The `(by norm_num)` terms prove that both precisions are positive and $24 \le 53$.

```lean
example {β : FloatLib.Numerics.Radix} (x : ℝ) :
    @round β (flxExp 24) (flxValidExp 24 (by norm_num)) floorRound
        (@round β (flxExp 53) (flxValidExp 53 (by norm_num)) floorRound x) =
      @round β (flxExp 24) (flxValidExp 24 (by norm_num)) floorRound x :=
  round_floor_double_FLX (by norm_num) (by norm_num) (by norm_num) x
```

Nearest rounding is less forgiving. Round $2.51$ to one decimal place and you get $2.5$. Round that to a whole number, ties to even, and you get $2$, while $2.51$ rounded straight to a whole number is $3$. The same thing happens in binary. Take

$$
x = 1 + 2^{-24} + 2^{-53}.
$$

Rounded straight to binary32, $x$ sits just above the midpoint between $1$ and $1 + 2^{-23}$, so it goes up. Rounded to binary64 first, its $2^{-53}$ term is exactly half the binary64 spacing at one, and the tie to even drops it. That leaves the binary32 midpoint $1 + 2^{-24}$, and this second tie goes to $1$. Since $x$ isn't a binary64 value, the code builds it as the exact fused multiply-add $2^{-29}\cdot 2^{-24} + (1 + 2^{-24})$ (`fma` computes $ab + c$ with one rounding).

```lean
def a : Binary64 := 1 / 536870912
def b : Binary64 := 1 / 16777216
def c : Binary64 := 1 + b

#eval ExecFloat.fma a b c
-- 1.0000000596046448

#eval ExecFloat.cast (target := Binary32) (ExecFloat.fma a b c)
-- .success 1 { inexact := true }

#eval ExecFloat.Mixed.fma (target := Binary32) a b c
-- .success 1.0000001 { inexact := true }
```

The binary64 fused multiply-add gives $1 + 2^{-24}$ and the cast gives $1$, while the mixed-format one rounds once into binary32 and gets the correctly rounded $1 + 2^{-23}$. That's the x87 spill problem from [chapter 02](#/chapter/from-reals-to-machine-numbers), where a result rounded in a wide register is rounded again when stored, and it's why computing in a wider format doesn't by itself make the narrower result correctly rounded.

### How to round twice safely

There's a nice trick for this, called round to odd. It sends an inexact result to the neighbour with an odd last digit, and so keeps the information that nearest rounding lost. [Boldo and Melquiond (2008)](https://doi.org/10.1109/TC.2007.70819) develop the technique for floating-point double rounding and FMA emulation. An inexact round-to-odd result lands on an odd index, and with at least two extra binary digits no coarse midpoint does, so an inexact result never poses as a tie. We prove that, with at least two extra binary digits, round to odd followed by nearest even equals one nearest-even rounding on the integer grid, and [[FloatLib.Floats.Formats.Flocq.roundAtScale_nearestEven_after_odd_binary_extra]] extends this to any fixed grid of positive step.

Both grids must be fixed, with one spacing everywhere, so this covers fixed point and affine quantization (integers standing for evenly spaced reals), and we haven't proved a floating-point version whose exponent depends on the input. Round to odd lands on the grid (`generic_format_round_odd`) and meets `round_odd_point`, which says an inexact result is a directed neighbour with an odd mantissa at the input's selected exponent. The Flocq-style `RoundOddCanonicalPoint` tests the canonical mantissa instead, which can differ under abrupt underflow, and we prove it for fixed grids (`round_odd_canonical_point_FIX`). In the example below, the odd-then-even theorem's first argument counts extra digits beyond the mandatory two, so zero means a fine step of $\mathrm{step}/2^{0+2}$:

```lean
example (step x : ℝ) (hstep : 0 < step) :
    roundAtScale nearestEven step hstep
        (roundAtScale oddRound (step / 2 ^ (0 + 2))
          (div_pos hstep (by positivity)) x) =
      roundAtScale nearestEven step hstep x :=
  roundAtScale_nearestEven_after_odd_binary_extra 0 step x hstep
```

## How FloatLib rounds only once

So how do the library's basic operations avoid rounding twice? Each basic reference operation on a binary format uses exact arithmetic to decide a single rounding. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] equates the decoded executable sum with $\mathrm{roundAt}$ of the exact sum, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] does the same for $xy + z$, and the other basic operations have one too, each an exact equality under its format, domain and finiteness hypotheses. That's how `ExecFloat.Mixed.fma` beat the cast: mixed-format operations decode the operands into a common exact domain, evaluate, and quantize (round into the target) once (the [mixed-format conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Conversion/Proof.lean) `Mixed.preparedSpec_fma`). `roundOnce` quantizes an exact expression once (`preparedSpec_roundOnce`) and doesn't undo rounding done while building it.

What's one plus negative one? Zero, but IEEE formats have two zeros, so which one? With a signed-zero destination, a cancelled zero gets its sign during exact addition and subtraction, so inside `roundOnce` the operations `ExactExpression.add` and `ExactExpression.sub` take the final rounding's `mode`. Ordinary `SignedRat` arithmetic (exact rationals with an IEEE sign bit) always uses the nearest-even rule, so there the answer is positive zero, and quantizing it downward keeps it positive. `ExactExpression.add` with `mode := .down` gives negative zero. The quantizer's contract covers only the last rounding, and keeping an exact operation faithful to its family's IEEE rules is the job of the family's `addExact` and `subExact`.

### How to add a list with one rounding

Sums and dot products get the same treatment. If you add up `[16777216, 1, -16777216]` from the left in binary32, you get zero, though the exact sum is one. A binary32 significand has 24 bits, so $2^{24} + 1$ rounds straight back to $2^{24}$, the one falls off the end, and subtracting $2^{24}$ leaves nothing. `sumList` and `sum` work differently. They decode every term to an exact dyadic, add them up in software, and round once at the end. Let's run the fold, then `sumList`, then a dot product (the sum of the products of matching entries):

```lean standalone
import FloatLib

open FloatLib.Floats

def values : List Binary32 := [16777216, 1, -16777216]

#eval values.foldl (· + ·) 0
-- 0
#eval ExecFloat.Binary.sumList values
-- 1
#eval ExecFloat.Binary.sumList values (status := true)
-- { value := 1, status := {}, ternary := Ordering.eq }
#eval ExecFloat.Binary.dot #[(1.5 : Binary32), 2, 4] #[2, 3, 4]
-- Except.ok 25
#eval ExecFloat.Binary.dotList [(1.5 : Binary32), 2, 4] [2, 3]
-- Except.error (FloatLib.Numerics.ReductionError.lengthMismatch 3 2)
```

`sumList` gets the exact one, and its empty status and `Ordering.eq` say it was representable. [[FloatLib.Floats.ExecFloat.Binary.dot]] keeps every product exact too, so $1.5 \cdot 2 + 2 \cdot 3 + 4 \cdot 4 = 25$ gets one rounding at the end. Lists of different lengths give an `Except.error` carrying both lengths before any arithmetic runs, as `dot_status_lengthMismatch` proves. `List.zip` would quietly drop the extra entries, and we'd rather tell you. `dot` has no initial-addend argument, since `fma` covers one product plus an addend and the [round-once expressions](#/chapter/ieee-binary-formats/how-to-round-a-whole-expression-once) cover anything larger.

Our reductions, the operations that combine many values into one, accumulate every finite input exactly and round once at the end. That's a guarantee we chose, since IEEE 754-2019 §9.4 permits implementation-defined reduction approximations and evaluation orders [@ieee754_2019]. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.sum_status_value_toReal_eq_roundAt_of_finite]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.dot_status_value_toReal_eq_roundAt_of_finite]] identify a sum, or a dot product of equal-length arrays, with one nearest-even rounding of the exact result when the inputs and the result are finite and the destination is a conventional IEEE format. That covers empty input and cancellation to zero, whose stored zero sign has its own theorems, but since the result must be finite, neither theorem covers overflow. A cast rounds the value it receives ([[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]]), so casting a rounded result rounds twice.

Two more theorems carry this over to proofs. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.sum_status_eq_round_of_finite_nonzero]] says a nonzero finite sum is one rounding of the exact sum, with that rounding's status, and [[FloatLib.Floats.ExecFloat.Binary.dot_status_eq_model]] says the configured dot is the model dot, errors and status included.

**Note:** The reduction bound that `#float_info [errors] Binary32` reports doesn't describe this exact `dot`. It's for a different algorithm, in which every cast, product and accumulator update rounds, under the specified IEEE formats and finite intermediate values.

## What if every addition rounds?

Not every sum gets to round once at the end, though. Say you add 2048, 1 and minus 2048 in binary16, like the binary32 fold above. When a reduction rounds every intermediate addition like this, the error depends on the evaluation order. A [[FloatLib.Numerics.ReductionTree]] holds the input occurrences at its leaves and the combining operations at its nodes, for a nonempty reduction (an empty one needs an identity chosen outside the tree). Think of the tree as the sum's brackets, drawn as a picture. If you build two trees that hold those three values with the cancellation in different places:

```lean
open FloatLib.Numerics (ReductionTree)

def leftSum : ReductionTree Binary16 :=
  .node (.node (.leaf 2048) (.leaf 1)) (.leaf (-2048))

def reorderedSum : ReductionTree Binary16 :=
  .node (.node (.leaf 2048) (.leaf (-2048))) (.leaf 1)

#eval leftSum.eval (· + ·) id
-- 0

#eval reorderedSum.eval (· + ·) id
-- 1
```

you get two answers from the same inputs. The first tree loses the `1`. At 2048 the binary16 spacing is $2$, so 2049 is a tie between 2048 and 2050, and ties to even picks 2048. The second cancels the big values first and keeps the `1`.

What can we prove about a tree like that? Say the addition at a node with computed operands $x$ and $y$ errs by at most an allowance $e(x,y)$, an error budget for that one step. Then [[FloatLib.Numerics.ReductionTree.abs_eval_sub_exact_le_errorBudget]] bounds the whole reduction by the sum of these allowances, needing the hypothesis only at pairs that occur in the tree. A uniform allowance $\delta$ gives $(n-1)\delta$ for $n$ inputs, and a mixed allowance $u(|x|+|y|)+\delta$ has a recursive bound. For IEEE descriptor models, [[FloatLib.Floats.Formats.BinaryInterchange.Model.ReductionTree.abs_toReal_eval_sub_sum_le]] takes each allowance from the half-ulp addition theorem, assuming finite inputs and intermediate results but no normal range, and a companion theorem bounds the gap between two finite schedules (evaluation orders) over the same inputs. [[FloatLib.Floats.Formats.BinaryInterchange.Model.ReductionTree.abs_toReal_eval_sub_sum_le_mixedBudget]] gives the mixed bound with $u = 2^{-p}$ and $\delta = 0$, since finite additions carry no underflow term.

## How running code decides which way to round

In the theory, rounding is a function of an exact real number, but an executable kernel, the code that does arithmetic on machine words, decides it from less: an integer quotient and a little information about the discarded part. In hardware the guard, round and sticky bits kept past the last digit carry that information, and here Flocq's bracket calculus does. In the [bracket model](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Calculation/Bracket.lean), a `Location` says whether $x$ is a grid point or lies below, at or above the midpoint between adjacent grid points, and an `Inbetween` proof says that record is correct before the refinement theorem can use it. Our bracket proofs show that each mode's decision to increment the mantissa agrees with floor, ceiling and nearest-even rounding. Dropping low bits changes the cell $x$ lies in, so `refineLocation_correct` updates the location, and our [truncation theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Calculation/Round.lean) `roundTruncatedNearestEven_correct` proves that the result is `round nearestEven x`. The kernels in [chapter 12](#/chapter/performance) use these refinements.

<a id="using-the-rounding-theorems"></a>

## How the grid connects to packed formats

We've been using grid theorems on binary32 values all chapter, so let's see how the grid and the library's formats connect. An [`EncodedFormat` instance](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/GenericFormat.lean) whose codes are canonical mantissa and exponent pairs turns the generic theory into a library format, and [[FloatLib.Floats.Formats.Flocq.representable_iff_genericFormat]] says representability in the common numerical system interface is the same as `genericFormat`. And for every finite word of every supported descriptor, IEEE or not, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_genericFormat_of_isFinite]] puts its value on the grid, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_toReal_eq]] says rounding it back to its own format is the identity.

Arithmetic needs more, because our grid is unbounded above (`fltExp` puts no ceiling on the exponent) while a packed format can overflow. So $\mathrm{decode}(\mathrm{add}(x,y)) = \mathrm{roundAt}(\mathrm{decode}(x) + \mathrm{decode}(y))$ needs a finite output, since an overflowed sum is an infinity with no real value. Criteria such as `isFinite_add_of_abs_add_le_posMaxFinite` prove that from bounds on the inputs. A finite square-root input that is nonnegative or a signed zero gives a finite result, so that theorem needs only the domain condition.

## How this relates to Flocq

If you know Flocq, how close is this chapter's grid theory to it? Our definitions follow it: `bpow`, `magnitude`, `cexp`, `genericFormat`, `ValidExp`, `ulp`, the point predicates, `Znearest` as `nearestChoice` and the bracket calculus have direct counterparts. It isn't a port of all of Flocq, though. We don't reproduce its proofs about individual arithmetic algorithms, which Boldo and Melquiond's book [@boldoMelquiondBook] discusses, its executable computation beyond bracket refinement and truncation, or its Coq-specific application modules.
