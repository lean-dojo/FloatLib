---
number: "07"
slug: the-mathematics-of-rounding
title: The mathematics of rounding
summary: The spacing of a numerical grid explains rounding error, exact subtraction, and the danger of rounding twice.
phases: [rounding-theory]
---

The binary32 addition `1 + 1e-8` from [Chapter 06](#/chapter/the-numerical-models) returns `1` because the increment is smaller than half the gap to the next representable value. The spacing between grid points bounds the possible error, and the rounding rule determines which neighbour is chosen. Above one the gap is $2^{-23}$; above two it is twice as large. We can describe that changing spacing on the real number line without choosing a packed bit layout.

Boldo and Melquiond's Flocq library for Coq develops this grid-based approach [@boldoMelquiond2011]. FloatLib follows it with an arbitrary radix and an exponent function, with proofs written in Lean against Mathlib [@leanMathlib2020]. To use a grid theorem for a packed format, we first prove that the format's operations agree with rounding on that grid, then check the theorem's hypotheses. The same proof can therefore apply to binary32, binary128, and custom IEEE-style descriptors without a case for each stored width.

## Rounding as a function on the reals

A rounding function maps $\mathbb{R}$ to $\mathbb{R}$, with the representable numbers as its image. It has to leave every representable number unchanged and be monotone, so $x \le y$ implies $\mathrm{round}(x) \le \mathrm{round}(y)$. Which neighbour it chooses, and how it breaks ties, is up to the rounding mode.

Scale by the local grid spacing and choosing a representable value turns into choosing an integer. An integer rounding rule is a function $\mathrm{rnd} : \mathbb{R} \to \mathbb{Z}$. `floorRound` is $\lfloor x \rfloor$, `ceilRound` is $\lceil x \rceil$, and `truncRound` picks whichever is closer to zero. [[FloatLib.Floats.Formats.Flocq.nearestEven]] picks the nearer integer and, at a tie, the even one. [[FloatLib.Floats.Formats.Flocq.oddRound]] leaves integers unchanged and otherwise picks the odd neighbour, and `awayRound` rounds away from zero.

A rule is valid, in the sense of the class `ValidRnd`, if it's monotone and leaves every integer unchanged. `ValidRndToNearest` adds the inequality $|\mathrm{rnd}(x) - x| \le \tfrac12$, whatever the tie policy. All six rules are instances of `ValidRnd`, and `nearestEven` is an instance of `ValidRndToNearest`, as is `nearestChoice` for every tie rule.

Rounding to a format is then three steps: scale, round the integer, scale back. Given a real $x$, we compute a canonical exponent $e$ from its magnitude, apply the integer rule to $x \cdot \beta^{-e}$, and multiply back:

$$
\mathrm{round}_{\mathrm{rnd}}(x) \;=\; \mathrm{rnd}\!\left(x\,\beta^{-e}\right)\cdot \beta^{e}, \qquad e = \mathrm{cexp}(x).
$$

With a grid step of $1/4$, we can do all three steps by hand. Rounding $11/8$ means scaling it to $11/2 = 5.5$, nearest-even chooses the integer 6, and scaling back gives $6/4 = 3/2$. The scaling and integer choice have separate jobs. The step determines which two representable values surround the input, and the integer rule resolves the tie.

This construction is [[FloatLib.Floats.Formats.Flocq.round]]. Much of the argument happens on the integers, where monotonicity, the half unit bound, and the choice of neighbour are elementary facts about $\mathrm{rnd}$, and scaling then carries them to the grid. When the exponent depends on the input magnitude, comparing two rounded values also requires handling changes of scale. [Figure 7.1](#/chapter/the-mathematics-of-rounding/figure-ch07-rounding-staircase) shows rounding on a grid with three binary digits. Each step is the set of reals sent to one grid point, and at the powers of two the canonical exponent changes and the steps double in width.

![Round to nearest even on a grid with three binary digits, from 0.5 to 2.5: each step is the set of reals sent to one grid point, the steps double in width at 1 and at 2, and a filled end marks the neighbour a tie goes to](assets/ch07-rounding-staircase.png "Nearest-even rounding with three binary digits; filled endpoints show the tie choice.")

Back in binary32, the next representable value gives us the spacing above one directly:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.Flocq

#eval (1 : Binary32) + 1e-8
-- 1

#eval ExecFloat.Binary.nextUp (1 : Binary32)
-- 1.0000001
```

Printed as `1.0000001`, the neighbour of one is $1 + 2^{-23}$, so the spacing there is $2^{-23}$ and $10^{-8}$ is about $0.084$ of it. That puts the increment below the midpoint of the gap, and nearest rounding returns one, just as we saw in the last chapter.

## A grid described by an exponent function

A grid has two parameters, a radix $\beta$ and a function $\mathrm{fexp} : \mathbb{Z} \to \mathbb{Z}$. The function says, for a number of a given magnitude, which exponent its representation should use. Describing the spacing with a function lets the same theory cover fixed point, floating point with unbounded exponent, and the normal and subnormal regions of IEEE formats. There are [three exponent families](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean). `fixExp` is the constant $e \mapsto e_{\min}$ and describes a fixed grid $\beta^{e_{\min}}\mathbb{Z}$. [[FloatLib.Floats.Formats.Flocq.flxExp]], $e \mapsto e - p$, gives $p$ digits at every magnitude and never underflows. And [[FloatLib.Floats.Formats.Flocq.fltExp]], $e \mapsto \max(e - p, e_{\min})$, has $p$ digits in the normal range and a flat grid of spacing $\beta^{e_{\min}}$ below it. That flat region is gradual underflow. Flush to zero policies get their own [abrupt underflow selector](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Special/FTZ.lean), `ftzExp`, which we keep apart from the gradual underflow model.

A grid point is written as a pair of integers, a mantissa $m$ and an exponent $e$, in the structure [[FloatLib.Floats.Formats.Flocq.FloatRep]]. The pair denotes $m\,\beta^{e}$ through [[FloatLib.Floats.Formats.Flocq.toReal]] and [[FloatLib.Floats.Formats.Flocq.bpow]]. To place a real number we need its magnitude, `magnitude`, which is $\lfloor \log_\beta |x| \rfloor + 1$ for nonzero $x$ and $0$ at zero, so that $\beta^{\mathrm{mag}(x)-1} \le |x| < \beta^{\mathrm{mag}(x)}$ (`magnitude_spec`). Its canonical exponent, [[FloatLib.Floats.Formats.Flocq.cexp]], is $\mathrm{fexp}$ applied to the magnitude. The scaled mantissa `scaledMantissa` is $x\,\beta^{-\mathrm{cexp}(x)}$. Representability, [[FloatLib.Floats.Formats.Flocq.genericFormat]], says that rescaling, taking the floor, and rescaling back returns $x$ unchanged. `generic_format_iff_scaled_mantissa_int` says the same thing another way: the scaled mantissa is an integer. Nothing here mentions storage, which is why the theory is format generic.

Where the magnitude changes, $\mathrm{fexp}$ has to satisfy consistency conditions. The class [[FloatLib.Floats.Formats.Flocq.ValidExp]] carries two such clauses from Flocq. The first says that if the format has genuine precision at magnitude $k$, that is $\mathrm{fexp}(k) < k$, then one magnitude up it uses an exponent of at most $k$. So the spacing there is at most $\beta^{k}$, the radix power that separates the two binades (the intervals between consecutive powers of the radix). That keeps the next grid point representable across the boundary.

The second clause governs magnitudes where $\mathrm{fexp}$ is at least as large as the magnitude itself. It requires constant spacing at smaller magnitudes. In an IEEE format that's what keeps the spacing constant towards zero. `validExp_FLX_iff` and `validExp_FLT_iff` show that FLX and FLT are valid exactly when the precision is positive. That's why callers check a precision with `FormatPrecision.ofInt?` before using it.

We want two things from `round`. The result must land on the grid, and rounding a grid point must leave it unchanged. [[FloatLib.Floats.Formats.Flocq.generic_format_round]] proves the first, following Flocq by separating inputs in the flat region from those outside it, and the second is `round_preserves_generic`. Together they make rounding idempotent and keep a chain of operations inside the format.

Our [monotonicity proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Order.lean) is `round_mono`. Inputs in different magnitude bins are scaled by different powers, so the proof bounds the rounded smaller input by the radix power that starts the larger input's bin. The [neighbour-selection theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Properties.lean), `round_eq_floor_or_ceil`, states that every valid mode returns the downward or the upward neighbour. On the scaled integers the rule fixes both endpoints, so monotonicity bounds the answer between the floor and ceiling, and an integer in that interval must be one of them. In Lean, we can apply these three facts to any valid exponent function and integer rounding rule:

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

Our relational specifications follow Flocq's `Rnd_DN_pt` and `Rnd_N_pt`. `RoundDownPoint` is the greatest representable number not above $x$, and `RoundUpPoint` the least not below it. `RoundNearestPoint` is a representable number at least as close to $x$ as every other. `round_floor_point`, `round_ceil_point`, and [[FloatLib.Floats.Formats.Flocq.round_toNearest_point]] show that the computed roundings meet these specifications. The specifications mention only representable values, so the double rounding argument below can use them without referring to the rounding algorithm.

## The unit in the last place

A ulp is the grid spacing at a point. Away from zero, [[FloatLib.Floats.Formats.Flocq.ulp]] is $\beta^{\mathrm{cexp}(x)}$. At zero the definition follows Flocq. If the format has a flat region below some exponent, selected by `negligibleExp`, the ulp of zero is the spacing of that region, and otherwise it is zero. For FLT, `ulp_zero_FLT` says this is $\beta^{e_{\min}}$, the smallest subnormal. For FLX, `ulp_zero_FLX` says it is zero, because with an unbounded exponent there's no smallest positive number.

Our [ulp proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Ulp.lean) and [neighbour proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Neighbors.lean) relate this spacing to adjacent representable values. For a nonrepresentable $x$ the two directed roundings differ by exactly one ulp, `round_ceil_eq_floor_add_ulp`. Neighbours `succ` and `pred` step to the adjacent grid point, with a special case at a radix power, where the spacing below differs from the spacing above. `generic_format_succ` and `generic_format_pred` prove the step lands back on the grid, and at the boundary where the spacing changes, representability comes from the first clause of `ValidExp`.

For a packed binary format, [[FloatLib.Floats.Formats.BinaryInterchange.Model.fexpOf]] computes the exponent function from the descriptor of [chapter 06](#/chapter/the-numerical-models). It is `fltExp` at the minimum subnormal exponent, with precision one more than the fraction width. For binary32 that is $e_{\min} = -149$ and $p = 24$, and you can check both in Lean:

```lean
example : Model.fexpOf FloatFormat.binary32 = fltExp (-149) 24 := by
  rfl

#eval ExecFloat.Binary.nextUp (0 : Binary32)
-- 1e-45
```

[[FloatLib.Floats.Formats.BinaryInterchange.Model.ulpAt]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.epsilonAt]] are the format level ulp and half ulp on this exponent function. The successor of zero above is the ulp of zero the theory predicts.

Substituting a few values into `fexpOf` gives the spacing changes from the opening example. At one the magnitude is $1$, so its canonical exponent is $\max(1-24,-149)=-23$. For two the magnitude is $2$, giving $-22$ instead, so one step above two is twice as large as one step above one. At the least normal value, $2^{-126}$, the magnitude is $-125$ and the canonical exponent is $\max(-125-24,-149)=-149$. Below that point the maximum keeps choosing $-149$ for positive values. So the subnormal grid continues with that same spacing all the way to zero, using fewer and fewer significant bits and never a smaller exponent.

## Absolute and relative error bounds

Nearest rounding is within half a ulp of the exact value. In the theory it is [[FloatLib.Floats.Formats.Flocq.error_bound_ulp]]:

$$
|\mathrm{round}_{\mathrm{rnd}}(x) - x| \;\le\; \frac{\mathrm{ulp}(x)}{2} \qquad \text{for every } \mathrm{rnd} \text{ with } |\mathrm{rnd}(t) - t| \le \tfrac12.
$$

At $x = 0$ rounding is exact. For a nonzero input, multiply the half-unit bound on the scaled mantissa by the positive factor $\beta^{\mathrm{cexp}(x)}$ and an error measured in grid steps becomes an error in the original units. The theorem asks only for `ValidRndToNearest`, so it covers every tie policy at once. For directed modes the corresponding fact is one full ulp, `round_abs_error_le_ulp`, and when the rounding was inexact, `round_abs_error_lt_ulp_of_inexact` makes it strict.

Our [relative-error proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/Bounds.lean) give two forms. `relative_error_round_ulp` divides the absolute bound by $|x|$, and `round_relative_error_ulp` restates it as the model numerical analysts use, $\mathrm{fl}(x) = x(1 + \delta)$ with $|\delta|$ bounded.

In a fixed precision format the bound on $\delta$ becomes a constant. For FLX with $p$ digits, [[FloatLib.Floats.Formats.Flocq.round_relative_error_FLX]] proves that there is $\delta$ with $|\delta| \le \beta^{1-p}/2$ and $\mathrm{round}(x) = x(1+\delta)$. That constant is the unit roundoff $u$. For binary32, where $p = 24$, it is $2^{-24}$. Its FLT version, `relative_error_round_FLT_normal`, requires the input to be in the normal range. Near zero a uniform relative bound of this size is false. Gradual underflow keeps the absolute spacing fixed while the values shrink, so there the useful statement is the absolute one. For FLX with at least two digits the sharper estimate is $u/(1+u)$, from [Jeannerod and Rump (2018), Theorem 2.1](https://doi.org/10.1090/mcom/3234).

For packed binary formats, [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] applies the FLT theorem at the descriptor's exponent function. It uses $u = 2^{-p}$, which gives the $2^{-24}$ relative bound for binary32 that `#float_info [errors]` shows in [chapter 01](#/chapter/using-the-library). We haven't proved the refinement to $u/(1+u)$ :)

[Figure 7.2](#/chapter/the-mathematics-of-rounding/figure-ch07-ulp) compares absolute and relative bounds for binary16, whose exponent function is `fltExp (-24) 11` by the same computation as binary32's. Its absolute half ulp bound is flat across the subnormal range and doubles at every power of two above it. Divide that by $x$ and you get a relative bound that stays between $u/2$ and $u$ in the normal range, while below it the relative bound is no longer uniform. You get the constant relative bound by cancelling the magnitude from the absolute bound. In a normal binade with magnitude index $e$, we have $|x| \ge \beta^{e-1}$ and half an ulp is $\beta^{e-p}/2$. Hence

$$
\frac{|\mathrm{round}(x)-x|}{|x|}
\le \frac{\beta^{e-p}}{2\,\beta^{e-1}}
= \frac{\beta^{1-p}}{2}.
$$

Numerator and denominator both scale with the binade, so their ratio loses its dependence on $e$. In the subnormal range that cancellation isn't available. Say we take the real input $2^{-150}$, halfway between zero and the least binary32 subnormal. Nearest even sends it to zero, so its absolute error is exactly half the subnormal spacing, yet its relative error is one. The half-ulp theorem holds here, and the example shows why the small constant relative bound requires a normal-range hypothesis. You can see it in the panels of Figure 7.2, where the constant subnormal bound in *Absolute spacing* grows near zero once it's divided by the input in *Relative bound*.

![Two binary16 panels for fltExp (-24) 11: Absolute spacing plots ulp and half ulp; Relative bound plots half ulp divided by x, between u/2 and u in the normal range and increasing as positive subnormal inputs approach zero](assets/ch07-ulp.png "Binary16 absolute and relative error bounds: the uniform relative bound requires a normal input.")

The examples below apply the generic half ulp bound, specialize the relative bound to FLX, and read off the binary32 instances. The second writes the `@round` form out in full, because the validity instance depends on `hprec`.

```lean
example {β : FloatLib.Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) :
    |round (β := β) (fexp := fexp) rnd x - x| ≤ ulp β fexp x / 2 :=
  error_bound_ulp rnd x

example {β : FloatLib.Numerics.Radix} (prec : ℤ) (hprec : 0 < prec)
    (rnd : ℝ → ℤ) [ValidRndToNearest rnd] (x : ℝ) (hx : x ≠ 0) :
    ∃ δ : ℝ, |δ| ≤ bpow β (1 - prec) / 2 ∧
      @round β (flxExp prec) (flxValidExp prec hprec) rnd x = x * (1 + δ) :=
  round_relative_error_FLX prec hprec rnd x hx

example (x : ℝ) :
    |Model.roundAt FloatFormat.binary32 x - x| ≤
      Model.epsilonAt FloatFormat.binary32 x :=
  Model.abs_roundAt_sub_le FloatFormat.binary32 x

example (x : ℝ) (hx : x ≠ 0)
    (hnormal : Model.minNormalAt FloatFormat.binary32 ≤ |x|) :
    ErrorBounds.relativeError x (Model.roundAt FloatFormat.binary32 x) hx ≤
      bpow FloatLib.Numerics.binaryRadix (1 - 24) / 2 :=
  Model.relativeError_roundAt_le_of_normal FloatFormat.binary32 x hx hnormal
```

Allow one more error term and the normal-range hypothesis can go. This is the standard model with gradual underflow used by Higham [@higham2002] and [Demmel (1984)](https://doi.org/10.1137/0905062). Every real $x$ satisfies $\mathrm{fl}(x) = x(1+\delta) + \eta$ with $|\delta| \le u$ and $|\eta| \le \eta_0$, and at most one of the two terms is nonzero. The constant $\eta_0 = 2^{e_{\min}-1}$ is half the subnormal spacing. In the normal range $\eta = 0$ and the relative bound applies. Below it $\delta = 0$ and $\eta$ is the half-ulp error, which for binary32 is at most $2^{-150}$. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_standardModel]] proves this for every binary format with no hypothesis on $x$. `roundAt_down_standardModel` and `roundAt_up_standardModel` give the directed versions with both constants doubled.

```lean
example (x : ℝ) :
    ∃ δ η : ℝ, Model.roundAt FloatFormat.binary32 x = x * (1 + δ) + η ∧
      |δ| ≤ Model.unitRoundoffAt FloatFormat.binary32 ∧
      |η| ≤ Model.underflowErrorAt FloatFormat.binary32 ∧ δ * η = 0 :=
  Model.roundAt_standardModel FloatFormat.binary32 x
```

Addition and subtraction do better. Both operands are multiples of the subnormal spacing, so an exact sum below the normal range is itself a grid point and rounds to itself. So for an IEEE descriptor, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_mul_one_add]] states $\mathrm{fl}(a+b) = (a+b)(1+\delta)$ with no $\eta$ term, assuming finite operands and result. For an addition tree this means the per-node premise of the mixed reduction bound later in this chapter holds with no absolute term.

To bound a single operation, we first rewrite its executable result using the refinement equality. For addition, `abs_toReal_add_sub_le` then applies `abs_roundAt_sub_le` to the exact sum, and that argument also bounds a product, quotient, square root, or fused multiply-add. Once the refinement theorem's hypotheses hold, apply `error_bound_ulp` to the exact expression. For these operations the corresponding `*_standardModel` lemmas package the relative and absolute terms, and [Chapter 08](#/chapter/ieee-binary-formats/from-executable-arithmetic-to-real-rounding) works through the finite-value and domain hypotheses.

## Exact subtraction

Sterbenz's lemma [@sterbenz1974] gives a condition under which subtraction is exact. If $y \le x \le 2y$ with both representable, then $x - y$ is representable, so subtracting them incurs no rounding at all.

What we like about our [Sterbenz proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Sterbenz.lean), `generic_format_FLX_sub_of_le_two_mul`, is that it never mentions rounding. A zero difference is already representable. Otherwise the operands are positive, and the ratio bound puts the magnitude indices of $x$ and $y$ at most one apart. So both are integer multiples of $\beta^{\mathrm{cexp}(y)}$, the smaller of the two canonical exponents, and so is their difference. Since $0 \le x - y \le y$, the canonical exponent of the difference is at most $\mathrm{cexp}(y)$, and an integer multiple of $\beta^{\mathrm{cexp}(y)}$ is then automatically on the grid at the difference's own exponent. [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]] is the order symmetric form. In [Figure 7.3](#/chapter/the-mathematics-of-rounding/figure-ch07-sterbenz), the shaded wedge is the region that hypothesis describes. We checked a grid with three binary digits, and every pair of grid points inside the wedge has a difference on the grid, while outside it some do and some don't.

![Sterbenz's hypothesis y/2 ≤ x ≤ 2y as a wedge in the plane, with every pair of grid points with three binary digits between 1/2 and 4 marked by whether x - y is on the grid: inside the wedge all 97 pairs are, outside it 38 are and 34 are not](assets/ch07-sterbenz.png "Subtraction is exact throughout the factor-of-two region; some pairs outside it also subtract exactly.")

Packed binary values actually use FLT, and there the argument has two regimes. A difference small enough to be subnormal is automatically representable. Every FLT value is a multiple of $\beta^{e_{\min}}$, so the difference is too, by `generic_format_FIX_sub`. In the subnormal range that's all representability asks. Otherwise the difference is normal, the FLX theorem applies, and we transport the result back to FLT. That [FLT proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/SterbenzFLT.lean) is `generic_format_FLT_sterbenz`.

At the packed level, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz_of_same_sign]] states the executable consequence. Two finite values of the same sign whose magnitudes are within a factor of two subtract exactly. The exact difference is bounded by one of the operands, so result finiteness follows and doesn't have to be assumed. Stating it with magnitudes also covers two negative operands and both signs of zero. If one magnitude is zero, the ratio bounds force the other to be zero too. Below, the theorem proves exactness, and the evaluations after it show both the difference and its inexact flag:

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

#eval (ExecFloat.Binary.sub (1.5 : Binary32) onePlusUlp (status := true)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false }
```

Here $x = 1.5$ and $y = 1 + 2^{-23}$ satisfy $y \le x \le 2y$. The difference $\tfrac12 - 2^{-23}$ is returned exactly, and the status word confirms that nothing was inexact. You can align the significands by hand to see why. At scale $2^{-23}$, the operands have integer significands $12582912$ and $8388609$, and their difference is $4194303$, which is the significand of the `0.49999988` printed above, $4194303 \cdot 2^{-23}$. That integer has fewer significant bits than either operand, so it fits easily once the result is normalized at its smaller magnitude. Cancellation made the answer smaller, but it didn't make us discard a single nonzero bit. Sterbenz's ratio condition guarantees this representability for the whole class of nearby operands, and gradual underflow gives the same protection when their difference reaches the fixed subnormal grid.

A second exactness result is about the error of an addition. For any nearest rounding rule, `add_round_error_generic` proves that $\mathrm{round}(x + y) - (x + y)$ is representable whenever $x$ and $y$ are. [[FloatLib.Floats.Formats.Flocq.add_round_exact_error]] restates it as $x + y = \mathrm{round}(x+y) + e$ with $e$ in the format. That's the mathematical content of the TwoSum and FastTwoSum error-free transformations used in compensated summation. For those, see [Møller's 1965 paper on addition](https://doi.org/10.1007/BF01975722), Knuth [@knuth1997], and Dekker [@dekker1971]. The theorem needs nearest rounding and a monotone exponent function, and it fails for directed rounding. With three binary digits, $1 - 2^{-10}$ rounded down gives $7/8$, and the error $2^{-3} - 2^{-10}$ needs seven digits.

What the theorem proves is that such an error value exists in the format, and `genericFormat_toReal_add_sub` carries that result to finite binary addition. Proving that TwoSum's sequence of floating-point operations actually computes $e$ would take a further argument, and we haven't included that algorithmic exactness proof. On packed values, the addition theorem requires a finite output so that its real value denotes the rounded sum:

```lean
example {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf fmt)
      (Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)) :=
  Model.genericFormat_toReal_add_sub x y hfmt hx hy hout
```

<details>
<summary>Residual theorems for multiplication, division, and square root</summary>

Companion [product-residual proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/Multiplication.lean) and [division and square-root residual proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/DivisionSqrt.lean) cover the other operations. `mul_round_error_FLX` shows that the residual of a rounded FLX product is representable for any valid mode, and `div_round_residual_FLX` shows the same for the division residual $x - qy$. For square root, `sqrt_round_residual_FLX` shows that the residual $x - q^2$ is representable for nearest-even rounding and precision above one.

</details>

## Double rounding

Rounding twice to the same format changes nothing, since rounding is idempotent. Rounding to a fine format and then to a coarse one is another matter, and whether that agrees with rounding straight to the coarse format depends on the mode. Two successive downward roundings are the easy case, because grid inclusion is enough. If every coarse grid point is also a fine grid point, the largest fine point below $x$ is at least the largest coarse point below $x$. Rounding that fine point down to the coarse grid can't go below the coarse point, because that point is itself available. Nor can it go above it, since the fine result is still at most the original input, so any larger coarse point would contradict the definition of the original coarse rounding. For upward rounding, reverse the inequalities.

Our [double-rounding theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Double.lean) `roundDownPoint_double` and `roundUpPoint_double` state this for arbitrary predicates related by inclusion. [[FloatLib.Floats.Formats.Flocq.round_floor_double_FLX]] and `round_ceil_double_FLX` instantiate them for two FLX precisions, using `generic_format_FLX_mono` for the inclusion. The following instance uses 53 and 24 binary digits, the binary64 and binary32 precisions. The `(by norm_num)` arguments discharge the side conditions: each precision is positive, as `flxValidExp` needs, and $24 \le 53$.

```lean
example {β : FloatLib.Numerics.Radix} (x : ℝ) :
    @round β (flxExp 24) (flxValidExp 24 (by norm_num)) floorRound
        (@round β (flxExp 53) (flxValidExp 53 (by norm_num)) floorRound x) =
      @round β (flxExp 24) (flxValidExp 24 (by norm_num)) floorRound x :=
  round_floor_double_FLX (by norm_num) (by norm_num) (by norm_num) x
```

Nearest rounding is less forgiving. It can turn a value just above a coarse midpoint into that midpoint, and that changes how the final tie is resolved. For example, take

$$
x = 1 + 2^{-24} + 2^{-53}.
$$

Rounded straight to binary32, $x$ sits just above the midpoint between $1$ and $1 + 2^{-23}$, so it goes up to $1 + 2^{-23}$. Round it to binary64 first and it becomes exactly $1 + 2^{-24}$. The spacing at one is $2^{-52}$, the term $2^{-53}$ is exactly half of it, and the tie goes to the even neighbour, which drops it. Now that value is itself a binary32 midpoint, and the second tie goes to even again, but this time the even neighbour is $1$. The intermediate rounding erased the information that the exact value was above the coarse midpoint, so the two answers differ by a full ulp. Since $x$ isn't representable in binary64, we produce it as the exact result of a fused multiply-add, $2^{-29}\cdot 2^{-24} + (1 + 2^{-24})$, whose three operands are representable in binary64.

```lean
def a : Binary64 := 1 / 536870912
def b : Binary64 := 1 / 16777216
def c : Binary64 := 1 + b

#eval ExecFloat.fma a b c
-- 1.0000000596046448

#eval (ExecFloat.cast (target := Binary32) (ExecFloat.fma a b c)).value?
-- some 1

#eval (ExecFloat.fmaAs (target := Binary32) a b c).value?
-- some 1.0000001
```

Here `a` is $2^{-29}$, `b` is $2^{-24}$, and `c` is $1 + 2^{-24}$. The first line is the binary64 rounding of $x$, which is $1 + 2^{-24}$, and casting it to binary32 gives $1$. Computing the same fused multiply-add exactly and rounding once into binary32 gives $1 + 2^{-23}$, the correctly rounded answer. This is the x87 spill problem from [chapter 04](#/chapter/why-verifying-floating-point-is-hard), and it's also why computing in a wider format doesn't by itself make the narrower result correctly rounded.

On fixed binary grids, round to odd can keep the information that nearest rounding loses in this example. [Boldo and Melquiond (2008)](https://doi.org/10.1109/TC.2007.70819) develop the technique for floating-point double rounding and FMA emulation. Round to odd leaves an exact integer alone and otherwise chooses the odd integer neighbour. Give the fine grid at least two extra binary digits and an inexact fine-grid result can't be a coarse-grid midpoint, because those midpoints have even indices on the fine grid. `nearestEven_roundOdd_binary_extra` shows that with at least two extra binary digits, round to odd followed by nearest even equals a single nearest-even rounding on the integer grid. [[FloatLib.Floats.Formats.Flocq.roundAtScale_nearestEven_after_odd_binary_extra]] extends this to any fixed grid of positive step.

Both grids must be fixed, so the result covers fixed point and affine quantization, and we haven't proved an exponent dependent floating-point version. `generic_format_round_odd` shows that round to odd itself lands on the grid, and the result satisfies the specification `round_odd_point`. That specification says an inexact result is a directed neighbour with an odd mantissa at the input’s selected grid exponent. By contrast, `RoundOddCanonicalPoint` tests the result’s canonical mantissa, as Flocq does. Under abrupt underflow the two exponents may differ, and `round_odd_canonical_point_FIX` proves the canonical contract for fixed grids.

Our double-rounding theorem takes the number of extra digits beyond the mandatory two as a parameter. With zero extra digits, which means a fine step of $\mathrm{step}/2^{0+2}$, it reads:

```lean
example (step x : ℝ) (hstep : 0 < step) :
    roundAtScale nearestEven step hstep
        (roundAtScale oddRound (step / 2 ^ (0 + 2))
          (div_pos hstep (by positivity)) x) =
      roundAtScale nearestEven step hstep x :=
  roundAtScale_nearestEven_after_odd_binary_extra 0 step x hstep
```

To check the midpoint claim, give the coarse grid a step $h$. Its midpoint between indices $k$ and $k+1$ is $(k+\tfrac12)h$. On the fine grid of step $h/2^{n+2}$, the same point has integer index $(2k+1)2^{n+1}$, which is even for every $n \ge 0$, so an inexact round-to-odd result can't manufacture that midpoint. If the original input is already the midpoint, it's exactly representable on the fine grid and stays there, and the final nearest-even rounding then still sees the genuine tie. With only one extra binary digit, a coarse midpoint would have an odd fine-grid index, so an inexact round-to-odd result could still land there. A second extra digit makes those midpoint indices even, and that's the reason for the theorem's two-digit requirement.

## Rounding directions and the ternary value

From the integer rules of the first section we get six rounding directions, the constructors of [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEERoundingMode]]. `down`, `up`, and `towardZero` round the scaled mantissa with `floorRound`, `ceilRound`, and `truncRound`, and `away` uses `awayRound`. The two nearest directions differ only at an exact tie. `nearest`, the default, is `nearestEven`, and `nearestAway` is `nearestChoice` with ties sent to the neighbour of larger magnitude. IEEE 754-2019 defines all of them except `away`. Our `down`, `up`, `towardZero`, `nearest`, and `nearestAway` are its roundTowardNegative, roundTowardPositive, roundTowardZero, roundTiesToEven, and roundTiesToAway [@ieee754_2019]. Rounding away from zero is GNU MPFR's `MPFR_RNDA` [@mpfrManual].

[[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] takes the direction as an option, `roundAt fmt x (mode := m)`. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_eq_round]] identifies each direction with Flocq's `round` under its integer rule [[FloatLib.Floats.Formats.Flocq.roundingFunction]]. So the grid theorems of this chapter that assume only `ValidRnd` hold in all six. Those that assume `ValidRndToNearest`, such as the half-ulp bound, hold for `nearest` and `nearestAway` only. Rounding $1 + 2^{-25}$ up in binary32 gives $1 + 2^{-23}$, an error of three quarters of an ulp. [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_neg]] relates them under negation. Rounding $-x$ gives the negation of rounding $x$ in the direction `mode.negate`, which exchanges `up` and `down` and fixes the other four.

A rounded value doesn't record which side of the exact result it lies on. MPFR returns that side with every operation as its ternary value [@fousseMpfr2007]. It is negative when the delivered value is below the exact result, zero when the two are equal, and positive when it is above. We keep the same orientation as an `Ordering`. With `(status := true)`, an operation returns an [[FloatLib.Floats.Formats.BinaryInterchange.Model.IEEEOutcome]]. Its three fields are the value, the five IEEE exception flags of [chapter 06](#/chapter/the-numerical-models/status-flags-as-data), and the ternary value, `Ordering.lt`, `Ordering.eq`, or `Ordering.gt`.

Each operation computes the ternary value by one exact comparison of the delivered value with the exact result it rounded. For the operations that round an exact dyadic, that comparison is [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicTernary]]. Below the overflow threshold the compiled code reads the inexact flag from the same comparison. [[FloatLib.Floats.Formats.BinaryInterchange.Model.dyadicRoundingOutcome_eq_internal]] proves that this shared computation builds the outcome the specification defines. Integral rounding compares the result with its input, as MPFR's `mpfr_rint` does.

Results without a finite exact value follow fixed conventions. A NaN propagated from a NaN operand or produced by an invalid operation has `Ordering.eq`, as does the positive zero that a fully finite format delivers for an invalid operation. An exact infinity has `Ordering.eq` only when that same infinity is delivered. If it's delivered as a saturated finite value, or as the NaN that replaces it in a format without infinities, it has `Ordering.lt` for $+\infty$ and `Ordering.gt` for $-\infty$. A finite exact result delivered as an overflow infinity, or as that replacement NaN, has `Ordering.gt` when it is positive and `Ordering.lt` when it is negative.

For a binary32 midpoint, the sum $1 + 2^{-24}$ lies exactly halfway between $1$ and its upper neighbour $1 + 2^{-23}$, and that's where the directions part ways. Here `0x33800000` is the word for $2^{-24}$:

```lean
open FloatLib.Rounding

def halfGap : Binary32 := ExecFloat.Binary.ofBits32 0x33800000

#eval ExecFloat.Binary.add 1 halfGap (status := true)
-- { value := 1,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true },
--   ternary := Ordering.lt }
#eval ExecFloat.Binary.add 1 halfGap (mode := nearestAway) (status := true)
-- { value := 1.0000001,
--   status := { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := true },
--   ternary := Ordering.gt }
#eval (ExecFloat.Binary.add 1 halfGap (mode := towardZero) (status := true)).ternary
-- Ordering.lt
```

Nearest-even keeps $1$, whose significand is even, so the delivered value lies below the exact sum and the ternary value is `Ordering.lt`. Nearest-away takes the neighbour of larger magnitude, above the exact sum. Both calls raise only `inexact`, so it's the ternary value that tells us the side. Toward zero also returns $1$. Off a tie, the two nearest directions agree.

## How the library rounds once

Each basic reference operation on a binary format uses exact arithmetic to determine a single rounding into the destination. The refinement theorems say so for single operations. Composing operations or casting their results can still round more than once. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] equates the decoded executable sum with $\mathrm{roundAt}$ of the exact real sum. Its siblings for subtraction, multiplication, division, square root, and fused multiply-add do the same, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] forms $xy + z$ exactly and rounds once. Under their format, domain, and finiteness hypotheses these are exact equalities. In its default direction, $\mathrm{roundAt}$ is `round` at `nearestEven` with the descriptor's exponent function. So a grid theorem applies once its hypotheses have been established for that exponent function.

Mixed format operations such as `fmaAs` above decode every operand into a common exact domain, evaluate, and quantize once. The [mixed-format conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Conversion/Proof.lean) `preparedSpec_fmaAs` states that contract. `roundOnce` similarly performs one final quantization of an expression in the chosen exact domain, with `preparedSpec_roundOnce` as its contract. Whether the expression's own operations were exact is another question. One final quantization doesn't undo rounding that already happened while the expression was being built.

For signed-rational expressions targeting binary or other signed-zero-preserving destinations, directed cancellation also needs the rounding direction during exact addition or subtraction. Inside a `roundOnce` expression, `ExactExpression.add` and `ExactExpression.sub` take it as the same `mode` option. Ordinary `SignedRat` addition and subtraction keep the nearest-even zero-sign rule. A final cast or quantization preserves the zero sign it's given without recomputing how it arose. The generic quantizer contract describes quantization. It's up to an instance's exact-operation hooks to preserve its family's exact value semantics.

Say we take exact signed-rational operands with values one and negative one. Ordinary `SignedRat` addition produces positive zero, and quantizing that zero downward into a binary destination keeps it positive, because the quantizer no longer has the two operands it would need to recover a cancellation rule. `ExactExpression.add` with that destination and `mode := .down` chooses negative zero while the operands are still available, before any quantization happens. Both paths have rational value zero. Their sign bits differ, and that's why preserving an exact numerical value and preserving the intended IEEE operation are two different obligations. Adding zeros of the same sign keeps the common sign under either rule.

Our reductions accumulate every finite input as an exact dyadic and invoke the destination rounder once at the end. That's a guarantee we chose, since IEEE 754-2019 §9.4 permits implementation-defined reduction approximations and evaluation orders [@ieee754_2019]. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.sum_status_value_toReal_eq_roundAt_of_finite]] identifies a finite sum result with one nearest-even rounding of the mathematical sum. [[FloatLib.Floats.Formats.BinaryInterchange.Model.Reduction.dot_status_value_toReal_eq_roundAt_of_finite]] gives the corresponding statement for equal-length arrays and their exact product sum. Both real-valued contracts include empty input and cancellation to zero. The stored zero sign gets its own specification, in the reduction's zero-result theorems. Their finite-result premise excludes overflow to infinity. A cast rounds the value it receives, as [[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt_of_isIEEE_destination]] states. So if that value is already the rounded result of an operation, the composition contains two roundings, as in the binary64-to-binary32 example.

## When every addition rounds

Many reductions round each intermediate addition, and then the error depends on the evaluation order, because $(a+b)+c$ and $a+(b+c)$ can lose different small terms. [[FloatLib.Numerics.ReductionTree]] records the input occurrences at its leaves and the combining operations at its internal nodes. It represents a nonempty reduction, and an empty reduction needs an identity chosen outside the tree.

These two trees use the same values but put the cancellation at different points. The constructors let us choose both the grouping and the order of the inputs:

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

The first tree loses the `1` when it rounds `2048 + 1`, and the second cancels the large values first. Balanced and other custom trees use the same constructors. Leaves can also be input indices, with a function supplying their values, so the schedule doesn't need a copy of the data. At a node with computed operands $x$ and $y$, suppose the new addition introduces at most $e(x,y)$ absolute error. [[FloatLib.Numerics.ReductionTree.abs_eval_sub_exact_le_errorBudget]] bounds the complete reduction by the sum of these local allowances. You need the hypothesis only at operand pairs that occur in that tree. A uniform allowance $\delta$ gives $(n-1)\delta$ for $n$ inputs. A mixed allowance $u(|x|+|y|)+\delta$ also has a recursive bound in terms of exact subtree sums, and its absolute term can account for underflow.

For IEEE descriptor models, [[FloatLib.Floats.Formats.BinaryInterchange.Model.ReductionTree.abs_toReal_eval_sub_sum_le]] obtains each allowance from the existing half-ULP addition theorem. It requires finite inputs and finite intermediate results, but no normal-range assumption. A companion theorem bounds the difference between two finite evaluation schedules with the same input occurrences by their combined budgets. Finite additions carry no underflow term, so [[FloatLib.Floats.Formats.BinaryInterchange.Model.ReductionTree.abs_toReal_eval_sub_sum_le_mixedBudget]] discharges the mixed allowance with $u = 2^{-p}$ and $\delta = 0$, again assuming only finite evaluation. Our exact accumulators from the previous section follow a different algorithm. They keep every finite contribution until the final rounding, so the repeatedly-rounded theorem neither replaces nor weakens their one-rounding guarantee.

## How a kernel decides to round

An executable kernel decides rounding from an integer quotient and information about the discarded part, without computing logarithms over $\mathbb{R}$. It needs only enough information to locate the exact result between adjacent grid points $d < u$. In the [bracket model](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Calculation/Bracket.lean), `Location` records either an exact result, meaning $x = d$, or an inexact result, along with whether $x$ is below, at, or above the midpoint. `Inbetween` is the proposition that the recorded location is correct. All of this follows Flocq's bracket calculus, and it describes what the guard, round, and sticky bits of a hardware implementation encode.

Every rounding mode then decides whether to increment the mantissa. Rounding upward increments unless the result is exact. Nearest rounding increments above the midpoint, never below it, and resolves a midpoint by its tie rule. Nearest-even increments exactly when the lower mantissa is odd. Our bracket proofs identify these decisions with floor, ceiling, and nearest-even rounding on the real line.

A kernel may still need to discard low bits before making that decision. Truncation changes the adjacent grid points, so it has to update the location too. A value above the midpoint of a small cell can lie below the midpoint of the larger cell containing it. `refineLocation_correct` proves how to carry that information to the coarser grid. Our [truncation theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Calculation/Round.lean), `roundTruncatedNearestEven_correct`, then identifies the selected result with `round nearestEven x`. The kernels in [chapter 15](#/chapter/kernels-fixed-word-algorithms) and [chapter 16](#/chapter/backends-and-the-planner) use these rounding refinements.

<a id="using-the-rounding-theorems"></a>

## Connecting the grid to packed formats

An [`EncodedFormat` instance](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/GenericFormat.lean) whose codes are canonical mantissa and exponent pairs makes the generic theory a format in the library's own sense, and [[FloatLib.Floats.Formats.Flocq.representable_iff_genericFormat]] identifies representability in the common numerical system interface with `genericFormat`. For packed binary formats the connection runs through `fexpOf` and `roundAt`. Two theorems hold for every finite decoded word of every supported descriptor, IEEE or not. [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_genericFormat_of_isFinite]] puts every finite value on its descriptor's grid, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_toReal_eq]] says rounding it back to its own format is the identity.

Connecting an arithmetic operation to the grid still requires that operation's refinement hypotheses. Our rounded-real grid is unbounded above. `fltExp` has no upper bound, so there's no largest element and no overflow. A packed format has both. So a theorem of the form $\mathrm{decode}(\mathrm{add}(x,y)) = \mathrm{roundAt}(\mathrm{decode}(x) + \mathrm{decode}(y))$ needs the hypothesis that the output is finite. If the exact sum overflows, the packed result is an infinity, which has no real value to decode, while the right side is an ordinary real number. Symbolic criteria such as `isFinite_add_of_abs_add_le_posMaxFinite` let callers discharge the output-finiteness hypothesis from input bounds. For square root, a finite input that is nonnegative or a signed zero produces a finite result, so its refinement theorem needs the input domain condition and no output-finiteness premise of its own.

## Relationship to Flocq

Our definitions follow Flocq. `bpow`, `magnitude`, `cexp`, `genericFormat`, `ValidExp`, `ulp`, the point predicates, `Znearest` as `nearestChoice`, and the bracket calculus all have direct counterparts, and the generic-format, ulp, and neighbour modules name the corresponding Coq files in their docstrings. The proofs are written in Lean against Mathlib. This isn't a port of the whole Flocq library, though. We don't reproduce Flocq's proofs about individual arithmetic algorithms, which Boldo and Melquiond's book [@boldoMelquiondBook] discusses. We also leave out its support for executable computation beyond bracket refinement and truncation, and its Coq-specific application modules.
