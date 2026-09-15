---
number: "07"
slug: the-mathematics-of-rounding
title: The mathematics of rounding
summary: The spacing of a numerical grid explains rounding error, exact subtraction, and the danger of rounding twice.
phases: [rounding-theory]
---

The binary32 addition $1 + 10^{-8}$ from [Chapter 06](#/chapter/the-numerical-models) returns `1` because the increment is smaller than half the gap to the next representable value. The spacing between grid points bounds the possible error, and the rounding rule determines which neighbour is chosen. We'll use a grid model to separate those two choices from the bits that store the result. That lets us prove error bounds without choosing a packed encoding.

Boldo and Melquiond's Flocq library for Coq develops this grid-based approach [@boldoMelquiond2011]. FloatLib follows it using an arbitrary radix and an exponent function, with proofs written in Lean against Mathlib [@leanMathlib2020]. To use a grid theorem for a packed format, we first prove that the format's operations agree with rounding on that grid, then check the theorem's hypotheses. The same proof can therefore apply to binary32, binary128, and custom IEEE-style descriptors without a case for each stored width.

## Rounding as a function on the reals

A rounding function maps $\mathbb{R}$ to $\mathbb{R}$, with the representable numbers as its image. It must leave every representable number unchanged and be monotone, so $x \le y$ implies $\mathrm{round}(x) \le \mathrm{round}(y)$. The rounding mode decides which neighbour to choose and how to break ties.

Scaling by the local grid spacing reduces the choice of a representable value to the choice of an integer. An integer rounding rule is a function $\mathrm{rnd} : \mathbb{R} \to \mathbb{Z}$. `floorRound` is $\lfloor x \rfloor$, `ceilRound` is $\lceil x \rceil$, `truncRound` picks whichever is closer to zero, and [[FloatLib.Floats.Formats.Flocq.nearestEven]] picks the nearer integer and, at a tie, the even one. [[FloatLib.Floats.Formats.Flocq.oddRound]] leaves integers unchanged and otherwise picks the odd neighbour; `awayRound` rounds away from zero.

The class `ValidRnd` requires the integer rule to be monotone and leave every integer unchanged. `ValidRndToNearest` adds the inequality $|\mathrm{rnd}(x) - x| \le \tfrac12$, regardless of tie policy. All six rules are instances of `ValidRnd`; `nearestEven` is an instance of `ValidRndToNearest`, and so is `nearestChoice` for every tie rule.

Rounding to a format is then scale, round the integer, and scale back. Given a real $x$, the theory computes a canonical exponent $e$ from its magnitude, applies the integer rule to $x \cdot \beta^{-e}$, and multiplies back:

$$
\mathrm{round}_{\mathrm{rnd}}(x) \;=\; \mathrm{rnd}\!\left(x\,\beta^{-e}\right)\cdot \beta^{e}, \qquad e = \mathrm{cexp}(x).
$$

This is [[FloatLib.Floats.Formats.Flocq.round]]. We can do much of the argument on the integers: monotonicity, the half unit bound, and the choice of neighbour are elementary facts about $\mathrm{rnd}$. Scaling then carries them to the grid. The exponent depends on the input magnitude, so comparing two rounded values also requires handling changes of scale. In [Figure 7.1](#/chapter/the-mathematics-of-rounding/figure-ch07-rounding-staircase), we can read rounding from a grid with three binary digits: each step is the set of reals sent to one grid point, and at the powers of two the canonical exponent changes and the steps double in width.

![Round to nearest even on a grid with three binary digits, from 0.5 to 2.5: each step is the set of reals sent to one grid point, the steps double in width at 1 and at 2, and a filled end marks the neighbour a tie goes to](assets/ch07-rounding-staircase.png "Nearest-even rounding on a grid with three significant binary digits. Filled endpoints identify the value chosen at a tie.")

We can inspect that gap directly. Add the small increment, then ask for the next representable neighbour of one:

```lean
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.Flocq

abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

#eval (1 : Binary32) + 1e-8
-- 1

#eval ExecFloat.Binary.nextUp (1 : Binary32)
-- 8388609 * 2^-23
```

The library prints values as an integer times a power of two, and $8388609$ is $2^{23} + 1$, so the neighbour of one is $1 + 2^{-23}$; the spacing there is $2^{-23}$ and $10^{-8}$ is about $0.084$ of it. The increment lies below the midpoint of that gap, so nearest rounding returns one.

Try increasing the increment until the sum changes :) Then use the printed neighbour to explain where that change happens.

## A grid described by an exponent function

The parameters of a grid are a radix $\beta$ and a function $\mathrm{fexp} : \mathbb{Z} \to \mathbb{Z}$ that says, for a number of a given magnitude, which exponent its representation should use. Encoding the format as a function rather than a precision is what lets one theory cover fixed point, floating point with unbounded exponent, and the mixture that real IEEE formats are. The [three exponent families](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Format/Formats.lean) are `fixExp`, the constant $e \mapsto e_{\min}$ describing a fixed grid $\beta^{e_{\min}}\mathbb{Z}$; [[FloatLib.Floats.Formats.Flocq.flxExp]], $e \mapsto e - p$, which gives $p$ digits at every magnitude and never underflows; and [[FloatLib.Floats.Formats.Flocq.fltExp]], $e \mapsto \max(e - p, e_{\min})$, which has $p$ digits in the normal range and a flat grid of spacing $\beta^{e_{\min}}$ below it; that flat region is gradual underflow. An [abrupt underflow selector](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Special/FTZ.lean) `ftzExp` models flush to zero policies and is kept apart from the gradual underflow model.

A grid point is written as a pair of integers, the structure [[FloatLib.Floats.Formats.Flocq.FloatRep]], a mantissa $m$ and an exponent $e$ denoting $m\,\beta^{e}$ through [[FloatLib.Floats.Formats.Flocq.toReal]] and [[FloatLib.Floats.Formats.Flocq.bpow]]. To place a real number we need its magnitude, `magnitude`, which is $\lfloor \log_\beta |x| \rfloor + 1$ for nonzero $x$ and $0$ at zero, so that $\beta^{\mathrm{mag}(x)-1} \le |x| < \beta^{\mathrm{mag}(x)}$ (`magnitude_spec`). The canonical exponent [[FloatLib.Floats.Formats.Flocq.cexp]] is $\mathrm{fexp}$ applied to the magnitude, and the scaled mantissa `scaledMantissa` is $x\,\beta^{-\mathrm{cexp}(x)}$. Representability, [[FloatLib.Floats.Formats.Flocq.genericFormat]], says that rescaling, taking the floor, and rescaling back returns $x$ unchanged, equivalently that the scaled mantissa is an integer (`generic_format_iff_scaled_mantissa_int`). Nothing here mentions storage, which is why the theory is format generic.

The exponent function $\mathrm{fexp}$ must satisfy consistency conditions where the magnitude changes. The class [[FloatLib.Floats.Formats.Flocq.ValidExp]] carries two such clauses from Flocq. The first says that if the format has genuine precision at magnitude $k$, that is $\mathrm{fexp}(k) < k$, then one magnitude up it uses an exponent of at most $k$, so the spacing there is at most $\beta^{k}$, the radix power that separates the two binades (the intervals between consecutive powers of the radix). This condition keeps the next grid point representable across that boundary.

The second clause governs magnitudes where $\mathrm{fexp}$ is at least as large as the magnitude itself, requiring constant spacing at smaller magnitudes. In an IEEE format this ensures the spacing remains constant towards zero. The theorems `validExp_FLX_iff` and `validExp_FLT_iff` show that FLX and FLT are valid exactly when the precision is positive, which is why callers check a precision with `FormatPrecision.ofInt?` before using it.

For `round`, we want two things: the result must land on the grid, and rounding a grid point must leave it unchanged. [[FloatLib.Floats.Formats.Flocq.generic_format_round]] proves the first, following Flocq by separating inputs in the flat region from those outside it. The second is `round_preserves_generic`. Together they make rounding idempotent and keep a chain of operations inside the format.

The [monotonicity proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Order.lean) is `round_mono`: inputs in different magnitude bins are scaled by different powers, so the proof bounds the rounded smaller input by the radix power that starts the larger input's bin. The [neighbour-selection theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Properties.lean) `round_eq_floor_or_ceil` states that every valid mode returns the downward or the upward neighbour. On the scaled integers, monotonicity bounds the answer between the floor and ceiling because the rule fixes both endpoints. An integer in that interval must be one of them.

In Lean, we can apply these three facts to any valid exponent function and integer rounding rule:

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

The relational specifications follow Flocq's `Rnd_DN_pt` and `Rnd_N_pt`: `RoundDownPoint` is the greatest representable number not above $x$, `RoundUpPoint` the least not below it, and `RoundNearestPoint` a representable number at least as close to $x$ as every other. `round_floor_point`, `round_ceil_point`, and [[FloatLib.Floats.Formats.Flocq.round_toNearest_point]] show that the computed roundings meet these specifications. Because the specifications mention only representable values, the double rounding argument below can use them without referring to the rounding algorithm.

## The unit in the last place

A ulp is the grid spacing at a point. Away from zero, [[FloatLib.Floats.Formats.Flocq.ulp]] is $\beta^{\mathrm{cexp}(x)}$. At zero the definition follows Flocq: if the format has a flat region below some exponent (selected by `negligibleExp`), the ulp of zero is the spacing of that region, and otherwise it is zero. For FLT this gives $\beta^{e_{\min}}$ (`ulp_zero_FLT`), the smallest subnormal; for FLX it gives zero (`ulp_zero_FLX`), because an unbounded exponent has no smallest positive number.

The [ulp proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Ulp.lean) and [neighbour proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Neighbors.lean) relate this spacing to adjacent representable values. For a nonrepresentable $x$ the two directed roundings differ by exactly one ulp, `round_ceil_eq_floor_add_ulp`. The neighbours `succ` and `pred` step to the adjacent grid point, with a special case at a radix power where the spacing below differs from the spacing above, and `generic_format_succ` and `generic_format_pred` prove the step lands back on the grid; the first clause of `ValidExp` ensures representability at the boundary where the spacing changes.

For a packed binary format, [[FloatLib.Floats.Formats.BinaryInterchange.Model.fexpOf]] computes the exponent function from the descriptor of [chapter 06](#/chapter/the-numerical-models): `fltExp` at the minimum subnormal exponent with precision one more than the fraction width. For binary32 that is $e_{\min} = -149$ and $p = 24$, and we can check both directly:

```lean
example : Model.fexpOf FloatFormat.binary32 = fltExp (-149) 24 := by
  rfl

#eval ExecFloat.Binary.nextUp (0 : Binary32)
-- 1 * 2^-149
```

[[FloatLib.Floats.Formats.BinaryInterchange.Model.ulpAt]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.epsilonAt]] are the format level ulp and half ulp on this exponent function, and the successor of zero above is the ulp of zero the theory predicts.

We can work out that change in spacing by substituting values into `fexpOf`. The magnitude of one is $1$, so its canonical exponent is $\max(1-24,-149)=-23$. The magnitude of two is $2$, giving $-22$ instead: one step above two is twice as large as one step above one. At the least normal value, $2^{-126}$, the magnitude is $-125$ and the canonical exponent is $\max(-125-24,-149)=-149$. For positive values below that point, the maximum keeps choosing $-149$. The subnormal grid continues with that same spacing all the way to zero, progressively using fewer significant bits rather than a smaller exponent.

<a id="what-a-rounded-result-promises"></a>

## Absolute and relative error bounds

Nearest rounding is within half a ulp of the exact value. In the theory it is [[FloatLib.Floats.Formats.Flocq.error_bound_ulp]]:

$$
|\mathrm{round}_{\mathrm{rnd}}(x) - x| \;\le\; \frac{\mathrm{ulp}(x)}{2} \qquad \text{for every } \mathrm{rnd} \text{ with } |\mathrm{rnd}(t) - t| \le \tfrac12.
$$

For $x = 0$, rounding is exact. For a nonzero input, multiplying the half-unit bound on the scaled mantissa by the positive factor $\beta^{\mathrm{cexp}(x)}$ converts an error measured in grid steps into an error in the original units. The theorem asks only for `ValidRndToNearest`, so it covers every tie policy at once. For directed modes the corresponding fact is one full ulp, `round_abs_error_le_ulp`, and strictly less when the rounding was inexact (`round_abs_error_lt_ulp_of_inexact`). The [relative-error proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/Bounds.lean) give two forms: `relative_error_round_ulp` divides the absolute bound by $|x|$, and `round_relative_error_ulp` restates it as the model numerical analysts use, $\mathrm{fl}(x) = x(1 + \delta)$ with $|\delta|$ bounded.

In a fixed precision format the bound on $\delta$ becomes a constant. For FLX with $p$ digits, [[FloatLib.Floats.Formats.Flocq.round_relative_error_FLX]] proves that there is $\delta$ with $|\delta| \le \beta^{1-p}/2$ and $\mathrm{round}(x) = x(1+\delta)$. That constant is the unit roundoff $u$, and for binary32, where $p = 24$, it is $2^{-24}$. The FLT version, `relative_error_round_FLT_normal`, requires the input to be in the normal range. Near zero a uniform relative bound of this size is false: gradual underflow keeps the absolute spacing fixed while the values shrink, so the useful statement there is the absolute one. A sharper classical estimate replaces unit roundoff by $u/(1+u)$.

For packed binary formats, [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]] applies the FLT theorem at the descriptor's exponent function. It uses $u = 2^{-p}$, giving the $2^{-24}$ relative bound for binary32 shown by `#float_info [errors]` in [chapter 01](#/chapter/using-the-library). The refinement to $u/(1+u)$ is not proved here.

The figure compares absolute and relative bounds for binary16, whose exponent function is `fltExp (-24) 11` by the same computation as binary32's: the absolute half ulp bound is flat across the subnormal range and doubles at every power of two above it, and dividing it by $x$ gives a relative bound that stays between $u/2$ and $u$ in the normal range and is no longer uniform below it.

The constant relative bound follows by cancelling the magnitude from the absolute bound. In a normal binade with magnitude index $e$, we have $|x| \ge \beta^{e-1}$ and half an ulp is $\beta^{e-p}/2$. Hence

$$
\frac{|\mathrm{round}(x)-x|}{|x|}
\le \frac{\beta^{e-p}}{2\,\beta^{e-1}}
= \frac{\beta^{1-p}}{2}.
$$

Both numerator and denominator scale with the binade, so their ratio loses its dependence on $e$. In the subnormal range that cancellation is unavailable. For example, the real input $2^{-150}$ is halfway between zero and the least binary32 subnormal. Nearest even sends it to zero. Its absolute error is exactly half the subnormal spacing, yet its relative error is one. This satisfies the half-ulp theorem and explains why the small constant relative bound requires a normal-range hypothesis. Compare the two panels of [Figure 7.2](#/chapter/the-mathematics-of-rounding/figure-ch07-ulp): a constant absolute bound on the left becomes a growing relative bound near zero on the right.

![The unit in the last place of binary16, whose exponent function is fltExp (-24) 11, with the half ulp bound of nearest rounding beside it, and on the right the same bound divided by x, which stays between u/2 and u only in the normal range](assets/ch07-ulp.png "Binary16 grid spacing and its nearest-rounding error bound. Half an ulp bounds absolute error; a uniform relative bound stops applying near zero.")

We can now apply the generic half ulp bound, specialize the relative bound to FLX, and read off the binary32 instances. The second example uses the explicit `@round` form because the validity instance depends on `hprec`.

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

The last two examples apply [[FloatLib.Floats.Formats.BinaryInterchange.Model.abs_roundAt_sub_le]] and [[FloatLib.Floats.Formats.BinaryInterchange.Model.relativeError_roundAt_le_of_normal]]. These specialize the generic bounds to the descriptor's exponent function.

To bound a single operation, we first rewrite its executable result using the refinement equality. For addition, `abs_toReal_add_sub_le` in the same file then applies `abs_roundAt_sub_le` to the exact sum. The argument works for a product, quotient, square root, or fused multiply-add too: once the refinement theorem's hypotheses hold, apply `error_bound_ulp` to the exact expression.

## Exact subtraction

Sterbenz's lemma [@sterbenz1974] gives a condition under which subtraction is exact: if $y \le x \le 2y$ with both representable, then $x - y$ is representable, so subtracting them incurs no rounding at all. The [Sterbenz proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/Sterbenz.lean), `generic_format_FLX_sub_of_le_two_mul`, does not mention rounding. A zero difference is already representable. In the remaining case the operands are positive, and the ratio bound puts the magnitude indices of $x$ and $y$ at most one apart, so both are integer multiples of $\beta^{\mathrm{cexp}(y)}$, the smaller of the two canonical exponents, and so is their difference. Since $0 \le x - y \le y$, the canonical exponent of the difference is at most $\mathrm{cexp}(y)$, and an integer multiple of $\beta^{\mathrm{cexp}(y)}$ is then automatically on the grid at the difference's own exponent. The order symmetric form is [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]]. The shaded wedge in [Figure 7.3](#/chapter/the-mathematics-of-rounding/figure-ch07-sterbenz) is the region that hypothesis describes. Checking a grid with three binary digits, we find that every pair of grid points inside the wedge has a difference on the grid, and outside it some do and some do not.

![Sterbenz's hypothesis y/2 ≤ x ≤ 2y as a wedge in the plane, with every pair of grid points with three binary digits between 1/2 and 4 marked by whether x - y is on the grid: inside the wedge all 97 pairs are, outside it 38 are and 34 are not](assets/ch07-sterbenz.png "Subtracting the displayed grid points is exact throughout the factor-of-two region. Exact differences also occur outside it, where Sterbenz’s sufficient condition does not apply.")

The format that packed binary values actually use is FLT, and there the argument has two regimes. If the difference is small enough to be subnormal it is automatically representable: every FLT value is a multiple of $\beta^{e_{\min}}$, so the difference is too (`generic_format_FIX_sub`), and in the subnormal range that is all representability asks. Otherwise the difference is normal, the FLX theorem applies, and the result is transported back to FLT. The [FLT proof](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Analysis/SterbenzFLT.lean) is `generic_format_FLT_sterbenz`. At the packed level, [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_sub_eq_of_sterbenz]] states the executable consequence: two positive finite values within a factor of two subtract exactly, and since the exact difference is bounded by one of the operands, result finiteness follows rather than being assumed.

We can use the theorem below to prove exactness and the evaluations after it to inspect both the difference and its inexact flag:

```lean
example {fmt : FloatFormat} {x y : Model fmt}
    (hfmt : fmt.isIEEE = true)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hxpos : 0 < Model.toReal x) (hypos : 0 < Model.toReal y)
    (hxy : Model.toReal x ≤ 2 * Model.toReal y)
    (hyx : Model.toReal y ≤ 2 * Model.toReal x) :
    Model.toReal (Model.sub x y) = Model.toReal x - Model.toReal y :=
  Model.toReal_sub_eq_of_sterbenz hfmt hx hy hxpos hypos hxy hyx

def onePlusUlp : Binary32 := ExecFloat.Binary.nextUp 1

#eval (1.5 : Binary32) - onePlusUlp
-- 4194303 * 2^-23

#eval (ExecFloat.Binary.subWithStatus (1.5 : Binary32) onePlusUlp
  (rounding := .nearestEven)).2
-- { invalid := false, divideByZero := false, overflow := false, underflow := false, inexact := false }
```

Here $x = 1.5$ and $y = 1 + 2^{-23}$ satisfy $y \le x \le 2y$, the difference $\tfrac12 - 2^{-23}$ is returned exactly, and the status word confirms that nothing was inexact.

For this subtraction we can align the significands ourselves. At scale $2^{-23}$, the operands have integer significands $12582912$ and $8388609$. Their difference is $4194303$, exactly the significand printed above. That integer has fewer significant bits than either operand, so it fits easily once the result is normalized at its smaller magnitude. Cancellation has reduced the size of the answer; it has not required us to discard any nonzero bits. Sterbenz's ratio condition guarantees this representability for the whole class of nearby operands, and gradual underflow supplies the same protection when their difference reaches the fixed subnormal grid.

A second exactness result concerns the error of addition rather than the difference itself. For any nearest rounding rule, `add_round_error_generic` proves that $\mathrm{round}(x + y) - (x + y)$ is representable whenever $x$ and $y$ are, and [[FloatLib.Floats.Formats.Flocq.add_round_exact_error]] restates it as $x + y = \mathrm{round}(x+y) + e$ with $e$ in the format. This is the mathematical content of the TwoSum and FastTwoSum error-free transformations [@dekker1971] used in compensated summation.

The statement needs nearest rounding and a monotone exponent function. It fails for directed rounding: with three binary digits, $1 - 2^{-10}$ rounded down gives $7/8$, and the error $2^{-3} - 2^{-10}$ needs seven digits. The theorem proves that such an error value exists in the format, and `genericFormat_toReal_add_sub` carries that result to finite binary addition. A proof that TwoSum's sequence of floating-point operations actually computes $e$ would require a further argument; that algorithmic exactness proof is not included.

Companion [product-residual proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/Multiplication.lean) and [division and square-root residual proofs](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Error/DivisionSqrt.lean) show that the residual of a rounded FLX product is representable for any valid mode (`mul_round_error_FLX`), as is the division residual $x - qy$ (`div_round_residual_FLX`); the square root residual $x - q^2$ is representable for nearest-even rounding and precision above one (`sqrt_round_residual_FLX`). The packed addition theorem requires a finite output so that its real value denotes the rounded sum:

```lean
example {fmt : FloatFormat} (x y : Model fmt)
    (hfmt : fmt.isIEEE = true)
    (hx : Model.isFinite x = true) (hy : Model.isFinite y = true)
    (hout : Model.isFinite (Model.add x y) = true) :
    genericFormat FloatLib.Numerics.binaryRadix (Model.fexpOf fmt)
      (Model.toReal (Model.add x y) - (Model.toReal x + Model.toReal y)) :=
  Model.genericFormat_toReal_add_sub x y hfmt hx hy hout
```

<a id="the-double-rounding-hazard"></a>

## Double rounding

Rounding twice to the same format changes nothing, since rounding is idempotent. Rounding to a fine format and then to a coarse one is a different matter, and whether it agrees with rounding directly to the coarse format depends on the mode.

For two successive downward roundings, grid inclusion is enough. If every coarse grid point is also a fine grid point, the largest fine point below $x$ is at least the largest coarse point below $x$. Rounding that fine point down to the coarse grid cannot go below the coarse point, because the latter is itself available. It also cannot go above it: the fine result is still at most the original input, so any larger coarse point would contradict the definition of the original coarse rounding. The upward argument reverses the inequalities. The [double-rounding theorems](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Theory/Rounding/Double.lean) `roundDownPoint_double` and `roundUpPoint_double` state exactly this for arbitrary predicates related by inclusion, and [[FloatLib.Floats.Formats.Flocq.round_floor_double_FLX]] and `round_ceil_double_FLX` instantiate them for two FLX precisions, using `generic_format_FLX_mono` for the inclusion. Instantiated at 53 and 24 digits, the binary64 and binary32 precisions, the statement reads as follows; the `(by norm_num)` arguments discharge the side conditions, that each precision is positive (which `flxValidExp` needs) and that $24 \le 53$.

```lean
example {β : FloatLib.Numerics.Radix} (x : ℝ) :
    @round β (flxExp 24) (flxValidExp 24 (by norm_num)) floorRound
        (@round β (flxExp 53) (flxValidExp 53 (by norm_num)) floorRound x) =
      @round β (flxExp 24) (flxValidExp 24 (by norm_num)) floorRound x :=
  round_floor_double_FLX (by norm_num) (by norm_num) (by norm_num) x
```

Nearest rounding can turn a value just above a coarse midpoint into that midpoint, changing how the final tie is resolved. Take

$$
x = 1 + 2^{-24} + 2^{-53}.
$$

Rounded directly to binary32, $x$ sits just above the midpoint between $1$ and $1 + 2^{-23}$, so it goes up to $1 + 2^{-23}$. Rounded first to binary64 it becomes exactly $1 + 2^{-24}$: the spacing at one is $2^{-52}$, the term $2^{-53}$ is exactly half of it, and the tie goes to the even neighbour, which drops it. That value is now precisely a binary32 midpoint, and the second tie goes to even again; the even neighbour this time is $1$. The intermediate rounding has erased the information that the exact value was above the coarse midpoint, so the two answers differ by a full ulp. The value $x$ is not representable in binary64, so we produce it as the exact result of a fused multiply-add, $2^{-29}\cdot 2^{-24} + (1 + 2^{-24})$, whose three operands are representable in binary64.

```lean
def a : Binary64 := 1 / 536870912
def b : Binary64 := 1 / 16777216
def c : Binary64 := 1 + b

#eval ExecFloat.fma a b c
-- 16777217 * 2^-24

#eval (ExecFloat.cast (target := Binary32) (ExecFloat.fma a b c)).value?
-- some 1

#eval (ExecFloat.fmaAs (result := Binary32) a b c).value?
-- some 8388609 * 2^-23
```

Here `a` is $2^{-29}$, `b` is $2^{-24}$, and `c` is $1 + 2^{-24}$. Follow the rounding through the three outputs: the first line is the binary64 rounding of $x$, which is $1 + 2^{-24}$. Casting it to binary32 gives $1$. Computing the same fused multiply-add exactly and rounding once into binary32 gives $1 + 2^{-23}$, the correctly rounded answer. This is the x87 spill problem that [chapter 04](#/chapter/why-verifying-floating-point-is-hard) described, and it is why computing in a wider format does not by itself make the narrower result correctly rounded.

On fixed binary grids, round to odd can preserve the information that nearest rounding loses in this example. It leaves an exact integer alone and otherwise chooses the odd integer neighbour. With at least two extra binary digits, an inexact fine-grid result cannot be a coarse-grid midpoint: those midpoints have even indices on the fine grid. The theorem `nearestEven_roundOdd_binary_extra` shows that with at least two extra binary digits, round to odd followed by nearest even equals nearest even directly on the integer grid, and [[FloatLib.Floats.Formats.Flocq.roundAtScale_nearestEven_after_odd_binary_extra]] extends this to any fixed grid of positive step.

Both grids must be fixed, so the result covers fixed point and affine quantization; no exponent dependent floating-point version is proved. Round to odd itself lands on the grid (`generic_format_round_odd`) and satisfies the specification `round_odd_point`: an inexact result is a directed neighbour with an odd mantissa. The theorem takes the number of extra digits beyond the mandatory two as a parameter; with zero extra digits, so a fine step of $\mathrm{step}/2^{0+2}$, it reads:

```lean
example (step x : ℝ) (hstep : 0 < step) :
    roundAtScale nearestEven step hstep
        (roundAtScale oddRound (step / 2 ^ (0 + 2))
          (div_pos hstep (by positivity)) x) =
      roundAtScale nearestEven step hstep x :=
  roundAtScale_nearestEven_after_odd_binary_extra 0 step x hstep
```

To check the midpoint claim, give the coarse grid a step $h$. Its midpoint between indices $k$ and $k+1$ is $(k+\tfrac12)h$. On the fine grid of step $h/2^{n+2}$, the same point has integer index $(2k+1)2^{n+1}$, which is even for every $n \ge 0$. An inexact round-to-odd result therefore cannot manufacture that midpoint. If the original input is already the midpoint, it is exactly representable on the fine grid and stays there, preserving the genuine tie for the final nearest-even rounding.

With only one extra binary digit, a coarse midpoint would have an odd fine-grid index, so an inexact round-to-odd result could still land there. The second extra digit makes those midpoint indices even. This is the reason for the theorem's two-digit requirement.

## How the library rounds once

Each basic reference operation on a binary format uses exact arithmetic to determine a single rounding into the destination. Composing operations or casting their results can still round more than once. The refinement theorems say precisely that: [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_add_eq_roundAt]] equates the decoded executable sum with $\mathrm{roundAt}$ of the exact real sum, and its siblings for subtraction, multiplication, division, square root, and fused multiply-add ([[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_fma_eq_roundAt]] forms $xy + z$ exactly and rounds once) do the same. Under their format, domain, and finiteness hypotheses, these are exact equalities. Since [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt]] is `round` at `nearestEven` with the descriptor's exponent function, a grid theorem applies after its hypotheses have been established for that exponent function.

Mixed format operations such as `fmaAs` above decode every operand into a common exact domain, evaluate, and quantize once; the [mixed-format conversion theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/ExecFloat/Conversion/Proof.lean) `preparedSpec_fmaAs` states that contract. `roundOnce` similarly performs one final quantization of an expression in the chosen exact domain, with `preparedSpec_roundOnce` as its contract. Exactness of the expression's operations is a separate requirement: one final quantization does not undo rounding that already occurred while constructing the expression.

For signed-rational expressions targeting binary or other signed-zero-preserving destinations, directed cancellation also needs the destination context during exact addition or subtraction. Inside a `roundOnceWith` expression, `ExactExpression.addWith` and `ExactExpression.subWith` supply that context. Ordinary `SignedRat` addition and subtraction retain the nearest-even zero-sign rule; a final cast or quantization preserves a supplied zero sign rather than recomputing how it arose. The generic quantizer contract describes quantization, while an instance's exact-operation hooks must separately preserve its family's exact value semantics.

For a concrete cancellation, take exact signed-rational operands with values one and negative one. Ordinary `SignedRat` addition produces positive zero. Quantizing that supplied zero downward into a binary destination keeps it positive; the quantizer no longer has the two operands from which it could recover a cancellation rule. Using `ExactExpression.addWith` with that destination and a downward context chooses negative zero while the operands are still available, before any quantization occurs. Both paths have rational value zero. Their different sign bits explain why preserving an exact numerical value and preserving the intended IEEE operation are separate obligations. Same-sign zero addition retains the common sign under either rule.

Reductions accumulate the exact sum of every finite input as a dyadic and invoke the descriptor rounder once at the end; the [reduction theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/BinaryInterchange/Reduction/Proof.lean) `Model.Reduction.sumWithStatus_eq_round_of_finite_nonzero` states this for every array of finite inputs whose exact sum is nonzero. A cast rounds the value it receives ([[FloatLib.Floats.Formats.BinaryInterchange.Model.cast_eq_roundAt]]). If that value is already the rounded result of an operation, the composition contains two roundings, as in the binary64-to-binary32 example.

## How a kernel decides to round

An executable kernel decides rounding from an integer quotient and information about the discarded part, without computing logarithms over $\mathbb{R}$. It needs only enough information to locate the exact result between adjacent grid points $d < u$. In the [bracket model](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Calculation/Bracket.lean), `Location` records either an exact result, meaning $x = d$, or an inexact result, recording whether $x$ is below, at, or above the midpoint. The proposition `Inbetween` states that the recorded location is correct. This follows Flocq's bracket calculus and describes what the guard, round, and sticky bits of a hardware implementation encode.

Every rounding mode is then a function from a location to one boolean, whether to increment the mantissa. `roundUpLocation` increments unless the location is exact; `roundNearestLocation` increments above the midpoint, never below it, and at the midpoint defers to a tie rule, which for `nearestEvenChoice` is to increment exactly when the lower mantissa is odd. `inbetweenInt_floor`, `inbetweenInt_ceil`, and `inbetweenInt_nearestEven` prove that these decisions agree with `floorRound`, `ceilRound`, and `nearestEven` on the real line. Kernels see the exact value at a finer scale and must truncate, which changes the location; `refineLocation_correct` shows how a location in one cell of a subdivided interval determines the location in the whole, and the [truncation theorem](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/Calculation/Round.lean) `roundTruncatedNearestEven_correct` proves that nearest-even selection after truncation is `round nearestEven x`. Composing the bracket and truncation theorems establishes the rounding refinement that [chapter 13](#/chapter/kernels-fixed-word-algorithms) and [chapter 14](#/chapter/backends-and-the-planner) rely on.

## Connecting the grid to packed formats

The generic theory becomes a format in the library's own sense through an [`EncodedFormat` instance](https://github.com/lean-dojo/FloatLib/blob/main/FloatLib/Floats/Formats/Flocq/GenericFormat.lean) whose codes are canonical mantissa and exponent pairs, and [[FloatLib.Floats.Formats.Flocq.representable_iff_genericFormat]] identifies representability in the common numerical system interface with `genericFormat`.

For packed binary formats the connection runs through `fexpOf` and `roundAt`, and two theorems hold for every finite decoded word of every supported descriptor, IEEE or not: [[FloatLib.Floats.Formats.BinaryInterchange.Model.toReal_genericFormat_of_isFinite]] puts every finite value on its descriptor's grid, and [[FloatLib.Floats.Formats.BinaryInterchange.Model.roundAt_toReal_eq]] says rounding it back to its own format is the identity. Connecting an arithmetic operation to the grid still requires that operation's refinement hypotheses.

The rounded-real grid is unbounded above: `fltExp` has no upper bound, so there is no largest element and no overflow. A packed format has both. A theorem of the form $\mathrm{decode}(\mathrm{add}(x,y)) = \mathrm{roundAt}(\mathrm{decode}(x) + \mathrm{decode}(y))$ therefore needs the hypothesis that the output is finite, because if the exact sum overflows, the packed result is an infinity, which has no real value to decode, while the right side is an ordinary real number. Symbolic criteria such as `isFinite_add_of_abs_add_le_posMaxFinite` let callers discharge the output-finiteness hypothesis from input bounds. For square root, a finite input that is nonnegative or a signed zero produces a finite result, so its refinement theorem needs the input domain condition but no separate output-finiteness premise.

<a id="what-we-took-from-flocq-and-what-we-did-not"></a>

## Relationship to Flocq

The definitions follow Flocq: `bpow`, `magnitude`, `cexp`, `genericFormat`, `ValidExp`, `ulp`, the point predicates, `Znearest` as `nearestChoice`, and the bracket calculus all have direct counterparts. The docstrings name the Coq files they follow, and the proofs are written in Lean against Mathlib.

This is not a port of the whole Flocq library. It does not reproduce Flocq's proofs about individual arithmetic algorithms, discussed in Boldo and Melquiond's book [@boldoMelquiondBook], its support for executable computation beyond bracket refinement and truncation, or its Coq-specific application modules.

<a id="finding-the-rounding-theory"></a>

## Using the rounding theorems

To use the theory in a proof, start with [[FloatLib.Floats.Formats.Flocq.genericFormat]] for representability and [[FloatLib.Floats.Formats.Flocq.round]] for rounding. [[FloatLib.Floats.Formats.Flocq.error_bound_ulp]] bounds a nearest rounding's error; [[FloatLib.Floats.Formats.Flocq.generic_format_FLX_sterbenz]] proves exact subtraction under the Sterbenz hypotheses. For a code type whose meaning is given by the common numerical system interface, [[FloatLib.Floats.Formats.Flocq.representable_iff_genericFormat]] connects that notion of representation to the grid.
