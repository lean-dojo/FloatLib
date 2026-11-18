# Generated forward bounds against measured errors

`roundoff mixed theorem` reads a program and proves a bound on its rounding error. This page
asks how far that bound is from the error that actually occurs, in binary32, for a sum, a dot
product, one entry of a matrix product, one output of a linear layer, Horner's rule, a softmax
weight, a log-sum-exp, one output of a perceptron with one hidden layer, and the two schedules of
the target gradient of cross-entropy. A second part has the cancellation cases: a difference
that does not round, the linear constants of sums and inner products, and a relative entropy of
two close distributions in two forms.

Which part is Lean and which is the script:

- Lean: `benchmarks/roundoff/Programs.lean` defines the programs and generates their theorems.
  Run `lake env lean benchmarks/roundoff/Programs.lean`: it prints every generated statement:
  the mixed forward bound, the backward-error statement and the forward bound in closed form of
  the programs that have one, and, from `#roundoff_shape`, whether each mixed bound is relative.
  Those statements are proved for every IEEE binary format and every length.
- Script: `benchmarks/roundoff/bounds.py` runs the programs in binary32 (numpy `float32`, with a
  correctly rounded exponential and logarithm from mpmath), computes the exact results with
  300-bit arithmetic, and evaluates the bounds by following the recurrences of the printed
  statements. The recurrences are transcribed by hand. Every number in the tables below is the
  script's, not Lean's. The script checks that no measured error exceeds a bound.

The tables are `python3 benchmarks/roundoff/bounds.py --trials 100 --json
benchmarks/results/roundoff/bounds.json` (seed 20261115, about a minute, 47 MB),
measured on 2026-11-15. Rows of length 4,096 and the perceptron rows use 25 trials. A trial whose
computed result is exact is left out of the ratios.

## Bound over measured error

Each cell is a bound divided by the measured error, so 1 means the bound is attained.

- Stated bound: the bound of the theorem from `roundoff mixed theorem`. It follows the partial
  sums of the exact computation, so it depends on the data, and its premise is a range
  condition at every step.
- Closed form of the loop: `List.abs_sub_le_of_sumFold`, the closed form of a summation loop,
  `((1 + u)^n - 1) * sum |t_j| + (1 + u)^n * sum c_j`, applied by hand to the stated bound.
  Horner's rule and the perceptron have none.
- Generated closed form: the bound of the theorem from `roundoff closed theorem`. Term `j`
  of `n` is weighted by the bound `(1 + u)^(n - 1 - j + k) - 1` of its own perturbation, not by
  the largest one, and the premise is a finite result. Horner's rule accumulates the weighted
  coefficients through the exact loop, and the perceptron is a sum over its hidden units of
  sums over their weights. In the softmax weight and the log-sum-exp each exponential is
  weighted by its own roundings, and the quotient and the logarithm carry the premise that the
  change of the sum is below the sum.
- If the first step were exact: what the stated bound would be if the analysis used that the
  first addition, to an exact zero, does not round. The analysis does not do this; the column
  measures what it would gain.

| program | n | trials | stated bound / error: least | median | closed form of the loop | generated closed form | if the first step were exact |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| sum, worst case | 4 | 1 | 1.33 | 1.33 | 1.33 | 1.33 | 1 |
| sum, worst case | 16 | 1 | 1.07 | 1.07 | 1.07 | 1.07 | 1 |
| sum, worst case | 256 | 1 | 1 | 1 | 1 | 1 | 1 |
| sum, worst case | 4,096 | 1 | 1 | 1 | 1 | 1 | 1 |
| dot product, worst case | 4 | 1 | 1.67 | 1.67 | 1.67 | 1.67 | 1.33 |
| dot product, worst case | 16 | 1 | 1.13 | 1.13 | 1.13 | 1.13 | 1.07 |
| dot product, worst case | 256 | 1 | 1.01 | 1.01 | 1.01 | 1.01 | 1 |
| dot product, worst case | 4,096 | 1 | 1 | 1 | 1 | 1 | 1 |
| sum, positive terms | 4 | 100 | 1.52 | 4.41 | 7.02 | 4.41 | 4.04 |
| sum, positive terms | 16 | 100 | 3.56 | 11.8 | 21.7 | 11.8 | 11.7 |
| sum, positive terms | 256 | 100 | 15.8 | 68.5 | 136 | 68.5 | 68.5 |
| sum, positive terms | 4,096 | 25 | 51.5 | 216 | 430 | 216 | 216 |
| sum, mixed signs | 4 | 100 | 1.35 | 5.4 | 14 | 8.43 | 4.72 |
| sum, mixed signs | 16 | 100 | 2.71 | 12 | 111 | 57.9 | 11.7 |
| sum, mixed signs | 256 | 100 | 14.9 | 50.1 | 1.45e+03 | 734 | 50.1 |
| sum, mixed signs | 4,096 | 25 | 58.8 | 120 | 1.91e+04 | 9.47e+03 | 120 |
| dot product | 4 | 100 | 1.91 | 8.42 | 17.4 | 12.7 | 7.45 |
| dot product | 16 | 100 | 3.98 | 14 | 59.2 | 34.3 | 13.8 |
| dot product | 256 | 100 | 15.8 | 62.9 | 1.17e+03 | 608 | 62.9 |
| dot product | 4,096 | 25 | 47.1 | 213 | 2.09e+04 | 1.06e+04 | 213 |
| matrix product entry | 4 | 100 | 2.29 | 8.94 | 16.9 | 11.2 | 7.38 |
| matrix product entry | 16 | 100 | 3.65 | 12.6 | 53 | 31.6 | 12.5 |
| matrix product entry | 256 | 100 | 13.3 | 49.1 | 1.04e+03 | 534 | 49.1 |
| matrix product entry | 4,096 | 25 | 47.4 | 202 | 1.87e+04 | 9.53e+03 | 202 |
| linear layer output | 4 | 100 | 1.56 | 7.26 | 11.5 | 9.76 | 6.73 |
| linear layer output | 16 | 100 | 3.49 | 13.5 | 54.5 | 36.1 | 13.2 |
| linear layer output | 256 | 100 | 12.6 | 52.8 | 1.24e+03 | 645 | 52.8 |
| linear layer output | 4,096 | 25 | 63.3 | 171 | 1.53e+04 | 7.58e+03 | 171 |
| Horner's rule | 4 | 100 | 1.48 | 5.7 |  | 7.62 | 5.58 |
| Horner's rule | 16 | 100 | 1.52 | 9.07 |  | 20.9 | 8.96 |
| Horner's rule | 64 | 100 | 1.91 | 9.6 |  | 19.6 | 9.6 |
| softmax weight | 4 | 100 | 2.21 | 9.61 |  | 9.61 | 9.05 |
| softmax weight | 16 | 100 | 2.66 | 12.2 |  | 12.2 | 12.2 |
| softmax weight | 256 | 100 | 8.8 | 53.6 |  | 53.6 | 53.6 |
| log-sum-exp | 4 | 100 | 1.51 | 5.62 |  | 5.62 | 5.44 |
| log-sum-exp | 16 | 100 | 2 | 7.51 |  | 7.51 | 7.46 |
| log-sum-exp | 256 | 100 | 7.24 | 25.9 |  | 25.9 | 25.9 |
| perceptron output | 16 x 8 | 25 | 8.12 | 17.5 |  | 42.7 | 17.2 |
| perceptron output | 64 x 32 | 25 | 21.8 | 57.7 |  | 227 | 57.5 |
| perceptron output | 256 x 64 | 25 | 47.5 | 137 |  | 1.18e+03 | 137 |

What the table says:

- The stated bound is attained. In the two worst-case rows every addition is a tie that rounds
  the same way. For the sum the bound is 1.33 times the error at length 4 and equal to it to
  three digits from length 256 on; for the dot product it is 1.67 and 1.01 times. The factor at
  small lengths is the first step: the bound counts `n` rounding errors of additions where
  `n - 1` occur, and for the dot product the rounding of a first product that is exact here.
- On random data the ratio grows like the square root of the length, from 5 to 9 at length 4
  to between 120 and 216 at length 4,096. Rounding errors of random data cancel like a random
  walk, and a bound that holds for every input cannot use that. We found no step where the
  analysis itself loses more than a factor `1 + u`, apart from the first step of a loop.
- The generated closed form needs no range conditions. It is about half the closed form of the
  loop on random data and equal to the stated bound for positive terms. For terms of mixed
  signs both closed forms are far above the stated bound
  (9,470 against 120 at length 4,096), because a closed form in `sum |t_j|` cannot see
  cancellation in the partial sums. For Horner's rule the closed form is within 1.3 to 2.3 times
  the stated bound, and for the perceptron within 2.4 to 8.6 times. For the softmax weight and
  the log-sum-exp, whose terms are positive, it equals the stated bound to three digits.
- Treating the first step as exact would gain about 12% at length 4 and about 2% at length 16.
  It would put a case distinction into every generated loop statement, so we left it out.

Whether each bound is relative, from `#roundoff_shape` in Lean (a reading of the generated
statement, for every format and length): the softmax weight and `-(s / (1 + s))` are relative.
The sum, the dot product, the matrix product entry, the linear layer, Horner's rule and the
perceptron are not relative for data of any sign, and the dot product is relative under the
premise that its factors are nonnegative (`tests/FloatLibTests/Conformance/BinaryInterchange/
RoundoffShape.lean`). The log-sum-exp and `1 / (1 + s) - 1` are not relative.

## Cancellation and constants

Three more tables measure cancellation and constants (the same command and seed, 100 trials,
1 min 18 s, 49 MB). The statements they transcribe are printed by the last section of
`benchmarks/roundoff/Programs.lean`.

### A difference that does not round

`(x - y) * z` with `y / 2 <= x <= 2 y`: the subtraction is exact (Sterbenz), so the product is
the only rounding. "Charged" is the bound of the statement that does not use the two
hypotheses, which charges the subtraction a rounding; "exact" is the bound of
`scaledDifference_forward` and `scaledDifference_closed`. Each cell is the median of bound over
measured error.

| x and y | trials | mixed, subtraction charged | mixed, subtraction exact | closed, subtraction charged | closed, subtraction exact |
| --- | ---: | ---: | ---: | ---: | ---: |
| within a factor of two | 100 | 6.1 | 3.05 | 48.8 | 24.4 |
| within 1e-3 | 100 | 5.95 | 2.98 | 2.72e+04 | 1.36e+04 |
| within 1e-6 | 46 | 4.93 | 2.46 | 1.83e+07 | 9.13e+06 |

The mixed bound with the exact subtraction is half of the charged one and stays within three
times the error however close the operands are, because it is relative to the product. The
closed form is also half, and still far off where the operands are close: it is stated in `|x|`
and `|y|` and cannot see that they cancel. In the last row 54 of the 100 trials had no rounding error at all and are
left out.

### The linear constants of a sum and of an inner product

`Analysis/Summation.lean` proves `(n - 1) u` for a sum (Rump 2012) and `n u` for an inner product
without underflow (Jeannerod and Rump 2013). The table compares three closed bounds over the
measured error, for positive terms in exact rational arithmetic at 24 bits of precision
(binary32) and at 8 bits (the significand of bfloat16), five trials each: the classical power
`((1 + u)^(n-1) - 1) * sum |t|`, the weighted form of `roundoff closed theorem`, in which term
`j` is weighted by the roundings it takes part in, and the linear constant.

| precision | n | ((1 + u)^(n-1) - 1) / ((n-1) u) | sum: power, weighted, (n-1) u | inner product: power, weighted, n u |
| ---: | ---: | ---: | --- | --- |
| 24 | 16 | 1 | 20.5, 11.7, 20.5 | 32.2, 20.4, 32.2 |
| 24 | 256 | 1.00001 | 74.8, 38.3, 74.8 | 129, 65.3, 129 |
| 24 | 1024 | 1.00003 | 569, 284, 569 | 150, 73.6, 150 |
| 8 | 16 | 1.02781 | 9.48, 5.42, 9.23 | 12.5, 7.51, 12.1 |
| 8 | 256 | 1.70911 | 157, 67, 92.1 | 82.6, 34.3, 48.2 |
| 8 | 1024 | 13.2538 | 105, 24.3, 7.91 | 113, 25.9, 8.51 |

In binary32 the linear constant and the power agree to four digits, and the weighted form is
the tightest, about half of either. At eight bits the power grows past the linear constant, by
a factor of 13 at length 1,024, and there the linear constant is the tightest of the three: 7.9
times the error against 24 for the weighted form. So the generated closed form stays as it is,
and the two theorems are there for long loops in short formats.

### A relative entropy of two close distributions

Sixteen outcomes in binary32; `q` is `p` with each weight changed by a uniform relative amount
up to the spread, then normalized. The program computes the logarithms, correctly rounded. The
sum of `p * (log p - log q)` has terms of both signs that cancel. The sum of
`p * expm1x (log q - log p)` has nonnegative terms; it is the same quantity for two
distributions. Each bound is divided by the magnitude of its own exact reference: at or above
one, the theorem does not fix the sign of the result. "Not positive" counts the trials whose
computed value was zero or negative.

| spread of q around p | p (log p - log q): error / exact | bound / exact (median, largest) | not positive | p expm1x (log q - log p): error / exact | bound / exact (median, largest) | not positive |
| --- | ---: | --- | ---: | ---: | --- | ---: |
| 0.1 | 1.17e-05 | 0.000206, 0.000386 | 0 | 6.48e-07 | 1.1e-05, 1.51e-05 | 0 |
| 0.01 | 0.0012 | 0.0224, 0.0471 | 0 | 7.63e-06 | 0.000105, 0.000142 | 0 |
| 0.001 | 0.115 | 2.21, 4.66 | 0 | 6.54e-05 | 0.00104, 0.0015 | 0 |
| 0.0001 | 2.02 | 36.3, 1.19e+03 | 39 | 0.000698 | 0.0101, 0.0148 | 0 |

The bound of the first form passes the size of the entropy at a spread of one part in a
thousand, and at one part in ten thousand the computed entropy was zero or negative in 39 of
100 trials. `#roundoff_check` warns on that theorem at such inputs. The bound of the second form
is two thousand times smaller there, and the computed value was positive in every trial. Its
bound still grows as the distributions approach, because the argument `log q - log p` is itself
a difference of rounded logarithms; computing that argument from logits without the subtraction
would remove that too.

## An interval endpoint in a directed rounding attribute

The lower endpoint of `x * y + z`: the product and the sum are rounded toward negative infinity
(`ExecFloat.Binary.mul x y (mode := .down)` and `add`), with standard normal inputs in binary32.
The bound is that of `lowerAffine_forward`: relative `2 u`, the unit roundoff of a directed
attribute, and absolute `(1 + 2 u) (2 u |x y| + 2 eta)`. The same endpoint by one fused
multiply-add rounded toward negative infinity (`ExecFloat.Binary.fma x y z (mode := .down)`)
has the bound of `lowerFused_forward`: relative `2 u` and absolute `2 eta`, one rounding of the
exact value. In the second pair of rows `z` is within one part in a thousand of `-x y`, so the
sum cancels.

| lower endpoint of x * y + z | trials | computed at or below exact | bound / error (least, median) | bound / exact (median) |
| --- | ---: | ---: | --- | ---: |
| product and sum, z independent | 100 | 100 | 1.06, 3.39 | 1.65e-07 |
| one fused multiply-add, z independent | 100 | 100 | 1.03, 2.69 | 1.19e-07 |
| product and sum, z within 1e-3 of -x y | 100 | 100 | 1.13, 3.37 | 0.000253 |
| one fused multiply-add, z within 1e-3 of -x y | 100 | 100 | 1.27, 2.61 | 1.19e-07 |

The computed endpoint was at or below the exact value in every trial, and the bounds are within
a factor of 1.06 and 1.03 of the error at their tightest. Where the sum cancels, the bound of
the two operations is 2.5e-4 of the exact value, because the rounding of the product is charged
against `|x y|`; the fused endpoint keeps `2 u` of the exact value, two thousand times less.

## One call of `expm1x` in closed form

`expm1x x` at `x = 2^-k` in binary32. The closed forward bound of the call, divided by the value
`exp x - 1 - x`: with the rounding of the function spread over the three terms of the
reference, `(exp x + 1 + |x|) u + eta`, and with the rounding kept on the value,
`|exp x - 1 - x| u + eta` (`expm1xCall_closed`).

| x | exp x - 1 - x | error / value | closed bound / value, rounding on the terms | on the value |
| --- | ---: | ---: | ---: | ---: |
| 2^-2 | 0.034 | 2.67e-08 | 4.44e-06 | 5.96e-08 |
| 2^-6 | 0.000123 | 1.56e-08 | 0.000987 | 5.96e-08 |
| 2^-10 | 4.77e-07 | 3.97e-08 | 0.25 | 5.96e-08 |
| 2^-14 | 1.86e-09 | 3.94e-08 | 64 | 5.96e-08 |
| 2^-18 | 7.28e-12 | 3.97e-08 | 1.64e+04 | 5.96e-08 |

With the rounding on the terms, the closed bound passes the value itself between `2^-10` and
`2^-14`. With the rounding on the value, which is what `expm1xCall_closed` states, it is one unit
roundoff of the value at every argument, as the mixed theorem is.

## The target gradient

The gradient of cross-entropy with respect to the target logit is `-(s / (1 + s))`, where `s`
is the sum of the other exponentials over the target's. Computed as `1 / (1 + s) - 1` it is
exactly zero once `s` is below the unit roundoff, which is how training stops in Softmax
Collapse. Each bound is divided by the exact gradient: a value near or above 1 says the bound
allows the computed gradient to be zero.

| s | exact gradient | `1 / (1 + s) - 1`: computed | bound / exact | `-(s / (1 + s))`: computed | bound / exact |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1e-2 | -0.00990099 | -0.00990099 | 1.2e-05 | -0.00990099 | 1.19e-07 |
| 1e-4 | -9.999e-05 | -0.000100017 | 0.00119 | -9.999e-05 | 1.19e-07 |
| 1e-6 | -9.99999e-07 | -9.53674e-07 | 0.119 | -9.99999e-07 | 1.19e-07 |
| 3.0459e-8 | -3.0459e-08 | 0 | 3.91 | -3.0459e-08 | 1.19e-07 |
| 1e-9 | -1e-09 | 0 | 119 | -1e-09 | 1.19e-07 |

The bound of `1 / (1 + s) - 1` is not relative and reaches the size of the gradient at
`s = 1e-6`. The bound of `-(s / (1 + s))` is relative: 1.19e-7, two unit roundoffs, at every
`s`. `#roundoff_shape` reports this difference from the two generated statements alone.
