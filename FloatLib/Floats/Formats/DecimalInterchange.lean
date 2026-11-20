/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Basic
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Posit.Configured.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Environment.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Words
public import FloatLib.Floats.Formats.DecimalInterchange.Interval
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Classification
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Comparison
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Conversion
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Division
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Encoding
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Neighbors
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Power
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Quantum
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Reduction
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Remainder
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Root
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Sqrt
public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Text
public import FloatLib.Floats.Formats.DecimalInterchange.Recommended.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.ScaledProduct.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Schedule.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Neighbors.Endpoints
public import FloatLib.Floats.Formats.DecimalInterchange.Remainder.Ties
public import FloatLib.Floats.Formats.DecimalInterchange.Scaling.Semantics

/-!
# IEEE decimal interchange

In decimal floating point, `1 × 10^0` and `10 × 10^-1` have the same value but are different
datums. They belong to the same cohort, and IEEE 754 says which member an operation should
return. So a datum here keeps its coefficient and its quantum exponent, and cohort members stay
distinct even when they are numerically equal. One `Format` descriptor covers decimal32,
decimal64, decimal128, and custom layouts. The BID and DPD codecs preserve complete datums, and
arithmetic rounds the exact expression into the chosen format and returns its exception outcome
along with the result.

`Algebraic` adds square, reciprocal square root, hypotenuse, integer powers, and integer-degree
roots in all five rounding modes, and each of them rounds the whole expression once. For the
finite-result `expm1` and `logp1` certificates, import
`DecimalInterchange.Transcendentals.Certified.Proof`. That import also brings the 26 functions
of one argument that IEEE 754-2019 §9.2 recommends, certified in the same way
(`Transcendentals.Certified.exp2`, `sin`, `atanh`, ...): a result when an enclosure settles the
nearest-even rounding of the real function, and `none` otherwise.

`Recommended` adds `quantum` (IEEE 754-2019 §5.3.2), the eight minimum and maximum operations
of §9.6 and the NaN payload operations of §9.7. `Reduction` adds the reductions `sum`, `dot`,
`sumSquare` and `sumAbs` of §9.4, which add their terms without error and round once, and
`Reduction.ScaledProduct` the scaled products `scaledProd`, `scaledProdSum` and
`scaledProdDiff`, which round the exact product once after scaling it by a power of ten.
`Reduction.Schedule` has the other members of the family that §9.4 allows: `reduceAlong` and
`reduceInOrder` add the terms of a reduction in a chosen association order and accumulator
format, with one rounding at each addition and the flags of every step. Their error bounds
are in `DecimalInterchange.Reduction.Schedule.Proof`.

The functions of §9.2 as total functions with flags, in the five rounding directions, are
`Transcendentals.CorrectlyRounded.exp`, `sin`, `pow`, `atan2` and the others, behind the import
`DecimalInterchange.Transcendentals.CorrectlyRounded.Proof`: each rounds the real function once
by exact comparisons, and its theorem `*_roundsTo` states the value and the flags for every
finite operand of every decimal format.

`KernelPath` computes sums, differences, products and fused multiply-adds on the fields of the
data, and its theorems `add_eq`, `sub_eq`, `mul_eq` and `fma_eq`, tagged `@[kernel_optimize]`,
let `float_decide` check a decimal operation in Lean's kernel in a fraction of a millisecond.
`KernelPath.Comparison` does the same for the 22 comparisons, the total order and the eight
minimum and maximum operations, with a comparison of the aligned coefficients (`compare_eq`,
`compareQuiet_eq`, `compareSignaling_eq`, `totalOrder_eq`, `extremum_eq`), and
`KernelPath.Classification` for `class`, `isNormal` and `isSubnormal`, with a comparison of
digit counts (`classify_eq`, `isNormal_eq`, `isSubnormal_eq`). `KernelPath.Conversion` projects
on natural numbers for `scaleB`, the conversion between decimal formats and the conversion from
an integer, and counts digits for `logB` (`scale_eq`, `convertFormat_eq`, `convertFromInt_eq`,
`logB_eq`), and `KernelPath.Quantum`
rounds at a quantum on natural numbers for `quantize`, the integral roundings and the ten
conversions to an integer (`quantize_eq`, `roundToIntegralExact_eq`, `roundToIntegral_eq`,
`convertToInteger_eq`). `KernelPath.Neighbors` steps to the neighbouring coefficient for
`nextUp` and `nextDown` (`nextUp_eq`), `KernelPath.Division` rounds the ratio of two
coefficients for `div` (`div_eq`), `KernelPath.Sqrt` rounds the integer square root of a
ratio for `sqrt`, `rSqrt` and `hypot` (`sqrt_eq`, `rSqrt_eq`, `hypot_eq`), and
`KernelPath.Reduction` adds the terms of `sum`, `sumAbs`, `sumSquare` and `dot` as natural
numbers at their least quantum exponent (`sum_eq`, `sumAbs_eq`, `sumSquare_eq`, `dot_eq`).
`KernelPath.Power` rounds an integer power of a coefficient, or its reciprocal, for `pown`
(`pown_eq`). `KernelPath.Remainder` decides the nearest integer quotient of two coefficients on
their common quantum for `remainder` (`remainder_eq`), `KernelPath.Root` rounds the integer
root of a ratio for `rootn` (`rootn_eq`), `KernelPath.Encoding` computes the interchange words
and their data for the four encoding operations (`encodeDecimal_eq`, `decodeDecimal_eq`,
`encodeBinary_eq`, `decodeBinary_eq`), and `KernelPath.Text` writes and reads character
sequences with the digit loop of `Numerics.Kernel.Text` (`formatExact_eq`, `parse_eq`).

`Environment` carries the current rounding direction and the sticky exception flags through pure
computations. Neighbors, remainder, the exponent operations, and text conversion all work on the
same datums and the same projection. Each part also has narrower imports, so you can run the code
without pulling in its numerical and representation proofs.

## References

* IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* Mike Cowlishaw, *General Decimal Arithmetic*,
  <https://speleotrove.com/decimal/decarith.html>.
-/
