/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Basic
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Integer.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Binary.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Posit.Configured.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Environment.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Formatting.Words
public import FloatLib.Floats.Formats.DecimalInterchange.Interval
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
finite-result `expMinus1` and `logPlus1` certificates, import
`DecimalInterchange.Transcendentals.Certified.Proof`.

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
