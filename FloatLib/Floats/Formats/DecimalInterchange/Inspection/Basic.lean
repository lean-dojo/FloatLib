/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Inspection.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Proof

/-!
# Decimal inspection with mathematical guarantees

Import this module for decimal inspection together with its proofs:

* comparison agrees with exact extended rational order and ignores cohorts, so `1.0` equals `1.00`
* classification agrees with numerical zero and the normal and subnormal thresholds
* total ordering tells complete datums apart, with proofs of transitivity, totality,
  antisymmetry, the signed-zero and cohort tie rules, and NaN ordering
* stored sign operations preserve every non-sign bit, redundant encodings included, and decoding
  commutes with sign replacement

Neighbor operations and integer, format, and character conversions have their
own proofs in `Neighbors`, `Conversion`, and `Formatting`.
-/
