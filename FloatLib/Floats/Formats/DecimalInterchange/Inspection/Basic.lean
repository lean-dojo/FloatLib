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

Comparison agrees with exact extended rational order and ignores cohorts.
Classification agrees with numerical zero and normal/subnormal thresholds.
Total ordering distinguishes complete datums, with transitivity, totality,
antisymmetry, signed-zero/cohort tie rules and NaN ordering proofs.
Stored sign operations preserve all non-sign bits, including redundant encodings,
and decoding commutes with sign replacement.

Neighbor operations and integer, format, and character conversions have their
own proofs in `Neighbors`, `Conversion`, and `Formatting`.
-/
