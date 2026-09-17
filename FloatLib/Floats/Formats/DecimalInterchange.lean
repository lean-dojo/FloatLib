/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Basic
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

The shared `Format` descriptor includes decimal32, decimal64, decimal128, and custom
layouts. Datums retain a coefficient and quantum exponent, including distinct
cohort members with the same numerical value. BID and DPD codecs
preserve complete datums, and arithmetic rounds exact expressions into the chosen
decimal format with explicit exception outcomes.

`Environment` threads the current rounding direction and sticky exception flags through
pure computations. Neighbors, remainder, exponent operations, and external text conversion
use the same datums and projection. Narrower imports separate execution from the
accompanying numerical and representation proofs.

## References

* IEEE, *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* Mike Cowlishaw, *General Decimal Arithmetic*,
  <https://speleotrove.com/decimal/decarith.html>.
-/
