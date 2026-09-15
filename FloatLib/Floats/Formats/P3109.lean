/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Selection
public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Correctness
public import FloatLib.Floats.Formats.P3109.Projection.Direction
public import FloatLib.Floats.Formats.P3109.Projection.Selection
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Proof
public import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public import FloatLib.Floats.Formats.P3109.Conversion.Proof
public import FloatLib.Floats.Formats.P3109.Conversion.Range
public import FloatLib.Floats.Formats.P3109.Conversion.Instances
public meta import FloatLib.Floats.Formats.P3109.Info

/-!
# P3109 formats

Signed and unsigned P3109 descriptors, exact arithmetic, round-then-saturate projection, and
`ExecFloat.P3109` conversions. `ofDyadic` and `ofRat` project exact values directly; `convert`,
`cast`, and mixed-expression operations use the same projection rules. Named constructors provide
zero, NaN, and supported infinities. `ofFiniteFields?` checks field widths and reserved encodings;
`ofNatBits` accepts serialized codes.

Core arithmetic evaluates exact rational intermediates and performs one destination projection.
Square root uses exact integer comparisons with a proof against `Real.sqrt`. The common
`ExecFloat` capabilities provide add, subtract, multiply, divide, square root, and FMA;
`ExecFloat.P3109.*To` also permits independent P3109 source and destination descriptors.
The mixed-operation interface covers fused addition, scaled arithmetic, and external
binary16, binary32, and BFloat16 destinations. Extrema, classification, format queries, and
neighbor operations follow the same descriptor's datum set.

The implementation follows Interim Report v4.0.3. This is a working-group report, not an approved
IEEE standard. Conversion indicators are defined by FloatLib.

Finite values use binary scientific notation with `P - 1` stored trailing bits and an implicit
leading bit for normal values. A separate descriptor is needed because:

* unsigned profiles have no sign bit;
* one exponent bit and zero trailing bits are allowed, below `FloatFormat`'s minimum widths;
* NaN occupies a profile-dependent endpoint or midpoint, and extended profiles reserve endpoint
  infinities instead of IEEE 754's all-ones-exponent class.

The family shares exact dyadics, comparison, and deterministic rounding with the other formats.
Field classification and saturation use the P3109 rules.

## Reference

* IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
  version 4.0.3 (1 September 2026), repository revision `34f5964`,
  <https://github.com/P3109/Public/tree/34f5964d9bb2382b2665d15467fc3517b990b308>.

## Projection

This is the public entry point for exact P3109 round-then-saturate projection, direct encoding,
their correctness theorems, and the rounding-direction theorems for the deterministic modes.
-/

@[expose] public section
