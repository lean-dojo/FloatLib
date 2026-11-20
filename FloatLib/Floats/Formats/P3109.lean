/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.P3109
public import FloatLib.Floats.Formats.P3109.Arithmetic.External.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Extrema.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Instances
public import FloatLib.Floats.Formats.P3109.KernelPath.Rules
public import FloatLib.Floats.Formats.P3109.Block.Root.Report
public import FloatLib.Floats.Formats.P3109.Arithmetic.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Square
public import FloatLib.Floats.Formats.P3109.Arithmetic.Scaled
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Selection
public import FloatLib.Floats.Formats.P3109.Arithmetic.Queries.Standard
public import FloatLib.Floats.Formats.P3109.Block.Format
public import FloatLib.Floats.Formats.P3109.Block.Proof
public import FloatLib.Floats.Formats.P3109.Block.Root.Proof
public import FloatLib.Floats.Formats.P3109.Conversion.Instances
public import FloatLib.Floats.Formats.P3109.Conversion.Proof
public import FloatLib.Floats.Formats.P3109.Conversion.Range
public import FloatLib.Floats.Formats.P3109.Conversion.Runtime
public import FloatLib.Floats.Formats.P3109.Block.Operations
public import FloatLib.Floats.Formats.P3109.Arithmetic.ScaledFunctionsProof
public import FloatLib.Floats.Formats.P3109.Functions.Proof
public import FloatLib.Floats.Formats.P3109.Functions.Domain
public import FloatLib.Floats.Formats.P3109.Functions.Recommended.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Correctness
public import FloatLib.Floats.Formats.P3109.Projection.Direction
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Proof
public import FloatLib.Floats.Formats.P3109.Projection.Rational.Runtime
public import FloatLib.Floats.Formats.P3109.Projection.Selection

/-!
# P3109 formats

P3109 describes a whole family of low-precision formats through four parameters, and the order of
its steps matters. In `binary8p4se`, nearest-even conversion with no saturation request sends 232
to 224 but 233 to positive infinity, because 233 first rounds to 240, which has no finite
encoding. This package implements the family: signed and unsigned P3109 descriptors, exact
arithmetic, round-then-saturate projection, and `ExecFloat.P3109` conversions. `ofDyadic` and
`ofRat` project exact values, and `convert`, `cast`, and mixed-expression operations use the same
projection rules. Named constructors provide zero, NaN, and supported infinities.
`ofFiniteFields?` checks field widths and reserved encodings, and `ofNatBits` accepts serialized
codes.

Arithmetic computes the exact rational result and projects it once into the destination. Square
root gets there by exact integer comparisons, with a proof against `Real.sqrt`. Add, subtract,
multiply, divide, square root, and FMA come through the common `ExecFloat` capabilities, and each
`ExecFloat.P3109` operation also accepts operands of independent descriptors and takes
`(target := ...)`, `(mode := ...)`, and `(saturation := ...)` options. Literals round once from
their exact value, `square` projects the exact square once, and `==` is numerical equality with
NaN unequal to itself. The mixed-operation interface covers fused addition, scaled arithmetic, and
external binary16, binary32, and BFloat16 destinations. Extrema, classification, format queries,
and neighbor operations follow the same descriptor's datum set.

A `Block` is a nonempty sequence with a scale of its own type. Its conversion, maximum-finite scale
selection, exact reductions, and mixed block dots follow chapter 5 of the report. Generic
elementwise closed arithmetic and per-lane stochastic rounding words share one projection
interface. Block square root, reciprocal square root, and hypotenuse normalize the exact radicand
before one destination rounding, zero, infinite, and negative result scales included.

The standard-named API follows Interim Report v4.1, a working-group report not approved as an
IEEE standard. The conversion indicators are FloatLib's own. So are the functions of
`Functions.Recommended`, the functions of IEEE 754-2019 clause 9.2 that the report does not
list: `Exp10`, `Exp2MinusOne`, `Exp10MinusOne`, `Log10`, `Log2OnePlus`, `Log10OnePlus`, `Rootn`,
`Cbrt`, `Pown`, `Pow`, `Powr` and `Compound`. Each is one projection of the real result, in
every rounding and saturation mode and between independent descriptors.

Finite values use binary scientific notation with `P - 1` stored trailing bits and an implicit
leading bit for normal values. That sounds like IEEE 754, but P3109 needs a descriptor of its own:

* unsigned profiles have no sign bit
* one exponent bit and zero trailing bits are allowed, below `FloatFormat`'s minimum widths
* NaN occupies a profile-dependent endpoint or midpoint, and extended profiles reserve endpoint
  infinities instead of IEEE 754's all-ones-exponent class

Exact dyadics, comparison, and deterministic rounding are shared with the other formats, while
field classification and saturation follow the P3109 rules.

## Reference

* IEEE Working Group P3109, *Interim Report on Arithmetic Formats for Machine Learning*,
  version 4.1 (14 September 2026), repository revision `2d45cf2`,
  <https://github.com/P3109/Public/tree/2d45cf2fe0314d32251f5439d9d3ed078f93fbb9>.

## Projection

Projection comes in through this module too: exact round-then-saturate projection, direct
encoding, their correctness theorems, and the rounding-direction theorems for the deterministic
modes.

Reference: P3109 Interim Report v4.1 (unapproved draft), §§3.1, 4.7, 4.9–4.16 and 5.2–5.8.
-/

@[expose] public section
