/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.CoreProof
public import FloatLib.Floats.Formats.BinaryInterchange.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Classification.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Square
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Algebraic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Formatting
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Interval
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.PrecisionProof
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.DecimalFormattingProof
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Text.Roundtrip
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeDispatch
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
public meta import FloatLib.Floats.ExecFloat.Instances

/-!
# Configured binary values and literals

Import this module to use binary formats. The standard formats are `Binary16`, `BFloat16`,
`Binary32`, `Binary64`, `Binary128`, and `Binary256`. Any other format is selected by its exponent
and fraction widths:

```lean
def x : Binary32 := 1.5
def y : ExecFloat.Binary (exponentBits := 7) (fractionBits := 16) := 0.75
```

`Configured.Type` owns the public type constructor, the modules below `Configured.Storage` own
packed-carrier selection and codecs, and `Configured.NativeDispatch` plus
`Configured.Plan.Instances` install certified operation backends. The value-facing implementation
is separated further:

* `Configured.Value.Core` provides packing, decoding, classification, special values, and the
  format constants `minNormal`, `minSubnormal`, `epsilon`, and `ulp` without importing arithmetic
  dispatch;
* `Configured.Value.CoreProof` proves lossless model and bit-pattern round trips;
* `Configured.Classification` connects the ten value classes to their exact numerical meaning;
* `Configured.Real` reads a value as a real number with `toReal` and `toReal?`, and states the
  rounding contract and half-ulp error of `+`, `-`, `*`, `/`, and square root on the type;
* `Configured.Instances` installs comparison, display, literals, and negation;
* `Configured.Rounding.Runtime` exposes all six primitive operations and `ofRat`, rounding an
  exact rational, with an IEEE direction argument and `IEEEOutcome.bind` to chain their statuses,
  while `Configured.Rounding.Proof` supplies their contracts and the decoding theorems for `+`,
  `-`, `*`, `/`, and negation;
* `Configured.Comparison` provides quiet and signaling predicates that return their exception
  flags;
* `Configured.TotalOrder` orders complete representations, including zero signs and NaN metadata;
* `Configured.Operations.Runtime` exposes integral rounding, `toInt?`, scaling, exponent,
  adjacency, and sign tools, while `Configured.Operations.Proof` supplies their contracts;
* `Configured.Square` reuses the certified multiplication kernels for a single operand;
* `Configured.Algebraic` provides reciprocal square root, hypotenuse, integer powers, and
  integer-degree roots, with one final nearest-even rounding;
* `Configured.Parsing` accepts exact decimal and radix-two character input without a host float;
* `Configured.Formatting` writes decimal or hexadecimal text at exact or requested precision,
  and the text conversion proofs establish rounding bounds and exact round trips;
* `Configured.Reduction` provides exact accumulation with one final rounding and error bounds
  for trees of separately rounded additions; and
* `Configured.Interval` provides outward-rounded intervals with configured endpoints, reusing
  the model interval arithmetic and enclosure proofs.

`Configured.Transcendentals` is a named import, not part of this module: it lifts the
deterministic elementary-function kernels and the power to this type, with `certify := true` for
correctly rounded results. `import FloatLib` does not install `ExecFloat.Binary.exp`,
`ExecFloat.Binary.pow`, `Model.exp`, `Model.pow`, or the binary `MathFunctions` instances.

Natural and scientific literals are rounded once from exact rationals into the destination
format. They never pass through Lean's host `Float`, C `double`, or an IEEE bit-pattern parser.

Import `FloatLib.Floats.Formats.BinaryInterchange.Info.Command` when `#float_info` is also
required.

## References

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019, Sections 3.4 and 4.3.1,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* Lean scientific literal elaboration,
  <https://lean-lang.org/doc/reference/latest/Terms/Numeric-Literals/>.

## Plan

Configured formats make two static decisions:

1. `StoragePlan` chooses the persistent carrier from encoded width.
2. The `Configured.Plan` modules choose a certified kernel independently for each operation.

The implementation is split by responsibility:

* `Estimates` decorates arithmetic costs with carrier adaptation.
* `NativeCandidates` names the fixed-format certificates for binary32 and binary64.
* `Descriptor.Plan.Routes` recognizes structural word, fixed-format, and fixed-limb eligibility.
* `Candidates` packages structural routes and the generic kernel with pointwise refinement proofs.
* `WideLimbCandidates` certifies the wide-limb kernels on the limb carrier of formats wider than
  128 bits.
* `Automatic` adds the direct byte-table and wide-limb fast paths after dependent elimination of
  the selected carrier.
* `Instances` installs the resulting operation capabilities.
* `FirstOrder` relates first-order entry points to policy-selected certificates.

All selection is structural. Word and pair kernels declare which descriptors they serve, so
layout-specific implementations are specialized without testing catalogued format names. Every
supported descriptor keeps the generic kernel as a fallback.
-/
