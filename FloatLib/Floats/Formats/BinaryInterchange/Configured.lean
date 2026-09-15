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
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Operations.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Parsing
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Formatting
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

Import this module to define a binary format by its exponent and fraction widths:

```lean
ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
```

`Configured.Type` owns the public type constructor, the modules below `Configured.Storage` own
packed-carrier selection and codecs, and `Configured.NativeDispatch` plus
`Configured.Plan.Instances` install certified operation backends. The value-facing implementation
is separated further:

* `Configured.Value.Core` provides packing, decoding, classification, and special values without
  importing arithmetic dispatch;
* `Configured.Value.CoreProof` proves lossless model and bit-pattern round trips;
* `Configured.Classification` connects the ten value classes to their exact numerical meaning;
* `Configured.Instances` installs comparison, display, literals, and negation;
* `Configured.Rounding.Runtime` exposes all six primitive operations with an explicit IEEE
  direction, while `Configured.Rounding.Proof` supplies their contracts;
* `Configured.Comparison` provides quiet and signaling predicates with explicit exception flags;
* `Configured.TotalOrder` orders complete representations, including zero signs and NaN metadata;
* `Configured.Operations.Runtime` exposes integral rounding, scaling, exponent, adjacency, and
  sign tools, while `Configured.Operations.Proof` supplies their contracts;
* `Configured.Parsing` accepts exact decimal and radix-two character input without a host float;
* `Configured.Formatting` writes decimal or hexadecimal text at exact or requested precision;
  the text conversion proofs establish rounding bounds and exact round trips; and
* `Configured.Reduction` provides exact accumulation with one final rounding.

`Configured.Transcendentals` is a named import, not part of this module: it lifts the
deterministic elementary-function kernels to this type. `import FloatLib` does not install
`ExecFloat.Binary.exp`, `Model.exp`, `Model.pow`, or the binary `MathFunctions` instances.

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
2. This module chooses a certified kernel independently for each operation.

The implementation is split by responsibility:

* `Estimates` decorates arithmetic costs with carrier adaptation.
* `NativeCandidates` names the fixed-format certificates for binary32 and binary64.
* `Routes` recognizes structural word, fixed-format, and fixed-limb eligibility.
* `Candidates` packages structural routes and the generic kernel with pointwise refinement proofs.
* `WideLimbCandidates` certifies the wide-limb kernels on the limb carrier of formats wider than
  128 bits.
* `Automatic` adds the direct byte-table and wide-limb fast paths after dependent elimination of
  the selected carrier.
* `Instances` installs the resulting operation capabilities.
* `Proof` relates first-order entry points to policy-selected certificates.

All selection is structural. Word and pair kernels advertise explicit descriptor capabilities;
layout-specific implementations remain specialized without testing catalogued format names.
Every supported descriptor retains the generic kernel as a fallback.
-/
