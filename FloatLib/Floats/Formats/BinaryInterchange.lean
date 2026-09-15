/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Lean
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Accumulation
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Matmul
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Activations
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Automation
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Automation
public meta import FloatLib.Floats.Formats.BinaryInterchange.Complex.Info
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte
public import FloatLib.Floats.Formats.BinaryInterchange.Interval
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Agreement
public meta import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public meta import FloatLib.Floats.Formats.BinaryInterchange.Info.Command

/-!
# Binary-interchange formats

Descriptors for sign/exponent/fraction encodings, with exact decoding, directed and status-bearing
arithmetic, software backends, and refinement proofs. The descriptors cover IEEE layouts and
finite-only exceptional-value policies.

`Configured` supplies the `ExecFloat.Binary` API. The descriptor-level `Model` supports bit-level
and mathematical proofs. Scalar conversions and finite reductions are included; reductions
accumulate the exact sum or dot product and round the final result once.

## References

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.

## Runtime

Public runtime entry point for the generic kernel (`Model fmt`): layout, the four implemented
IEEE rounding modes,
exception status, dyadic/rational rounding, arithmetic, comparisons, format casts,
outward-rounded intervals, mixed-precision `mulAcc` / `dotSequential` / `matmul`, and
standard numeric instances.

Elementary functions (`exp`, `log`, `sin`, ...) and `Model.pow` are not on this import.
Import `FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` (or the
model barrel `BinaryInterchange.Transcendentals`) by name to install `Model.exp`,
`Model.pow`, and `MathFunctions`. These are software approximation kernels without a general
accuracy theorem; they do not call the host FPU. Certified `sqrt` and `abs` are available here;
their `MathFunctions` aliases require the elementary-function import.

Import `FloatLib.Floats.ExecFloat` for the universal capability API, or this module directly for
descriptor-model execution. Import `FloatLib.Floats.Formats.BinaryInterchange.Semantics` for the
descriptor model's real-refinement theorems.
-/

@[expose] public section
