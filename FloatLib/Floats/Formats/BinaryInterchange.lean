/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.BinaryInterchange.Command
public meta import FloatLib.Tactic.FloatInfo.BinaryInterchange.Complex
public meta import FloatLib.Tactic.FloatInfo.BinaryInterchange.Profile
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Homogeneous
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.SquareRoot.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Automation
public import FloatLib.Floats.Formats.BinaryInterchange.Automation.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Automation
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.ErrorBounds
public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Text.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion
public import FloatLib.Floats.Formats.BinaryInterchange.Conversion.Cast.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Cast
public import FloatLib.Floats.Formats.BinaryInterchange.DType.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.DType.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Backends
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Plan.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Rational
public import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Interval
public import FloatLib.Floats.Formats.BinaryInterchange.Interval.Activations
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lanes
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Model.ExactValue
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Instances
public import FloatLib.Floats.Formats.BinaryInterchange.Model.Lean
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Compare.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Accumulation
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.MixedPrecision.Matmul
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Proof.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Directed.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.Agreement
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.NearestAwayAgreement
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.ScaledDyadic
public import FloatLib.Floats.Formats.BinaryInterchange.Semantics
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte
public import FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Status.Runtime

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Binary-interchange formats

Descriptors for sign/exponent/fraction encodings, with exact decoding, directed and status-bearing
arithmetic, software backends, and refinement proofs. The descriptors cover IEEE layouts and
finite-only exceptional-value policies.

`Configured` supplies the `ExecFloat.Binary` API. The descriptor-level `Model` supports bit-level
and mathematical proofs. Scalar conversions and finite reductions are included. Reductions
accumulate the exact sum or dot product and round the final result once.
Square, reciprocal square root, hypotenuse, integer powers, and integer-degree roots also
round once, with real-rounding theorems for conventional IEEE descriptors.
`Model.formatOfAddition`, `formatOfSubtraction`, `formatOfMultiplication`, `formatOfDivision` and
`formatOfFusedMultiplyAdd` are the arithmetic of IEEE 754-2019 §5.4.1 with operands and result
in different formats: one rounding of the exact result into the destination, with flags. In
one format and for finite operands they deliver `add`, `sub`, `mul`, `div` and `fma` in every
rounding direction (`Operations.FormatOf.Homogeneous`).

## References

* IEEE Standard for Floating-Point Arithmetic, IEEE 754-2019,
  <https://doi.org/10.1109/IEEESTD.2019.8766229>.
* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.

## Runtime

Public runtime entry point for the generic kernel (`Model fmt`): layout, the five IEEE rounding
directions and rounding away from zero, exception status, dyadic/rational rounding, arithmetic,
comparisons, format casts, outward-rounded intervals, mixed-precision `mulAcc` / `dotSequential` /
`matmul`, and standard numeric instances.

Elementary functions (`exp`, `log`, `sin`, ...) and `Model.pow` are not on this import. Import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals` (or the model barrel
`BinaryInterchange.Transcendentals`) by name to install `Model.exp`, `Model.pow`, and
`MathFunctions`. These are software approximation kernels without a general accuracy theorem, and
they do not call the host FPU. Opening the scope
`FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath` switches the `MathFunctions`
`exp` and `log` of IEEE descriptors to the correctly rounded `Transcendentals.CorrectlyRounded`
functions. For an IEEE descriptor, `Model.pow` with a finite base and a finite integral exponent
is correctly rounded whenever its result is finite
(`Model.Power.toReal_pow_of_eq_intCast`), and a finite positive base with any other finite exponent
is correctly rounded whenever its certified enclosure search settles
(`Model.Power.pow_spec_of_certified`). Certified `sqrt` and `abs` are available here, but their
`MathFunctions` aliases need the elementary-function import.

## Computing in the kernel

The `KernelPath` modules define the six arithmetic operations in all six rounding directions, their
status flags and those of integral rounding, of rounded rational numbers and of casts, literals,
comparisons, the total order, classification, casts and conversions to integers and to exact
rational values on encodings, with natural-number operations that Lean's kernel accelerates. They
prove each one equal to its reference operation for every descriptor and lift them to configured,
static-byte and descriptor values. The tactic `float_decide` rewrites a goal to these operations
and lets the kernel decide it. `Configured.Recommended.KernelPath` adds, for configured values,
the 22 comparisons of IEEE 754-2019 §5.11, the integral roundings and integer conversions under
their names, `abs`, `copySign` and the eight minimum and maximum operations of §9.6, `nextUp`,
`nextDown` and `remainder` of §5.3.1, `scaleB` and `logB`, the formatOf operations of §5.4.1,
the reductions of §9.4, the augmented operations of §9.5, the payload operations of §9.7, and
`pown`, `rootn`, `rSqrt` and `hypot` of §9.2. `Configured.Text.KernelPath` does the same for the
conversions to and from character sequences, and `DType.KernelPath` and
`Reduction.Schedule.KernelPath` for the integer conversions and the reductions of the
descriptor model.

Import `FloatLib.Floats.ExecFloat` for the universal capability API, or this module for
descriptor-model execution. Import `FloatLib.Floats.Formats.BinaryInterchange.Semantics` for the
descriptor model's real-refinement theorems.
-/

@[expose] public section
