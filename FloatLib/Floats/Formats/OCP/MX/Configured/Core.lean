/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Block
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics

/-!
# Configured OCP MX identities

E8M0 is an exponent-only shared scale, not a scalar floating-point layout. An MX block jointly
stores that scale with an array of binary element words. Both families use the common `ExecFloat`
carrier while retaining their complete encodings.

## References

* Open Compute Project, *OCP Microscaling Formats (MX) Specification, Version 1.0*:
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
* ONNX, *E8M0 technical specification*:
  <https://onnx.ai/onnx/technical/float8.html#e8m0>.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange

namespace ExecFloat.OCP.MX

namespace E8M0

/-- Type-level identity of the OCP E8M0 exponent-only scale encoding. -/
inductive Family where
  | format

instance : EncodedFormat Family where
  Code := Formats.OCP.MX.E8M0
  Scalar := Numerics.Dyadic

instance : FormatSemantics Family where
  denote scale := Formats.OCP.MX.E8M0.numericalSystem.denote scale

end E8M0

/-- OCP E8M0 exponent-only shared scale on the common executable carrier. -/
abbrev E8M0 := FloatLib.Floats.ExecFloat E8M0.Family

namespace Block

/-- Type-level identity of an E8M0-scaled block with one binary element descriptor. -/
inductive Family (format : FloatFormat) where
  | format

instance (format : FloatFormat) : EncodedFormat (Family format) where
  Code := Formats.OCP.MX.BlockCode format
  Scalar := Array Numerics.Dyadic

instance (format : FloatFormat) : FormatSemantics (Family format) where
  denote block := (Formats.OCP.MX.blockSystem format).denote block

end Block

/-- Runtime-sized E8M0-scaled block with the selected binary element descriptor. -/
abbrev Block (format : FloatFormat) :=
  FloatLib.Floats.ExecFloat (Block.Family format)

end ExecFloat.OCP.MX
end FloatLib.Floats
