/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Carrier
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics

/-!
# Configured E8M0 identity

E8M0 is an exponent-only shared scale with no sign and no fraction, so it doesn't fit the scalar
floating-point layout. It gets its own family on the common `ExecFloat` carrier and keeps its
complete encoding there. A block that stores an E8M0 scale with its elements is a stored tensor of
the general block format, `ExecFloat.Block (Standard.format group profile)`.

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
  /-- The only value: the family names a format in types and carries no data. -/
  | format

instance : EncodedFormat Family where
  Code := Formats.OCP.MX.E8M0
  Scalar := Numerics.Dyadic

instance : FormatSemantics Family where
  denote scale := Formats.OCP.MX.E8M0.numericalSystem.denote scale

end E8M0

/-- OCP E8M0 exponent-only shared scale on the common executable carrier. -/
abbrev E8M0 := FloatLib.Floats.ExecFloat E8M0.Family

end ExecFloat.OCP.MX
end FloatLib.Floats
