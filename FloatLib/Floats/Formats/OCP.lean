/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.OCP.FP8.E4M3
public import FloatLib.Floats.Formats.OCP.FP8.E5M2
public import FloatLib.Floats.Formats.OCP.FP8.Overflow
public import FloatLib.Floats.Formats.OCP.MX

/-!
# Open Compute Project numerical formats

The Open Compute Project specifies two 8-bit floats, FP8 E4M3 and E5M2, and the microscaling (MX)
formats, in which a block of narrow elements shares one scale. This module collects our executable
packages for both, and each format is its own nominal type.

## References

* Open Compute Project, *8-bit Floating Point Specification*, revision 1.0,
  <https://www.opencompute.org/documents/ocp-8-bit-floating-point-specification-ofp8-revision-1-0-2023-12-01-pdf-1>.
* Open Compute Project, *OCP Microscaling Formats (MX) Specification, Version 1.0*,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.

Reference: OCP 8-bit Floating Point Specification (OFP8), revision 1.0, §5.1; OCP Microscaling
Formats (MX) Specification v1.0, §§5.1–5.2.
-/

@[expose] public section
