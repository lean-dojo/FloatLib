/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.Block.SharedScale.Proof
public import FloatLib.Floats.Formats.Block.Configured.Proof
public import FloatLib.Floats.Formats.Block.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Block.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Block.Configured.Conversion.Instances
public meta import FloatLib.Floats.Formats.Block.Configured.Info
public meta import FloatLib.Floats.Formats.Block.SharedScale.Info

/-!
# Contextual and block-scaled numerical formats

Block formats assign runtime codes and scalar meanings to whole blocks.

## References

* Open Compute Project, *OCP Microscaling Formats (MX) Specification, Version 1.0*,
  <https://www.opencompute.org/documents/ocp-microscaling-formats-mx-v1-0-spec-final-pdf>.
-/

@[expose] public section
