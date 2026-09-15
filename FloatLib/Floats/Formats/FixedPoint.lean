/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.FixedPoint.Automation
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Automation
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Proof
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Core
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Proof
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Info
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.FixedPoint.Configured.Instances
public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Info
public meta import FloatLib.Floats.Formats.FixedPoint.Configured.Info
public meta import FloatLib.Floats.Formats.FixedPoint.Exact.Info
public meta import FloatLib.Numerics.Capabilities.Radix

/-!
# Radix-parametric fixed-point formats

This is the public entry point for exact and fixed-width fixed-point arithmetic. It exports the
unbounded exact model, the common configured `ExecFloat.FixedPoint` carrier, explicit bounded
overflow policies, numerical automation, and `#float_info` support.

The exact and bounded submodules remain independently importable for internal developments.

## References

* ISO/IEC, *Programming languages, C, Extensions to support embedded processors*,
  ISO/IEC TR 18037:2008.
-/

@[expose] public section
