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
public import FloatLib.Floats.Formats.FixedPoint.Display
public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Info
public meta import FloatLib.Floats.Formats.FixedPoint.Configured.Info
public meta import FloatLib.Floats.Formats.FixedPoint.Exact.Info
public meta import FloatLib.Numerics.Capabilities.Radix

/-!
# Radix-parametric fixed-point formats

A fixed-point number is an integer coefficient read at a fixed scale. With radix 10 and two
fractional digits, the coefficient `314` means `3.14`. This module is the public entry point for
both kinds the library has: the unbounded exact model, where no operation rounds or overflows, and
fixed-width words with a named overflow policy. It exports those, the common configured
`ExecFloat.FixedPoint` carrier, numerical automation, and `#float_info` support.

For work inside the library, the exact and bounded submodules can also be imported on their own.

## References

* ISO/IEC, *Programming languages, C, Extensions to support embedded processors*,
  ISO/IEC TR 18037:2008.
-/

@[expose] public section
