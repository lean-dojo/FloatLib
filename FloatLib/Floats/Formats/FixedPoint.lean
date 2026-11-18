/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Numerics.Capabilities.Radix
public meta import FloatLib.Tactic.FloatInfo.FixedPoint.Bounded
public meta import FloatLib.Tactic.FloatInfo.FixedPoint.Bounded.Configured
public meta import FloatLib.Tactic.FloatInfo.FixedPoint.Configured
public meta import FloatLib.Tactic.FloatInfo.FixedPoint.Exact
public import FloatLib.Floats.Formats.FixedPoint.Automation
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Automation
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Configured.Proof
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Core
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Semantics.Proof
public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.FixedPoint.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.FixedPoint.Configured.Instances
public import FloatLib.Floats.Formats.FixedPoint.Display
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Examples
public import FloatLib.Floats.Formats.FixedPoint.Embedded.Roundoff
public import FloatLib.Floats.Formats.FixedPoint.Exact.Proof

/-!
# Radix-parametric fixed-point formats

A fixed-point number is an integer coefficient read at a fixed scale. With radix 10 and two
fractional digits, the coefficient `314` means `3.14`. This module is the public entry point for
the unbounded exact model, where no operation rounds or overflows, fixed-width words with a named
overflow policy, and the signed/unsigned `_Fract` and `_Accum` value families of N1169. It exports
those, the common configured `ExecFloat.FixedPoint` carrier, numerical automation, and
`#float_info` support. The `Embedded` family implements N1169's round-then-overflow rules and
usual fixed-point conversions independently of host ABI widths.

For work inside the library, the exact and bounded submodules can also be imported on their own.

## References

* WG14 N1169, *Programming languages, C, Extensions to support embedded processors*,
  draft labelled ISO/IEC TR 18037:2006(E), §4.1 and C 7.18a.
-/

@[expose] public section
