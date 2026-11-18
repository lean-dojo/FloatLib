/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.OCP.MX.Configured
public meta import FloatLib.Tactic.FloatInfo.OCP.MX.E8M0
public import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.OCP.MX.Configured.Proof
public import FloatLib.Floats.Formats.OCP.MX.E2M1
public import FloatLib.Floats.Formats.OCP.MX.E2M3
public import FloatLib.Floats.Formats.OCP.MX.E3M2
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Automation
public import FloatLib.Floats.Formats.OCP.MX.Standard.Conversion
public import FloatLib.Floats.Formats.OCP.MX.Standard.ErrorBounds
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Semantics
public import FloatLib.Floats.Formats.OCP.MX.Standard.Format
public import FloatLib.Floats.Formats.OCP.MX.Standard.Compiled
public import FloatLib.Floats.Formats.OCP.MX.Standard.KernelPath

/-!
# OCP microscaling formats

In OCP MX, a block of 32 narrow elements shares one scale. Here you'll find the one-byte element
types `E2M1`, `E2M3`, and `E3M2`, the E8M0 shared scale, and `Standard.format`, which makes the six
concrete MX profiles instances of the general block-scaled format of
`FloatLib.Floats.Formats.Block`.
Quantization with proved nearest-even rounding at the selected scale, exact decoding, and dot
products that accumulate exactly and round once are the general operations of that module.

## E8M0

Ordinary binary formats, including IEEE, finite-max-NaN, FNUZ, and fully finite encodings, live in
their standard or family packages under `FloatLib.Floats.Formats`.

This import collects the OCP microscaling concepts:

* E8M0 exponent-only scales, which have no sign bit, zero, or fraction
* the element codecs of the six profiles, including fixed-point INT8 with six fractional bits,
  with the SAT and OVF element conversion policies
* the E8M0 scale codec with max-binade scale selection
* their exact numerical-system contracts and `numerics` automation
* optional `#float_info` inspection metadata

Reference: OCP Microscaling Formats (MX) Specification v1.0, §§5.1–5.4 and 6.3.
-/

@[expose] public section
