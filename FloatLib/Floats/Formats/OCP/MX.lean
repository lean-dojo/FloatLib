/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.OCP.MX.Configured.Conversion.Runtime
public meta import FloatLib.Floats.Formats.OCP.MX.Configured.Info
public import FloatLib.Floats.Formats.OCP.MX.Configured.Proof
public import FloatLib.Floats.Formats.OCP.MX.E2M1
public import FloatLib.Floats.Formats.OCP.MX.E2M3
public import FloatLib.Floats.Formats.OCP.MX.E3M2
public import FloatLib.Floats.Formats.OCP.MX.E8M0.Automation
public meta import FloatLib.Floats.Formats.OCP.MX.E8M0.Info
public import FloatLib.Floats.Formats.OCP.MX.Standard.Configured.DotProduct.Proof
public import FloatLib.Floats.Formats.OCP.MX.Standard.Configured.Proof

/-!
# OCP microscaling formats

Direct-byte nominal packages for the E2M1, E2M3, and E3M2 scalar element codes used in OCP MX
blocks, together with the E8M0 shared scale and contextual block semantics.
`Standard` supplies the six concrete 32-element MX profiles, exact decoding, and destination
quantization with proved nearest-even rounding at the selected shared scale.
Its dot products accumulate exact rational products across any number of blocks, then round
once to binary32.

## E8M0

Ordinary binary formats, including IEEE, finite-max-NaN, FNUZ, and fully finite encodings, live in
their standard or family packages under `FloatLib.Floats.Formats`.

This import collects the OCP microscaling concepts:

* E8M0 exponent-only scales, which have no sign bit, zero, or fraction;
* block decoding with one shared E8M0 scale;
* concrete 32-element profiles, including fixed-point INT8 with six fractional bits;
* max-binade scale selection and explicit SAT/OVF element conversion policies;
* mixed-profile dot products with exact accumulation and one binary32 projection;
* their exact numerical-system contracts and `numerics` automation; and
* optional `#float_info` inspection metadata.
-/

@[expose] public section
