/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Floats.ExecFloat.Instances
public import FloatLib.Floats.Formats.Posit.Configured.Functions.Basic
public import FloatLib.Floats.Formats.Posit.Configured.Functions.IntegerProof
public import FloatLib.Floats.Formats.Posit.Configured.Algebraic.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Algebraic.RationalPower.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Integer.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Integer.Unsigned.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Logarithm.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Elementary.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Hyperbolic.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Pi.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Trigonometric.Atan2.Proof
public import FloatLib.Floats.Formats.Posit.Formatting.Configured.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Plan.Dispatch
public import FloatLib.Floats.Formats.Posit.Configured.Value.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Type
public import FloatLib.Floats.Formats.Posit.Configured.Instances
public import FloatLib.Floats.Formats.Posit.Configured.Interval

/-!
# Configured posit `ExecFloat` values

Import this module to define a standard posit by its total encoded width:

```lean
abbrev P32 := ExecFloat.Posit (bits := 32)
```

Every configured posit is an ordinary `ExecFloat` value, uses a statically selected
carrier, and exposes its exact semantics through the common proof infrastructure.

`Configured.Type` owns the public type constructor, the modules below `Configured.Storage` own
packed-carrier selection and codecs, and `Configured.Plan.Dispatch` installs certified operation
backends. The value-facing implementation is separated further:

* `Configured.Value.Runtime` provides packing, decoding, classification, and raw-word conversion;
* `Configured.Instances` installs comparison, display, literals, and negation;
* `Configured.Value.Proof` proves round trips, special-value semantics, and comparison laws.

Raw words are deliberately lower-level than ordinary numeric construction. They are useful for
serialization, conformance vectors, and encoding proofs; arithmetic clients should use numeric
literals and the operation interface once the corresponding certified capability is imported.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, Supercomputing Frontiers and Innovations 9(1),
  2022, <https://doi.org/10.14529/jsfi220102>.
-/
