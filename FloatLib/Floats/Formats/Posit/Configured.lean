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

Import this module to use posits. The standard widths are `Posit8`, `Posit16`, `Posit32`, and
`Posit64`, and you get any other width by giving its total encoded width:

```lean
def x : Posit32 := 1.5
def y : ExecFloat.Posit (bits := 12) := 0.75
```

Both are ordinary `ExecFloat` values. Each width gets a carrier chosen statically, and its exact
semantics go through the same proof infrastructure as every other format.

`Configured.Type` owns the public type constructor, the modules below `Configured.Storage` choose
the packed carrier and its codecs, and `Configured.Plan.Dispatch` installs the certified operation
backends. The value layer is split three ways:

* `Configured.Value.Runtime` provides packing, decoding, classification, and raw-word conversion.
* `Configured.Instances` defines `ofRat` and installs comparison, display, literals, and negation.
* `Configured.Value.Proof` proves round trips, special-value semantics, and comparison laws.

Raw words sit deliberately below ordinary numeric construction. We keep them for serialization,
conformance vectors, and encoding proofs. If you are doing arithmetic, build values from numeric
literals or `.ofRat q`, import the certified capability you need, and use the operation interface.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, Supercomputing Frontiers and Innovations 9(1),
  2022, <https://doi.org/10.14529/jsfi220102>.
-/
