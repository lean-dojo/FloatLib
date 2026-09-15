/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public import FloatLib.Floats.Formats.Posit.Arithmetic.Spec
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Add.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sub.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Mul.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sqrt.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Fma.Proof
public import FloatLib.Floats.Formats.Posit.Cast.Widening
public import FloatLib.Floats.Formats.Posit.Configured
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.Posit.Configured.Projective
public import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Convergence
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Views
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Capacity
public import FloatLib.Floats.Formats.Posit.Quire.Accumulation
public meta import FloatLib.Floats.Formats.Posit.Quire.Info
public meta import FloatLib.Floats.Formats.Posit.Info

/-!
# Posit numerical formats

The public entry point is `ExecFloat.Posit (bits := n)`. It denotes the Posit Standard (2022)
layout at any valid static width and uses the common `ExecFloat` carrier and capability hierarchy.
Its associated exact accumulator is `ExecFloat.Posit.Quire (bits := n)`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*,
  <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, *Supercomputing Frontiers and
  Innovations* 9(1), 2022, <https://doi.org/10.14529/jsfi220102>.

## Arithmetic

This module exposes the exact specifications for the six universal arithmetic
operations. Certified exact-dyadic, native-word, and two-limb rounding backends are exposed here;
static selection lives under `Posit.Configured`.
-/

@[expose] public section
