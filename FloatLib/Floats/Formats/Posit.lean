/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module -- shake: keep-all

public meta import FloatLib.Tactic.FloatInfo.Posit
public meta import FloatLib.Tactic.FloatInfo.Posit.Quire
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Dyadic.Runtime
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Add.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Fma.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Mul.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sqrt.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Limb.Packed.Sub.Proof
public import FloatLib.Floats.Formats.Posit.Arithmetic.Spec
public import FloatLib.Floats.Formats.Posit.Arithmetic.Square
public import FloatLib.Floats.Formats.Posit.Arithmetic.Word.Packed.Dyadic.Proof
public import FloatLib.Floats.Formats.Posit.Cast.Widening
public import FloatLib.Floats.Formats.Posit.Configured
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Instances
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Conversion.Runtime
public import FloatLib.Floats.ExecFloat.Conversion.PositIEEE
public import FloatLib.Floats.Formats.Posit.Configured.Real
public import FloatLib.Floats.Formats.Posit.Configured.Projective
public import FloatLib.Floats.Formats.Posit.Quire.Accumulation
public import FloatLib.Floats.Formats.Posit.Quire.Capacity
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Proof
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Conversion.Runtime
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Proof
public import FloatLib.Floats.Formats.Posit.General.Standard
public import FloatLib.Floats.Formats.Posit.Quire.Configured.Views
public import FloatLib.Floats.Formats.Posit.Rounding.Enclosure.Convergence

/-!
# Posit numerical formats

You reach posits through one type, `ExecFloat.Posit (bits := n)`. It is the Posit Standard
(2022) layout at any valid static width, and it runs on the common `ExecFloat` carrier and
capability hierarchy that the other formats share. Every width also comes with an exact
accumulator, `ExecFloat.Posit.Quire (bits := n)`.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*,
  <https://posithub.org/docs/posit_standard-2.pdf>.
* John L. Gustafson, *Standard Posit Arithmetic*, *Supercomputing Frontiers and
  Innovations* 9(1), 2022, <https://doi.org/10.14529/jsfi220102>.

## Other exponent sizes

The Posit Standard (2022) fixes two exponent bits. `Posit.General` is a FloatLib extension
beyond it, on the natural-number encodings that `Posit.KernelPath.Core` computes with: the
values of the codes, their order and the rounding of a result are proved for every number `es`
of exponent bits and every width (`General.value`, `General.value_strictMono`,
`General.encode_value`, `General.encode_between`), and so is every operation of the kernel path
against a specification on values (`General.IsRoundedTo`): the sum, the difference, the
product, the fused multiply-add, the quotient, the square root, literals, the conversions
between formats and to integers, the negation, the absolute value, the comparisons and the
neighbours. `General.Standard` identifies the instance `es = 2` with the standard's model. The
public types, the quire and the elementary functions stay at `es = 2`.

## Arithmetic

This module exposes the exact specifications of the six universal arithmetic operations, along
with the certified exact-dyadic, native-word, and two-limb rounding backends. Picking a backend
for a static width happens under `Posit.Configured`. `square` gets no kernel of its own, because it
reuses the selected multiplication kernel and its refinement theorem.

Reference: Standard for Posit Arithmetic (2022), §§3.1–3.4.
-/

@[expose] public section
