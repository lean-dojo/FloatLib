/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Block
public import FloatLib.Floats.Formats.Codebook
public import FloatLib.Floats.Formats.Logarithmic
public import FloatLib.Floats.Formats.OCP.MX

/-!
# Specialized formats

Not every quantity is best stored as a float. If our values are always powers of ten, a logarithmic
number multiplies exactly. If a layer only ever holds `-1` and `+1`, a one-bit codebook is enough.
If four neighbouring lanes share a magnitude, one exponent can serve all of them, which is what a
shared-scale block and an OCP MX block do: both are instances of one block format. Each section
below constructs such a value, computes with
it, and decodes the result.

`BasicOperations` introduces the ordinary scalar interface, and each representation here has its own
operations.
-/

-- These runnable examples intentionally keep their helper values private.
set_option linter.privateModule false

@[expose] public section

namespace FloatLib.Examples.SpecializedFormats

open FloatLib.Floats
open FloatLib.Numerics

/-! ## Exact logarithmic multiplication -/

/-- Zero and signed integral powers of ten. -/
private abbrev DecimalPower :=
  ExecFloat.Logarithmic decimalRadix

private def hundred : DecimalPower :=
  .ofExponent 2

private def negativeTenth : DecimalPower :=
  .ofExponent (-1) (negative := true)

private def logarithmicProduct : DecimalPower :=
  hundred * negativeTenth

private def logarithmicCode : Formats.Logarithmic.Code decimalRadix :=
  ExecFloat.Logarithmic.toCode logarithmicProduct
-- Code.value true 1

/-
`.ofExponent e` is `10 ^ e`, and `(negative := true)` makes it negative. Multiplication combines
the signs and adds the exponents, so `100 * (-0.1)` is exactly `-10`: a negative sign and
exponent 1. No rounding can occur in a product of two such values.
-/

/-! ## Finite codebook arithmetic -/

/-- A one-bit table whose two words denote negative and positive one. -/
private abbrev Bipolar :=
  ExecFloat.Codebook Formats.Codebook.Catalog.bipolar1

private def bipolarProduct : Bipolar :=
  ExecFloat.Codebook.Catalog.bipolar1.negativeOne *
    ExecFloat.Codebook.Catalog.bipolar1.positiveOne

private def bipolarMeaning : NumericalValue Int :=
  ExecFloat.Codebook.decode bipolarProduct
-- NumericalValue.finite (-1)

/-
A codebook is a finite set of values with lookup tables for the operations it supports. The
multiplication table sends the pair `(-1, +1)` to the word for `-1`, and decoding reads that word
back as the integer.
-/

/-! ## A generic shared-scale block -/

/-- Four lanes of unbounded integers sharing one binary exponent. -/
private abbrev Block4 :=
  ExecFloat.Block (Formats.Block.sharedScale (Fin 4))

private def blockInput : Vector Rat 4 :=
  ⟨#[1, 3 / 2, -2, 3 / 8], by decide⟩

/-- Quantize at the exponent `-2`, which the caller selects. -/
private def quantizedBlock : Block4 :=
  ExecFloat.Block.quantize _ (Formats.Block.sharedExponent (Fin 4) (-2)) fun lane =>
    SignedRat.ofRat blockInput[lane]

private def sharedScaleReport : Int × Array Int × Array Rat :=
  (quantizedBlock.toCode.scales.1 (),
    Array.ofFn quantizedBlock.toCode.elements,
    Array.ofFn quantizedBlock.value)
-- (-2, #[4, 6, -8, 2], #[1, 3/2, -2, 1/2])

/-
The shared-scale block is the general block format with integer elements and one power-of-two
scale that the caller supplies. Exponent `-2` puts every lane on a grid with spacing `2^-2 = 1/4`,
and the integer coefficients are the inputs divided by that spacing. The first three inputs sit on
the grid. The last, `3/8`, is halfway between `1/4` and `1/2`, and ties-to-even chooses the even
coefficient 2, so it decodes as `1/2`.
-/

/-! ## Combine an E8M0 scale with E2M1 elements -/

open FloatLib.Floats.Formats.OCP.MX

/-- An MXFP4 block of two elements: the scale `2 ^ 1` and the E2M1 words of `1` and `-1`. -/
private def mxBlock : Formats.Block.Tensor (Standard.format (fun _ : Fin 2 => ()) .e2m1) where
  scales := (fun _ => E8M0.ofExponentSaturating 1, ())
  elements lane := if lane = 0 then 2#4 else 10#4

private def mxValues : Array (NumericalValue SignedRat) :=
  Array.ofFn mxBlock.decode
-- #[NumericalValue.finite 2, NumericalValue.finite -2]

private def mxRationals : Array Rat :=
  Array.ofFn mxBlock.value
-- #[2, -2]

/-
The elements are stored unscaled as the E2M1 words of `1` and `-1`. The shared E8M0 scale is
applied during decoding, which is why both decoded values are `±2`. A block whose scale is the
exceptional E8M0 code decodes to NaN at every position, and an element infinity or NaN of an FP8
profile is kept under a finite scale, so each position has its own class.
-/

end FloatLib.Examples.SpecializedFormats
