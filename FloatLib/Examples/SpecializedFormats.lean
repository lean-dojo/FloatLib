/-
Copyright (c) 2026 FloatLib
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

Not every quantity is best stored as a float. If our values are always powers of ten, a
logarithmic number multiplies exactly. If a layer only ever holds `-1` and `+1`, a one-bit codebook
is enough. If four neighbouring lanes share a magnitude, one exponent can serve all of them, which
is what a shared-scale block and an OCP MX block do. Each section below constructs such a value,
computes with it, and decodes the result.

`BasicOperations` introduces the ordinary scalar interface; each representation here has its own
operations.
-/

@[expose] public section

namespace FloatLib.Examples.SpecializedFormats

open FloatLib.Floats
open FloatLib.Numerics

/-! ## Exact logarithmic multiplication -/

/-- Zero and signed integral powers of ten. -/
private abbrev DecimalPower :=
  ExecFloat.Logarithmic decimalRadix

private def hundred : DecimalPower :=
  ExecFloat.Logarithmic.ofSignExponent false 2

private def negativeTenth : DecimalPower :=
  ExecFloat.Logarithmic.ofSignExponent true (-1)

private def logarithmicProduct : DecimalPower :=
  hundred * negativeTenth

private def logarithmicCode : Formats.Logarithmic.Code decimalRadix :=
  ExecFloat.Logarithmic.toCode logarithmicProduct
-- Code.value true 1

/-
The Boolean selects the sign, `false` positive and `true` negative, and the integer is the exponent
of ten. Multiplication combines the signs and adds the exponents, so `100 * (-0.1)` is exactly
`-10`: a negative sign and exponent 1. No rounding can occur in a product of two such values.
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

/-- Four rational lanes sharing one caller-selected binary exponent. -/
private abbrev Block4 :=
  ExecFloat.SharedScale 4

private def blockInput : Vector Rat 4 :=
  ⟨#[1, 3 / 2, -2, 3 / 8], by decide⟩

private def quantizedBlock : Block4 :=
  ExecFloat.SharedScale.quantizeAt (-2) blockInput

private def sharedScaleReport : Int × Array Int × Array Rat :=
  (ExecFloat.SharedScale.exponent quantizedBlock,
    (ExecFloat.SharedScale.significands quantizedBlock).toArray,
    (ExecFloat.SharedScale.decode quantizedBlock).toArray)
-- (-2, #[4, 6, -8, 2], #[1, 3/2, -2, 1/2])

/-
The lane count is part of the type, so building the input vector includes a proof of its length.
Exponent `-2` puts every lane on a grid with spacing `2^-2 = 1/4`; the integer coefficients are the
inputs divided by that spacing. The first three inputs sit on the grid. The last, `3/8`, is halfway
between `1/4` and `1/2`, and ties-to-even chooses the even coefficient 2, so it decodes as `1/2`.
-/

/-! ## Combine an E8M0 scale with E2M1 elements -/

open FloatLib.Floats.Formats.BinaryInterchange

/-- An E8M0 scale representing multiplication by two. -/
private def scaleTwo : ExecFloat.OCP.MX.E8M0 :=
  ExecFloat.OCP.MX.E8M0.ofExponentSaturating 1

private abbrev MXElement :=
  ExecFloat Formats.OCP.MX.E2M1

private def elementValues : Array MXElement :=
  #[1, -1]

private def mxBlock : ExecFloat.OCP.MX.Block FloatFormat.e2m1 :=
  ExecFloat.OCP.MX.Block.ofElements scaleTwo elementValues

private def mxValues : Option (Array Numerics.Dyadic) :=
  ExecFloat.OCP.MX.Block.decode? mxBlock
-- some #[{ negative := false, significand := 2, exponent := 0 },
--        { negative := true, significand := 2, exponent := 0 }]

private def mxRationals : Option (Array Rat) :=
  mxValues.map fun values => values.map (·.toRat)
-- some #[2, -2]

/-
The elements are stored unscaled as E2M1 values `1` and `-1`; the shared E8M0 scale is applied
during block decoding, which is why both decoded dyadics are `±2`. Decoding returns `none` when the
shared scale is the exceptional E8M0 code, so a block is either entirely finite or entirely
undefined.
-/

end FloatLib.Examples.SpecializedFormats
