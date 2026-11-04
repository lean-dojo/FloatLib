/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Quotient.Direct.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.SquareRoot.Direct.Runtime

/-!
# Direct arbitrary-width exact-dyadic posit arithmetic

Once a posit is too wide for packed fixed-width storage, its arithmetic runs here, at any width.
These kernels decode the operands to exact dyadics with the shared decoder, do integer arithmetic,
and build the standard regime/exponent/fraction stream of the result.

Division computes a quotient prefix of the destination width, runs one exact remainder test,
and gives the guard and sticky bits to the direct packer. Square root works the same way with an
integer-root prefix of the destination width, and its sticky bit comes from one exact test of the
square remainder. `Direct.Proof` has the refinement theorems.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.DirectDyadicArithmetic

variable {format : Format}

/-- Exact dyadic addition followed by certified direct result packing. -/
@[noinline] def add (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      DirectDyadicPacking.round format
        (FloatLib.Numerics.Dyadic.add leftValue rightValue)
  | _, _ =>
      nar format

/-- Exact dyadic subtraction followed by certified direct result packing. -/
@[noinline] def sub (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      DirectDyadicPacking.round format
        (FloatLib.Numerics.Dyadic.sub leftValue rightValue)
  | _, _ =>
      nar format

/-- Exact integer multiplication followed by certified direct result packing. -/
@[noinline] def mul (left right : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic? with
  | some leftValue, some rightValue =>
      DirectDyadicPacking.round format
        (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
  | _, _ =>
      nar format

/--
Apply the shared quotient-prefix kernel to two already-decoded operands.

Keeping exceptional-value dispatch at this boundary lets every storage representation reuse the
same division implementation after supplying its proved decoder.
-/
@[always_inline, inline] def divDecoded
    (format : Format)
    (numerator denominator : Option FloatLib.Numerics.Dyadic) :
    Model format :=
  match numerator, denominator with
  | some numerator, some denominator =>
      DirectDyadicQuotient.round format numerator denominator
  | _, _ =>
      nar format

/--
Correctly rounded division using one destination-width quotient prefix and exact remainder
rounding.
-/
@[noinline] def div (left right : Model format) : Model format :=
  divDecoded format left.toDyadic? right.toDyadic?

/-- Correctly rounded square root using one integer-root prefix and exact sticky bit. -/
@[noinline] def sqrt (value : Model format) : Model format :=
  match value.toDyadic? with
  | none =>
      nar format
  | some radicand =>
      if radicand.isLess FloatLib.Numerics.Dyadic.zero then
        nar format
      else
        DirectDyadicSquareRoot.round format radicand

/-- Exact fused multiply-add with one certified direct final packing step. -/
@[noinline] def fma (left right addend : Model format) : Model format :=
  match left.toDyadic?, right.toDyadic?, addend.toDyadic? with
  | some leftValue, some rightValue, some addendValue =>
      DirectDyadicPacking.round format
        (FloatLib.Numerics.Dyadic.add
          (FloatLib.Numerics.Dyadic.mul leftValue rightValue)
          addendValue)
  | _, _, _ =>
      nar format

end FloatLib.Floats.Formats.Posit.Model.DirectDyadicArithmetic
