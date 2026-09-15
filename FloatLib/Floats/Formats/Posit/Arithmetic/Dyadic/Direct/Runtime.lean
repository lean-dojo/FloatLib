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

Direct posit arithmetic combines shared exact-dyadic operand decoding and integer arithmetic
with construction of the standard regime/exponent/fraction stream. It is the width-generic
executable tier used after fixed packed storage ends.

Division uses a destination-width quotient prefix, one exact remainder test, and direct
guard/sticky packing. Square root uses one destination-width integer-root prefix and one exact
square-remainder sticky bit. Refinement theorems live in `Direct.Proof`.
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
