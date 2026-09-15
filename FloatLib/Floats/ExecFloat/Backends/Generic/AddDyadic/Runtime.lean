/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Executable signed-magnitude dyadic addition

Exact dyadic addition uses separate signs and natural-number magnitudes. Correctness proofs and
the compiler substitution live in `AddDyadic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Add two nonzero signed magnitudes at a shared dyadic exponent. -/
@[inline] def addDyadicMagnitudes
    (leftSign rightSign : Bool) (left right : Nat) (exponent : Int) : Numerics.Dyadic :=
  if leftSign == rightSign then
    { negative := leftSign, significand := left + right, exponent := exponent }
  else if left == right then
    { negative := leftSign && rightSign, significand := 0, exponent := 0 }
  else if left < right then
    { negative := rightSign, significand := right - left, exponent := exponent }
  else
    { negative := leftSign, significand := left - right, exponent := exponent }

/--
Exact dyadic addition using separate signs and natural-number magnitudes.

Zero operands are handled before alignment. For two nonzero operands, the significand with the
larger exponent is shifted to the smaller exponent before the magnitudes are combined. No
rounding occurs here.
-/
@[inline] def addDyadicImpl (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  if a.significand == 0 then
    if b.significand == 0 then
      { negative := a.negative && b.negative, significand := 0, exponent := 0 }
    else
      b
  else if b.significand == 0 then
    a
  else if a.exponent ≤ b.exponent then
    let shift := Int.toNat (b.exponent - a.exponent)
    addDyadicMagnitudes a.negative b.negative a.significand
      (Nat.shiftLeft b.significand shift) a.exponent
  else
    let shift := Int.toNat (a.exponent - b.exponent)
    addDyadicMagnitudes a.negative b.negative
      (Nat.shiftLeft a.significand shift) b.significand b.exponent

end FloatLib.Floats.Formats.BinaryInterchange.Model
