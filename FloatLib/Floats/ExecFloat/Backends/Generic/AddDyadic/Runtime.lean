/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic

/-!
# Executable signed-magnitude dyadic addition

This is exact dyadic addition in sign-magnitude form, on natural-number magnitudes. Correctness
proofs and the compiler substitution live in `AddDyadic.Proof`.
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
Exact dyadic addition in sign-magnitude form.

Zero operands are handled before alignment. For two nonzero operands, the significand with the
larger exponent is shifted to the smaller exponent before the magnitudes are combined. No
rounding occurs here.
-/
@[inline] def Internal.addDyadic (a b : Numerics.Dyadic) : Numerics.Dyadic :=
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

/--
Dyadic addition for a sum that is rounded next, to at most `keep - 3` fraction bits.

It is `Internal.addDyadic` unless the operands are far apart: when both are nonzero and the gap
between their exponents exceeds both `2 * keep` and the bit length of the lower significand. Then
the higher significand is aligned only `keep` positions down, and the lower one is folded into
those positions with a sticky bit, exactly as `Numerics.shiftRightJam` folds the exact sum. A
large exponent gap therefore builds no correspondingly large integer, and rounding the result
gives the rounding of the exact sum (`roundDyadic_addDyadicForRounding`).
-/
@[inline] def addDyadicForRounding (keep : Nat) (a b : Numerics.Dyadic) : Numerics.Dyadic :=
  if a.exponent ≤ b.exponent then aligned keep a b else aligned keep b a
where
  /-- The sum of `low` and `high`, where `high` has the larger exponent. -/
  @[inline] aligned (keep : Nat) (low high : Numerics.Dyadic) : Numerics.Dyadic :=
    let gap := Int.toNat (high.exponent - low.exponent)
    if 2 * keep < gap ∧ low.significand.log2 + 1 < gap ∧ high.significand ≠ 0 ∧
        low.significand ≠ 0 then
      let discard := gap - keep
      let upper := high.significand <<< keep
      let lower := low.significand >>> discard
      -- A zero `lower` means a nonzero discarded part, and is tested first so that no shift by
      -- `discard` is formed.
      let exact := lower != 0 && low.significand == lower <<< discard
      { negative := high.negative
        significand :=
          if high.negative == low.negative then
            if exact then upper + lower else (upper + lower) ||| 1
          else
            if exact then upper - lower else (upper - lower - 1) ||| 1
        exponent := low.exponent + discard }
    else
      Internal.addDyadic low high

end FloatLib.Floats.Formats.BinaryInterchange.Model
