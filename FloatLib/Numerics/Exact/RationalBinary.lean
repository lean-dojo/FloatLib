/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic
public import FloatLib.Numerics.Kernel.Log2

/-!
# Exact rational scaling by powers of two

Binary formats keep needing the same few exact operations. They locate a positive rational between
consecutive powers of two, move a binary exponent into a numerator or a denominator, and compare a
signed rational with a dyadic without constructing an enormous shifted integer.

We put these operations in the exact numerical layer and in no particular floating-point format, so
IEEE interchange, P3109, posits, and application-defined binary quantizers can share them without
importing one another's encoding or exceptional-value policy.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace RationalBinary

/-- Test `numerator / denominator < 2^exponent` for a positive denominator, using integers. -/
@[inline] def lessThanPowerOfTwo
    (numerator denominator : Nat) (exponent : Int) : Bool :=
  match exponent with
  | .ofNat shift => numerator < Nat.shiftLeft denominator shift
  | .negSucc shift => Nat.shiftLeft numerator (shift + 1) < denominator

/-- Nonnegative exponents shift the denominator in the strict comparison. -/
@[simp, grind =] theorem lessThanPowerOfTwo_ofNat
    (numerator denominator shift : Nat) :
    lessThanPowerOfTwo numerator denominator (Int.ofNat shift) =
      decide (numerator < Nat.shiftLeft denominator shift) :=
  rfl

/-- A natural exponent shifts the denominator in the strict comparison. -/
@[simp, grind =] theorem lessThanPowerOfTwo_natCast
    (numerator denominator shift : Nat) :
    lessThanPowerOfTwo numerator denominator (shift : Int) =
      decide (numerator < Nat.shiftLeft denominator shift) :=
  rfl

/-- Negative exponents shift the numerator in the strict comparison. -/
@[simp, grind =] theorem lessThanPowerOfTwo_negSucc
    (numerator denominator shift : Nat) :
    lessThanPowerOfTwo numerator denominator (Int.negSucc shift) =
      decide (Nat.shiftLeft numerator (shift + 1) < denominator) :=
  rfl

/-- Test `numerator / denominator ≥ 2^exponent` for a positive denominator, using integers. -/
@[inline] def atLeastPowerOfTwo
    (numerator denominator : Nat) (exponent : Int) : Bool :=
  match exponent with
  | .ofNat shift => numerator ≥ Nat.shiftLeft denominator shift
  | .negSucc shift => Nat.shiftLeft numerator (shift + 1) ≥ denominator

/-- Nonnegative exponents shift the denominator in the non-strict comparison. -/
@[simp, grind =] theorem atLeastPowerOfTwo_ofNat
    (numerator denominator shift : Nat) :
    atLeastPowerOfTwo numerator denominator (Int.ofNat shift) =
      decide (numerator ≥ Nat.shiftLeft denominator shift) :=
  rfl

/-- A natural exponent shifts the denominator in the non-strict comparison. -/
@[simp, grind =] theorem atLeastPowerOfTwo_natCast
    (numerator denominator shift : Nat) :
    atLeastPowerOfTwo numerator denominator (shift : Int) =
      decide (numerator ≥ Nat.shiftLeft denominator shift) :=
  rfl

/-- Negative exponents shift the numerator in the non-strict comparison. -/
@[simp, grind =] theorem atLeastPowerOfTwo_negSucc
    (numerator denominator shift : Nat) :
    atLeastPowerOfTwo numerator denominator (Int.negSucc shift) =
      decide (Nat.shiftLeft numerator (shift + 1) ≥ denominator) :=
  rfl

/--
Compute `⌊log₂(numerator / denominator)⌋`.

It is meant for a positive numerator and denominator. We keep the kernel total because that's
convenient inside executable quantizers, and proofs establish the preconditions where logarithmic
bounds are used.

The first estimate is the difference of the positions of the two leading bits. They are read by
`Kernel.log2`, which Lean's kernel evaluates in a few native operations where `Nat.log2` takes
one step for each bit, and which compiled code runs as `Nat.log2`; `floorLog2_eq_log2` is the
definition with `Nat.log2`.
-/
@[inline] def floorLog2 (numerator denominator : Nat) : Int :=
  let initial :=
    Int.ofNat (Kernel.log2 numerator) - Int.ofNat (Kernel.log2 denominator)
  let lower :=
    if lessThanPowerOfTwo numerator denominator initial then
      initial - 1
    else
      initial
  if atLeastPowerOfTwo numerator denominator (lower + 1) then
    lower + 1
  else
    lower

/-- `floorLog2` with the leading bits read by `Nat.log2`: the form that proofs unfold. -/
theorem floorLog2_eq_log2 (numerator denominator : Nat) :
    floorLog2 numerator denominator =
      (let initial :=
        Int.ofNat numerator.log2 - Int.ofNat denominator.log2
      let lower :=
        if lessThanPowerOfTwo numerator denominator initial then
          initial - 1
        else
          initial
      if atLeastPowerOfTwo numerator denominator (lower + 1) then
        lower + 1
      else
        lower) := by
  unfold floorLog2
  rw [Kernel.log2_eq, Kernel.log2_eq]

/--
Represent `(numerator / denominator) * 2^exponent` as a ratio of natural numbers.

Positive exponents shift the numerator and negative exponents shift the denominator. No division
or approximation occurs.
-/
@[inline] def scaleByPowerOfTwo
    (numerator denominator : Nat) : Int → Nat × Nat
  | .ofNat shift => (Nat.shiftLeft numerator shift, denominator)
  | .negSucc shift =>
      (numerator, Nat.shiftLeft denominator (shift + 1))

/-- Scaling by a nonnegative exponent shifts only the numerator. -/
@[simp, grind =] theorem scaleByPowerOfTwo_ofNat
    (numerator denominator shift : Nat) :
    scaleByPowerOfTwo numerator denominator (Int.ofNat shift) =
      (Nat.shiftLeft numerator shift, denominator) :=
  rfl

/-- Scaling by a natural exponent shifts only the numerator. -/
@[simp, grind =] theorem scaleByPowerOfTwo_natCast
    (numerator denominator shift : Nat) :
    scaleByPowerOfTwo numerator denominator (shift : Int) =
      (Nat.shiftLeft numerator shift, denominator) :=
  rfl

/-- Scaling by `2^0` leaves both sides of the exact quotient unchanged. -/
@[simp, grind =] theorem scaleByPowerOfTwo_zero
    (numerator denominator : Nat) :
    scaleByPowerOfTwo numerator denominator 0 =
      (numerator, denominator) := by
  simp [scaleByPowerOfTwo]

/-- Scaling by a negative exponent shifts only the denominator. -/
@[simp, grind =] theorem scaleByPowerOfTwo_negSucc
    (numerator denominator shift : Nat) :
    scaleByPowerOfTwo numerator denominator (Int.negSucc shift) =
      (numerator, Nat.shiftLeft denominator (shift + 1)) :=
  rfl

/-- A nonzero numerator remains nonzero after exact binary scaling. -/
theorem scaleByPowerOfTwo_fst_ne_zero
    (numerator denominator : Nat) (exponent : Int)
    (hnumerator : numerator ≠ 0) :
    (scaleByPowerOfTwo numerator denominator exponent).1 ≠ 0 := by
  cases exponent with
  | ofNat shift =>
      simp only [scaleByPowerOfTwo_ofNat]
      exact mt Nat.shiftLeft_eq_zero_iff.mp hnumerator
  | negSucc shift =>
      simpa using hnumerator

/-- A nonzero denominator remains nonzero after exact binary scaling. -/
theorem scaleByPowerOfTwo_snd_ne_zero
    (numerator denominator : Nat) (exponent : Int)
    (hdenominator : denominator ≠ 0) :
    (scaleByPowerOfTwo numerator denominator exponent).2 ≠ 0 := by
  cases exponent with
  | ofNat shift =>
      simpa using hdenominator
  | negSucc shift =>
      simp only [scaleByPowerOfTwo_negSucc]
      exact mt Nat.shiftLeft_eq_zero_iff.mp hdenominator

/--
Compare `(numerator / denominator) * 2^exponent`, with the supplied sign, against a dyadic.

A zero denominator returns `none`. After multiplying the denominator by the dyadic significand, a
leading-position test often decides the result. Only equal leading positions need exponent
alignment, and that shift is then bounded by the integer operand widths.
-/
def compareDyadicScaled? (negative : Bool) (numerator denominator : Nat)
    (exponent : Int) (value : Dyadic) : Option Ordering :=
  if denominator == 0 then
    none
  else if numerator == 0 then
    if value.significand == 0 then some .eq
    else if value.negative then some .gt else some .lt
  else if value.significand == 0 then
    if negative then some .lt else some .gt
  else if negative != value.negative then
    if negative then some .lt else some .gt
  else
    let relativeExponent := exponent - value.exponent
    let scaledDenominator := denominator * value.significand
    let leadingExponent :=
      floorLog2 numerator scaledDenominator + relativeExponent
    let magnitudeOrder :=
      if leadingExponent < 0 then
        .lt
      else if leadingExponent > 0 then
        .gt
      else
        let scaled :=
          scaleByPowerOfTwo numerator scaledDenominator relativeExponent
        compare scaled.1 scaled.2
    some (if negative then magnitudeOrder.swap else magnitudeOrder)

/-- Compare an exact signed rational with a dyadic. -/
def compareDyadic? (negative : Bool) (numerator denominator : Nat)
    (value : Dyadic) : Option Ordering :=
  compareDyadicScaled? negative numerator denominator 0 value

end RationalBinary
end FloatLib.Numerics
