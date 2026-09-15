/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Exact.Runtime
public import FloatLib.Numerics.Operation.Proof.Finite

/-!
# Rational semantics and correctness of exact fixed point

A coefficient `m` with `d` fractional radix digits denotes `m / β^d`; the numerical system and
erased proof views relate the runtime operations to rational arithmetic. Common-scale addition
is exact; multiplication changes the scale to the sum of the operand fractional-digit counts.

Import `Exact.Runtime` for the representation and executable functions. The configured family
uses the refinement theorems here to provide the same operations through `ExecFloat`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.FixedPoint

open FloatLib.Numerics

/-- The exact rational numerical system at one fixed radix and scale. -/
def numericalSystem (radix : Radix) (fractionalDigits : Nat) : NumericalSystem :=
  NumericalSystem.ofFinite
    (fun value : Code radix fractionalDigits ↦ value.toRat)

/-- A fixed-point code with an erased proof of its complete denotation. -/
abbrev At (radix : Radix) (fractionalDigits : Nat) (value : NumericalValue ℚ) :=
  (numericalSystem radix fractionalDigits).At value

/-- A fixed-point code with an erased proof of its exact rational value. -/
abbrev AtFinite (radix : Radix) (fractionalDigits : Nat) (value : ℚ) :=
  (numericalSystem radix fractionalDigits).AtFinite value

end FloatLib.Floats.Formats.FixedPoint

/-! ## Arithmetic refinement -/

namespace FloatLib.Floats.Formats.FixedPoint

open FloatLib.Numerics

namespace Code

/-- Decoding exact fixed-point addition gives rational addition. -/
@[simp] theorem toRat_add {radix : Radix} {fractionalDigits : Nat}
    (left right : Code radix fractionalDigits) :
    toRat (add left right) = toRat left + toRat right := by
  simp [toRat, add]
  ring

/-- Decoding exact fixed-point negation gives rational negation. -/
@[simp] theorem toRat_neg {radix : Radix} {fractionalDigits : Nat}
    (value : Code radix fractionalDigits) :
    toRat (neg value) = -toRat value := by
  simp only [toRat, neg, Int.cast_neg]
  exact neg_div _ _

/-- Decoding exact fixed-point subtraction gives rational subtraction. -/
@[simp] theorem toRat_sub {radix : Radix} {fractionalDigits : Nat}
    (left right : Code radix fractionalDigits) :
    toRat (sub left right) = toRat left - toRat right := by
  simp [sub, sub_eq_add_neg]

/-- Decoding scale-composing fixed-point multiplication gives rational multiplication. -/
@[simp] theorem toRat_mul {radix : Radix} {p q : Nat}
    (left : Code radix p) (right : Code radix q) :
    toRat (mul left right) = toRat left * toRat right := by
  simp [toRat, mul, FixedPoint.scale, pow_add]
  ring

end Code

/-- Representation in the fixed-point numerical system is equality of decoded rationals. -/
@[simp] theorem numericalSystem_represents_iff {radix : Radix} {fractionalDigits : Nat}
    (value : Code radix fractionalDigits) (scalar : ℚ) :
    (numericalSystem radix fractionalDigits).Represents value scalar ↔
      value.toRat = scalar := by
  simp [NumericalSystem.Represents, numericalSystem]

/-- Fixed-point addition is a finite refinement of rational addition. -/
theorem add_refines {radix : Radix} {fractionalDigits : Nat} :
    Operation.Finite2 (numericalSystem radix fractionalDigits)
      (numericalSystem radix fractionalDigits) (numericalSystem radix fractionalDigits)
      Code.add (fun left right : ℚ => left + right) := by
  exact Operation.Finite2.ofFinite Code.toRat_add

/-- Fixed-point negation exactly refines rational negation. -/
theorem neg_refines {radix : Radix} {fractionalDigits : Nat} :
    Operation.Finite1 (numericalSystem radix fractionalDigits)
      (numericalSystem radix fractionalDigits) Code.neg (fun value : ℚ => -value) := by
  exact Operation.Finite1.ofFinite Code.toRat_neg

/-- Fixed-point subtraction exactly refines rational subtraction. -/
theorem sub_refines {radix : Radix} {fractionalDigits : Nat} :
    Operation.Finite2 (numericalSystem radix fractionalDigits)
      (numericalSystem radix fractionalDigits) (numericalSystem radix fractionalDigits)
      Code.sub (fun left right : ℚ => left - right) := by
  exact Operation.Finite2.ofFinite Code.toRat_sub

/-- Multiplication composes the two fixed scales and refines rational multiplication exactly. -/
theorem mul_refines {radix : Radix} {p q : Nat} :
    Operation.Finite2 (numericalSystem radix p) (numericalSystem radix q)
      (numericalSystem radix (p + q)) Code.mul (fun left right : ℚ => left * right) := by
  exact Operation.Finite2.ofFinite Code.toRat_mul

end FloatLib.Floats.Formats.FixedPoint
