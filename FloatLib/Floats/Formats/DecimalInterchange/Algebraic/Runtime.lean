/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Algebraic.Root.Runtime

/-!
# Decimal algebraic operations with one rounding

Squares and integer powers project an exact rational result. Reciprocal square
root and hypotenuse pass an exact rational radicand to the square-root rounder:
neither a reciprocal nor a sum of squares is rounded first.

Exact results select the preferred cohort. Integer powers multiply the operand
quantum by the exponent; reciprocal square root uses the floor of its negated
half-quantum; hypotenuse uses the smaller operand quantum.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Square with the same single rounding, preferred cohort, and flags as multiplication. -/
def square (f : Format) (mode : RoundingMode) (x : Datum) : Outcome :=
  mul f mode x x

/-- Sign of an integer power, including negative odd exponents and signed zero. -/
def powerSign (negative : Bool) (exponent : Int) : Bool :=
  negative && decide (exponent % 2 = 1)

/-- Integer power with an exact rational intermediate and one final projection.
A quiet NaN to power zero gives the rounded value one; a signaling NaN raises invalid.
Negative powers of either zero raise divide-by-zero, with the odd-power sign. -/
def powInt (f : Format) (mode : RoundingMode) : Datum → Int → Outcome
  | .nan s t p, n =>
      if n = 0 ∧ t = false then project f mode 1 0
      else nanResult f s p t
  | .infinity s, n =>
      if n = 0 then project f mode 1 0
      else if n < 0 then projectMagnitude f mode (powerSign s n) 0 f.minQuantum
      else { value := .infinity (powerSign s n) }
  | .finite s c q, n =>
      if n < 0 ∧ c = 0 then
        { value := .infinity (powerSign s n), status := { divideByZero := true } }
      else
        project f mode (Datum.finiteValue s c q ^ n) (q * n) (powerSign s n)

/-- Reciprocal square root, rounding the root of the exact rational reciprocal.
Either zero gives the correspondingly signed infinity and divide-by-zero.
A negative nonzero input raises invalid; positive infinity gives positive zero. -/
def rsqrt (f : Format) (mode : RoundingMode) : Datum → Outcome
  | .nan s t p => nanResult f s p t
  | .infinity s =>
      if s then invalidResult else projectMagnitude f mode false 0 f.minQuantum
  | .finite s c q =>
      if c = 0 then { value := .infinity s, status := { divideByZero := true } }
      else if s then invalidResult
      else sqrtMagnitude f mode (((c : ℚ) * (10 : ℚ) ^ q)⁻¹) ((-q) / 2)

/-- Hypotenuse with an exact sum of squares and one square-root rounding.
An infinity dominates a quiet NaN. A signaling NaN raises invalid and propagates
the first NaN's diagnostics, as in the other decimal binary operations. -/
def hypot (f : Format) (mode : RoundingMode) : Datum → Datum → Outcome
  | .nan s t p, y =>
      if t || y.isSignaling then nanResult f s p true
      else match y with
        | .infinity _ => { value := .infinity false }
        | _ => nanResult f s p false
  | x, .nan s t p =>
      if t then nanResult f s p true
      else match x with
        | .infinity _ => { value := .infinity false }
        | _ => nanResult f s p false
  | .infinity _, _ | _, .infinity _ => { value := .infinity false }
  | .finite sx cx qx, .finite sy cy qy =>
      sqrtMagnitude f mode
        (Datum.finiteValue sx cx qx ^ 2 + Datum.finiteValue sy cy qy ^ 2) (min qx qy)

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
