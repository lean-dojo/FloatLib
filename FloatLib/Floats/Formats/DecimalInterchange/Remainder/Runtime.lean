/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime

/-!
# Exact decimal remainder

IEEE 754-2019 §5.3.1 uses the nearest integer quotient, with even ties, regardless
of the current rounding direction. Aligning the integer coefficients at the
smaller quantum makes the computation exact, even for a quotient too large to
represent as a decimal floating-point number. The result retains that preferred
quantum. An exact zero keeps the dividend's sign (§6.3).

The default status has no underflow or inexact flag, including tiny exact
remainders. Alternate exception handling is outside this pure result API.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Whether the nearest integer quotient lies above the truncated quotient. -/
def remainderRoundUp (a b : Nat) : Bool :=
  decide (b < 2 * (a % b) ∨ (b = 2 * (a % b) ∧ a / b % 2 = 1))

/-- Unbounded nearest-even quotient of two nonnegative integers. -/
def remainderQuotient (a b : Nat) : Nat :=
  a / b + if remainderRoundUp a b then 1 else 0

/-- Magnitude of the signed remainder on the common integer grid. -/
def remainderCoefficient (a b : Nat) : Nat :=
  if remainderRoundUp a b then b - a % b else a % b

/-- Exact remainder of finite operands on their common, preferred decimal grid. -/
def remainderFinite (sx : Bool) (cx : Nat) (qx : Int) (cy : Nat) (qy : Int) : Datum :=
  let q := min qx qy
  let a := cx * 10 ^ (qx - q).toNat
  let b := cy * 10 ^ (qy - q).toNat
  .finite (if remainderRoundUp a b then !sx else sx) (remainderCoefficient a b) q

/-- IEEE remainder, independent of the rounding direction.
Finite dividend/infinite divisor returns the dividend, including its cohort. -/
def remainder (f : Format) : Datum → Datum → Outcome
  | .nan s t p, y => nanResult f s p (t || y.isSignaling)
  | _, .nan s t p => nanResult f s p t
  | .infinity _, _ => invalidResult
  | .finite sx cx qx, .infinity _ => { value := .finite sx cx qx }
  | .finite sx cx qx, .finite _ cy qy =>
      if cy = 0 then invalidResult
      else { value := remainderFinite sx cx qx cy qy }

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
