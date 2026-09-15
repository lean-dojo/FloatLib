/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime

/-!
# Decimal rational arithmetic

Addition, subtraction, multiplication, division, and fused multiply-add compute
their finite intermediate values in `ℚ`, then project once. Preferred exponents
follow IEEE 754-2019 §5.4.1; signs and exceptional operands follow §§6–7.

NaN propagation chooses the first NaN operand, preserving its sign and payload
when the payload fits the destination. Any signaling operand raises invalid.
For `fma(0, infinity, quietNaN)`, this implementation raises invalid, one of the
two behaviors permitted by §7.2(c). These operations return default exception
flags; they do not implement trapping or a mutable floating-point environment.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Exact value of a finite representation, including either signed zero. -/
def Datum.finiteValue (negative : Bool) (coefficient : Nat) (quantum : Int) : ℚ :=
  (if negative then -1 else 1) * (coefficient : ℚ) * (10 : ℚ) ^ quantum

/-- Test the signaling bit only on a NaN. -/
def Datum.isSignaling : Datum → Bool
  | .nan _ signaling _ => signaling
  | _ => false

/-- Reverse the sign bit without quieting a NaN or changing its payload. -/
def Datum.negate : Datum → Datum
  | .finite s c q => .finite (!s) c q
  | .infinity s => .infinity (!s)
  | .nan s signaling payload => .nan (!s) signaling payload

namespace Arithmetic

/-- Quiet NaN propagation. An unrepresentable payload becomes zero. -/
def nanResult (f : Format) (negative : Bool) (payload : Nat) (invalid : Bool) : Outcome :=
  { value := .nan negative false (if payload < f.payloadBound then payload else 0)
    status := { invalid := invalid } }

/-- Default result of an invalid operation without an input NaN. -/
def invalidResult : Outcome :=
  { value := .nan false false 0, status := { invalid := true } }

/-- Sign of an exact zero sum. Equal signs survive; cancellation rounds downward to `-0`. -/
def zeroSumSign (mode : RoundingMode) (left right : Bool) : Bool :=
  if left = right then left else decide (mode = .towardNegative)

/-- Addition, with preferred quantum the smaller operand quantum. -/
def add (f : Format) (mode : RoundingMode) : Datum → Datum → Outcome
  | .nan s t p, y => nanResult f s p (t || y.isSignaling)
  | _, .nan s t p => nanResult f s p t
  | .infinity sx, .infinity sy =>
      if sx = sy then { value := .infinity sx } else invalidResult
  | .infinity s, .finite _ _ _ | .finite _ _ _, .infinity s =>
      { value := .infinity s }
  | .finite sx cx qx, .finite sy cy qy =>
      project f mode (Datum.finiteValue sx cx qx + Datum.finiteValue sy cy qy)
        (min qx qy) (zeroSumSign mode sx sy)

/-- Subtraction preserves input NaN diagnostics before reversing the second numeric sign. -/
def sub (f : Format) (mode : RoundingMode) : Datum → Datum → Outcome
  | .nan s t p, y => nanResult f s p (t || y.isSignaling)
  | _, .nan s t p => nanResult f s p t
  | x, y => add f mode x y.negate

/-- Multiplication, with preferred quantum the sum of the operand quanta. -/
def mul (f : Format) (mode : RoundingMode) : Datum → Datum → Outcome
  | .nan s t p, y => nanResult f s p (t || y.isSignaling)
  | _, .nan s t p => nanResult f s p t
  | .infinity sx, .infinity sy => { value := .infinity (sx ^^ sy) }
  | .infinity sx, .finite sy c _ | .finite sx c _, .infinity sy =>
      if c = 0 then invalidResult else { value := .infinity (sx ^^ sy) }
  | .finite sx cx qx, .finite sy cy qy =>
      project f mode (Datum.finiteValue sx cx qx * Datum.finiteValue sy cy qy)
        (qx + qy) (sx ^^ sy)

/-- Division, including the distinction between finite nonzero/zero and infinity/zero.
By §5.2, an infinity has quantum exponent `+∞`; finite/infinity therefore selects
the smallest quantum in the signed-zero cohort. -/
def div (f : Format) (mode : RoundingMode) : Datum → Datum → Outcome
  | .nan s t p, y => nanResult f s p (t || y.isSignaling)
  | _, .nan s t p => nanResult f s p t
  | .infinity _, .infinity _ => invalidResult
  | .infinity sx, .finite sy _ _ => { value := .infinity (sx ^^ sy) }
  | .finite sx _ _, .infinity sy =>
      { value := .finite (sx ^^ sy) 0 f.minQuantum }
  | .finite sx cx qx, .finite sy cy qy =>
      if cy = 0 then
        if cx = 0 then invalidResult
        else { value := .infinity (sx ^^ sy), status := { divideByZero := true } }
      else
        project f mode (Datum.finiteValue sx cx qx / Datum.finiteValue sy cy qy)
          (qx - qy) (sx ^^ sy)

/-- Add a signed infinity to a third operand after a fused product is classified. -/
def addInfinity (f : Format) (negative : Bool) : Datum → Outcome
  | .nan s t p => nanResult f s p t
  | .infinity s =>
      if negative = s then { value := .infinity negative } else invalidResult
  | .finite _ _ _ => { value := .infinity negative }

/-- Test the invalid zero-times-infinity product, without assigning a value to it. -/
def invalidProduct : Datum → Datum → Bool
  | .infinity _, .finite _ c _ | .finite _ c _, .infinity _ => c == 0
  | _, _ => false

/-- Fused multiply-add with unbounded intermediate range and exactly one rounding.
Neither an overflowing nor an underflowing intermediate product raises a flag. -/
def fma (f : Format) (mode : RoundingMode) : Datum → Datum → Datum → Outcome
  | .nan s t p, y, z => nanResult f s p (t || y.isSignaling || z.isSignaling)
  | _, .nan s t p, z => nanResult f s p (t || z.isSignaling)
  | x, y, .nan s t p => nanResult f s p (t || invalidProduct x y)
  | .finite sx cx qx, .finite sy cy qy, .finite sz cz qz =>
      project f mode
        (Datum.finiteValue sx cx qx * Datum.finiteValue sy cy qy +
          Datum.finiteValue sz cz qz)
        (min (qx + qy) qz) (zeroSumSign mode (sx ^^ sy) sz)
  | .finite _ _ _, .finite _ _ _, .infinity s => { value := .infinity s }
  | .infinity sx, .finite sy c _, z | .finite sx c _, .infinity sy, z =>
      if c = 0 then invalidResult else addInfinity f (sx ^^ sy) z
  | .infinity sx, .infinity sy, z => addInfinity f (sx ^^ sy) z

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
