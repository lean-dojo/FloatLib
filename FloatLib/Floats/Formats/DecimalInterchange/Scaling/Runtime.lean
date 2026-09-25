/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime

/-!
# Decimal exponent operations

`scale` implements IEEE 754-2019 §5.3.3 `scaleB`: multiply by an exact integral
power of ten, then round once. Its preferred exponent is the input quantum plus the scale.
The integer argument is unbounded; it does not impose the coefficient restriction
of the older General Decimal Arithmetic `scaleb` operation.

`decimalExponent` implements `logB` with an integer result format. For zero, infinity and NaN
§5.3.3 asks for a value outside the range `±2 × (emax + p - 1)`, where `emax` is the largest
exponent of a finite value in scientific form. The sentinel is `2 × (emax + p - 1) + 1`, enlarged
if needed so that it also exceeds twice the absolute bound on every finite exponent, and zero
gets its negation. Exceptional inputs raise invalid, including quiet NaNs, as specified for an
integer `logBFormat` in §5.3.3. These are default
exception results, without a mutable environment or alternate exception handling.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Multiply by `10^n` and round once (IEEE 754 `scaleB`), using the input quantum plus `n`
as the preferred quantum. -/
def scale (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) : Outcome :=
  match x with
  | .nan s t p => nanResult f s p t
  | .infinity s => { value := .infinity s }
  | .finite s c q =>
      projectScaled f mode s c (q + n) (q + n)

/-- Integer result and default status for an exponent query. -/
structure DecimalExponentOutcome where
  /-- Radix exponent for a nonzero finite input, or the signed exceptional sentinel. -/
  value : Int
  /-- Default exception flags; exceptional integer deliveries signal invalid. -/
  status : Status := {}
  deriving DecidableEq, Repr

/-- The IEEE 754-2019 §5.3.3 bound `emax + p - 1` for an integer `logB` result. Here
`emax = maxQuantum + p - 1` is the largest scientific exponent of a finite value. -/
def logBBound (f : Format) : Int :=
  f.maxQuantum + 2 * (f.precision : Int) - 2

/-- Exceptional integer exponent. It lies outside `±2 × (emax + p - 1)` as §5.3.3 requires, and
beyond twice either absolute finite exponent bound. -/
def decimalExponentSentinel (f : Format) : Int :=
  2 * max (max |f.minQuantum| |f.maxQuantum + (f.precision : Int) - 1|) |logBBound f| + 1

/-- Leading decimal exponent as an integer (IEEE 754 `logB`).
Zero uses the negative sentinel; infinity and either kind of NaN use the positive one. -/
def decimalExponent (f : Format) : Datum → DecimalExponentOutcome
  | .finite _ 0 _ => { value := -decimalExponentSentinel f, status := { invalid := true } }
  | .finite _ (c + 1) q => { value := q + (Nat.log 10 (c + 1) : Int) }
  | .infinity _ | .nan _ _ _ =>
      { value := decimalExponentSentinel f, status := { invalid := true } }

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
