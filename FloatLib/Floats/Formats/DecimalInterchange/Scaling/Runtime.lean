/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime

/-!
# Decimal exponent operations

`scaleB` multiplies by an exact integral power of ten before its single rounding.
Its preferred exponent is the input quantum plus the scale (IEEE 754-2019 §5.3.3).
The integer argument is unbounded; it does not impose the coefficient restriction
of the older General Decimal Arithmetic `scaleb` operation.

`logB` uses an integer result format. Its format-dependent sentinel exceeds twice
the absolute bounds on finite exponents. Exceptional inputs raise invalid, including
quiet NaNs, as specified for an integer `logBFormat` in §5.3.3. These are default
exception results, without a mutable environment or alternate exception handling.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange
namespace Arithmetic

/-- Multiply by a power of the radix, using the input quantum plus the scale
as the preferred quantum for projection. -/
def scaleB (f : Format) (mode : RoundingMode) (x : Datum) (n : Int) : Outcome :=
  match x with
  | .nan s t p => nanResult f s p t
  | .infinity s => { value := .infinity s }
  | .finite s c q =>
      projectMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ (q + n)) (q + n)

/-- Integer result and default status for an exponent query. -/
structure LogBOutcome where
  /-- Radix exponent for a nonzero finite input, or the signed exceptional sentinel. -/
  value : Int
  /-- Default exception flags; exceptional integer deliveries signal invalid. -/
  status : Status := {}
  deriving DecidableEq, Repr

/-- Exceptional integer exponent, beyond twice either absolute finite exponent bound. -/
def logBSentinel (f : Format) : Int :=
  2 * max |f.minQuantum| |f.maxQuantum + (f.precision : Int) - 1| + 1

/-- Radix-ten exponent, using an integer `logBFormat`.
Zero uses the negative sentinel; infinity and either kind of NaN use the positive one. -/
def logB (f : Format) : Datum → LogBOutcome
  | .finite _ 0 _ => { value := -logBSentinel f, status := { invalid := true } }
  | .finite _ (c + 1) q => { value := q + (Nat.log 10 (c + 1) : Int) }
  | .infinity _ | .nan _ _ _ =>
      { value := logBSentinel f, status := { invalid := true } }

end Arithmetic
end FloatLib.Floats.Formats.DecimalInterchange
