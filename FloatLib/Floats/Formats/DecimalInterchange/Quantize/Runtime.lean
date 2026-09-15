/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime

/-!
# Rounding to a specified decimal quantum

IEEE 754-2019 §5.3.2 specifies quantize independently of ordinary projection:
the target quantum is fixed, and a coefficient that does not fit produces invalid
instead of changing that quantum. Underflow and overflow flags are never raised.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Arithmetic

/-- Round a nonnegative magnitude to a fixed quantum, retaining the supplied sign.
An invalid quantum or an oversized rounded coefficient produces a quiet NaN. -/
def quantizeMagnitude (f : Format) (mode : RoundingMode) (s : Bool)
    (x : ℚ) (q : Int) : Outcome :=
  let c := mode.roundAt s x q
  if f.minQuantum ≤ q ∧ q ≤ f.maxQuantum ∧ c < f.coefficientBound then
    { value := .finite s c q
      status := { inexact := decide ((c : ℚ) * (10 : ℚ) ^ q ≠ x) } }
  else invalidResult

/-- Quantize the first operand to the second operand's quantum.
The second operand's sign and coefficient do not affect a finite result. -/
def quantize (f : Format) (mode : RoundingMode) : Datum → Datum → Outcome
  | .nan s t p, y => nanResult f s p (t || y.isSignaling)
  | _, .nan s t p => nanResult f s p t
  | .infinity s, .infinity _ => { value := .infinity s }
  | .infinity _, .finite _ _ _ | .finite _ _ _, .infinity _ => invalidResult
  | .finite s c q, .finite _ _ r =>
      quantizeMagnitude f mode s ((c : ℚ) * (10 : ℚ) ^ q) r

end FloatLib.Floats.Formats.DecimalInterchange.Arithmetic
