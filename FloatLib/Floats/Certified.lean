/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Repr

/-!
# Search budgets and failures of certified functions

A certified function keeps refining a rational enclosure of the real result until both endpoints
round to the same value in the destination format. `Budget` puts a bound on that search, and the
binary and decimal certified functions take it as `(budget := { maxAttempts := 4 })`. When a binary
certified function returns no result, it says why with a `Failure`.
-/

@[expose] public section

namespace FloatLib.Floats.Certified

open FloatLib.Numerics

/--
The search budget of a certified function, made of the first Taylor degree and the number of
enclosure attempts. It limits the number of attempts and says nothing about total work or elapsed
time. Exact comparisons outside the search, such as the screens for underflow and overflow, run to
completion, and one attempt can take longer than the one before it.
-/
structure Budget where
  /-- First Taylor degree. Zero is promoted to one before refinement. -/
  initialDegree : Nat := 8
  /-- Maximum enclosure attempts, including retries at higher degree or precision. -/
  maxAttempts : Nat := 16
  deriving DecidableEq, Repr

/--
Why a certified evaluation returned no result.

An `inconclusive` result makes no claim about whether more refinement would succeed. The other
cases identify a format, input, domain, or finite-range obstruction.
-/
inductive Failure where
  /-- The function does not support the format. The binary functions require an IEEE descriptor. -/
  | unsupportedFormat
  /-- An input is a NaN or an infinity. -/
  | nonfiniteInput
  /--
  The input is outside the supported real domain, such as the logarithm of a number at most zero,
  `log (1 + x)` for `x ≤ -1`, or a power whose base is at most zero.
  -/
  | domain
  /-- The exact result rounds beyond the largest finite value of the format. -/
  | range
  /--
  The search stopped without a certificate: its attempts ran out, or the exact result lies on or
  too close to a rounding boundary, or it is a power the search does not settle.
  -/
  | inconclusive
  deriving DecidableEq

/-- `#eval` writes a failure with a leading dot, as `.domain` or `.inconclusive`. -/
instance : Repr Failure where
  reprPrec failure prec :=
    match failure with
    | .unsupportedFormat => reprConstructor "unsupportedFormat" [] prec
    | .nonfiniteInput => reprConstructor "nonfiniteInput" [] prec
    | .domain => reprConstructor "domain" [] prec
    | .range => reprConstructor "range" [] prec
    | .inconclusive => reprConstructor "inconclusive" [] prec

end FloatLib.Floats.Certified
