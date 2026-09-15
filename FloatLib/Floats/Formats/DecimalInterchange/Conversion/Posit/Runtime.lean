/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Conversion.Format.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Runtime

/-!
# Numeric conversion between posits and decimal interchange

Both directions decode the source exactly and round once to the destination.
Posit-to-decimal conversion uses the requested decimal rounding direction and
prefers quantum zero on an exact result. This preferred quantum is the library's
nondecimal-conversion policy; the Posit Standard does not prescribe decimal cohorts.
For an exact result, projection chooses the quantum closest to zero among that
result's representable cohort members, including when the layout excludes quantum zero.

Posit zero becomes positive decimal zero. NaR becomes a quiet decimal NaN with
zero payload and clear status. In the other direction, decimal NaNs and either
infinity become NaR, either signed zero becomes posit zero, and finite values use
the standard appended-bit posit rounding rule.

## References

* Posit Standard (2022), §§4.1 and 6.5.
* IEEE 754-2019, §§4.3 and 5.4.2.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Conversion

open FloatLib.Floats.Formats

/-- Convert an arbitrary-width posit to decimal, preferring quantum zero.
NaR maps to a quiet zero-payload NaN without raising invalid. -/
def fromPosit {fmt : Posit.Format} (target : Format) (mode : RoundingMode)
    (x : Posit.Model fmt) : Outcome :=
  match Posit.Model.toRat? x with
  | some value => project target mode value 0 false
  | none => { value := .nan false false 0 }

/-- Convert a decimal datum to an arbitrary-width posit. Finite values are rounded
once by the Posit Standard rule; all decimal nonfinite values become NaR. -/
def toPosit (target : Posit.Format) (x : Datum) : Posit.Model target :=
  match x.toRat? with
  | some value => Posit.Model.roundRat target value
  | none => Posit.Model.nar target

end FloatLib.Floats.Formats.DecimalInterchange.Conversion
