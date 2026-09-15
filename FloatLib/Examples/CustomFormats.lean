/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured
public import FloatLib.Floats.Formats.FixedPoint.Configured.Instances
public import FloatLib.Floats.Formats.P3109
public import FloatLib.Floats.Formats.Posit.Configured

/-!
# Custom formats

Suppose a sensor sends 16-bit words that look like binary16 but reserve the all-ones exponent and
fraction pattern for NaN and have no infinities. How do we compute with those words in Lean,
and how do we check that a calculation in them is exact? A configured format is an ordinary
Lean type: we choose its parameters once in an `abbrev`, then use literals, operators, and
conversions at that type.

The four sections below build a custom binary layout, a posit width, a decimal fixed-point grid,
and a P3109 format. They are independent; `BasicOperations` introduces the shared interface.
-/

@[expose] public section

namespace FloatLib.Examples.CustomFormats

open FloatLib.Floats
open FloatLib.Numerics

/-! ## Choose a binary layout and exceptional-value policy -/

/-- One sign bit, five exponent bits, and ten fraction bits make a 16-bit telemetry word. -/
private abbrev Telemetry16 :=
  ExecFloat.Binary
    (exponentBits := 5)
    (fractionBits := 10)
    (encoding := .finiteMaxNaN)
    (bias := 14)

private def telemetryReading : Telemetry16 :=
  1.5

private def telemetryResult : Telemetry16 :=
  telemetryReading * 2.25 + 0.5
-- 3.875

private def telemetryMeaning : Option Rat :=
  ExecFloat.Binary.toRat? telemetryResult
-- some (31/8)

/-
`1.5 * 2.25 + 0.5 = 31/8` exactly, and this format represents every step. Normal values carry
eleven significant bits including the implicit leading one, and an exponent field `e` denotes
`2^(e - 14)`. `finiteMaxNaN` reserves the all-ones exponent and fraction for NaN with either sign;
the remaining top-exponent patterns are finite. This is not IEEE binary16 even
though the field widths agree; the bias of 14 rather than 15 is a second deliberate difference.
-/

/-! ## Choose a posit width -/

/-- `bits` is the complete stored width, including the sign and regime fields. -/
private abbrev Posit12 :=
  ExecFloat.Posit (bits := 12)

private def positReading : Posit12 :=
  1.5

private def positResult : Posit12 :=
  positReading * 2.25 + 0.5
-- 3.875

private def positMeaning : Option Rat :=
  ExecFloat.Posit.toRat? positResult
-- some (31/8)

/-
The same calculation is exact in a 12-bit posit as well. Posits have no fixed exponent field; the
regime and exponent bits adapt to the magnitude, and values near one get the most fraction bits.
-/

/-! ## Exact decimal fixed-point -/

/-- Values on an exact decimal grid with three fractional digits. -/
private abbrev Thousandths :=
  ExecFloat.FixedPoint decimalRadix 3

private def fixedReading : Thousandths :=
  1.125

private def fixedTotal : Thousandths :=
  fixedReading + 2.375

private def fixedReport : Int × Rat :=
  (ExecFloat.FixedPoint.coefficient fixedTotal,
    ExecFloat.FixedPoint.toRat fixedTotal)
-- (3500, 7/2)

/-
Here the parameter 3 is a decimal scale, not a storage width. An integer coefficient `c`
represents `c / 1000`, the coefficient is unbounded, and addition on this grid never rounds. A
fixed-point value has no display instance of its own, so we inspect it through `coefficient` and
`toRat`; the coefficient 3500 is the number a ledger would store.
-/

/-! ## Select a P3109 descriptor and conversion policy -/

/-- Six total bits and precision five, with a sign and an extended exceptional-value domain. -/
private def compactP3109 : Formats.P3109.Format :=
  .signed 6 5 .extended

private abbrev CompactP3109 :=
  ExecFloat.P3109 compactP3109

private def p3109Reading : ExecFloat.ConversionOutcome CompactP3109 :=
  ExecFloat.convert (target := CompactP3109) (3 / 16 : Rat)

private def p3109TowardZero : ExecFloat.ConversionOutcome CompactP3109 :=
  ExecFloat.convertWith (target := CompactP3109) (1 / 3 : Rat)
    { rounding := .towardZero, saturation := .finite }

private def p3109Meaning : Option (NumericalValue Rat) :=
  p3109Reading.value?.map ExecFloat.P3109.Conversion.decodeRat
-- some (NumericalValue.finite (3/16))

private def p3109TowardZeroMeaning : Option (NumericalValue Rat) :=
  p3109TowardZero.value?.map ExecFloat.P3109.Conversion.decodeRat
-- some (NumericalValue.finite (5/16))

/-
The source is a `Rat`, so `3/16` is exact before the destination rounds it, and it is
representable. `1/3` is not; rounding toward zero picks the neighbour below, `5/16`, and the
`.finite` saturation policy would clamp an overflowing result to the largest finite value instead
of producing an exceptional code. A successful outcome carries the value and status, a failure
carries its reason, and `value?` keeps only the optional value. Decoding then separates finite
rationals from the format's exceptional values through `NumericalValue`.
-/

end FloatLib.Examples.CustomFormats
