/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Operations
public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Status
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Minimal
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Minimal
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Direction
public import FloatLib.Floats.Formats.DecimalInterchange.Quantize.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Integral.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Inspection.Basic

/-!
# Decimal interchange arithmetic and its numerical guarantees

This is the import for decimal arithmetic together with its proofs. Addition, subtraction,
multiplication, division, and fused multiply-add compute with exact rational intermediates, and
square root uses an integer square root and compares exact squared midpoints.

The imported theorems prove that
* every result is a valid datum of the destination format
* nearest and directed rounding meet their error bounds
* a result that is representable comes back with no rounding error
* exact results get the right signed zero and the preferred cohort
* inexact results get the cohort with the least quantum
* the inexact flag means the value really differs from the exact one

Quantize rounds straight to the quantum you ask for, with proofs of its fixed-grid error and its
status. For valid finite inputs in a format whose maximum quantum is nonnegative, integral rounding
keeps `max(Q(x), 0)` and returns an integer. A custom format with a negative maximum quantum can't
store that preferred quantum, so it returns invalid. The two integral variants differ only in
whether numerical inexactness raises a flag. Decimal tininess is tested before rounding, except
that quantize never signals underflow. These guarantees are about the operations provided here,
and we don't claim a complete or certified IEEE 754 implementation.

`Inspection.Basic` adds exact comparisons and their flags, numerical classification, the
total-order laws and tie rules, quantum queries, and the sign operations that keep every bit.

For the BID and DPD interchange codecs, import `DecimalInterchange.Basic` on its own. If all you
need is executable arithmetic, `Arithmetic.Operations` is enough.
-/
