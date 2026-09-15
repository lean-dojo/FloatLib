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

Exact rational intermediates implement addition, subtraction, multiplication,
division, and fused multiply-add. An integer square root and exact squared
midpoint comparisons implement square root.

The imported theorems establish destination validity, nearest and directed
rounding bounds, exactness on every representable rational, signed-zero and
preferred-cohort optimality for exact results, least-quantum cohorts for inexact
results, and numerical inexactness. Quantize
rounds directly to its requested quantum, with fixed-grid error and status proofs.
For valid finite inputs in formats with nonnegative maximum quantum, integral
rounding preserves `max(Q(x), 0)` and produces an integer. A custom format with
negative maximum quantum returns invalid because it cannot store that preferred
quantum. The two variants differ only in whether numerical inexactness raises a flag.
Decimal tininess is tested before rounding, except that quantize never signals
underflow. These guarantees cover the operations provided here;
they are not a claim of complete IEEE 754 implementation or certification.

`Inspection.Basic` adds exact comparisons and their flags, numerical classification,
total-order laws and tie rules, quantum queries, and bit-preserving sign operations.

Use `DecimalInterchange.Basic` separately for BID/DPD interchange codecs, or
`Arithmetic.Operations` when only executable arithmetic is needed.
-/
