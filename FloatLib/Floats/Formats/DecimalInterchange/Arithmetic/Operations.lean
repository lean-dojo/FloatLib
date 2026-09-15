/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.Arithmetic.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Sqrt.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Quantize.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Integral.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Inspection.Runtime

/-!
# Executable decimal interchange arithmetic

This import provides `Arithmetic.add`, `sub`, `mul`, `div`, `fma`, `sqrt`, `quantize`,
and the exact and explicit-direction integral-rounding variants,
with all five rounding modes, preferred decimal cohorts, and default exception
flags. It also includes `Inspection.Runtime`: sign operations, classification,
all 22 comparison predicates, total ordering and quantum queries.
It contains no proof-facet imports. Use `Arithmetic.Basic` for the value,
range, error, signed-zero, and status theorems.

The operations consume and return `Datum`; BID and DPD remain representation
choices at the codec boundary. Traps and a mutable exception environment are not
part of this functional API.
-/
