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

Import this when you want to run decimal arithmetic and don't need the proofs. You get
`Arithmetic.add`, `sub`, `mul`, `div`, `fma`, `sqrt`, `quantize`, and the integral-rounding
variants, both the exact one and those that take a direction, all with the five rounding modes,
preferred decimal cohorts, and default exception flags. `Inspection.Runtime` comes along too, with
the sign operations, classification, all 22 comparison predicates, total ordering, and quantum
queries. Nothing here imports a proof facet, so for the value, range, error, signed-zero, and
status theorems you import `Arithmetic.Basic`.

The operations take and return `Datum`. BID and DPD only come in at the codec boundary. Traps and a
mutable exception environment aren't part of this functional API.
-/
