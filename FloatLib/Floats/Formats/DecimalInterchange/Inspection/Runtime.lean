/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Runtime

/-!
# Executable decimal inspection

This module has the executable inspection operations, without proofs:

* stored-bit and datum sign operations
* the ten-way classification and all classification predicates
* stored-word canonicality
* all 22 IEEE comparison predicates
* total ordering, magnitude ordering, and sameQuantum

On top of those, `Datum.quantumExponent` is a finite-only query of our own. Non-computational
queries and sign operations never signal exceptions, and the quiet and signaling comparisons
return their invalid flag as part of the result. Import `Inspection.Basic` for the proofs.
-/
