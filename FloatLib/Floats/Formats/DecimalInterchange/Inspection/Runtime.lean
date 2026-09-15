/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.DecimalInterchange.TotalOrder.Runtime

/-!
# Executable decimal inspection

Provides stored-bit and datum sign operations; the ten-way classification and
all classification predicates; stored-word canonicality; all 22 IEEE comparison
predicates; total ordering, magnitude ordering and sameQuantum.

`Datum.quantumExponent` is an additional finite-only query. Non-computational
queries and sign operations do not signal exceptions. Quiet/signaling comparisons
return their invalid flag explicitly. Import `Inspection.Basic` for proofs.
-/
