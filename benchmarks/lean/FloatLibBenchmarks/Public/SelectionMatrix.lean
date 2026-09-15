/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.BinaryLow
import FloatLibBenchmarks.Public.SelectionMatrix.BinaryWide
import FloatLibBenchmarks.Public.SelectionMatrix.Core
import FloatLibBenchmarks.Public.SelectionMatrix.Custom
import FloatLibBenchmarks.Public.SelectionMatrix.NonIeee
import FloatLibBenchmarks.Public.SelectionMatrix.PositHigh
import FloatLibBenchmarks.Public.SelectionMatrix.PositLow

/-!
# Authoritative automatic-backend selection matrix

This executable reports the certificate actually projected by each public `ExecFloat` operation.
It deliberately reads capability instances rather than reproducing family heuristics or attaching
handwritten labels. Consequently the CSV remains truthful when candidate availability, policies,
or cost estimates change.

The matrix covers:

* every configured precision used by the public 2-through-4096-bit sweep;
* current-standard posits on both sides of every carrier boundary and throughout the public
  comparison sweep;
* IEEE and non-IEEE eight-bit nominal formats;
* the same non-IEEE layouts through the parameterized configured carrier; and
* a user-defined direct-byte format with an arbitrary custom candidate list.

`maximumSignificandBits` is the ordinary fixed precision for binary formats. For posits it is the
largest tapered precision, attained around one; precision decreases as the regime consumes more
of the encoded word.

`candidateCount` includes the mandatory complete exact candidate. `warmCost`, `coldCost`, and
`score` are engineering-model units, not elapsed nanoseconds. Runtime measurements remain the
calibration authority.

The family/range modules are intentionally separate translation units. The matrix instantiates
many proof-carrying format families; keeping those instantiations independent lets Lake compile
this development diagnostic in parallel without changing its output.
-/

namespace FloatLibBenchmarks.Public.SelectionMatrix

def run : IO Unit := do
  printHeader
  printBinaryLow
  printBinaryWide
  printNonIeee
  printPositLow
  printPositHigh
  printCustom

end FloatLibBenchmarks.Public.SelectionMatrix

public def main : IO Unit :=
  FloatLibBenchmarks.Public.SelectionMatrix.run
