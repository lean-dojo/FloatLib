/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.NonIeee.Configured
import FloatLibBenchmarks.Public.SelectionMatrix.NonIeee.Nominal

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printNonIeee : IO Unit := do
  printNominalNonIeee
  printConfiguredNonIeee

end FloatLibBenchmarks.Public.SelectionMatrix
