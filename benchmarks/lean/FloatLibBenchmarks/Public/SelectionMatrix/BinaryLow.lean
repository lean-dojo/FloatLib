/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.BinaryLow.Boundary
import FloatLibBenchmarks.Public.SelectionMatrix.BinaryLow.Exhaustive
import FloatLibBenchmarks.Public.SelectionMatrix.BinaryLow.Precision

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printBinaryLow : IO Unit := do
  printBinaryExhaustive
  printBinaryBoundary
  printBinarySmallPrecision

end FloatLibBenchmarks.Public.SelectionMatrix
