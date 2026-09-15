/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.BinaryWide.Extended
import FloatLibBenchmarks.Public.SelectionMatrix.BinaryWide.Huge
import FloatLibBenchmarks.Public.SelectionMatrix.BinaryWide.Standard

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printBinaryWide : IO Unit := do
  printBinaryStandard
  printBinaryExtended
  printBinaryHuge

end FloatLibBenchmarks.Public.SelectionMatrix
