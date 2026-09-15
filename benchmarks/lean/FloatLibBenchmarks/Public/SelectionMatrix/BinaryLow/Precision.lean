/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.Core

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.SelectionMatrix

set_option maxHeartbeats 1000000 in
public def printBinarySmallPrecision : IO Unit := do
  printFormat "configured binary" "p4" 6 4 (ExecFloat.Binary.Family 2 3)
  printFormat "configured binary" "p5" 8 5 (ExecFloat.Binary.Family 3 4)
  printFormat "configured binary" "p6" 10 6 (ExecFloat.Binary.Family 4 5)
  printFormat "configured binary" "p7" 11 7 (ExecFloat.Binary.Family 4 6)

end FloatLibBenchmarks.Public.SelectionMatrix
