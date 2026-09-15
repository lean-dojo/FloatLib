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
public def printBinaryBoundary : IO Unit := do
  printFormat "configured binary" "binary7-e3m3" 7 4 (ExecFloat.Binary.Family 3 3)
  printFormat "configured binary" "binary8-e4m3" 8 4 (ExecFloat.Binary.Family 4 3)

end FloatLibBenchmarks.Public.SelectionMatrix
