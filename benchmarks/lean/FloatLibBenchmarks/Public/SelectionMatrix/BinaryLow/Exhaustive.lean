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
public def printBinaryExhaustive : IO Unit := do
  printFormat "configured binary" "binary4-e2m1" 4 2 (ExecFloat.Binary.Family 2 1)
  printFormat "configured binary" "binary5-e2m2" 5 3 (ExecFloat.Binary.Family 2 2)
  printFormat "configured binary" "binary6-e3m2" 6 3 (ExecFloat.Binary.Family 3 2)

end FloatLibBenchmarks.Public.SelectionMatrix
