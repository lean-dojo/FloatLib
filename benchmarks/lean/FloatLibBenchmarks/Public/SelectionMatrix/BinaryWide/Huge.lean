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
public def printBinaryHuge : IO Unit := do
  printFormat "configured binary" "p1024" 1043 1024 (ExecFloat.Binary.Family 19 1023)
  printFormat "configured binary" "p2048" 2067 2048 (ExecFloat.Binary.Family 19 2047)
  printFormat "configured binary" "p4096" 4115 4096 (ExecFloat.Binary.Family 19 4095)

end FloatLibBenchmarks.Public.SelectionMatrix
