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
public def printBinaryStandard : IO Unit := do
  printFormat "configured binary" "bfloat16" 16 8 (ExecFloat.Binary.Family 8 7)
  printFormat "configured binary" "binary16" 16 11 (ExecFloat.Binary.Family 5 10)
  printFormat "configured binary" "binary32" 32 24 (ExecFloat.Binary.Family 8 23)
  printFormat "configured binary" "binary64" 64 53 (ExecFloat.Binary.Family 11 52)

end FloatLibBenchmarks.Public.SelectionMatrix
