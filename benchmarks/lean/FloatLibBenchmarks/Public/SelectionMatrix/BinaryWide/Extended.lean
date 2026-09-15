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
public def printBinaryExtended : IO Unit := do
  printFormat "configured binary" "binary96-e15m80" 96 81 (ExecFloat.Binary.Family 15 80)
  printFormat "configured binary" "binary112-e15m96" 112 97 (ExecFloat.Binary.Family 15 96)
  printFormat "configured binary" "binary128" 128 113 (ExecFloat.Binary.Family 15 112)
  printFormat "configured binary" "p161" 180 161 (ExecFloat.Binary.Family 19 160)
  printFormat "configured binary" "binary256" 256 237 (ExecFloat.Binary.Family 19 236)
  printFormat "configured binary" "p493" 512 493 (ExecFloat.Binary.Family 19 492)

end FloatLibBenchmarks.Public.SelectionMatrix
