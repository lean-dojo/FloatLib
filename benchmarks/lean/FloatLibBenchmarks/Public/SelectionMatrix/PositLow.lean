/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.Core
import FloatLib.Floats.Formats.Posit

open FloatLib.Floats
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.SelectionMatrix

set_option maxHeartbeats 1000000 in
public def printPositLow : IO Unit := do
  printFormat "configured posit" "posit2" 2 1 (ExecFloat.Posit.Family 2)
  printFormat "configured posit" "posit3" 3 1 (ExecFloat.Posit.Family 3)
  printFormat "configured posit" "posit4" 4 1 (ExecFloat.Posit.Family 4)
  printFormat "configured posit" "posit5" 5 1 (ExecFloat.Posit.Family 5)
  printFormat "configured posit" "posit6" 6 2 (ExecFloat.Posit.Family 6)
  printFormat "configured posit" "posit7" 7 3 (ExecFloat.Posit.Family 7)
  printFormat "configured posit" "posit8" 8 4 (ExecFloat.Posit.Family 8)
  printFormat "configured posit" "posit9" 9 5 (ExecFloat.Posit.Family 9)
  printFormat "configured posit" "posit16" 16 12 (ExecFloat.Posit.Family 16)
  printFormat "configured posit" "posit17" 17 13 (ExecFloat.Posit.Family 17)
  printFormat "configured posit" "posit32" 32 28 (ExecFloat.Posit.Family 32)
  printFormat "configured posit" "posit33" 33 29 (ExecFloat.Posit.Family 33)
  printFormat "configured posit" "posit64" 64 60 (ExecFloat.Posit.Family 64)

end FloatLibBenchmarks.Public.SelectionMatrix
