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
public def printPositHigh : IO Unit := do
  printFormat "configured posit" "posit65" 65 61 (ExecFloat.Posit.Family 65)
  printFormat "configured posit" "posit128" 128 124 (ExecFloat.Posit.Family 128)
  printFormat "configured posit" "posit129" 129 125 (ExecFloat.Posit.Family 129)
  printFormat "configured posit" "posit256" 256 252 (ExecFloat.Posit.Family 256)
  printFormat "configured posit" "posit512" 512 508 (ExecFloat.Posit.Family 512)
  printFormat "configured posit" "posit1024" 1024 1020 (ExecFloat.Posit.Family 1024)
  printFormat "configured posit" "posit2048" 2048 2044 (ExecFloat.Posit.Family 2048)
  printFormat "configured posit" "posit4096" 4096 4092 (ExecFloat.Posit.Family 4096)

end FloatLibBenchmarks.Public.SelectionMatrix
