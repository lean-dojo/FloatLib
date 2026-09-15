/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.Core
import FloatLibTests.Fixtures.CustomByte

open FloatLibTests.Fixtures.CustomByte

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printCustom : IO Unit := do
  printAddOnly "custom" "TestByte" 8 8 TestByte

end FloatLibBenchmarks.Public.SelectionMatrix
