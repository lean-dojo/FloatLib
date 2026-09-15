/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.Core
import FloatLib.Floats.Formats.FiniteOnly

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printConfiguredNonIeee : IO Unit := do
  printFormat "configured binary" "finiteMaxNaN E4M3" 8 4
    (ExecFloat.Binary.Family 4 3 (encoding := .finiteMaxNaN))
  printFormat "configured binary" "finiteMaxNaN E5M2" 8 3
    (ExecFloat.Binary.Family 5 2 (encoding := .finiteMaxNaN))
  printFormat "configured binary" "finiteUnsignedZero E4M3" 8 4
    (ExecFloat.Binary.Family 4 3 (encoding := .finiteUnsignedZero))
  printFormat "configured binary" "finiteUnsignedZero E5M2" 8 3
    (ExecFloat.Binary.Family 5 2 (encoding := .finiteUnsignedZero))
  printFormat "configured binary" "custom-bias finite16" 16 11
    (ExecFloat.Binary.Family 5 10 (encoding := .finite) (bias := 11))

end FloatLibBenchmarks.Public.SelectionMatrix
