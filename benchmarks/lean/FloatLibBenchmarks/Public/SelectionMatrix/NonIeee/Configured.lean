/-
Copyright (c) 2026 FloatLib. All rights reserved.
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

/-!
One definition per format: each call inlines the six capabilities of its format, and five
formats in one definition exceed the compiler's default budget for a single declaration.
-/

private def printFiniteMaxNaNE4M3 : IO Unit :=
  printFormat "configured binary" "finiteMaxNaN E4M3" 8 4
    (ExecFloat.Binary.Family 4 3 (encoding := .finiteMaxNaN))

private def printFiniteMaxNaNE5M2 : IO Unit :=
  printFormat "configured binary" "finiteMaxNaN E5M2" 8 3
    (ExecFloat.Binary.Family 5 2 (encoding := .finiteMaxNaN))

private def printFiniteUnsignedZeroE4M3 : IO Unit :=
  printFormat "configured binary" "finiteUnsignedZero E4M3" 8 4
    (ExecFloat.Binary.Family 4 3 (encoding := .finiteUnsignedZero))

private def printFiniteUnsignedZeroE5M2 : IO Unit :=
  printFormat "configured binary" "finiteUnsignedZero E5M2" 8 3
    (ExecFloat.Binary.Family 5 2 (encoding := .finiteUnsignedZero))

private def printCustomBiasFinite16 : IO Unit :=
  printFormat "configured binary" "custom-bias finite16" 16 11
    (ExecFloat.Binary.Family 5 10 (encoding := .finite) (bias := 11))

public def printConfiguredNonIeee : IO Unit := do
  printFiniteMaxNaNE4M3
  printFiniteMaxNaNE5M2
  printFiniteUnsignedZeroE4M3
  printFiniteUnsignedZeroE5M2
  printCustomBiasFinite16

end FloatLibBenchmarks.Public.SelectionMatrix
