/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.SelectionMatrix.Core
import FloatLib.Floats.Formats.FiniteOnly
import FloatLib.Floats.Formats.OCP.FP8.E4M3FN
import FloatLib.Floats.Formats.OCP.FP8.E5M2

open FloatLib.Floats.Formats.FiniteOnly
open FloatLib.Floats.Formats.OCP.FP8

open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.SelectionMatrix

public def printNominalNonIeee : IO Unit := do
  printFormat "nominal byte" "OCP E4M3FN" 8 4 E4M3FN
  printFormat "nominal byte" "OCP E5M2" 8 3 E5M2
  printFormat "nominal byte" "ONNX E4M3FNUZ" 8 4 E4M3FNUZ
  printFormat "nominal byte" "ONNX E5M2FNUZ" 8 3 E5M2FNUZ

end FloatLibBenchmarks.Public.SelectionMatrix
