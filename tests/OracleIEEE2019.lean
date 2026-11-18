/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibTests.Oracle.IEEE2019
meta import FloatLibTests.Oracle.IEEE2019

/-!
# `oracle ieee2019` in Lean's interpreter

`lean --run` on this file runs the checks of `FloatLibTests.Oracle.IEEE2019` without linking the
`oracle` executable. The module is imported a second time as `meta`, which makes its compiled
code available to the interpreter. `tests/oracles/ieee2019.sh` is the driver.
-/

/-- `exhaustive`, `formatOf`, or `check` with the cases on standard input. -/
public def main (args : List String) : IO UInt32 :=
  FloatLibTests.Oracle.IEEE2019.run args
