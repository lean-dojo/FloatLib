/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.IEEE754.Native.Roundoff
public meta import FloatLib.Tactic.Roundoff.Extension

/-!
# Native carrier registration for roundoff

The native arithmetic rules remain beside the IEEE754 native proofs. This module registers
imports of stored `Float32` and `Float` values into their matching configured formats, so the
roundoff analyzer can follow a native computation through its exact word import.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff

open Lean

/-- Lean's native floats for `roundoff`: `ExecFloat.Binary.ofFloat32` into binary32 and
`ExecFloat.Binary.ofFloat` into binary64 move the word of a native value, so the import of a
stored native value is a stored value, and a native computation is analyzed through its import.
An import into another format rounds and is not registered. -/
def nativeFloats : Extension where
  imports := #[
    { head := ``ExecFloat.Binary.ofFloat32, arity := 4, value := 2, target := ``Binary32 },
    { head := ``ExecFloat.Binary.ofFloat, arity := 4, value := 2, target := ``Binary64 }]

attribute [roundoff_extension] nativeFloats

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff
