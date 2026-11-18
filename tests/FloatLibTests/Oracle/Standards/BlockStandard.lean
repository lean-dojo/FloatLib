module

import FloatLibTests.Oracle.Block

/-!
Narrow executable for the existing block-format oracle. Its protocol matches
`oracle block`, without importing unrelated oracle families.
-/

/-- Emit the documented comparison corpus through the compiled public operations. -/
public def main (arguments : List String) : IO UInt32 :=
  match arguments with
  | "block" :: rest => FloatLibTests.Oracle.Block.run rest
  | _ => pure 2
