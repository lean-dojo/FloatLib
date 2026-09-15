/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibTests.Oracle.Binary16
import FloatLibTests.Oracle.Formats
import FloatLibTests.Oracle.Posit
import FloatLibTests.Oracle.Primitives
import FloatLibTests.Oracle.Reductions
import FloatLibTests.Oracle.TestFloat

/-!
# External comparison protocols

Dispatch the vector emitters and TestFloat stream checker used by `tests/oracles/`.
Each command owns its output format; binary16 writes binary words and the other emitters write text.
-/

private def usage : String :=
  "usage: oracle COMMAND [ARGS]\n" ++
  "  primitives                         binary32/binary64 arithmetic vectors\n" ++
  "  reductions                         exact sum and dot-product vectors\n" ++
  "  formats onnx                       ONNX low-bit decoding vectors\n" ++
  "  formats p3109 MIN_WIDTH MAX_WIDTH   P3109 decoding vectors\n" ++
  "  binary16 {add|mul} INDEX COUNT      binary16 shard (binary output)\n" ++
  "  posit [REPORTS]                     check a SoftPosit binary stream\n" ++
  "  testfloat FORMAT OP MODE [REPORTS]  check vectors from stdin"

open FloatLibTests.Oracle in
/-- Dispatch a stream protocol, preserving its output and failure status. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | ["primitives"] => Primitives.run; return 0
  | ["reductions"] => Reductions.run; return 0
  | "formats" :: rest => Formats.run rest
  | "binary16" :: rest => Binary16.run rest; return 0
  | "posit" :: rest => Posit.run rest
  | "testfloat" :: rest => TestFloat.run rest
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 2
