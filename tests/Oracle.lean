/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibTests.Oracle.Binary16
import FloatLibTests.Oracle.Block
import FloatLibTests.Oracle.Complex
import FloatLibTests.Oracle.ComplexTiming
import FloatLibTests.Oracle.Formats
import FloatLibTests.Oracle.IEEE2019
import FloatLibTests.Oracle.P3109Kernel
import FloatLibTests.Oracle.Posit
import FloatLibTests.Oracle.PositGeneral
import FloatLibTests.Oracle.Primitives
import FloatLibTests.Oracle.Reductions
import FloatLibTests.Oracle.TestFloat

/-!
# External comparison protocols

Dispatch the vector emitters and TestFloat stream checker used by `tests/oracles/`.
Each command owns its output format; binary16 writes binary words and the other emitters write text.
-/

def usage : String :=
  "usage: oracle COMMAND [ARGS]\n" ++
  "  primitives                         binary32/binary64 arithmetic vectors\n" ++
  "  reductions                         exact sum and dot-product vectors\n" ++
  "  formats onnx                       ONNX low-bit decoding vectors\n" ++
  "  formats p3109 MIN_WIDTH MAX_WIDTH   P3109 decoding vectors\n" ++
  "  binary16 {add|mul} INDEX COUNT      binary16 shard (binary output)\n" ++
  "  block CASE [ARGS]                  block-format codes for tensors on stdin\n" ++
  "  complex                            complex function requests on stdin\n" ++
  "  posit [REPORTS]                     check a SoftPosit binary stream\n" ++
  "  posit-general P ES                 posit operations with ES exponent bits, from stdin\n" ++
  "  p3109-kernel                       P3109 kernel operations on encodings, from stdin\n" ++
  "  testfloat FORMAT OP MODE [REPORTS]  check vectors from stdin\n" ++
  "  ieee2019 exhaustive                IEEE 754-2019 clause 9 on a six-bit format\n" ++
  "  ieee2019 check                     IEEE 754-2019 cases from stdin"

open FloatLibTests.Oracle in
/-- Dispatch a stream protocol, preserving its output and failure status. -/
public def main (args : List String) : IO UInt32 := do
  match args with
  | ["primitives"] => Primitives.run; return 0
  | ["reductions"] => Reductions.run; return 0
  | "formats" :: rest => Formats.run rest
  | "binary16" :: rest => Binary16.run rest; return 0
  | "block" :: rest => Block.run rest
  | ["complex"] => Complex.run; return 0
  | ["complex-timing"] => ComplexTiming.run; return 0
  | ["complex-timing", "functions"] => ComplexTiming.runFunctions; return 0
  | ["complex-timing", "pow"] => ComplexTiming.runPow; return 0
  | "posit" :: rest => Posit.run rest
  | "posit-general" :: rest => PositGeneral.run rest
  | "p3109-kernel" :: rest => P3109Kernel.run rest
  | "testfloat" :: rest => TestFloat.run rest
  | "ieee2019" :: rest => IEEE2019.run rest
  | ["--help"] | ["-h"] => IO.println usage; return 0
  | _ => IO.eprintln usage; return 2
