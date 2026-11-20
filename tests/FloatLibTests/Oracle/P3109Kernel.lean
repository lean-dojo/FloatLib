/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.Formats.P3109.KernelPath.Binary
import FloatLibTests.Oracle.Parsing

/-!
# P3109 kernel operations on encodings, for external comparison

`oracle p3109-kernel` reads one request per line from standard input and writes what the kernel
operations of `P3109.KernelPath.Core` return. A request is an operation name followed by
nineteen hexadecimal fields: the descriptors `K P sg ex` of three operand formats and of the
destination, and three operand codes. An operation with fewer operands ignores the others.

* An arithmetic operation, an extremum or `clamp` writes one line of codes: the result in each
  rounding mode and, within a mode, in each saturation mode (finite, propagate, none). The modes
  are toward zero, up, down, nearest away, nearest even, to odd, and then, for each random-word
  width from zero to three and each random word of that width, stochastic A, B and C.
* A comparison or a classification query writes one for true and zero for false, and a
  neighbour writes its code.
* `convertbinary` converts a word of a binary interchange format: the first descriptor holds
  the exponent width, the fraction width and the encoding of the source (zero for IEEE, one for
  a NaN at the largest pattern, two for a NaN at the negative zero, three for finite only).

`tests/oracles/p3109_kernel.py` compares the output with the operations of the interim report
on `Fraction`.
-/

namespace FloatLibTests.Oracle.P3109Kernel

open FloatLib.Floats.Formats.P3109
open FloatLibTests.Oracle.Parsing

/-- The rounding modes of one output line: the index, the width and the random word. -/
def modes : List (Nat × Nat × Nat) :=
  [(0, 0, 0), (1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0), (5, 0, 0)] ++
    (List.range 4).flatMap fun width =>
      (List.range (2 ^ width)).flatMap fun random =>
        [(6, width, random), (7, width, random), (8, width, random)]

/-- The binary format of an exponent width, a fraction width and an encoding index. -/
def binaryFormat? (expWidth fracWidth encoding : Nat) :
    Option FloatLib.Floats.Formats.BinaryInterchange.FloatFormat :=
  if h₁ : 2 ≤ expWidth then
    if h₂ : 0 < fracWidth then
      match encoding with
      | 0 => some (.ieee expWidth fracWidth h₁ h₂)
      | 1 => some (.finiteMaxNaN expWidth fracWidth h₁ h₂)
      | 2 => some (.finiteUnsignedZero expWidth fracWidth h₁ h₂)
      | 3 => some (.finite expWidth fracWidth h₁ h₂)
      | _ => none
    else none
  else none

/-- A projecting operation as a function of the destination policy, or `none`. -/
def projecting (operation : String) (f : Array Nat) : Option (Nat → Nat → Nat → Nat → Nat) :=
  let k₁ := f[0]!; let p₁ := f[1]!; let s₁ := f[2]!; let e₁ := f[3]!
  let k₂ := f[4]!; let p₂ := f[5]!; let s₂ := f[6]!; let e₂ := f[7]!
  let k₃ := f[8]!; let p₃ := f[9]!; let s₃ := f[10]!; let e₃ := f[11]!
  let k := f[12]!; let p := f[13]!; let s := f[14]!; let e := f[15]!
  let a := f[16]!; let b := f[17]!; let c := f[18]!
  let extremum (mx mag var : Nat) : Option (Nat → Nat → Nat → Nat → Nat) :=
    some fun mi n r si =>
      KernelPath.extremum mx mag var k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si a b
  match operation with
  | "convert" => some fun mi n r si => KernelPath.convert k₁ p₁ s₁ e₁ k p s e mi n r si 0 a
  | "convertbinary" =>
      (binaryFormat? k₁ p₁ s₁).map fun source => fun mi n r si =>
        KernelPath.convertBinary source k p s e mi n r si a
  | "negate" => some fun mi n r si => KernelPath.convert k₁ p₁ s₁ e₁ k p s e mi n r si 1 a
  | "abs" => some fun mi n r si => KernelPath.convert k₁ p₁ s₁ e₁ k p s e mi n r si 2 a
  | "add" =>
      some fun mi n r si => KernelPath.add k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si 0 a b
  | "sub" =>
      some fun mi n r si => KernelPath.add k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si 1 a b
  | "mul" => some fun mi n r si => KernelPath.mul k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si a b
  | "div" => some fun mi n r si => KernelPath.div k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si a b
  | "fma" =>
      some fun mi n r si =>
        KernelPath.fma k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k₃ p₃ s₃ e₃ k p s e mi n r si a b c
  | "faa" =>
      some fun mi n r si =>
        KernelPath.faa k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k₃ p₃ s₃ e₃ k p s e mi n r si a b c
  | "recip" => some fun mi n r si => KernelPath.recip k₁ p₁ s₁ e₁ k p s e mi n r si a
  | "copysign" =>
      some fun mi n r si => KernelPath.copySign k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si a b
  | "sqrt" => some fun mi n r si => KernelPath.sqrt k₁ p₁ s₁ e₁ k p s e mi n r si a
  | "rsqrt" => some fun mi n r si => KernelPath.rsqrt k₁ p₁ s₁ e₁ k p s e mi n r si a
  | "hypot" =>
      some fun mi n r si => KernelPath.hypot k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k p s e mi n r si a b
  | "min" => extremum 0 0 0
  | "max" => extremum 1 0 0
  | "minnum" => extremum 0 0 1
  | "maxnum" => extremum 1 0 1
  | "minmag" => extremum 0 1 0
  | "maxmag" => extremum 1 1 0
  | "minmagnum" => extremum 0 1 1
  | "maxmagnum" => extremum 1 1 1
  | "minfinite" => extremum 0 0 2
  | "maxfinite" => extremum 1 0 2
  | "clamp" =>
      some fun mi n r si =>
        KernelPath.clamp k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ k₃ p₃ s₃ e₃ k p s e mi n r si a b c
  | _ => none

/-- A comparison, a query or a neighbour as one number, or `none`. -/
def scalar (operation : String) (f : Array Nat) : Option Nat :=
  let k₁ := f[0]!; let p₁ := f[1]!; let s₁ := f[2]!; let e₁ := f[3]!
  let k₂ := f[4]!; let p₂ := f[5]!; let s₂ := f[6]!; let e₂ := f[7]!
  let a := f[16]!; let b := f[17]!
  let bit (value : Bool) : Option Nat := some (if value then 1 else 0)
  match operation with
  | "less" => bit (KernelPath.less k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ a b)
  | "equal" => bit (KernelPath.equal k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ a b)
  | "lessequal" => bit (KernelPath.lessEqual k₁ p₁ s₁ e₁ k₂ p₂ s₂ e₂ a b)
  | "iszero" => bit (Nat.beq a 0)
  | "isnan" => bit (KernelPath.isNaN k₁ s₁ a)
  | "isinf" => bit (KernelPath.isInfinite k₁ s₁ e₁ a)
  | "isfinite" => bit (KernelPath.isFinite k₁ s₁ e₁ a)
  | "issignminus" => bit (KernelPath.isSignMinus k₁ s₁ a)
  | "isone" => bit (KernelPath.isOne k₁ p₁ s₁ e₁ a)
  | "isnormal" => bit (KernelPath.isNormal k₁ p₁ s₁ e₁ a)
  | "issubnormal" => bit (KernelPath.isSubnormal k₁ p₁ s₁ e₁ a)
  | "nextup" => some (KernelPath.nextUp k₁ s₁ a)
  | "nextdown" => some (KernelPath.nextDown k₁ s₁ a)
  | _ => none

/-- The output line of one request, or `none` for a request that is not understood. -/
def answerLine (operation : String) (f : Array Nat) : Option String :=
  if f.size ≠ 19 then none
  else
    match projecting operation f with
    | some result =>
        some (" ".intercalate
          (modes.flatMap fun (mi, n, r) =>
            [0, 1, 2].map fun si => toString (result mi n r si)))
    | none => (scalar operation f).map toString

/-- Answer the requests of standard input, one per line. -/
partial def answer : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let rec loop (failures : UInt32) : IO UInt32 := do
    let line ← stdin.getLine
    if line.isEmpty then
      return failures
    match fields line with
    | operation :: rest =>
        match rest.mapM parseHex? >>= fun values => answerLine operation values.toArray with
        | some result =>
            stdout.putStrLn result
            loop failures
        | none =>
            stdout.putStrLn "error"
            loop (failures + 1)
    | [] => loop failures
  loop 0

/-- Dispatch `oracle p3109-kernel`. -/
public def run (arguments : List String) : IO UInt32 := do
  match arguments with
  | [] => answer
  | _ =>
      IO.eprintln "usage: oracle p3109-kernel"
      return 2

end FloatLibTests.Oracle.P3109Kernel
