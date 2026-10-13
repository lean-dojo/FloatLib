/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLib.Floats.ExecFloat.Runtime
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Value.Core
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan.Instances
import FloatLib.Floats.Formats.BinaryInterchange.Configured.Rounding.Runtime

/-!
# Exhaustive 16-bit arithmetic and binary32 square root

For binary16 and bfloat16, `pairs` evaluates addition, subtraction, multiplication, or division on
a block of operand pairs in one rounding direction. The pair with index `i` has first operand
`i / 65536` and second operand `i % 65536`, so 65,536 blocks of one first operand each cover all
`2^32` ordered pairs. For binary32, `sqrt` evaluates a block of consecutive encodings.

Each result records the encoded value and the five IEEE exception flags of
`Model.*WithStatus`. In nearest-even mode it also records whether the planner-selected kernel
behind the ordinary operator (`+`, `-`, `*`, `/`, `ExecFloat.sqrt`) returns a different encoding.
An external program compares the block with Berkeley SoftFloat or MPFR.

A 16-bit result is one little-endian 32-bit word: value in bits 0–15, flags in bits 16–20
(inexact, underflow, overflow, divide by zero, invalid), bit 24 if the kernel returns a different
non-NaN encoding, and bit 25 if both are NaNs with different encodings. A binary32 result is a
64-bit word with the value in bits 0–31 and the same fields shifted up by 16.
-/

open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

namespace FloatLibBenchmarks.Public.Exhaustive

abbrev H := ExecFloat.Binary 5 10
abbrev BF := ExecFloat.Binary 8 7
abbrev S := ExecFloat.Binary 8 23

def statusBits (status : Model.IEEEStatus) : Nat :=
  (if status.inexact then 1 else 0) +
  (if status.underflow then 2 else 0) +
  (if status.overflow then 4 else 0) +
  (if status.divideByZero then 8 else 0) +
  (if status.invalid then 16 else 0)

def parseRounding? : String → Option Model.IEEERoundingMode
  | "near_even" => some .nearestEven
  | "minMag" => some .towardZero
  | "min" => some .towardNegativeInfinity
  | "max" => some .towardPositiveInfinity
  | _ => none

/-- One operation of one format: the kernel result and the model's value and flags. -/
structure Operation (T : Type) where
  ofBits : Nat → T
  toBits : T → Nat
  isNaN : T → Bool
  kernel : T → T → T
  status : T → T → Model.IEEERoundingMode → T × Nat

/-- Pick a binary operation of one configured binary format by its TestFloat name. -/
macro "binaryOperation%" name:term : term =>
  `(match ($name : String) with
    | "add" => some (Operation.mk ExecFloat.Binary.ofNatBits ExecFloat.Binary.toNatBits
        ExecFloat.Binary.isNaN (· + ·) fun x y m =>
          let o := ExecFloat.Binary.addWithStatus x y m; (o.1, statusBits o.2))
    | "sub" => some (Operation.mk ExecFloat.Binary.ofNatBits ExecFloat.Binary.toNatBits
        ExecFloat.Binary.isNaN (· - ·) fun x y m =>
          let o := ExecFloat.Binary.subWithStatus x y m; (o.1, statusBits o.2))
    | "mul" => some (Operation.mk ExecFloat.Binary.ofNatBits ExecFloat.Binary.toNatBits
        ExecFloat.Binary.isNaN (· * ·) fun x y m =>
          let o := ExecFloat.Binary.mulWithStatus x y m; (o.1, statusBits o.2))
    | "div" => some (Operation.mk ExecFloat.Binary.ofNatBits ExecFloat.Binary.toNatBits
        ExecFloat.Binary.isNaN (· / ·) fun x y m =>
          let o := ExecFloat.Binary.divWithStatus x y m; (o.1, statusBits o.2))
    | _ => none)

/-- The kernel fields of a result word: bit 0 for a different non-NaN encoding, bit 1 for
different NaN encodings. -/
@[inline] def kernelBits {T : Type} (op : Operation T) (kernel model : T) : Nat :=
  let k := op.toBits kernel
  let v := op.toBits model
  if k == v then 0 else if op.isNaN kernel && op.isNaN model then 2 else 1

def pairs {T : Type} (op : Operation T) (mode : Model.IEEERoundingMode)
    (start count : Nat) (out : System.FilePath) : IO Unit := do
  let mut buf := ByteArray.emptyWithCapacity (4 * count)
  for i in [0:count] do
    let n := start + i
    let x := op.ofBits (n / 65536)
    let y := op.ofBits (n % 65536)
    let (value, flags) := op.status x y mode
    let kernel := if mode == .nearestEven then kernelBits op (op.kernel x y) value else 0
    let w : UInt32 := (op.toBits value + flags * 65536 + kernel * 16777216).toUInt32
    buf := ((buf.push w.toUInt8).push (w >>> 8).toUInt8).push (w >>> 16).toUInt8
      |>.push (w >>> 24).toUInt8
  IO.FS.writeBinFile out buf

def sqrtRange (mode : Model.IEEERoundingMode) (start count : Nat) (out : System.FilePath) :
    IO Unit := do
  let mut buf := ByteArray.emptyWithCapacity (8 * count)
  for i in [0:count] do
    let x : S := ExecFloat.Binary.ofNatBits (start + i)
    let o := ExecFloat.Binary.sqrtWithStatus x mode
    let value := ExecFloat.Binary.toNatBits o.1
    let kernel :=
      if mode == .nearestEven then
        let k := ExecFloat.Binary.toNatBits (ExecFloat.sqrt x)
        if k == value then 0
        else if ExecFloat.Binary.isNaN (ExecFloat.sqrt x) && ExecFloat.Binary.isNaN o.1 then 2
        else 1
      else 0
    let w : UInt64 :=
      (value + statusBits o.2 * 4294967296 + kernel * 1099511627776).toUInt64
    for j in [0:8] do
      buf := buf.push (w >>> (8 * j).toUInt64).toUInt8
  IO.FS.writeBinFile out buf

end FloatLibBenchmarks.Public.Exhaustive

open FloatLibBenchmarks.Public.Exhaustive in
public def main (args : List String) : IO UInt32 := do
  let usage := "usage: execFloatExhaustive pairs f16|bf16 add|sub|mul|div MODE START COUNT OUT\n" ++
    "       execFloatExhaustive sqrt f32 sqrt MODE START COUNT OUT\n" ++
    "MODE is near_even, minMag, min, or max"
  match args with
  | [kind, format, name, modeText, start, count, out] =>
      match parseRounding? modeText with
      | none => IO.eprintln usage; return 1
      | some mode =>
        match kind, format with
        | "pairs", "f16" =>
            match (binaryOperation% name : Option (Operation H)) with
            | some op => pairs op mode start.toNat! count.toNat! out; return 0
            | none => IO.eprintln usage; return 1
        | "pairs", "bf16" =>
            match (binaryOperation% name : Option (Operation BF)) with
            | some op => pairs op mode start.toNat! count.toNat! out; return 0
            | none => IO.eprintln usage; return 1
        | "sqrt", "f32" =>
            sqrtRange mode start.toNat! count.toNat! out; return 0
        | _, _ => IO.eprintln usage; return 1
  | _ =>
      IO.eprintln usage
      return 1
