/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Support.Environment
import FloatLib.Floats.ExecFloat
import FloatLib.Floats.Formats.BinaryInterchange.Configured
import FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Runtime

/-!
# Configured binary dispatch benchmark

This benchmark measures the ordinary user-facing parameterized types

```lean
ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)
ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)
```

at two otherwise identical observation boundaries:

* `ConfiguredPublic`: the public `ExecFloat` operation;
* `ConfiguredDirect`: the exact first-order kernel selected for that configured type.

Both rows consume the same preconstructed values, execute the same monomorphic tail-recursive
loop, mix the same raw result into the same sink, and are checked for pointwise and whole-loop
equality before timing. Consequently, their ratio measures residual public-dispatch cost rather
than a different numerical algorithm. Odd and even trials reverse the pair order through
`BENCH_REVERSE`, reducing systematic placement bias.

All twelve public and direct rows use the proved fixed-format word kernels. The explicit
`NativeFPU.Unchecked` host API is intentionally outside this abstraction-cost benchmark. The
generated-code contract in `benchmarks/scripts/checks/configured-binary-codegen.sh` separately
checks native carrier signatures, absence of runtime capability closures, and the opt-in host
surface.
-/

namespace FloatLibBenchmarks.Kernels.ConfiguredBinary

open FloatLib.Floats
open FloatLibBenchmarks.Support.Environment
open FloatLib.Floats.Formats.BinaryInterchange

/-- The user spelling for IEEE 754 binary32 used by the benchmark. -/
abbrev Binary32 :=
  ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)

/-- The user spelling for IEEE 754 binary64 used by the benchmark. -/
abbrev Binary64 :=
  ExecFloat.Binary (exponentBits := 11) (fractionBits := 52)

private instance : Inhabited Binary32 :=
  ⟨Configured.NativeFPU.ofBinary32Bits 0⟩

private instance : Inhabited Binary64 :=
  ⟨Configured.NativeFPU.ofBinary64Bits 0⟩

/-- Mix one binary32 result into the benchmark sink. -/
@[inline] def mix32 (sink value : UInt32) : UInt32 :=
  (sink ^^^ value) * 16777619

/-- Mix one binary64 result into the benchmark sink. -/
@[inline] def mix64 (sink value : UInt64) : UInt64 :=
  (sink ^^^ value) * 1099511628211

/-- Observe a configured binary32 value without decoding it. -/
@[always_inline, inline] def observe32 (value : Binary32) : UInt32 :=
  value.raw.1

/-- Observe a configured binary64 value without decoding it. -/
@[always_inline, inline] def observe64 (value : Binary64) : UInt64 :=
  value.raw.1

private def binary32OffsetSpan : Nat :=
  2 ^ 21

private def binary64OffsetSpan : Nat :=
  2 ^ 50

/-- First deterministic family of finite normal binary32 words near magnitude one. -/
def inputWords32X : Array UInt32 :=
  (Array.range 16).map fun i =>
    let sign : UInt32 := if i % 5 = 0 then 0x80000000 else 0
    let fraction := UInt32.ofNat ((i * 0x1f123bb5 + 12345) % binary32OffsetSpan)
    sign ||| 0x3f800000 ||| fraction

/-- Second deterministic family of finite normal binary32 words near magnitude one. -/
def inputWords32Y : Array UInt32 :=
  (Array.range 16).map fun i =>
    let sign : UInt32 := if i % 3 = 0 then 0x80000000 else 0
    let fraction := UInt32.ofNat ((i * 0x2a3456d7 + 54321) % binary32OffsetSpan)
    sign ||| 0x3f800000 ||| fraction

/-- Nonnegative binary32 inputs used only by square root. -/
def inputWords32Sqrt : Array UInt32 :=
  inputWords32X.map fun bits => bits &&& 0x7fffffff

/-- First deterministic family of finite normal binary64 words near magnitude one. -/
def inputWords64X : Array UInt64 :=
  (Array.range 16).map fun i =>
    let sign : UInt64 := if i % 5 = 0 then 0x8000000000000000 else 0
    let fraction :=
      UInt64.ofNat ((i * 0x1f123bb5 + 12345) % binary64OffsetSpan)
    sign ||| 0x3ff0000000000000 ||| fraction

/-- Second deterministic family of finite normal binary64 words near magnitude one. -/
def inputWords64Y : Array UInt64 :=
  (Array.range 16).map fun i =>
    let sign : UInt64 := if i % 3 = 0 then 0x8000000000000000 else 0
    let fraction :=
      UInt64.ofNat ((i * 0x2a3456d7 + 54321) % binary64OffsetSpan)
    sign ||| 0x3ff0000000000000 ||| fraction

/-- Nonnegative binary64 inputs used only by square root. -/
def inputWords64Sqrt : Array UInt64 :=
  inputWords64X.map fun bits => bits &&& 0x7fffffffffffffff

/-- Construct configured binary32 values before entering a timed loop. -/
def wrap32 (words : Array UInt32) : Array Binary32 :=
  words.map Configured.NativeFPU.ofBinary32Bits

/-- Construct configured binary64 values before entering a timed loop. -/
def wrap64 (words : Array UInt64) : Array Binary64 :=
  words.map Configured.NativeFPU.ofBinary64Bits

syntax "binary32_binary_workload " ident " using " term : command
syntax "binary32_unary_workload " ident " using " term : command
syntax "binary32_ternary_workload " ident " using " term : command
syntax "binary64_binary_workload " ident " using " term : command
syntax "binary64_unary_workload " ident " using " term : command
syntax "binary64_ternary_workload " ident " using " term : command

macro_rules
  | `(binary32_binary_workload $name:ident using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array Binary32 → Array Binary32 → UInt32 → UInt32
        | 0, _, _, sink => sink
        | n + 1, xs, ys, sink =>
            let i := n &&& 15
            let result : Binary32 := $operation xs[i]! ys[i]!
            $name n xs ys (mix32 sink (observe32 result)))
  | `(binary32_unary_workload $name:ident using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array Binary32 → UInt32 → UInt32
        | 0, _, sink => sink
        | n + 1, xs, sink =>
            let i := n &&& 15
            let result : Binary32 := $operation xs[i]!
            $name n xs (mix32 sink (observe32 result)))
  | `(binary32_ternary_workload $name:ident using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array Binary32 → Array Binary32 → Array Binary32 → UInt32 → UInt32
        | 0, _, _, _, sink => sink
        | n + 1, xs, ys, zs, sink =>
            let i := n &&& 15
            let result : Binary32 := $operation xs[i]! ys[i]! zs[i]!
            $name n xs ys zs (mix32 sink (observe32 result)))
  | `(binary64_binary_workload $name:ident using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array Binary64 → Array Binary64 → UInt64 → UInt64
        | 0, _, _, sink => sink
        | n + 1, xs, ys, sink =>
            let i := n &&& 15
            let result : Binary64 := $operation xs[i]! ys[i]!
            $name n xs ys (mix64 sink (observe64 result)))
  | `(binary64_unary_workload $name:ident using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array Binary64 → UInt64 → UInt64
        | 0, _, sink => sink
        | n + 1, xs, sink =>
            let i := n &&& 15
            let result : Binary64 := $operation xs[i]!
            $name n xs (mix64 sink (observe64 result)))
  | `(binary64_ternary_workload $name:ident using $operation:term) =>
      `(@[noinline] def $name :
          Nat → Array Binary64 → Array Binary64 → Array Binary64 → UInt64 → UInt64
        | 0, _, _, _, sink => sink
        | n + 1, xs, ys, zs, sink =>
            let i := n &&& 15
            let result : Binary64 := $operation xs[i]! ys[i]! zs[i]!
            $name n xs ys zs (mix64 sink (observe64 result)))

binary32_binary_workload public32Add using ExecFloat.add
binary32_binary_workload public32Sub using ExecFloat.sub
binary32_binary_workload public32Mul using ExecFloat.mul
binary32_binary_workload public32Div using ExecFloat.div
binary32_unary_workload public32Sqrt using ExecFloat.sqrt
binary32_ternary_workload public32Fma using ExecFloat.fma

binary32_binary_workload direct32Add using Configured.Backend.wordAdd
binary32_binary_workload direct32Sub using Configured.Backend.wordSub
binary32_binary_workload direct32Mul using Configured.Backend.wordMul
binary32_binary_workload direct32Div using Configured.Backend.wordDiv
binary32_unary_workload direct32Sqrt using Configured.Backend.wordSqrt
binary32_ternary_workload direct32Fma using Configured.NativeFPU.softwareFma32

binary64_binary_workload public64Add using ExecFloat.add
binary64_binary_workload public64Sub using ExecFloat.sub
binary64_binary_workload public64Mul using ExecFloat.mul
binary64_binary_workload public64Div using ExecFloat.div
binary64_unary_workload public64Sqrt using ExecFloat.sqrt
binary64_ternary_workload public64Fma using ExecFloat.fma

binary64_binary_workload direct64Add using Configured.Backend.wordAdd
binary64_binary_workload direct64Sub using Configured.Backend.wordSub
binary64_binary_workload direct64Mul using Configured.Backend.wordMul
binary64_binary_workload direct64Div using Configured.Backend.wordDiv
binary64_unary_workload direct64Sqrt using Configured.Backend.wordSqrt
binary64_ternary_workload direct64Fma using Configured.NativeFPU.softwareFma64

/-- Read and validate the common iteration-count override. -/
def iterations : IO Nat := do
  positiveNat "BENCH_ITERATIONS" 250000

/-- Whether this trial measures each direct row before its corresponding public row. -/
def reversePairs : IO Bool := do
  bool "BENCH_REVERSE"

/-- Force one complete loop before measuring it. -/
def warmup {α : Type} (initial : α) (run : Unit → α) : IO Unit := do
  let sink ← IO.mkRef initial
  sink.set (run ())

/--
Measure one monomorphic loop.

The mutable reference is allocated before the first timestamp. Its write prevents the pure loop
from being floated below the second timestamp by generated-code optimization.
-/
def timeRow {α : Type} [ToString α] (initial : α)
    (width implementation operation executionClass : String)
    (count : Nat) (run : Unit → α) : IO Unit := do
  warmup initial run
  let resultRef ← IO.mkRef initial
  let start ← IO.monoNanosNow
  resultRef.set (run ())
  let stop ← IO.monoNanosNow
  let sink ← resultRef.get
  IO.println
    s!"{width},{implementation},{operation},{executionClass},{count},{stop - start},{sink}"

/-- Time a matched public/direct pair in the trial's chosen order. -/
def timePair {α : Type} [BEq α] [ToString α] (initial : α)
    (reverse : Bool) (width operation executionClass : String) (count : Nat)
    (publicRun directRun : Unit → α) : IO Unit := do
  let publicSink := publicRun ()
  let directSink := directRun ()
  unless publicSink == directSink do
    throw <| IO.userError <|
      s!"configured binary{width} loop mismatch for {operation}: " ++
      s!"public={publicSink}, direct={directSink}"
  let publicRow :=
    timeRow initial width "ConfiguredPublic" operation executionClass count publicRun
  let directRow :=
    timeRow initial width "ConfiguredDirect" operation executionClass count directRun
  if reverse then
    directRow
    publicRow
  else
    publicRow
    directRow

/-- Reject a pointwise mismatch before the benchmark can publish timings. -/
def checkSame {α : Type} [BEq α] [ToString α]
    (width operation : String) (publicValue directValue : α) : IO Unit := do
  unless publicValue == directValue do
    throw <| IO.userError <|
      s!"configured binary{width} mismatch for {operation}: " ++
      s!"public={publicValue}, direct={directValue}"

/-- Pointwise semantic preflight for every generated binary32 operand. -/
def verify32 (xs ys sqrtXs : Array Binary32) : IO Unit := do
  for i in [0:16] do
    checkSame "32" "add"
      (observe32 <| ExecFloat.add xs[i]! ys[i]!)
      (observe32 <| Configured.Backend.wordAdd xs[i]! ys[i]!)
    checkSame "32" "sub"
      (observe32 <| ExecFloat.sub xs[i]! ys[i]!)
      (observe32 <| Configured.Backend.wordSub xs[i]! ys[i]!)
    checkSame "32" "mul"
      (observe32 <| ExecFloat.mul xs[i]! ys[i]!)
      (observe32 <| Configured.Backend.wordMul xs[i]! ys[i]!)
    checkSame "32" "div"
      (observe32 <| ExecFloat.div xs[i]! ys[i]!)
      (observe32 <| Configured.Backend.wordDiv xs[i]! ys[i]!)
    checkSame "32" "sqrt"
      (observe32 <| ExecFloat.sqrt sqrtXs[i]!)
      (observe32 <| Configured.Backend.wordSqrt sqrtXs[i]!)
    checkSame "32" "fma"
      (observe32 <| ExecFloat.fma xs[i]! ys[i]! xs[i]!)
      (observe32 <| Configured.NativeFPU.softwareFma32 xs[i]! ys[i]! xs[i]!)

/-- Pointwise semantic preflight for every generated binary64 operand. -/
def verify64 (xs ys sqrtXs : Array Binary64) : IO Unit := do
  for i in [0:16] do
    checkSame "64" "add"
      (observe64 <| ExecFloat.add xs[i]! ys[i]!)
      (observe64 <| Configured.Backend.wordAdd xs[i]! ys[i]!)
    checkSame "64" "sub"
      (observe64 <| ExecFloat.sub xs[i]! ys[i]!)
      (observe64 <| Configured.Backend.wordSub xs[i]! ys[i]!)
    checkSame "64" "mul"
      (observe64 <| ExecFloat.mul xs[i]! ys[i]!)
      (observe64 <| Configured.Backend.wordMul xs[i]! ys[i]!)
    checkSame "64" "div"
      (observe64 <| ExecFloat.div xs[i]! ys[i]!)
      (observe64 <| Configured.Backend.wordDiv xs[i]! ys[i]!)
    checkSame "64" "sqrt"
      (observe64 <| ExecFloat.sqrt sqrtXs[i]!)
      (observe64 <| Configured.Backend.wordSqrt sqrtXs[i]!)
    checkSame "64" "fma"
      (observe64 <| ExecFloat.fma xs[i]! ys[i]! xs[i]!)
      (observe64 <| Configured.NativeFPU.softwareFma64 xs[i]! ys[i]! xs[i]!)

/-- Measure all twelve public/direct operation pairs. -/
def run : IO Unit := do
  let count ← iterations
  let reverse ← reversePairs

  let xs32 := wrap32 inputWords32X
  let ys32 := wrap32 inputWords32Y
  let sqrtXs32 := wrap32 inputWords32Sqrt
  let xs64 := wrap64 inputWords64X
  let ys64 := wrap64 inputWords64Y
  let sqrtXs64 := wrap64 inputWords64Sqrt

  verify32 xs32 ys32 sqrtXs32
  verify64 xs64 ys64 sqrtXs64

  IO.println
    "width,implementation,operation,executionClass,iterations,totalNanos,sink"

  timePair 0 reverse "32" "add" "proved-fixed-format-word-kernel" count
    (fun _ => public32Add count xs32 ys32 0)
    (fun _ => direct32Add count xs32 ys32 0)
  timePair 0 reverse "32" "sub" "proved-fixed-format-word-kernel" count
    (fun _ => public32Sub count xs32 ys32 0)
    (fun _ => direct32Sub count xs32 ys32 0)
  timePair 0 reverse "32" "mul" "proved-fixed-format-word-kernel" count
    (fun _ => public32Mul count xs32 ys32 0)
    (fun _ => direct32Mul count xs32 ys32 0)
  timePair 0 reverse "32" "div" "proved-fixed-format-word-kernel" count
    (fun _ => public32Div count xs32 ys32 0)
    (fun _ => direct32Div count xs32 ys32 0)
  timePair 0 reverse "32" "sqrt" "proved-fixed-format-word-kernel" count
    (fun _ => public32Sqrt count sqrtXs32 0)
    (fun _ => direct32Sqrt count sqrtXs32 0)
  timePair 0 reverse "32" "fma" "proved-fixed-format-word-kernel" count
    (fun _ => public32Fma count xs32 ys32 xs32 0)
    (fun _ => direct32Fma count xs32 ys32 xs32 0)

  timePair 0 reverse "64" "add" "proved-fixed-format-word-kernel" count
    (fun _ => public64Add count xs64 ys64 0)
    (fun _ => direct64Add count xs64 ys64 0)
  timePair 0 reverse "64" "sub" "proved-fixed-format-word-kernel" count
    (fun _ => public64Sub count xs64 ys64 0)
    (fun _ => direct64Sub count xs64 ys64 0)
  timePair 0 reverse "64" "mul" "proved-fixed-format-word-kernel" count
    (fun _ => public64Mul count xs64 ys64 0)
    (fun _ => direct64Mul count xs64 ys64 0)
  timePair 0 reverse "64" "div" "proved-fixed-format-word-kernel" count
    (fun _ => public64Div count xs64 ys64 0)
    (fun _ => direct64Div count xs64 ys64 0)
  timePair 0 reverse "64" "sqrt" "proved-fixed-format-word-kernel" count
    (fun _ => public64Sqrt count sqrtXs64 0)
    (fun _ => direct64Sqrt count sqrtXs64 0)
  timePair 0 reverse "64" "fma" "proved-fixed-format-word-kernel" count
    (fun _ => public64Fma count xs64 ys64 xs64 0)
    (fun _ => direct64Fma count xs64 ys64 xs64 0)

end FloatLibBenchmarks.Kernels.ConfiguredBinary

/-- Native executable entry point. -/
public def main : IO Unit :=
  FloatLibBenchmarks.Kernels.ConfiguredBinary.run
