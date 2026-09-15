/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep
import FloatLib.Floats.Formats.FiniteOnly
import FloatLib.Floats.Formats.OCP.FP8.E4M3FN
import FloatLib.Floats.Formats.OCP.FP8.E5M2

/-!
# Public FP8 execution benchmark

This executable compares each supported eight-bit floating-point format at two public boundaries:

* its nominal direct-byte type, whose persistent carrier is `UInt8`; and
* the same exact `FloatFormat` through the general descriptor carrier.

Both carriers use the shared `BenchmarkCarrier` input generation and workload templates, so they
round the same exact rationals before timing. This also keeps their result sinks comparable. Timed
loops are monomorphic, table initialization occurs during warmup, and every row records the
selected steady-state backend. The FMA rows deliberately identify the proved arithmetic fallback:
an exhaustive eight-bit ternary table would require 16,777,216 entries per format.
-/

open FloatLib.Floats
open FloatLibBenchmarks.Public.Sweep
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.StaticByte
open FloatLib.Floats.Formats.FiniteOnly
open FloatLib.Floats.Formats.OCP.FP8
open FloatLib.Numerics
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.FP8

private instance staticByteBenchmarkCarrier (F : Type) [Family F] :
    Support.BenchmarkCarrier F FloatFormat Model where
  format := Family.format (F := F)
  toModel := StaticByte.toModel
  ofModel := StaticByte.ofModel
  lowBits := fun value => UInt64.ofNat (StaticByte.toNatBits value)

abbrev OcpE4M3FN := ExecFloat E4M3FN
abbrev OcpE5M2 := ExecFloat E5M2
abbrev OnnxE4M3FNUZ := ExecFloat E4M3FNUZ
abbrev OnnxE5M2FNUZ := ExecFloat E5M2FNUZ

abbrev DescriptorE4M3FN := ExecFloat (Descriptor FloatFormat.e4m3fn)
abbrev DescriptorE5M2 := ExecFloat (Descriptor FloatFormat.e5m2)
abbrev DescriptorE4M3FNUZ := ExecFloat (Descriptor FloatFormat.e4m3fnuz)
abbrev DescriptorE5M2FNUZ := ExecFloat (Descriptor FloatFormat.e5m2fnuz)

def printNamedHeader : IO Unit :=
  IO.println <|
    "implementation,format,storageBits,precision,backend,policy,expectedCalls," ++
      "operation,iterations,totalNanos,sink"

def timeNamedRow (implementation formatName : String) (storageBits precision : Nat)
    (candidate : ExecFloat.Backend.Candidate) (policy : ExecFloat.Backend.Policy)
    (operation : String) (iterations : Nat)
    (run : Unit → UInt64) : IO Unit := do
  let sink ← IO.mkRef 0
  let start ← IO.monoNanosNow
  sink.set (run ())
  let stop ← IO.monoNanosNow
  let result ← sink.get
  IO.println <|
    s!"{implementation},{formatName},{storageBits},{precision},{candidate.name}," ++
      s!"{policy.profileName},{policy.expectedCalls},{operation}," ++
      s!"{iterations},{stop - start},{result.toNat}"

private def runBinary
    {F : Type} [EncodedFormat F] [Support.BenchmarkCarrier F FloatFormat Model]
    (implementation formatName : String)
    (candidate : ExecFloat.Backend.Candidate) (policy : ExecFloat.Backend.Policy)
    (operation : String) (precision : Nat)
    (workload : Nat → Array (ExecFloat F) → Array (ExecFloat F) → UInt64 → UInt64) :
    IO Unit := do
  let xs := inputsX F
  let ys := inputsY F
  let warmup ← IO.mkRef 0
  warmup.set (workload 32 xs ys 0)
  let iterations ← iterationsFor precision
  timeNamedRow implementation formatName 8 precision candidate policy operation iterations fun _ =>
    workload iterations xs ys 0

private def runTernary
    {F : Type} [EncodedFormat F] [Support.BenchmarkCarrier F FloatFormat Model]
    (implementation formatName : String)
    (candidate : ExecFloat.Backend.Candidate) (policy : ExecFloat.Backend.Policy)
    (operation : String) (precision : Nat)
    (workload : Nat → Array (ExecFloat F) → Array (ExecFloat F) →
      Array (ExecFloat F) → UInt64 → UInt64) : IO Unit := do
  let xs := inputsX F
  let ys := inputsY F
  let zs := xs.reverse
  let warmup ← IO.mkRef 0
  warmup.set (workload 32 xs ys zs 0)
  let iterations ← iterationsFor precision
  timeNamedRow implementation formatName 8 precision candidate policy operation iterations fun _ =>
    workload iterations xs ys zs 0

private def runUnary
    {F : Type} [EncodedFormat F] [Support.BenchmarkCarrier F FloatFormat Model]
    (implementation formatName : String)
    (candidate : ExecFloat.Backend.Candidate) (policy : ExecFloat.Backend.Policy)
    (operation : String) (precision : Nat)
    (workload : Nat → Array (ExecFloat F) → UInt64 → UInt64) : IO Unit := do
  let xs := inputsSqrt F
  let warmup ← IO.mkRef 0
  warmup.set (workload 32 xs 0)
  let iterations ← iterationsFor precision
  timeNamedRow implementation formatName 8 precision candidate policy operation iterations fun _ =>
    workload iterations xs 0

binary_sweep_workload nominalE4M3FNAdd : OcpE4M3FN using ExecFloat.add
binary_sweep_workload nominalE5M2Add : OcpE5M2 using ExecFloat.add
binary_sweep_workload nominalE4M3FNUZAdd : OnnxE4M3FNUZ using ExecFloat.add
binary_sweep_workload nominalE5M2FNUZAdd : OnnxE5M2FNUZ using ExecFloat.add
binary_sweep_workload descriptorE4M3FNAdd : DescriptorE4M3FN using ExecFloat.add
binary_sweep_workload descriptorE5M2Add : DescriptorE5M2 using ExecFloat.add
binary_sweep_workload descriptorE4M3FNUZAdd : DescriptorE4M3FNUZ using ExecFloat.add
binary_sweep_workload descriptorE5M2FNUZAdd : DescriptorE5M2FNUZ using ExecFloat.add

binary_sweep_workload nominalE4M3FNSub : OcpE4M3FN using ExecFloat.sub
binary_sweep_workload nominalE5M2Sub : OcpE5M2 using ExecFloat.sub
binary_sweep_workload nominalE4M3FNUZSub : OnnxE4M3FNUZ using ExecFloat.sub
binary_sweep_workload nominalE5M2FNUZSub : OnnxE5M2FNUZ using ExecFloat.sub
binary_sweep_workload descriptorE4M3FNSub : DescriptorE4M3FN using ExecFloat.sub
binary_sweep_workload descriptorE5M2Sub : DescriptorE5M2 using ExecFloat.sub
binary_sweep_workload descriptorE4M3FNUZSub : DescriptorE4M3FNUZ using ExecFloat.sub
binary_sweep_workload descriptorE5M2FNUZSub : DescriptorE5M2FNUZ using ExecFloat.sub

binary_sweep_workload nominalE4M3FNMul : OcpE4M3FN using ExecFloat.mul
binary_sweep_workload nominalE5M2Mul : OcpE5M2 using ExecFloat.mul
binary_sweep_workload nominalE4M3FNUZMul : OnnxE4M3FNUZ using ExecFloat.mul
binary_sweep_workload nominalE5M2FNUZMul : OnnxE5M2FNUZ using ExecFloat.mul
binary_sweep_workload descriptorE4M3FNMul : DescriptorE4M3FN using ExecFloat.mul
binary_sweep_workload descriptorE5M2Mul : DescriptorE5M2 using ExecFloat.mul
binary_sweep_workload descriptorE4M3FNUZMul : DescriptorE4M3FNUZ using ExecFloat.mul
binary_sweep_workload descriptorE5M2FNUZMul : DescriptorE5M2FNUZ using ExecFloat.mul

binary_sweep_workload nominalE4M3FNDiv : OcpE4M3FN using ExecFloat.div
binary_sweep_workload nominalE5M2Div : OcpE5M2 using ExecFloat.div
binary_sweep_workload nominalE4M3FNUZDiv : OnnxE4M3FNUZ using ExecFloat.div
binary_sweep_workload nominalE5M2FNUZDiv : OnnxE5M2FNUZ using ExecFloat.div
binary_sweep_workload descriptorE4M3FNDiv : DescriptorE4M3FN using ExecFloat.div
binary_sweep_workload descriptorE5M2Div : DescriptorE5M2 using ExecFloat.div
binary_sweep_workload descriptorE4M3FNUZDiv : DescriptorE4M3FNUZ using ExecFloat.div
binary_sweep_workload descriptorE5M2FNUZDiv : DescriptorE5M2FNUZ using ExecFloat.div

unary_sweep_workload nominalE4M3FNSqrt : OcpE4M3FN using ExecFloat.sqrt
unary_sweep_workload nominalE5M2Sqrt : OcpE5M2 using ExecFloat.sqrt
unary_sweep_workload nominalE4M3FNUZSqrt : OnnxE4M3FNUZ using ExecFloat.sqrt
unary_sweep_workload nominalE5M2FNUZSqrt : OnnxE5M2FNUZ using ExecFloat.sqrt
unary_sweep_workload descriptorE4M3FNSqrt : DescriptorE4M3FN using ExecFloat.sqrt
unary_sweep_workload descriptorE5M2Sqrt : DescriptorE5M2 using ExecFloat.sqrt
unary_sweep_workload descriptorE4M3FNUZSqrt : DescriptorE4M3FNUZ using ExecFloat.sqrt
unary_sweep_workload descriptorE5M2FNUZSqrt : DescriptorE5M2FNUZ using ExecFloat.sqrt

ternary_sweep_workload nominalE4M3FNFma : OcpE4M3FN using ExecFloat.fma
ternary_sweep_workload nominalE5M2Fma : OcpE5M2 using ExecFloat.fma
ternary_sweep_workload nominalE4M3FNUZFma : OnnxE4M3FNUZ using ExecFloat.fma
ternary_sweep_workload nominalE5M2FNUZFma : OnnxE5M2FNUZ using ExecFloat.fma
ternary_sweep_workload descriptorE4M3FNFma : DescriptorE4M3FN using ExecFloat.fma
ternary_sweep_workload descriptorE5M2Fma : DescriptorE5M2 using ExecFloat.fma
ternary_sweep_workload descriptorE4M3FNUZFma : DescriptorE4M3FNUZ using ExecFloat.fma
ternary_sweep_workload descriptorE5M2FNUZFma : DescriptorE5M2FNUZ using ExecFloat.fma

def runAdd : IO Unit := do
  runBinary "ExecFloat nominal" "OCP E4M3FN"
    (ExecFloat.Add.selectedCandidate (F := E4M3FN))
    (ExecFloat.Add.policy (F := E4M3FN)) "add" 4 nominalE4M3FNAdd
  runBinary "ExecFloat descriptor" "OCP E4M3FN"
    (ExecFloat.Add.selectedCandidate (F := Descriptor FloatFormat.e4m3fn))
    (ExecFloat.Add.policy (F := Descriptor FloatFormat.e4m3fn))
    "add" 4 descriptorE4M3FNAdd
  runBinary "ExecFloat nominal" "ONNX E4M3FNUZ"
    (ExecFloat.Add.selectedCandidate (F := E4M3FNUZ))
    (ExecFloat.Add.policy (F := E4M3FNUZ)) "add" 4 nominalE4M3FNUZAdd
  runBinary "ExecFloat descriptor" "ONNX E4M3FNUZ"
    (ExecFloat.Add.selectedCandidate (F := Descriptor FloatFormat.e4m3fnuz))
    (ExecFloat.Add.policy (F := Descriptor FloatFormat.e4m3fnuz))
    "add" 4 descriptorE4M3FNUZAdd
  runBinary "ExecFloat nominal" "OCP E5M2"
    (ExecFloat.Add.selectedCandidate (F := E5M2))
    (ExecFloat.Add.policy (F := E5M2)) "add" 3 nominalE5M2Add
  runBinary "ExecFloat descriptor" "OCP E5M2"
    (ExecFloat.Add.selectedCandidate (F := Descriptor FloatFormat.e5m2))
    (ExecFloat.Add.policy (F := Descriptor FloatFormat.e5m2))
    "add" 3 descriptorE5M2Add
  runBinary "ExecFloat nominal" "ONNX E5M2FNUZ"
    (ExecFloat.Add.selectedCandidate (F := E5M2FNUZ))
    (ExecFloat.Add.policy (F := E5M2FNUZ)) "add" 3 nominalE5M2FNUZAdd
  runBinary "ExecFloat descriptor" "ONNX E5M2FNUZ"
    (ExecFloat.Add.selectedCandidate (F := Descriptor FloatFormat.e5m2fnuz))
    (ExecFloat.Add.policy (F := Descriptor FloatFormat.e5m2fnuz))
    "add" 3 descriptorE5M2FNUZAdd

def runSub : IO Unit := do
  runBinary "ExecFloat nominal" "OCP E4M3FN"
    (ExecFloat.Sub.selectedCandidate (F := E4M3FN))
    (ExecFloat.Sub.policy (F := E4M3FN)) "sub" 4 nominalE4M3FNSub
  runBinary "ExecFloat descriptor" "OCP E4M3FN"
    (ExecFloat.Sub.selectedCandidate (F := Descriptor FloatFormat.e4m3fn))
    (ExecFloat.Sub.policy (F := Descriptor FloatFormat.e4m3fn))
    "sub" 4 descriptorE4M3FNSub
  runBinary "ExecFloat nominal" "ONNX E4M3FNUZ"
    (ExecFloat.Sub.selectedCandidate (F := E4M3FNUZ))
    (ExecFloat.Sub.policy (F := E4M3FNUZ)) "sub" 4 nominalE4M3FNUZSub
  runBinary "ExecFloat descriptor" "ONNX E4M3FNUZ"
    (ExecFloat.Sub.selectedCandidate (F := Descriptor FloatFormat.e4m3fnuz))
    (ExecFloat.Sub.policy (F := Descriptor FloatFormat.e4m3fnuz))
    "sub" 4 descriptorE4M3FNUZSub
  runBinary "ExecFloat nominal" "OCP E5M2"
    (ExecFloat.Sub.selectedCandidate (F := E5M2))
    (ExecFloat.Sub.policy (F := E5M2)) "sub" 3 nominalE5M2Sub
  runBinary "ExecFloat descriptor" "OCP E5M2"
    (ExecFloat.Sub.selectedCandidate (F := Descriptor FloatFormat.e5m2))
    (ExecFloat.Sub.policy (F := Descriptor FloatFormat.e5m2))
    "sub" 3 descriptorE5M2Sub
  runBinary "ExecFloat nominal" "ONNX E5M2FNUZ"
    (ExecFloat.Sub.selectedCandidate (F := E5M2FNUZ))
    (ExecFloat.Sub.policy (F := E5M2FNUZ)) "sub" 3 nominalE5M2FNUZSub
  runBinary "ExecFloat descriptor" "ONNX E5M2FNUZ"
    (ExecFloat.Sub.selectedCandidate (F := Descriptor FloatFormat.e5m2fnuz))
    (ExecFloat.Sub.policy (F := Descriptor FloatFormat.e5m2fnuz))
    "sub" 3 descriptorE5M2FNUZSub

def runMul : IO Unit := do
  runBinary "ExecFloat nominal" "OCP E4M3FN"
    (ExecFloat.Mul.selectedCandidate (F := E4M3FN))
    (ExecFloat.Mul.policy (F := E4M3FN)) "mul" 4 nominalE4M3FNMul
  runBinary "ExecFloat descriptor" "OCP E4M3FN"
    (ExecFloat.Mul.selectedCandidate (F := Descriptor FloatFormat.e4m3fn))
    (ExecFloat.Mul.policy (F := Descriptor FloatFormat.e4m3fn))
    "mul" 4 descriptorE4M3FNMul
  runBinary "ExecFloat nominal" "ONNX E4M3FNUZ"
    (ExecFloat.Mul.selectedCandidate (F := E4M3FNUZ))
    (ExecFloat.Mul.policy (F := E4M3FNUZ)) "mul" 4 nominalE4M3FNUZMul
  runBinary "ExecFloat descriptor" "ONNX E4M3FNUZ"
    (ExecFloat.Mul.selectedCandidate (F := Descriptor FloatFormat.e4m3fnuz))
    (ExecFloat.Mul.policy (F := Descriptor FloatFormat.e4m3fnuz))
    "mul" 4 descriptorE4M3FNUZMul
  runBinary "ExecFloat nominal" "OCP E5M2"
    (ExecFloat.Mul.selectedCandidate (F := E5M2))
    (ExecFloat.Mul.policy (F := E5M2)) "mul" 3 nominalE5M2Mul
  runBinary "ExecFloat descriptor" "OCP E5M2"
    (ExecFloat.Mul.selectedCandidate (F := Descriptor FloatFormat.e5m2))
    (ExecFloat.Mul.policy (F := Descriptor FloatFormat.e5m2))
    "mul" 3 descriptorE5M2Mul
  runBinary "ExecFloat nominal" "ONNX E5M2FNUZ"
    (ExecFloat.Mul.selectedCandidate (F := E5M2FNUZ))
    (ExecFloat.Mul.policy (F := E5M2FNUZ)) "mul" 3 nominalE5M2FNUZMul
  runBinary "ExecFloat descriptor" "ONNX E5M2FNUZ"
    (ExecFloat.Mul.selectedCandidate (F := Descriptor FloatFormat.e5m2fnuz))
    (ExecFloat.Mul.policy (F := Descriptor FloatFormat.e5m2fnuz))
    "mul" 3 descriptorE5M2FNUZMul

def runDiv : IO Unit := do
  runBinary "ExecFloat nominal" "OCP E4M3FN"
    (ExecFloat.Div.selectedCandidate (F := E4M3FN))
    (ExecFloat.Div.policy (F := E4M3FN)) "div" 4 nominalE4M3FNDiv
  runBinary "ExecFloat descriptor" "OCP E4M3FN"
    (ExecFloat.Div.selectedCandidate (F := Descriptor FloatFormat.e4m3fn))
    (ExecFloat.Div.policy (F := Descriptor FloatFormat.e4m3fn))
    "div" 4 descriptorE4M3FNDiv
  runBinary "ExecFloat nominal" "ONNX E4M3FNUZ"
    (ExecFloat.Div.selectedCandidate (F := E4M3FNUZ))
    (ExecFloat.Div.policy (F := E4M3FNUZ)) "div" 4 nominalE4M3FNUZDiv
  runBinary "ExecFloat descriptor" "ONNX E4M3FNUZ"
    (ExecFloat.Div.selectedCandidate (F := Descriptor FloatFormat.e4m3fnuz))
    (ExecFloat.Div.policy (F := Descriptor FloatFormat.e4m3fnuz))
    "div" 4 descriptorE4M3FNUZDiv
  runBinary "ExecFloat nominal" "OCP E5M2"
    (ExecFloat.Div.selectedCandidate (F := E5M2))
    (ExecFloat.Div.policy (F := E5M2)) "div" 3 nominalE5M2Div
  runBinary "ExecFloat descriptor" "OCP E5M2"
    (ExecFloat.Div.selectedCandidate (F := Descriptor FloatFormat.e5m2))
    (ExecFloat.Div.policy (F := Descriptor FloatFormat.e5m2))
    "div" 3 descriptorE5M2Div
  runBinary "ExecFloat nominal" "ONNX E5M2FNUZ"
    (ExecFloat.Div.selectedCandidate (F := E5M2FNUZ))
    (ExecFloat.Div.policy (F := E5M2FNUZ)) "div" 3 nominalE5M2FNUZDiv
  runBinary "ExecFloat descriptor" "ONNX E5M2FNUZ"
    (ExecFloat.Div.selectedCandidate (F := Descriptor FloatFormat.e5m2fnuz))
    (ExecFloat.Div.policy (F := Descriptor FloatFormat.e5m2fnuz))
    "div" 3 descriptorE5M2FNUZDiv

def runSqrt : IO Unit := do
  runUnary "ExecFloat nominal" "OCP E4M3FN"
    (ExecFloat.Sqrt.selectedCandidate (F := E4M3FN))
    (ExecFloat.Sqrt.policy (F := E4M3FN)) "sqrt" 4 nominalE4M3FNSqrt
  runUnary "ExecFloat descriptor" "OCP E4M3FN"
    (ExecFloat.Sqrt.selectedCandidate (F := Descriptor FloatFormat.e4m3fn))
    (ExecFloat.Sqrt.policy (F := Descriptor FloatFormat.e4m3fn))
    "sqrt" 4 descriptorE4M3FNSqrt
  runUnary "ExecFloat nominal" "ONNX E4M3FNUZ"
    (ExecFloat.Sqrt.selectedCandidate (F := E4M3FNUZ))
    (ExecFloat.Sqrt.policy (F := E4M3FNUZ)) "sqrt" 4 nominalE4M3FNUZSqrt
  runUnary "ExecFloat descriptor" "ONNX E4M3FNUZ"
    (ExecFloat.Sqrt.selectedCandidate (F := Descriptor FloatFormat.e4m3fnuz))
    (ExecFloat.Sqrt.policy (F := Descriptor FloatFormat.e4m3fnuz))
    "sqrt" 4 descriptorE4M3FNUZSqrt
  runUnary "ExecFloat nominal" "OCP E5M2"
    (ExecFloat.Sqrt.selectedCandidate (F := E5M2))
    (ExecFloat.Sqrt.policy (F := E5M2)) "sqrt" 3 nominalE5M2Sqrt
  runUnary "ExecFloat descriptor" "OCP E5M2"
    (ExecFloat.Sqrt.selectedCandidate (F := Descriptor FloatFormat.e5m2))
    (ExecFloat.Sqrt.policy (F := Descriptor FloatFormat.e5m2))
    "sqrt" 3 descriptorE5M2Sqrt
  runUnary "ExecFloat nominal" "ONNX E5M2FNUZ"
    (ExecFloat.Sqrt.selectedCandidate (F := E5M2FNUZ))
    (ExecFloat.Sqrt.policy (F := E5M2FNUZ)) "sqrt" 3 nominalE5M2FNUZSqrt
  runUnary "ExecFloat descriptor" "ONNX E5M2FNUZ"
    (ExecFloat.Sqrt.selectedCandidate (F := Descriptor FloatFormat.e5m2fnuz))
    (ExecFloat.Sqrt.policy (F := Descriptor FloatFormat.e5m2fnuz))
    "sqrt" 3 descriptorE5M2FNUZSqrt

def runFma : IO Unit := do
  runTernary "ExecFloat nominal" "OCP E4M3FN"
    (ExecFloat.Fma.selectedCandidate (F := E4M3FN))
    (ExecFloat.Fma.policy (F := E4M3FN)) "fma" 4 nominalE4M3FNFma
  runTernary "ExecFloat descriptor" "OCP E4M3FN"
    (ExecFloat.Fma.selectedCandidate (F := Descriptor FloatFormat.e4m3fn))
    (ExecFloat.Fma.policy (F := Descriptor FloatFormat.e4m3fn))
    "fma" 4 descriptorE4M3FNFma
  runTernary "ExecFloat nominal" "ONNX E4M3FNUZ"
    (ExecFloat.Fma.selectedCandidate (F := E4M3FNUZ))
    (ExecFloat.Fma.policy (F := E4M3FNUZ)) "fma" 4 nominalE4M3FNUZFma
  runTernary "ExecFloat descriptor" "ONNX E4M3FNUZ"
    (ExecFloat.Fma.selectedCandidate (F := Descriptor FloatFormat.e4m3fnuz))
    (ExecFloat.Fma.policy (F := Descriptor FloatFormat.e4m3fnuz))
    "fma" 4 descriptorE4M3FNUZFma
  runTernary "ExecFloat nominal" "OCP E5M2"
    (ExecFloat.Fma.selectedCandidate (F := E5M2))
    (ExecFloat.Fma.policy (F := E5M2)) "fma" 3 nominalE5M2Fma
  runTernary "ExecFloat descriptor" "OCP E5M2"
    (ExecFloat.Fma.selectedCandidate (F := Descriptor FloatFormat.e5m2))
    (ExecFloat.Fma.policy (F := Descriptor FloatFormat.e5m2))
    "fma" 3 descriptorE5M2Fma
  runTernary "ExecFloat nominal" "ONNX E5M2FNUZ"
    (ExecFloat.Fma.selectedCandidate (F := E5M2FNUZ))
    (ExecFloat.Fma.policy (F := E5M2FNUZ)) "fma" 3 nominalE5M2FNUZFma
  runTernary "ExecFloat descriptor" "ONNX E5M2FNUZ"
    (ExecFloat.Fma.selectedCandidate (F := Descriptor FloatFormat.e5m2fnuz))
    (ExecFloat.Fma.policy (F := Descriptor FloatFormat.e5m2fnuz))
    "fma" 3 descriptorE5M2FNUZFma

def run : IO Unit := do
  printNamedHeader
  runAdd
  runSub
  runMul
  runDiv
  runSqrt
  runFma

end FloatLibBenchmarks.Public.FP8

public def main : IO Unit :=
  FloatLibBenchmarks.Public.FP8.run
