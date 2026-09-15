/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Support.Environment
import FloatLibBenchmarks.Support.Posit

/-!
# Posit interoperability vectors

This executable emits the complete encoded inputs and results used by the public posit benchmark.
Independent implementations consume these vectors before timing. A benchmark row is accepted only
when every operation on every timed input agrees bit-for-bit with FloatLib.

Codes are fixed-width binary strings rather than host integers. The representation therefore
remains lossless at arbitrary static widths, including 4,096 bits, and does not require an
external big-integer parser.

These vectors validate the measured workload, not every possible input. Exhaustive small-format
tests and the formal refinement theorems remain separate obligations.
-/

open FloatLib.Floats
open FloatLib.Numerics
open FloatLibBenchmarks.Support
open FloatLibBenchmarks.Support.Environment
open FloatLib.Floats.Formats.Posit
open FloatLibBenchmarks.Support.Posit

namespace FloatLibBenchmarks.Public.PositVectors

/-- Render one complete unsigned encoding with exactly `width` binary digits. -/
private def binaryCode (width bits : Nat) : String :=
  let digits := Nat.toDigits 2 bits
  String.ofList (List.replicate (width - digits.length) '0' ++ digits)

/-- Read a positive optional width filter. -/
private def selectedWidth : IO (Option Nat) := do
  positiveNat? "POSIT_VECTOR_WIDTH"

/-- Complete unsigned encoding of one configured posit. -/
private def bits
    {F : Type} [EncodedFormat F] [carrier : BenchmarkCarrier F Format Model]
    (width : Nat) (value : ExecFloat F) : String :=
  binaryCode width (carrier.toModel value).toNatBits

/--
Emit the sixteen benchmark cases for one statically configured posit format.

The operation results pass through the same public `ExecFloat` API measured by the benchmark, so
the corpus also catches a disagreement between a selected backend and its reference definition.
-/
private def emit
    (F : Type)
    [ExecFloat.Backend.PolicyFor F] [EncodedFormat F]
    [carrier : BenchmarkCarrier F Format Model]
    [ExecFloat.Add F] [ExecFloat.Sub F] [ExecFloat.Mul F]
    [ExecFloat.Div F] [ExecFloat.Sqrt F] [ExecFloat.Fma F]
    (selected : Option Nat) (width : Nat) : IO Unit := do
  unless selected.all (· == width) do
    return
  let xs := inputsX F
  let ys := inputsY F
  let sqrtXs := inputsSqrt F
  for index in [0:16] do
    let x := xs[index]!
    let y := ys[index]!
    let z := xs[15 - index]!
    let sqrtInput := sqrtXs[index]!
    IO.println <| String.intercalate "," [
      toString width,
      toString index,
      bits width x,
      bits width y,
      bits width z,
      bits width sqrtInput,
      bits width (ExecFloat.add x y),
      bits width (ExecFloat.sub x y),
      bits width (ExecFloat.mul x y),
      bits width (ExecFloat.div x y),
      bits width (ExecFloat.sqrt sqrtInput),
      bits width (ExecFloat.fma x y z)
    ]

set_option maxHeartbeats 2000000 in
def run : IO Unit := do
  let selected ← selectedWidth
  IO.println "totalBits,index,x,y,z,sqrtInput,add,sub,mul,div,sqrt,fma"
  emit (ExecFloat.Posit.Family 2 (by decide)) selected 2
  emit (ExecFloat.Posit.Family 3 (by decide)) selected 3
  emit (ExecFloat.Posit.Family 4 (by decide)) selected 4
  emit (ExecFloat.Posit.Family 5 (by decide)) selected 5
  emit (ExecFloat.Posit.Family 6 (by decide)) selected 6
  emit (ExecFloat.Posit.Family 7 (by decide)) selected 7
  emit (ExecFloat.Posit.Family 8 (by decide)) selected 8
  emit (ExecFloat.Posit.Family 16 (by decide)) selected 16
  emit (ExecFloat.Posit.Family 32 (by decide)) selected 32
  emit (ExecFloat.Posit.Family 64 (by decide)) selected 64
  emit (ExecFloat.Posit.Family 128 (by decide)) selected 128
  emit (ExecFloat.Posit.Family 256 (by decide)) selected 256
  emit (ExecFloat.Posit.Family 512 (by decide)) selected 512
  emit (ExecFloat.Posit.Family 1024 (by decide)) selected 1024
  emit (ExecFloat.Posit.Family 2048 (by decide)) selected 2048
  emit (ExecFloat.Posit.Family 4096 (by decide)) selected 4096

end FloatLibBenchmarks.Public.PositVectors

public def main : IO Unit :=
  FloatLibBenchmarks.Public.PositVectors.run
