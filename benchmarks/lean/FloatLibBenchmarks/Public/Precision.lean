/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

import FloatLibBenchmarks.Public.Sweep

/-!
# Public arithmetic across static precisions

One executable measures addition, subtraction, multiplication, division, square root, and FMA
over the same precision catalog. The command below generates six monomorphic workloads for each
format. Operation selection happens before timing; the timed loops retain their closed carrier
and certified backend, exact inputs, warmup, and result sink from `Public.Sweep`.

Run `execFloatSweep add` for one operation, or `execFloatSweep all` for all six. Each invocation
emits one CSV header followed by its measurements. `BENCH_ITERATIONS` overrides iteration counts.
-/

open FloatLib.Floats
open FloatLibBenchmarks.Public.Sweep
open scoped FloatLib.Floats.ExecFloat.Backend.PlanningThroughput

namespace FloatLibBenchmarks.Public.Precision

-- Declare each format once while keeping ordinary, specialized functions in the generated code.
macro "precision_workloads " name:ident " : " type:term " at " precision:num : command => do
  let add := Lean.mkIdent (name.getId.appendAfter "Add")
  let sub := Lean.mkIdent (name.getId.appendAfter "Sub")
  let mul := Lean.mkIdent (name.getId.appendAfter "Mul")
  let div := Lean.mkIdent (name.getId.appendAfter "Div")
  let sqrt := Lean.mkIdent (name.getId.appendAfter "Sqrt")
  let fma := Lean.mkIdent (name.getId.appendAfter "Fma")
  let declarations ← #[
    `(binary_sweep_workload $add : $type using ExecFloat.add),
    `(binary_sweep_workload $sub : $type using ExecFloat.sub),
    `(binary_sweep_workload $mul : $type using ExecFloat.mul),
    `(binary_sweep_workload $div : $type using ExecFloat.div),
    `(unary_sweep_workload $sqrt : $type using ExecFloat.sqrt),
    `(ternary_sweep_workload $fma : $type using ExecFloat.fma),
    `(def $name (operation : String) : IO Unit :=
        match operation with
        | "add" => runAdd $precision $add
        | "sub" => runSub $precision $sub
        | "mul" => runMul $precision $mul
        | "div" => runDiv $precision $div
        | "sqrt" => runSqrt $precision $sqrt
        | "fma" => runFma $precision $fma
        | _ => throw <| IO.userError s!"unknown arithmetic operation: {operation}")
    ].mapM id
  return ⟨Lean.mkNullNode declarations⟩

precision_workloads p2 : P2 at 2
precision_workloads p3 : P3 at 3
precision_workloads p4 : P4 at 4
precision_workloads p5 : P5 at 5
precision_workloads p6 : P6 at 6
precision_workloads p7 : P7 at 7
precision_workloads p8 : P8 at 8
precision_workloads p11 : P11 at 11
precision_workloads p24 : P24 at 24
precision_workloads p53 : P53 at 53
precision_workloads p113 : P113 at 113
precision_workloads p161 : P161 at 161
precision_workloads p237 : P237 at 237
precision_workloads p493 : P493 at 493
precision_workloads p1024 : P1024 at 1024
precision_workloads p2048 : P2048 at 2048
precision_workloads p4096 : P4096 at 4096

def operations : List String := ["add", "sub", "mul", "div", "sqrt", "fma"]

def run (operation : String) : IO Unit := do
  for measure in [p2, p3, p4, p5, p6, p7, p8, p11, p24, p53, p113, p161, p237,
      p493, p1024, p2048, p4096] do
    measure operation

end FloatLibBenchmarks.Public.Precision

public def main (args : List String) : IO UInt32 := do
  let usage := "usage: execFloatSweep [all|add|sub|mul|div|sqrt|fma]"
  if args = ["--help"] then
    IO.println usage
    return 0
  let selected ← match args with
    | [] | ["all"] => pure FloatLibBenchmarks.Public.Precision.operations
    | [operation] =>
        if FloatLibBenchmarks.Public.Precision.operations.contains operation then
          pure [operation]
        else
          IO.eprintln usage
          return 2
    | _ =>
        IO.eprintln usage
        return 2
  printHeader
  for operation in selected do
    FloatLibBenchmarks.Public.Precision.run operation
  return 0
