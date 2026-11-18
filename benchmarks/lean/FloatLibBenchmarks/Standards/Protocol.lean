/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Tactic.KernelEval
public import FloatLib.Tactic.KernelOptimize
public import FloatLib.Numerics.Executable.Conversion.Core

/-!
# Complete-result timing protocol

The operation returns a natural number observing its entire result. Inputs are
prepared before timing. An untimed warm-up chooses a repetition count targeting
about ten milliseconds per trial, with at least one pass over the input array.
Three independent trials retain the count, elapsed time, checksum and sample-zero
observation. No overhead is subtracted. Callers must use a nonempty input array.
-/

@[expose] public section

namespace FloatLibBenchmarks.Standards

/-- Full signed-integer observation, distinguishing the two signs. -/
def observeInt (value : Int) : Nat :=
  2 * value.natAbs + (decide (value < 0)).toNat

/-- Observe every character of a result string, including order and length. -/
def observeString (value : String) : Nat :=
  value.toList.foldl (fun n c => n * 1114112 + c.toNat + 1) 1

/-- Every diagnostic flag contributes one distinct bit. -/
def observeStatus (status : FloatLib.Floats.ExecFloat.ConversionStatus) : Nat :=
  status.inexact.toNat + 2 * status.overflow.toNat + 4 * status.underflow.toNat +
    8 * status.saturated.toNat + 16 * status.wrapped.toNat +
    32 * status.mappedSpecial.toNat + 64 * status.invalid.toNat

/-- Observe the complete success result or every field of a failure's printed representation. -/
def observeOutcome {α : Type} (observe : α → Nat) :
    FloatLib.Floats.ExecFloat.ConversionOutcome α → Nat
  | .success value status => 1 + 2 * (128 * observe value + observeStatus status)
  | .failure reason => 2 * observeString (reprStr reason)

attribute [kernel_optimize unfold] observeInt observeString observeStatus observeOutcome

/-- Three native trials over preconstructed inputs, observing complete results. -/
@[noinline] def measure {α : Type} (family label : String) (width : Nat)
    (inputs : Array α) (operation : α → Nat) : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn s!"MATRIX_BEGIN {family} {label} width={width}"
  stdout.flush
  let some input := inputs[0]? | throw (IO.userError "empty benchmark input")
  let warmStart ← IO.monoNanosNow
  let observation := operation input
  let warmTime := (← IO.monoNanosNow) - warmStart
  let repetitions := max 1 (min 32 (10000000 / max (warmTime * inputs.size) 1))
  let count := repetitions * inputs.size
  for trial in [0:3] do
    let mut sink := 0
    let start ← IO.monoNanosNow
    for _ in [0:repetitions] do
      for input in inputs do
        sink := sink + operation input
    let elapsed := (← IO.monoNanosNow) - start
    stdout.putStrLn s!"MATRIX_NATIVE {family} {label} width={width} trial={trial} \
      count={count} elapsed={elapsed} ns={elapsed / count} sink={sink} value={observation}"
    stdout.flush

end FloatLibBenchmarks.Standards
