/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelCost
public meta import Lean.Elab.Command
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Tactic.KernelEval

/-!
# Kernel evaluation command tests

`#kernel_eval` evaluates a natural number and a configured addition; its timing messages are
discarded. `#kernel_cost` reports are pinned line by line with the measured times masked: a term
that the tagged rules rewrite, the rewritten form alone, a term that no rule rewrites, and the
refusal of a term that is not closed.
-/

public meta section

namespace FloatLibTests.Conformance.BinaryInterchange.KernelPath

open Lean Elab Command

/-- `text` with the number of every line `label: <number> µs` replaced by `_`. -/
def maskTimes (text : String) : String :=
  "\n".intercalate <| (text.splitOn "\n").map fun line =>
    match line.splitOn ": " with
    | [label, value] => if value.endsWith " µs" then s!"{label}: _ µs" else line
    | _ => line

/--
`#masked cmd` runs `cmd` and prints each of its messages with the measured times masked, so that
a test pins everything else in a report.
-/
elab "#masked " cmd:command : command => do
  let saved ← modifyGet fun state => (state.messages, { state with messages := {} })
  elabCommand cmd
  let produced := (← get).messages
  modify fun state => { state with messages := saved }
  for message in produced.toList do
    logInfo (maskTimes (← message.data.toString))

end FloatLibTests.Conformance.BinaryInterchange.KernelPath

end

@[expose] public section

namespace FloatLibTests.Conformance.BinaryInterchange.KernelPath

open FloatLib.Floats FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

/-- A natural number comes out as a numeral. The time varies, so the test reads the value only. -/
def kernelEvalValue : Nat := 2 ^ 100 % 7

#guard_msgs (drop info) in
#kernel_eval kernelEvalValue

#guard_msgs (drop info) in
#kernel_eval toNat (Value.add .nearest (ofNat 0x3fc00000 : Binary32) (ofNat 0x40100000))

/-! ## `#kernel_cost` -/

/-!
A sum that the tagged rules rewrite: the time as written, the time of the rewritten form, and
the value, here the encoding of `3.75`.
-/

/--
info: as written: _ µs
with the tagged kernel rules: _ µs
value: 1081081856
-/
#guard_msgs in
#masked #kernel_cost toNat ((1.5 : Binary32) + 2.25)

/-! The rewritten form alone, for a term whose written form is too slow to measure. -/

/--
info: with the tagged kernel rules: _ µs
value: 1081081856
-/
#guard_msgs in
#masked #kernel_cost rewritten toNat ((1.5 : Binary32) + 2.25)

/-! A term that no tagged rule rewrites is measured as written. -/

/--
info: as written: _ µs
no tagged kernel rule applies
value: 5
-/
#guard_msgs in
#masked #kernel_cost Nat.add 2 3

/-! A term with a hole is refused. -/

/-- error: #kernel_cost: the term is not closed and fully elaborated -/
#guard_msgs in
#kernel_cost Nat.add (_ : Nat) 3

end FloatLibTests.Conformance.BinaryInterchange.KernelPath
