/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Dispatch
public import FloatLibTests.Fixtures.CustomByte

/-!
# Automatic-selection code-generation probes

These exported entry points guard the execution boundary for a user-defined format whose
capability advertises several certified candidates. The format does not name or manually install
the selected backend. Its ordinary `ExecFloat.Add` instance relies on the universal planner.

The compiler output must keep the plan in a closed memoized object. Repeated public arithmetic may
invoke the selected custom kernel through a closure because the candidate list is extensible, but
it must not fold or score the candidate list inside the arithmetic loop.
-/

@[expose] public section

namespace FloatLibBenchmarks.Codegen.AutomaticSelection

open FloatLib.Floats
open FloatLibTests.Fixtures.CustomByte

/-- Retained public boundary for one automatically selected custom-format addition. -/
@[noinline] def customAdd
    (left right : ExecFloat TestByte) : ExecFloat TestByte :=
  ExecFloat.add left right

/--
Retained hot loop for checking that automatic candidate selection is evaluated once rather than
once per arithmetic operation.
-/
@[noinline] def customAddLoop
    (iterations : Nat) (left right : ExecFloat TestByte) : ExecFloat TestByte :=
  if iterations = 0 then
    left
  else
    customAddLoop (iterations - 1) (ExecFloat.add left right) right

end FloatLibBenchmarks.Codegen.AutomaticSelection
