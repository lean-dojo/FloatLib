/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Lean.Replay

/-!
# Replay the declarations of a compiled module in Lean's kernel

`lean --run tests/checks/KernelReplay.lean M` reads the compiled module `M`, builds the environment
of its imports, and gives every constant that `M` adds to Lean's kernel once more. It prints the
number of constants and fails if the kernel rejects one. A declaration that was put into the
environment without the kernel's check is found this way. It also fails if one of the constants
is an axiom: the library declares none, and Lean keeps a declaration that its kernel rejected as
an axiom.

One process replays one module, so a run needs the memory of one module and its imports, and
`tests/checks/kernel-replay.sh` starts this file once for each module of the library, several at
a time. The imports are loaded as the compiler loaded them: a file that starts with `module`
sees what its imports export, so the kernel unfolds exactly the definitions that it could unfold
when the module was compiled.
-/

open Lean

/-- The files of a compiled module: its `.olean` and, for a file that starts with `module`, the
server and private parts beside it. -/
def moduleFiles (module : Name) : IO (Array System.FilePath) := do
  let exported ← findOLean module
  unless (← exported.pathExists) do
    throw <| IO.userError s!"object file '{exported}' of module {module} does not exist"
  let server := OLeanLevel.server.adjustFileName exported
  unless (← server.pathExists) do
    return #[exported]
  let «private» := OLeanLevel.private.adjustFileName exported
  if (← «private».pathExists) then
    return #[exported, server, «private»]
  return #[exported, server]

/-- Check the constants that `module` adds again, in the environment of its imports, and that
none of them is an axiom. Returns how many there are. -/
def replayModule (module : Name) : IO Nat := do
  let parts ← readModuleDataParts (← moduleFiles module)
  let some (first, _) := parts[0]? | throw <| IO.userError s!"module {module} has no data"
  -- The last part is the most private one and holds the constants of the parts before it.
  let some (last, _) := parts.back? | throw <| IO.userError s!"module {module} has no data"
  -- The view the compiler had: a file that starts with `module` sees what its imports export.
  let level : OLeanLevel := if first.isModule then .exported else .private
  let (_, state) ← importModulesCore (globalLevel := level) first.imports |>.run
  let env ← finalizeImport state first.imports {} 0 false false (level := level)
  let mut added : Std.HashMap Name ConstantInfo := {}
  for name in last.constNames, info in last.constants do
    if info matches .axiomInfo _ then
      throw <| IO.userError s!"module {module} adds the axiom {name}"
    added := added.insert name info
  discard <| env.toKernelEnv.replay added
  return added.size

/-- Replay each named module and print one line for it. -/
def main (modules : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  for module in modules do
    let count ← replayModule module.toName
    IO.println s!"replayed {module}: {count} constants"
  return 0
