/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Lean.Data.Json
import Lean

/-!
# External validation process helpers

Validation packages may call external tools in the “untrusted producer, trusted checker” pattern:

- the external tool produces an artifact (often JSON),
- Lean parses it and checks it against a small trusted kernel.

This module centralizes the parts those wrappers must agree on: configured build-directory paths,
environment-variable command overrides, checked subprocess execution, and JSON parsing.

It makes no correctness claim about the external program.
-/

@[expose] public section

namespace FloatLibTests.External.Process

open Lean

/-!
## Artifact paths
-/

/--
Scratch space for one subprocess adapter under the configured build directory.

Uses `FLOATLIB_BUILD_DIR` when set and `.lake/build` otherwise.
-/
def artifactWorkDir (stem : String) : IO System.FilePath := do
  let buildDir := (← IO.getEnv "FLOATLIB_BUILD_DIR")
    |>.map System.FilePath.mk
    |>.getD (System.FilePath.mk ".lake/build")
  pure <| System.FilePath.mk s!"{buildDir.toString}/floatlib_{stem}"

/-!
## Executable resolution
-/

/--
Resolve an executable command name, allowing an environment-variable override.

Example:
- `resolveCmdFromEnv "FLOATLIB_ARBITRARY_TOOL" "tool"` uses the configured executable when the
  variable is set and otherwise returns `"tool"`.
-/
def resolveCmdFromEnv (envVar : String) (defaultCmd : String) : IO String := do
  pure <| (← IO.getEnv envVar) |>.getD defaultCmd

/-!
## Running a subprocess and parsing JSON
-/

/--
Run a subprocess and return its captured `stdout`.

On nonzero exit code, raises `IO.userError` including `stderr`. Any exception thrown by the
process runner (e.g. executable not found) is propagated to the caller.
-/
def runStdoutChecked (ctx : String)
    (cmd : String) (args : Array String) (cwd : Option String := some ".") : IO String := do
  let out ←
    try
      IO.Process.output { cmd := cmd, args := args, cwd := cwd }
    catch e =>
      throw <|
        IO.userError
          (s!"{ctx}: failed to start subprocess.\n" ++
           s!"cmd={cmd}\nargs={args.toList}\nerror: {e}\n")
  if out.exitCode != 0 then
    throw <|
      IO.userError
        (s!"{ctx}: subprocess failed.\n" ++
         s!"cmd={cmd}\nargs={args.toList}\nexit={out.exitCode}\nstderr:\n{out.stderr}\n")
  pure out.stdout

/--
Run a subprocess, treat its `stdout` as a single JSON payload, and parse it.

On nonzero exit code, raises `IO.userError`. If JSON parsing fails, raises `IO.userError` including
the raw stdout (which is usually the most helpful debug output).
-/
def runJsonStdoutChecked (ctx : String)
    (cmd : String) (args : Array String) (cwd : Option String := some ".") : IO Json := do
  let out ← runStdoutChecked (ctx := ctx) (cmd := cmd) (args := args) (cwd := cwd)
  match Json.parse out with
  | .ok j => pure j
  | .error msg =>
      throw <| IO.userError s!"{ctx}: JSON parse error: {msg}\nstdout:\n{out}"

end FloatLibTests.External.Process
