/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Benchmark environment variables

Shared validation for environment variables used by benchmark executables. Keeping parsing here
ensures that every harness rejects zero counts, malformed naturals, and non-Boolean flags in the
same way.
-/

@[expose] public section

namespace FloatLibBenchmarks.Support.Environment

/-- Read an optional environment variable as a strictly positive natural number. -/
def positiveNat? (name : String) : IO (Option Nat) := do
  match ← IO.getEnv name with
  | none => pure none
  | some text =>
      match text.toNat? with
      | some value =>
          if value = 0 then
            throw <| IO.userError s!"{name} must be positive"
          else
            pure (some value)
      | none => throw <| IO.userError s!"invalid {name}: {text}"

/-- Read a positive natural-number environment variable, using `default` when it is absent. -/
def positiveNat (name : String) (default : Nat) : IO Nat :=
  return (← positiveNat? name).getD default

/-- Read an optional `0`/`1` environment flag, defaulting to `false`. -/
def bool (name : String) : IO Bool := do
  match ← IO.getEnv name with
  | none | some "0" => pure false
  | some "1" => pure true
  | some value =>
      throw <| IO.userError s!"{name} must be 0 or 1, not {value}"

end FloatLibBenchmarks.Support.Environment
