/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Lean

/-!
# The constants of a module and the constants they use

`lean --run Closure.lean MODULE...` prints one line for each constant that concerns the modules
named:

* `root NAME`: a constant that one of the modules declares and that `leanexport` accepts by name;
* `hidden NAME`: a constant of the modules whose name has a numeric component, as private and
  generated names do. `leanexport` cannot be asked for it and writes it only when a `root` uses it;
* `compiled NAME`: an `unsafe` or `partial` definition of the modules. It is code for the compiler,
  no proof can mention it, and `nanoda_bin` and `con-ron` decline an export that contains one, so it
  is not exported;
* `uses NAME`: a constant of another module that a constant of the modules refers to in its type or
  its value;
* `unreachable NAME`: such a constant whose name `leanexport` does not accept.

`checkers.sh` exports the `root` constants, which brings everything they depend on, and exports
the `uses` constants as the baseline: the same dependencies without the modules' own declarations.
-/

open Lean

/-- Whether `leanexport` reads the printed form of `name` back as `name`. -/
def exportable (name : Name) : Bool :=
  Syntax.decodeNameLit ("`" ++ name.toString) == some name

/-- Print the constants of the modules `arguments` and the constants they use. -/
def main (arguments : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules := arguments.map String.toName
  let environment ← importModules (modules.toArray.map fun module => { module }) {}
  let indices := modules.filterMap environment.getModuleIdx?
  if indices.length != modules.length then
    IO.eprintln "Closure: a module was not loaded"
    return 1
  let own (name : Name) : Bool := (environment.getModuleIdxFor? name).any indices.contains
  let mut used : NameSet := {}
  for (name, info) in environment.constants.map₁ do
    if own name then
      if info.isUnsafe || info.isPartial then
        IO.println s!"compiled {name}"
      else
        IO.println s!"{if exportable name then "root" else "hidden"} {name}"
        for dependency in info.getUsedConstantsAsSet do
          unless own dependency do
            used := used.insert dependency
  for name in used do
    IO.println s!"{if exportable name then "uses" else "unreachable"} {name}"
  return 0
