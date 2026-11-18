/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Tactic.CompilerOptimize
public import FloatLib.Tactic.KernelOptimize

/-!
# Reference execution paths

`reference_paths` registers a computable specification as its own compiled path
and its defining equation as a kernel fallback. The shared `Certified.reference`
supplies execution equality at any function type; `compiled_reference%` constructs
its certificate on demand. Kernel equation registration preserves selection of
cheaper proved rules before unfolding. Registration alone claims no acceleration.
-/

public meta section

/-- Register each operation itself and its defining equation as reference execution paths. -/
macro (name := referencePaths) "reference_paths " operations:ident+ : command => do
  let equations := operations.map fun operation => Lean.mkIdent (operation.getId ++ `eq_def)
  `(attribute [compiler_optimize reference] $operations*
    attribute [kernel_optimize] $equations*)
