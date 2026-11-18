/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.CompilerOptimize

/-!
# `#compiler_backends`

Inspect the implementations registered by `@[compiler_optimize]`.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Backend.Tag

open Lean Meta Elab

/--
`#compiler_backends` prints the registered compiled backends by specification: the role and the
declaration of each. `#compiler_backends spec` prints the backends of the reference operation
`spec` only.
-/
elab "#compiler_backends" specification:(ppSpace ident)? : command => do
  let wanted ← specification.mapM fun name =>
    Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let backends ← Command.liftCoreM compilerBackends
  let backends := backends.filter fun backend =>
    wanted.all fun name => backend.specification == name
  let sorted := backends.qsort fun a b =>
    a.specification.toString < b.specification.toString ||
      (a.specification == b.specification && a.declName.toString < b.declName.toString)
  let lines := sorted.toList.map fun backend =>
    let role := match backend.role with
      | .alternative => "alternative"
      | .direct => "direct"
      | .baseline => "baseline"
      | .reference => "reference"
    m!"{backend.specification}: {.ofConstName backend.declName} ({role})"
  logInfo (MessageData.joinSep lines "\n")


end FloatLib.Floats.ExecFloat.Backend.Tag
