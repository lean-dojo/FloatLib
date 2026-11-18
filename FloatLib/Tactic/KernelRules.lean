/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelOptimize

/-!
# `#kernel_rules`

Inspect the implementations registered by `@[kernel_optimize]`.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.Backend.Tag

open Lean Meta Elab

/--
`#kernel_rules` prints the registered kernel rules by operation, cheapest first: the declared
cost in microseconds and the declaration that proves the rule. `#kernel_rules op` prints the
rules of the operation `op` only.
-/
elab "#kernel_rules" operation:(ppSpace ident)? : command => do
  let wanted ← operation.mapM fun name =>
    Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo name
  let rules ← Command.liftCoreM kernelRules
  let rules := rules.filter fun rule => wanted.all fun name => rule.operation == some name
  let key (rule : KernelRule) :=
    (rule.operation.getD .anonymous |>.toString, rule.cost.getD costCeiling,
      rule.declName.toString)
  let sorted := rules.qsort fun a b =>
    let (oa, ca, na) := key a
    let (ob, cb, nb) := key b
    oa < ob || (oa == ob && (ca < cb || (ca == cb && na < nb)))
  let mut lines : Array MessageData := #[]
  for rule in sorted do
    let cost := match rule.cost with
      | some cost => m!"{cost} µs"
      | none => m!"no declared cost"
    let what :=
      if rule.unfold then m!" (unfolded)" else if rule.inverted then m!" (←)" else m!""
    lines := lines.push
      m!"{rule.operation.getD .anonymous}: {.ofConstName rule.declName}, {cost}{what}"
  logInfo (MessageData.joinSep lines.toList "\n")


end FloatLib.Floats.ExecFloat.Backend.Tag
