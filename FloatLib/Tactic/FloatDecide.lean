/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelCheck
public meta import Lean.Elab.Tactic.Simp
public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop -- shake: keep

/-!
# `float_decide`

`float_decide` proves a closed statement about floating-point values by evaluation in Lean's
kernel. It rewrites the public operations in the goal to their kernel operations with the rules
tagged `@[kernel_optimize]`, then has the kernel decide the result. When several tagged rules
match one term, the rule with the lowest declared cost is used, so a cheaper kernel
implementation tagged in any imported module is picked up with no change here. Registration
checks that the tagged rules use only Lean's three standard axioms. A proof using an additional
lemma supplied by the caller inherits that lemma's assumptions.

`float_decide [f, g, h]` also unfolds the definitions `f` and `g` and rewrites with the
equation `h` before deciding, which is how the operations inside your own definitions become
visible to the rewrite.

The check itself is `KernelCheck.prove` on the main goal, the same function that `interval`
checks its closed conditions with. It also handles loops of a thousand steps, whose rewrite is
proved for every length so that the kernel does not run the loop to check it, and statements
about all pairs of indices of a small type.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Tactic Meta

/--
`float_decide` closes a goal that Lean's kernel can decide, after rewriting floating-point
operations to their kernel operations (the rules tagged `@[kernel_optimize]`, cheapest first).

* `float_decide [f, h]` also unfolds the definition `f` and rewrites with the equation `h`.
* A definition that names one stored value, such as `def tenth : Binary32 := 0.1`, is unfolded
  without being listed.
* A goal `∀ a b : Fin n, P a b` with a literal `n`, in which `a` and `b` occur only as their
  values, is checked by one loop over the `n * n` pairs (`forall_fin_pairs`).
* An operation that has no kernel operation stays as it is, and the kernel then evaluates its
  reference definition, which is correct and slow.
* Rewriting can close a goal with local variables or hypotheses. Only the statement left for
  decision must be closed. If it is open, has no `Decidable` instance, or does not evaluate to
  true, the tactic reports the reason and shows the original goal.
-/
syntax (name := floatDecide) "float_decide" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| float_decide $[[$lemmas,*]]?) => withMainContext do
  let goal ← getMainGoal
  let lemmas := lemmas.getD (Syntax.TSepArray.mk #[])
  -- The listed theorems and definitions, as `simp only` elaborates them.
  let (extra, simprocs) : SimpTheoremsArray × Simp.SimprocsArray ←
    if lemmas.getElems.isEmpty then pure (#[], #[]) else do
      let { ctx, simprocs, .. } ← mkSimpContext (← `(tactic| simp only [$lemmas,*]))
        (eraseLocal := false)
      pure (ctx.simpTheorems, simprocs)
  goal.assign (← FloatLib.Tactic.KernelCheck.prove (← goal.getType) extra simprocs)
  replaceMainGoal []

end FloatLib.Floats.ExecFloat.KernelPath
