/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelOptimize
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.Simp.Main

/-!
# Preparing proved kernel rewrites once

`kernel_prepare% e` applies the registered kernel equations to `e` and returns
the rewritten expression with a proof that it equals `e`. A definition can
store this pair once, then use its equality to register the prepared function.
Format parameters and operands may remain universally quantified.

Preparation uses the same rewrite set as `float_decide`. Its output includes
the simplifier's proof term, which Lean checks when the declaration is added;
the elaborator is not an additional trusted evaluator. This removes repeated
rewrite preparation, without asserting any bound on kernel evaluation.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Term Meta

/--
Prepare `e` with the current `kernel_optimize` equations and return
`{ result // result = e }`, with a kernel-checked equality.

Store the result in a `noncomputable` definition when the rewritten term
contains kernel-only recursors. For a prepared function `p`, `p.property`
transfers its result to the original specification at every argument.
-/
elab (name := kernelPrepare) "kernel_prepare% " term:term : term => do
  let expression ← elabTerm term none
  synthesizeSyntheticMVarsNoPostponing
  let expression ← instantiateMVars expression
  let rules ← Backend.Tag.kernelOptimizeExt.getTheorems
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← withOptions (fun options =>
      options.setBool `backward.isDefEq.respectTransparency false) <| simp expression context
  let equality ← mkEqSymm (← result.getProof)
  let predicate ← withLocalDeclD `result (← inferType expression) fun value => do
    mkLambdaFVars #[value] (← mkEq value expression)
  mkAppOptM ``Subtype.mk #[none, some predicate, some result.expr, some equality]

end FloatLib.Floats.ExecFloat.KernelPath
