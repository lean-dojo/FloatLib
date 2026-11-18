/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Tactic.KernelOptimize
public meta import FloatLib.Util.KernelReduction

/-!
# Kernel costs of registered rewrites

`#kernel_cost` compares repeated kernel evaluation before and after registered rewrites.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Command Meta

/--
`#kernel_cost t` prints the kernel time of the closed term `t` as written and after the rewrite
with the rules tagged `@[kernel_optimize]`, the form that `float_decide` evaluates, and the
value when it is a numeral. Each time is the median of repeated evaluations to weak head normal
form, so `t` should be a natural number, a Boolean or another value that its head determines
(wrap a stored value in its encoding). `#kernel_cost rewritten t` measures the rewritten form
only, for a term whose written form the kernel evaluates too slowly.

```lean
#kernel_cost KernelPath.toNat ((1.5 : Binary32) + 2.25)
```
-/
syntax (name := kernelCost) "#kernel_cost " (&"rewritten ")? term : command

@[command_elab kernelCost, inherit_doc kernelCost]
def elabKernelCost : CommandElab := fun stx => do
  let onlyRewritten := !stx[1].isNone
  let term : Term := ⟨stx[2]⟩
  let message ← liftTermElabM do
    let expr ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    if expr.hasMVar || expr.hasSorry || expr.hasFVar then
      throwError "#kernel_cost: the term is not closed and fully elaborated"
    let rules ← Backend.Tag.kernelOptimizeExt.getTheorems
    let context ← Simp.mkContext (simpTheorems := #[rules])
      (congrTheorems := ← getSimpCongrTheorems)
    let (result, _) ← withOptions (fun options =>
        options.setBool `backward.isDefEq.respectTransparency false) <| simp expr context
    let changed := result.expr != expr
    let mut message : MessageData := m!""
    let mut value : Option Expr := none
    unless onlyRewritten do
      let (time, normal) ← kernelTime expr
      message := m!"as written: {microseconds time}\n"
      value := some normal
    if changed then
      let (time, normal) ← kernelTime result.expr
      message := message ++ m!"with the tagged kernel rules: {microseconds time}"
      value := some normal
    else
      message := message ++ m!"no tagged kernel rule applies"
    if let some (.lit (.natVal n)) := value then
      message := message ++ m!"\nvalue: {n}"
    return message
  logInfo message

end FloatLib.Floats.ExecFloat.KernelPath
