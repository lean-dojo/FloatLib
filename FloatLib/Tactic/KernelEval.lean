/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import FloatLib.Util.KernelReduction
public meta import Lean.Elab.SyntheticMVars

/-!
# Evaluation by Lean's kernel

`#kernel_eval` prints the value of a closed term and its kernel evaluation time. For a constructor,
it also evaluates the data fields. Function bodies and proof fields are left as written.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Command Meta

/--
`#kernel_eval t` evaluates `t` with Lean's kernel and prints the value and the time it took.

The kernel is the proof checker: it unfolds definitions step by step and computes natively only
on natural-number literals, so this is the cost that `decide +kernel` and `rfl` pay. Use `#eval`
to run compiled code.

```lean
#kernel_eval 2 ^ 100 % 7
```
-/
elab "#kernel_eval " term:term : command => do
  let (value, nanos) ← liftTermElabM do
    let expr ← Term.elabTerm term none
    Term.synthesizeSyntheticMVarsNoPostponing
    let expr ← instantiateMVars expr
    if expr.hasMVar || expr.hasSorry then
      throwError "#kernel_eval: the term is not fully elaborated"
    let start ← IO.monoNanosNow
    let value ← kernelNormalize expr
    let stop ← IO.monoNanosNow
    return (value, stop - start)
  let micros := nanos / 1000
  logInfo m!"{value}\nkernel: {micros / 1000}.{(micros % 1000 + 1000).repr.drop 1} ms"

end FloatLib.Floats.ExecFloat.KernelPath
