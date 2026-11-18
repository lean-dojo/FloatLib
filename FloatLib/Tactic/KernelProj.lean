/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Term
public import Mathlib.Init -- Standard source linters.

/-!
# Primitive projections for kernel reduction

`x.val` elaborates to the projection function `Subtype.val x`, which Lean's kernel reduces in
three steps: it unfolds the function, applies it, and projects. `kernel_proj% x i` elaborates to
the primitive projection of field `i` (counted from zero), which the kernel reduces in one step.
The two are definitionally equal, so a definition written with `kernel_proj%` has the same meaning
and proofs can `show` the ordinary form.

The kernel-path wrappers read the natural-number encoding out of a stored value through several
nested structures (`Subtype`, `UInt32`, `BitVec`, `Fin`), so this saves about ten kernel steps for
each operand.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Term Meta

/--
`kernel_proj% x i` is field `i`, counted from zero, of the structure value `x`, as a primitive
projection that Lean's kernel reduces in one step. It is definitionally equal to the projection
function applied to `x`.
-/
elab "kernel_proj% " value:term:max index:num : term => do
  let value ← elabTerm value none
  let type ← whnf (← inferType value)
  let .const structName _ := type.getAppFn
    | throwError "kernel_proj%: the type of the value is not a structure{indentExpr type}"
  let some info := getStructureInfo? (← getEnv) structName
    | throwError "kernel_proj%: `{structName}` is not a structure"
  unless index.getNat < info.fieldNames.size do
    throwError "kernel_proj%: `{structName}` has no field {index.getNat}"
  return .proj structName index.getNat value

end FloatLib.Floats.ExecFloat.KernelPath
