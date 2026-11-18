/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Term
public meta import Lean.Meta.Basic
public import Mathlib.Init -- Standard source linters.

/-!
# Reflexivity checked by the kernel

`kernel_refl%` constructs reflexivity and leaves conversion checking to Lean's kernel.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Term Meta

/--
`kernel_refl%` proves an equation `a = b` by `Eq.refl a` and leaves the check that the two sides
are definitionally equal to Lean's kernel. Use it for `f = staged` where `f` was made with
`kernel_inline%`: the term is large and shares its parts, so the elaborator's own check can run
out of time, while the kernel unfolds the staged form and compares. An equation that does not
hold by reduction is refused by the kernel when the declaration is added.
-/
elab "kernel_refl%" : term <= expectedType => do
  let some (_, lhs, _) := (← instantiateMVars expectedType).eq?
    | throwError "`kernel_refl%` proves an equation, and the expected type \
      is{indentExpr expectedType}"
  mkExpectedTypeHint (← mkEqRefl lhs) expectedType

end FloatLib.Floats.ExecFloat.KernelPath
