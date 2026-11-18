/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Term
public meta import Lean.Meta.CtorRecognizer
public meta import Lean.Meta.Transform
public import Mathlib.Init -- Standard source linters.

/-!
# Unfolding stage functions for kernel reduction

Lean's kernel pays for a term in two ways. Unfolding a definition or applying a function copies
the body, about a quarter of a microsecond for each operation in it that mentions an argument,
whether the operation is then evaluated or not. Evaluating an operation on natural numbers costs
about four tenths of a microsecond more. The kernel-path operations are written and proved in
stages (decode, align, add, round, pack) that take the rounding direction as an argument, and a
computation runs several of them for every operation.

`kernel_inline% [c₁, …, cₙ] e` elaborates `e`, unfolds every application of the constants `cᵢ` in
it, reduces every beta-redex, writes every case analysis (`casesOn`) as the recursor it
abbreviates, and reduces every recursor whose scrutinee is a constructor, so that an operation
specialized to one rounding direction keeps the code of that direction only. Lean compiles no
code for recursors, so a definition made this way is `noncomputable`: it is for the kernel, and
compiled code uses the staged form. The result is definitionally equal to `e`, so a definition
`def f := kernel_inline% [g, h] (g (h x))` satisfies `f = g (h x)` by `rfl`, and every theorem
about the staged form transfers. Arguments that the stages use several times stay shared inside
the term, and the kernel still evaluates each of them once and copies the body once.

`kernel_refl%` proves such an equation `f = g (h x)` with the kernel's check alone.
-/

@[expose] public section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Term Meta

/--
`kernel_inline% [c₁, …, cₙ] e` is `e` with every application of the constants `cᵢ` unfolded,
every beta-redex reduced, every `casesOn` written as its recursor and every recursor on a
constructor reduced. It is definitionally equal to `e`, and Lean's kernel reduces it without the
calls. Lean compiles no code for it: mark the definition `noncomputable` and compile the staged
form.
-/
elab "kernel_inline% " "[" names:ident,* "]" body:term : term <= expectedType => do
  let constants ← names.getElems.mapM fun name => realizeGlobalConstNoOverloadWithInfo name
  let body ← elabTermEnsuringType body expectedType
  synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  let unfolded ← Meta.transform body (pre := fun e => do
    let e := e.headBeta
    if let .const name _ := e.getAppFn then
      if constants.contains name then
        if let some unfolded ← unfoldDefinition? e then
          return .visit unfolded.headBeta
    return .continue e)
  let reduced ← Core.betaReduce unfolded
  -- A case analysis becomes the recursor it abbreviates, which the kernel reduces in one step
  -- less, and a recursor applied to a constructor keeps the selected branch only.
  let environment ← getEnv
  let specialized ← Meta.transform reduced (pre := fun e => do
    if let .const name _ := e.getAppFn then
      if isCasesOnRecursor environment name then
        if let some unfolded ← unfoldDefinition? e then
          return .visit unfolded.headBeta
      if let some (.recInfo recursor) := environment.find? name then
        let arguments := e.getAppArgs
        if h : recursor.getMajorIdx < arguments.size then
          if ← isConstructorApp arguments[recursor.getMajorIdx] then
            let e' ← whnfCore e
            if e' != e then
              return .visit e'
    return .continue e)
  Core.betaReduce specialized

end FloatLib.Floats.ExecFloat.KernelPath
