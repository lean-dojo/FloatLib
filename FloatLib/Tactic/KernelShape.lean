/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import FloatLib.Util.Declaration
public import FloatLib.Tactic.KernelInline
public import FloatLib.Tactic.KernelTwin

/-!
# `kernel_shape`: a staged definition as Lean's kernel evaluates it best

A kernel-path operation that works on structured data (a decimal datum, an outcome with its
flags) is written in small stages that match on constructors and pass the pieces on. Unfolding
all of them into one term (`kernel_inline%`) does not suit such an operation: each binder of a
match copies everything below it, and a continuation is copied into every branch. The stages are
the right size for Lean's kernel. What costs it time is how they are written for the compiler:
`casesOn` in place of the recursor, numerals through `OfNat`, and the operations of core Lean on
integers.

`kernel_shape f` declares, for a definition `f`,

* `f.kernel`: the body of `f`, rewritten with the rules tagged `@[kernel_optimize]` that are in
  scope (the kernel arithmetic of `Int` and `Rat`, and `g.kernel` for every stage `g` that has
  one) and then put in its kernel shape (`kernelShape`: recursors for `casesOn` and matchers,
  literals for numerals, operations on literals computed). It is `noncomputable`: compiled code
  runs `f`;
* `f.kernel_eq : @f = @f.kernel`, tagged `@[kernel_optimize]`, so that `float_decide` evaluates
  `f.kernel` wherever a rule has put `f`.

`kernel_shape f inlining [g, h]` also unfolds the applications of `g` and `h` in the body first,
as `kernel_inline%` does, and the definitions tagged `@[kernel_inline]` are always unfolded.
Declare the shapes in the order of the definitions: a stage declared after the stages it calls
reaches their shapes. For a `private` definition the shape and the
rule are private, and the rule is in the rewrite set to the end of the section.

The proof of `f.kernel_eq` is the proof that the rewriting produced, so each called stage is
replaced by the equation of its own shape, and the kernel is left to compare two bodies that
call the same constants. It never compares a stage with its shape by unfolding both, which for
a recursion on a literal bound would take time exponential in the bound.

`kernel_twin` does the rewriting for a whole program that is not ours to edit, under another
namespace; `kernel_shape` is for the stages of a kernel path, one at a time, with the shape.
-/

public meta section

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Term Meta Command

/--
The body of the definition `name` after unfolding the applications of `inlined`, rewritten with
the tagged kernel rules, and the proof that the rewriting produced, if any rule applied.
-/
def stagedValue (name : Name) (inlined : Array Name) : MetaM Simp.Result := do
  let info ← getConstInfo name
  let some value := info.value?
    | throwError "`kernel_shape` is for a definition, and `{.ofConstName name}` has no value"
  let value ← unfoldConstants inlined value
  let context ← Simp.mkContext (config := { maxSteps := 10000000, singlePass := true })
    (simpTheorems := #[← Backend.Tag.twinRules]) (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp value context
  return result

/-- The names after `inlining`, as constants. -/
def inlinedConstants (names : Option (Syntax.TSepArray `ident ",")) : TermElabM (Array Name) :=
  match names with
  | none => pure #[]
  | some names => names.getElems.mapM fun name => realizeGlobalConstNoOverloadWithInfo name

/-- The type of the constant `c`: the type of its kernel shape. -/
elab "kernel_shape_type% " c:ident : term => do
  return (← getConstInfo (← realizeGlobalConstNoOverloadWithInfo c)).type

/--
The kernel shape of the definition `c`: its body, after unfolding the constants after
`inlining` and rewriting with the tagged kernel rules, in the shape of `kernelShape`.
-/
syntax (name := kernelShapeValue) "kernel_shape_value% " ident (" inlining " "[" ident,* "]")? :
  term

@[inherit_doc kernelShapeValue]
elab_rules : term
  | `(kernel_shape_value% $c:ident $[inlining [$names,*]]?) => do
  let name ← realizeGlobalConstNoOverloadWithInfo c
  kernelShape (← stagedValue name (← inlinedConstants names)).expr

/--
The proof of `@c = @c.kernel`: the proof of the rewriting of the body of `c` with the tagged
kernel rules. The kernel compares the rewritten body with its shape by reduction.
-/
syntax (name := kernelShapeProof) "kernel_shape_proof% " ident (" inlining " "[" ident,* "]")? :
  term

@[inherit_doc kernelShapeProof]
elab_rules : term <= expected
  | `(kernel_shape_proof% $c:ident $[inlining [$names,*]]?) => do
  let name ← realizeGlobalConstNoOverloadWithInfo c
  let result ← stagedValue name (← inlinedConstants names)
  mkExpectedTypeHint (← result.getProof) expected

/--
`kernel_shape f` declares `f.kernel`, the definition `f` as Lean's kernel evaluates it best (its
body rewritten with the tagged kernel rules in scope, with recursors for `casesOn` and matchers,
literals for the numerals of `Nat` and operations on literals computed) and the rule
`f.kernel_eq : @f = @f.kernel`, tagged `@[kernel_optimize]`. `kernel_shape f inlining [g, h]`
unfolds the applications of `g` and `h` in the body first. `f.kernel` is `noncomputable`:
compiled code runs `f`.
-/
syntax (name := kernelShapeCommand) "kernel_shape " ident (" inlining " "[" ident,* "]")? : command

@[inherit_doc kernelShapeCommand]
elab_rules : command
  | `(kernel_shape $c:ident $[inlining [$names,*]]?) => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo name
  unless info.hasValue do
    throwError "`kernel_shape` is for a definition, and `{.ofConstName name}` has no value"
  let levels := info.levelParams.toArray.map mkIdent
  -- A private definition gets a private shape, and its rule holds to the end of the section.
  let user := privateToUserName name
  let reference := mkIdent (`_root_ ++ user)
  let shape := mkIdent (`_root_ ++ user ++ `kernel)
  let rule := mkIdent (`_root_ ++ user ++ `kernel_eq)
  let shapeId ← if levels.isEmpty then `(Lean.Parser.Command.declId| $shape:ident)
    else `(Lean.Parser.Command.declId| $shape:ident.{$levels,*})
  let ruleId ← if levels.isEmpty then `(Lean.Parser.Command.declId| $rule:ident)
    else `(Lean.Parser.Command.declId| $rule:ident.{$levels,*})
  let shapeDoc := generatedDoc
    s!"`{user}` as Lean's kernel evaluates it best: its body with recursors, literals and the \
      kernel forms of what it calls (`{user ++ `kernel_eq}`). "
  let ruleDoc := generatedDoc s!"`{user}` is `{user ++ `kernel}`, which Lean's kernel evaluates. "
  if isPrivateName name then
    elabCommand (← `($shapeDoc:docComment private noncomputable def $shapeId :
      kernel_shape_type% $reference :=
        no_implicit_lambda% (kernel_shape_value% $reference $[inlining [$names,*]]?)))
    elabCommand (← `($ruleDoc:docComment @[local kernel_optimize] private theorem $ruleId :
      @$reference = @$shape := kernel_shape_proof% $reference $[inlining [$names,*]]?))
  else
    elabCommand (← `($shapeDoc:docComment noncomputable def $shapeId :
      kernel_shape_type% $reference :=
        no_implicit_lambda% (kernel_shape_value% $reference $[inlining [$names,*]]?)))
    elabCommand (← `($ruleDoc:docComment @[kernel_optimize] theorem $ruleId :
      @$reference = @$shape := kernel_shape_proof% $reference $[inlining [$names,*]]?))

end FloatLib.Floats.ExecFloat.KernelPath
