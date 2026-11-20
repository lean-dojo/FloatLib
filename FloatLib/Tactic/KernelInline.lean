/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Elab.Term
public meta import Lean.Meta.CtorRecognizer
public meta import Lean.Meta.Match.MatcherInfo
public meta import Lean.Meta.Transform
public meta import FloatLib.Util.Declaration
public import FloatLib.Tactic.KernelRefl

/-!
# Unfolding stage functions for kernel reduction

Lean's kernel pays for a term in two ways. Unfolding a definition or applying a function copies
the body, about seventy nanoseconds for each node in it that mentions an argument, whether the
node is then evaluated or not. Evaluating an operation on natural numbers costs about four tenths
of a microsecond more. The kernel-path operations are written and proved in stages (decode, align,
add, round, pack) that take the rounding direction as an argument, and a computation runs several
of them for every operation.

`kernel_inline% [c₁, …, cₙ] e` elaborates `e`, unfolds every application of the constants `cᵢ` in
it and of the definitions tagged `@[kernel_inline]`, reduces every beta-redex and gives the
result its kernel shape (`kernelShape`):

* a case analysis by `casesOn` becomes the recursor it abbreviates. The kernel unfolds a
  `casesOn` by instantiating its universe parameter in its body, which costs it three to six
  microseconds more than the recursor. (`kernel_shape` does the same for the matcher of a
  `match`; `kernel_inline%` keeps a matcher on a variable, because the elaborator compares the
  flat forms with their staged forms where a theorem is stated through both, and it does not
  unfold a matcher on a variable. A matcher on a constructor, such as the constants of a fixed
  profile, selects its branch in both.)
* a recursor whose scrutinee is a constructor keeps the selected branch only, so an operation
  specialized to one rounding direction keeps the code of that direction;
* a numeral `OfNat.ofNat n` of type `Nat` becomes the literal `n`, which the kernel reads in
  place of unfolding the instance (about three microseconds for each distinct numeral),
  `Nat.pred n` becomes `Nat.sub n 1`, and an operator of `Nat` (`a + b`, `a <<< b`) becomes the
  function behind it (`Nat.add a b`, `Nat.shiftLeft a b`), which the kernel computes on
  literals without unfolding the instances (about ten microseconds for each use);
* a kernel-accelerated operation on literals is computed (`literalValue?`), and a comparison
  of literals decides its branch, so the constants of a fixed width cost nothing in a proof.

Lean compiles no code for recursors, so a definition made this way is `noncomputable`: it is for
the kernel, and compiled code uses the staged form. The result is definitionally equal to `e`,
so a definition `def f := kernel_inline% [g, h] (g (h x))` satisfies `f = g (h x)` by `rfl`, and
every theorem about the staged form transfers. Arguments that the stages use several times stay
shared inside the term, and the kernel still evaluates each of them once and copies the body
once. A function that the stages apply at several places (a continuation) is copied into each of
them: keep such a stage out of the list, or shape the stages one by one (`kernel_shape`,
`FloatLib.Tactic.KernelShape`).

`kernel_refl%` proves such an equation `f = g (h x)` with the kernel's check alone.

Two declarations say how the constants of a format enter a flat form. A constant that every
operation evaluates (the position of the sign bit, a mask, the word of the largest finite value)
gets a copy in kernel shape by `kernel_constant`, and the flat forms call the copy: the kernel
computes it once in a proof and finds its value again at every later call, which costs less
than computing an unfolded formula again, and a flat form does not grow by its body at every
use. A formula that only such copies use (a field of the largest finite value) is tagged
`@[kernel_inline]` and unfolded inside them.
-/

public meta section

/--
`@[kernel_inline]` marks a definition that `kernel_inline%` and `kernel_shape` always unfold: a
formula of a format (a field of the largest finite value, the mask of a fraction) whose body is
a few operations. Unfolded, it takes the kernel shape of the term that uses it, so the kernel
computes `2 ^ w - 1` on literals where it would unfold the definition and the instances of `^`
and `-`. A formula that an operation evaluates at every call is better declared with
`kernel_constant`: the kernel finds the value of a call again, and computes a formula again.
-/
syntax (name := Parser.Attr.kernel_inline) "kernel_inline" : attr

namespace FloatLib.Floats.ExecFloat.KernelPath

open Lean Elab Term Meta

/-- The definitions tagged `@[kernel_inline]`. -/
initialize kernelInlineExt : SimpleScopedEnvExtension Name NameSet ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun names name => names.insert name }

initialize
  registerBuiltinAttribute {
    name := `kernel_inline
    descr := "a definition that `kernel_inline%` and `kernel_shape` always unfold"
    add := fun declName _ kind => do
      unless (← getConstInfo declName).hasValue do
        throwError "`@[kernel_inline]` is for a definition, and `{.ofConstName declName}` has \
          no value"
      kernelInlineExt.add declName kind }

/-- The largest bit length of a literal that `literalValue?` builds. -/
def literalBitLimit : Nat := 131072

/--
The value of a kernel-accelerated operation of `Nat` on literals: `Nat.succ`, `Nat.add`,
`Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftRight`,
and `Nat.shiftLeft` and `Nat.pow` when the result has at most `literalBitLimit` bits. `none` for
another operation, and for a result above the limit.
-/
def literalValue? (operation : Name) (arguments : Array Nat) : Option Nat :=
  match arguments with
  | #[a] => if operation == ``Nat.succ then some (a + 1) else none
  | #[a, b] =>
      if operation == ``Nat.add then some (a + b)
      else if operation == ``Nat.sub then some (a - b)
      else if operation == ``Nat.mul then some (a * b)
      else if operation == ``Nat.div then some (a / b)
      else if operation == ``Nat.mod then some (a % b)
      else if operation == ``Nat.land then some (a &&& b)
      else if operation == ``Nat.lor then some (a ||| b)
      else if operation == ``Nat.xor then some (a ^^^ b)
      else if operation == ``Nat.shiftRight then some (a >>> b)
      else if operation == ``Nat.shiftLeft then
        if a.log2 + 1 + b ≤ literalBitLimit then some (a <<< b) else none
      else if operation == ``Nat.pow then
        if (a.log2 + 1) * b ≤ literalBitLimit then some (a ^ b) else none
      else none
  | _ => none

/--
The value of a kernel-accelerated comparison of `Nat` on literals: `Nat.beq` and `Nat.ble`.
-/
def literalTest? (operation : Name) (a b : Nat) : Option Bool :=
  if operation == ``Nat.beq then some (a == b)
  else if operation == ``Nat.ble then some (decide (a ≤ b))
  else none

/-- The values of the arguments when all of them are natural-number literals. -/
def literalArguments? (arguments : Array Expr) : Option (Array Nat) :=
  arguments.mapM fun argument => argument.rawNatLit?

/--
The kernel-accelerated function of `Nat` behind a binary operator of core Lean (`+`, `-`, `*`,
`/`, `%`, `^`, `&&&`, `|||`, `^^^`, `<<<`, `>>>`), by the name of the operator's function.
-/
def natOperation? (operator : Name) : Option Name :=
  if operator == ``HAdd.hAdd then some ``Nat.add
  else if operator == ``HSub.hSub then some ``Nat.sub
  else if operator == ``HMul.hMul then some ``Nat.mul
  else if operator == ``HDiv.hDiv then some ``Nat.div
  else if operator == ``HMod.hMod then some ``Nat.mod
  else if operator == ``HPow.hPow then some ``Nat.pow
  else if operator == ``HAnd.hAnd then some ``Nat.land
  else if operator == ``HOr.hOr then some ``Nat.lor
  else if operator == ``HXor.hXor then some ``Nat.xor
  else if operator == ``HShiftLeft.hShiftLeft then some ``Nat.shiftLeft
  else if operator == ``HShiftRight.hShiftRight then some ``Nat.shiftRight
  else none

/--
The kernel shape of a term, definitionally equal to it: every `casesOn` and every matcher is
written as its recursor, a recursor on a constructor is reduced, a numeral of type `Nat` is the
literal, `Nat.pred n` is `Nat.sub n 1`, an operator of `Nat` is the function behind it, an
operation or a comparison of `Nat` on literals is computed, and every beta-redex is reduced.
With `matchers := false` a matcher on a variable is kept, and one on a constructor or a literal
selects its branch: Lean's elaborator, unlike its kernel, does not unfold a matcher on a
variable, so a term that the elaborator has to compare with its source keeps them.
-/
def kernelShape (e : Expr) (matchers : Bool := true) : MetaM Expr := do
  let environment ← getEnv
  let shaped ← Meta.transform e
    (pre := fun e => do
      if e.isAppOfArity ``OfNat.ofNat 3 then
        let arguments := e.getAppArgs
        -- The type of a numeral argument of `Nat.add` and its siblings is `@& Nat`.
        if arguments[0]!.consumeMData.isConstOf ``Nat && arguments[1]!.isRawNatLit &&
            arguments[2]!.isAppOfArity ``instOfNatNat 1 then
          return .done arguments[1]!
      -- `Nat.pred n` is `Nat.sub n 1`, which the kernel computes on a literal.
      if e.isAppOfArity ``Nat.pred 1 then
        return .visit (mkApp2 (mkConst ``Nat.sub) e.appArg! (mkRawNatLit 1))
      if let .const name _ := e.getAppFn then
        -- An operator of `Nat` becomes the function that the kernel computes on literals.
        if let some operation := natOperation? name then
          let arguments := e.getAppArgs
          if arguments.size == 6 &&
              (arguments.extract 0 3).all (·.consumeMData.isConstOf ``Nat) then
            let direct := mkApp2 (mkConst operation) arguments[4]! arguments[5]!
            if ← isDefEq e direct then
              return .visit direct
        -- A case analysis becomes the recursor it abbreviates.
        if isCasesOnRecursor environment name ||
            (matchers && isMatcherCore environment name) then
          if let some unfolded ← unfoldDefinition? e then
            return .visit unfolded.headBeta
        -- A matcher that is kept still selects its branch on a constructor or a literal.
        if isMatcherCore environment name then
          if let .reduced selected ← reduceMatcher? e then
            return .visit selected
      return .continue e)
    (post := fun e => do
      if let .const name _ := e.getAppFn then
        let arguments := e.getAppArgs
        if let some values := literalArguments? arguments then
          if let some value := literalValue? name values then
            return .done (mkRawNatLit value)
          if h : values.size = 2 then
            if let some value := literalTest? name values[0] values[1] then
              return .done (mkConst (if value then ``Bool.true else ``Bool.false))
        -- A recursor applied to a constructor keeps the selected branch only.
        if let some (.recInfo recursor) := environment.find? name then
          if h : recursor.getMajorIdx < arguments.size then
            if ← isConstructorApp arguments[recursor.getMajorIdx] then
              let e' ← whnfCore e
              if e' != e then
                return .visit e'
      return .done e)
  Core.betaReduce shaped

/-- The definitions with a copy declared by `kernel_constant`, and that copy. -/
initialize kernelConstantExt : SimpleScopedEnvExtension (Name × Name) (NameMap Name) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun copies entry => copies.insert entry.1 entry.2 }

/--
`e` with every application of the constants `constants` and of the definitions tagged
`@[kernel_inline]` unfolded, every constant that has a copy declared by `kernel_constant`
replaced by that copy, and every beta-redex reduced.
-/
def unfoldConstants (constants : Array Name) (e : Expr) : MetaM Expr := do
  let tagged := kernelInlineExt.getState (← getEnv)
  let copies := kernelConstantExt.getState (← getEnv)
  let unfolded ← Meta.transform e (pre := fun e => do
    let e := e.headBeta
    if let .const name levels := e.getAppFn then
      if let some copy := copies.find? name then
        unless constants.contains name do
          return .visit (mkAppN (.const copy levels) e.getAppArgs)
      if constants.contains name || tagged.contains name then
        if let some unfolded ← unfoldDefinition? e then
          return .visit unfolded.headBeta
    return .continue e)
  Core.betaReduce unfolded

/--
`kernel_inline% [c₁, …, cₙ] e` is `e` with every application of the constants `cᵢ` and of the
definitions tagged `@[kernel_inline]` unfolded and every beta-redex reduced, in its kernel
shape: every `casesOn` written as its recursor, every recursor on a constructor reduced,
numerals of `Nat` as literals and operations on literals computed. It is definitionally
equal to `e`, and Lean's kernel reduces it without the calls. Lean compiles no code for it: mark
the definition `noncomputable` and compile the staged form.
-/
elab "kernel_inline% " "[" names:ident,* "]" body:term : term <= expectedType => do
  let constants ← names.getElems.mapM fun name => realizeGlobalConstNoOverloadWithInfo name
  let body ← elabTermEnsuringType body expectedType
  synthesizeSyntheticMVarsNoPostponing
  let body ← instantiateMVars body
  kernelShape (← unfoldConstants constants body) (matchers := false)

/-- The type of the constant `c`: the type of its copy. -/
elab "kernel_constant_type% " c:ident : term => do
  return (← getConstInfo (← realizeGlobalConstNoOverloadWithInfo c)).type

/-- The value of the definition `c` with the tagged definitions unfolded, in its kernel shape. -/
elab "kernel_constant_value% " c:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo c
  let some value := (← getConstInfo name).value?
    | throwError "`kernel_constant` is for a definition, and `{.ofConstName name}` has no value"
  kernelShape (← unfoldConstants #[name] value) (matchers := false)

/-- `kernel_constant_register c copy` records `copy` as the copy of `c`. -/
elab "kernel_constant_register " c:ident copy:ident : command => do
  let name ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let copyName ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo copy
  modifyEnv fun env => kernelConstantExt.addEntry env (name, copyName)

/--
`kernel_constant c` is for a definition `c` that every operation of a format evaluates, such as
the word of its largest finite value: a formula in the widths that the kernel computes once in a
proof and then remembers. It is also for a stage that the flat forms call and do not unfold,
such as the result for operands that are not finite. It declares `c.kernel`, the definition `c`
with the definitions tagged `@[kernel_inline]` unfolded, in its kernel shape (definitionally
`c`: `c.kernel_eq`), and from then on `kernel_inline%` and `kernel_shape` write `c.kernel` where
a stage says `c`. The flat forms then call a constant, as before, and the kernel computes it in
a few operations on literals where it unfolded the instances of the operators in the body of
`c`. A copy calls the copies that were declared before it.
-/
syntax (name := kernelConstant) "kernel_constant " ident : command

@[inherit_doc kernelConstant]
elab_rules : command
  | `(kernel_constant $c:ident) => do
  let name ← Command.liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  let info ← getConstInfo name
  unless info.hasValue do
    throwError "`kernel_constant` is for a definition, and `{.ofConstName name}` has no value"
  let levels := info.levelParams.toArray.map mkIdent
  let reference := mkIdent (`_root_ ++ name)
  let copy := mkIdent (`_root_ ++ name ++ `kernel)
  let rule := mkIdent (`_root_ ++ name ++ `kernel_eq)
  let copyId ← if levels.isEmpty then `(Lean.Parser.Command.declId| $copy:ident)
    else `(Lean.Parser.Command.declId| $copy:ident.{$levels,*})
  let ruleId ← if levels.isEmpty then `(Lean.Parser.Command.declId| $rule:ident)
    else `(Lean.Parser.Command.declId| $rule:ident.{$levels,*})
  let copyDoc := generatedDoc
    s!"`{name}` in its kernel shape, with the formulas it uses unfolded \
      (`{name ++ `kernel_eq}`). "
  let ruleDoc := generatedDoc s!"`{name}` is `{name ++ `kernel}`, by unfolding. "
  Command.elabCommand (← `($copyDoc:docComment noncomputable def $copyId :
    kernel_constant_type% $reference := no_implicit_lambda% (kernel_constant_value% $reference)))
  Command.elabCommand (← `($ruleDoc:docComment theorem $ruleId : @$reference = @$copy :=
    kernel_refl%))
  Command.elabCommand (← `(kernel_constant_register $reference $copy))

end FloatLib.Floats.ExecFloat.KernelPath
