/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Enclosure.Expression.ExtensionsProof
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Transform
public meta import Lean.ScopedEnvExtension
public meta import Mathlib.Util.Qq

/-!
# Registering certified interval enclosures

Tag a `ConstantBounds c` definition or a theorem `E.Sound f` with `@[interval_extension]` to
associate the named real constant or function with its executable bounds. Importing the provider's
module imports the registration. Local and scoped attributes follow Lean's usual visibility rules.

Functions have a fixed number of real arguments; parameters of other types can be fixed in a
named wrapper. Registration checks the contract and does not introduce axioms or numerical facts.
-/

public meta section

open Lean Meta Qq

namespace FloatLib.Numerics.Interval.Tactic

/-- Registered certificate names indexed by the real function they enclose. -/
initialize intervalExtensionRegistry : SimpleScopedEnvExtension (Name × Name) (NameMap Name) ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := fun entries (function, proof) => entries.insert function proof }

/-- Recover the enclosure, named real function, and containment proof from a registration. -/
def extensionCertificate (name : Name) : MetaM (Q(Extension) × Lean.Expr × Nat × Lean.Expr) := do
  let info ← getConstInfo name
  let type ← instantiateMVars info.type
  if type.isAppOfArity ``ConstantBounds 1 then
    let c : Q(ℝ) ← pure type.getAppArgs[0]!
    unless c.isConst do
      throwError "interval_extension expects a named real constant; use a named wrapper"
    let certificate : Q(ConstantBounds $c) ← pure (mkConst name)
    return (q(ConstantBounds.toExtension $certificate), c, 0,
      q(ConstantBounds.toExtension_sound $certificate))
  unless type.isAppOfArity ``Extension.Sound 2 do
    throwError "interval_extension expects ConstantBounds c or a theorem of type E.Sound f"
  let E : Q(Extension) := type.getAppArgs[0]!
  let f := type.getAppArgs[1]!
  unless f.isConst do
    throwError "interval_extension expects a named real constant or function; use a named wrapper"
  let some arity ← getNatValue? (← whnf q(Extension.arity $E))
    | throwError "interval_extension requires a closed, computable argument count"
  return (E, f, arity, mkConst name)

/-- Register proved constant bounds or a containment theorem for a user-defined operation. -/
syntax (name := intervalExtensionAttr) "interval_extension" : attr

initialize registerBuiltinAttribute {
  name := `intervalExtensionAttr
  descr := "certified enclosure used by the interval tactic"
  applicationTime := .afterCompilation
  add := fun name _ kind => MetaM.run' do
    let (_, function, _, _) ← extensionCertificate name
    intervalExtensionRegistry.add (function.constName!, name) kind }

/-- Recognize registered applications through definitional aliases. -/
partial def registeredApplication? (e : Q(ℝ)) (visited : Array Name := #[]) :
    MetaM (Option (Name × Array Q(ℝ))) := do
  checkSystem "interval extension recognition"
  let e : Q(ℝ) ← zetaReduce e
  let .const name _ := e.getAppFn | return none
  let registrations := intervalExtensionRegistry.getState (← getEnv)
  if let some proof := registrations.find? name then
    let (_, _, arity, _) ← extensionCertificate proof
    if e.getAppNumArgs == arity then return some (proof, e.getAppArgs)
    return none
  if visited.contains name then return none
  let reduced : Q(ℝ) ← withTransparency .instances (whnf e)
  if reduced != e then
    return ← registeredApplication? reduced (visited.push name)
  let some unfolded ← unfoldDefinition? e | return none
  let unfolded : Q(ℝ) := unfolded.headBeta
  registeredApplication? unfolded (visited.push name)

end FloatLib.Numerics.Interval.Tactic
