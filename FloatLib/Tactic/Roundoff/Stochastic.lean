/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticRat
public import FloatLib.Numerics.Quantization.Stochastic.Affine
public import FloatLib.Tactic.Roundoff.Tactic

/-!
# Probabilistic `roundoff` for fresh stochastic arithmetic

`roundoff stochastic theorem name := computation` reads an executable
`roundedSum`, `roundedDot`, or `roundedAffine`, including calls exposed through user definitions.
The computation takes its entropy history last and returns the rounded rational.
The command recognizes which of the three loops the computation is and applies
that loop's certificate (`sum_certificate_auto`, `dot_certificate_auto`,
`affine_certificate_auto`) to the rounders and operands of the call. The
reference is the exact sum, dot product or affine value, and the budget is the
finite maximum of local cell widths over reachable histories, which is not a
number: `Rounder.Support` gives a rational budget for a concrete loop.

It generates `name` (the full certificate), `name_mean`, `name_second`,
`name_tail` (the explicit exponential bound), and `name_confidence` (the
square-root logarithmic bound). Reachable-state admissibility remains a premise.
Any supplied `Rounder.Law` is used; the binary runtime law is synthesized for
`binaryRounder` when positivity of its entropy range is available.

This mode supports the explicit fresh-entropy sum/dot/affine execution API. It does
not silently reinterpret deterministic arithmetic, infer independence of
arbitrary random products, or certify a PRNG.
-/

public meta section

namespace FloatLib.Floats.Formats.BinaryInterchange.Roundoff.StochasticMode

open Lean Meta Elab Tactic
open FloatLib.Numerics.Quantization.Stochastic
open FloatLib.Floats.Formats.BinaryInterchange.Model.Policy

/-- Expose a user wrapper until one of the supported execution heads is reached. -/
private def expose (value : Expr) (heads : Array Name) : MetaM Expr := do
  let mut value := value
  for _ in [:64] do
    value := (← instantiateMVars value).headBeta
    if value.getAppFn.isConst && heads.contains value.getAppFn.constName! then return value
    let some next ← unfoldDefinition? value (ignoreTransparency := true)
      | throwError "roundoff stochastic: unsupported execution {value}"
    value := next
  throwError "roundoff stochastic: too many wrapper definitions"

private def provePositive (target : Expr) : TermElabM Expr := do
  let proof ← mkFreshExprMVar target
  let remaining ← Tactic.run proof.mvarId! do
    evalTactic (← `(tactic| first | assumption | decide))
  unless remaining.isEmpty do
    throwError "roundoff stochastic: supply the positive entropy-range premise {target}"
  return ← instantiateMVars proof

/-- Resolve an existing proved local law, or construct the descriptor-parametric runtime law. -/
private def localLaw (rounder : Expr) : TermElabM Expr := do
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      let type ← instantiateMVars decl.type
      if type.isAppOf ``Rounder.Law then
        let args := type.getAppArgs
        if ← isDefEq args[args.size - 2]! rounder then return decl.toExpr
  let value ← expose rounder #[``binaryRounder]
  let args := value.getAppArgs
  let law ← mkAppM ``binaryRounder_law #[args[0]!, args[1]!]
  let .forallE _ condition _ _ ← whnf (← inferType law)
    | throwError "roundoff stochastic: malformed binary runtime law"
  return mkApp law (← provePositive condition)

/-- Construct the checked certificate from the execution's actual rounders and operands. -/
elab "stochastic_roundoff_proof% " computation:term : term => Term.withoutErrToSorry do
  let computation ← Term.elabTerm computation none
  Term.synthesizeSyntheticMVarsNoPostponing
  let computation ← instantiateMVars computation
  let proof ← forallTelescope (← inferType computation) fun arguments result => do
    unless ← isDefEq result (mkConst ``Rat) do
      throwError "roundoff stochastic: expected a rational observation, with entropy history last"
    if arguments.isEmpty then
      throwError "roundoff stochastic: the computation must take an entropy history"
    let actual ← expose (mkAppN computation arguments)
      #[``roundedSum, ``roundedDot, ``roundedAffine]
    let args := actual.getAppArgs
    unless args.back! == arguments.back! do
      throwError "roundoff stochastic: entropy history must be the final computation argument"
    let certificate ← if actual.isAppOf ``roundedSum then do
        let law ← localLaw args[1]!
        mkAppM ``sum_certificate_auto #[args[1]!, law, args[2]!, args[3]!, args[4]!]
      else do
        let productLaw ← localLaw args[2]!
        let accumulatorLaw ← localLaw args[3]!
        let rule := if actual.isAppOf ``roundedDot then ``dot_certificate_auto
          else ``affine_certificate_auto
        mkAppM rule
          #[args[2]!, args[3]!, productLaw, accumulatorLaw,
            args[4]!, args[5]!, args[6]!, args[7]!]
    mkLambdaFVars arguments.pop (← instantiateMVars certificate)
  if proof.hasExprMVar || proof.hasLooseBVars || proof.hasSorry then
    throwError "roundoff stochastic: generated proof has unresolved obligations"
  return proof

/-- Project a conclusion without re-analyzing the computation. -/
elab "stochastic_roundoff_projection% " field:ident proof:term : term =>
    Term.withoutErrToSorry do
  let proof ← Term.elabTerm proof none
  let name ← match field.getId with
    | `mean => pure ``Certificate.mean
    | `second => pure ``Certificate.second
    | `tail => pure ``Certificate.tail
    | `confidence => pure ``Certificate.confidence
    | _ => throwError "unknown stochastic certificate projection"
  forallTelescope (← inferType proof) fun arguments _ => do
    mkLambdaFVars arguments (← mkAppM name #[mkAppN proof arguments])

/--
`roundoff stochastic theorem name := computation` proves the certificate of a `roundedSum`,
`roundedDot` or `roundedAffine` execution that takes its entropy history last, and declares
`name`, `name_mean`, `name_second`, `name_tail` and `name_confidence`. A docstring before the
command goes to `name`.
-/
elab (name := roundoffStochasticTheorem) doc:(docComment)? "roundoff" "stochastic" "theorem"
    name:ident " := " computation:term : command => do
  let proofName ← Command.liftCoreM <| Core.mkFreshUserName (name.getId ++ `proof)
  let proof := mkIdentFrom name proofName
  let errorsBefore := (← get).messages.toList.countP (·.severity == .error)
  Command.elabCommand (← `(command|
    private abbrev $proof := @(stochastic_roundoff_proof% $computation)))
  if (← get).messages.toList.countP (·.severity == .error) > errorsBefore then return
  Command.elabCommand (← `(command|
    $[$doc:docComment]? theorem $name : type_of% (private_decl% @$proof) := @$proof))
  for field in #[`mean, `second, `tail, `confidence] do
    let derived := mkIdentFrom name (name.getId.appendAfter s!"_{field}")
    let field := mkIdent field
    Command.elabCommand (← `(command|
      theorem $derived : type_of%
          (stochastic_roundoff_projection% $field (private_decl% @$proof)) :=
        @(stochastic_roundoff_projection% $field @$proof)))

/-- The inputs and hypotheses that the computation of a `roundoff stochastic theorem` binds are
those of the theorems it declares, so the unused-variable linter does not ask for a reference to
them. -/
@[unused_variables_ignore_fn]
def ignoreTheoremBinders : Linter.IgnoreFunction := fun _ stack _ =>
  isComputationBinder ``roundoffStochasticTheorem stack

end FloatLib.Floats.Formats.BinaryInterchange.Roundoff.StochasticMode
