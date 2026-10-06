/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public meta import Lean.Elab.Command

/-!
# Inspection applicability regressions

A validated theorem name does not establish that its descriptor premises hold. These checks
exercise the profiles for a named IEEE format, a narrow IEEE-style format, and finite-only E2M3.
-/

public meta section

open Lean Elab Command Meta
open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.ExecFloat

private def checkIntegralProfile (format : Expr) (truncation integral : Bool) : TermElabM Unit := do
  let summary ← FloatInfo.inspectSummary format
  let profile := FloatInfo.profile summary "" "" []
  for (name, expected) in [(``Model.isFinite_roundToIntegral_towardZero, truncation),
      (``Model.isFinite_roundToIntegral, integral), (``Model.remainderWithStatus_exact, truncation)] do
    let surfaces := profile.theoremSurfaces.filter (fun surface => surface.declarations.contains name)
    let [surface] := surfaces
      | throwError "expected exactly one inspection surface for {name}"
    let verified := match surface.applicability with
      | .verifiedForType => true
      | _ => false
    unless verified == expected do
      throwError "incorrect descriptor applicability for {name}"

run_cmd liftTermElabM do
  checkIntegralProfile (mkConst ``FloatFormat.binary32) true true
  checkIntegralProfile (mkConst ``FloatFormat.e2m3) false false
  let narrow ← Term.elabTerm (← `(FloatFormat.ieee 2 3)) none
  Term.synthesizeSyntheticMVarsNoPostponing
  checkIntegralProfile (← instantiateMVars narrow) true false
