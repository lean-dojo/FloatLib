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
      (``Model.isFinite_roundToIntegral, integral), (``Model.remainder_exact, truncation)] do
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

/-- `#float_info` gives each constant as an exact power-of-two expression and six digits. -/
private def checkConstants (format : Expr) (expected : List (String × String)) :
    TermElabM Unit := do
  let summary ← FloatInfo.inspectSummary format
  let profile := FloatInfo.profile summary "" "" []
  for (label, value) in expected do
    match profile.values.find? (·.label == label) with
    | some entry =>
        unless entry.value == value do
          throwError "#float_info reports {label} as {entry.value}, expected {value}"
    | none => throwError "#float_info has no entry {label}"

run_cmd liftTermElabM do
  checkConstants (mkConst ``FloatFormat.binary32)
    [ ("largest finite value (maxFinite)", "(2 - 2^-23) * 2^127 ≈ 3.40282e38")
    , ("least normal value (minNormal)", "2^-126 ≈ 1.17549e-38")
    , ("least subnormal value (minSubnormal)", "2^-149 ≈ 1.40130e-45")
    , ("machine epsilon (epsilon)", "2^-23 ≈ 1.19209e-7") ]
  checkConstants (mkConst ``FloatFormat.binary64)
    [ ("largest finite value (maxFinite)", "(2 - 2^-52) * 2^1023 ≈ 1.79769e308")
    , ("least subnormal value (minSubnormal)", "2^-1074 ≈ 4.94066e-324") ]
  checkConstants (mkConst ``FloatFormat.e4m3fn)
    [ ("largest finite value (maxFinite)", "(2 - 2^-2) * 2^8 ≈ 4.48000e2") ]
