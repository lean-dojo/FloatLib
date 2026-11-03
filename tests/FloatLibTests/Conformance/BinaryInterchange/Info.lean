/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats
public import FloatLib.Floats.Formats.BinaryInterchange.Info.Profile
public meta import FloatLib.Floats.Formats.OCP.FP8.E5M2
public meta import Lean.Elab.Command

/-!
# Inspection applicability regressions

A validated theorem name does not establish that its descriptor premises hold. These checks
exercise the profiles for a named IEEE format, a narrow IEEE-style format, and finite-only E2M3.
They also check that a standard is named only for a matching layout, encoding, and bias, and that
a carrier's report lists the theorems about its own values apart from the proof model's.
-/

public meta section

open Lean Elab Command Meta

section Profiles

open FloatLib.Floats.Formats.BinaryInterchange
open FloatLib.Floats.ExecFloat

private def checkIntegralProfile (format : Expr) (truncation integral : Bool) : TermElabM Unit := do
  let summary ← FloatInfo.inspectSummary format
  let profile := FloatInfo.profile summary "" ""
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
  let profile := FloatInfo.profile summary "" ""
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

/-- Elaborate a descriptor term and read its report summary. -/
private def summaryOf (format : Term) : TermElabM FloatInfo.Summary := do
  let format ← Term.elabTerm format (some (mkConst ``FloatFormat))
  Term.synthesizeSyntheticMVarsNoPostponing
  FloatInfo.inspectSummary (← instantiateMVars format)

/-- `#float_info` names a standard from the complete layout, encoding, and bias. -/
private def checkStandard (format : Term) (expected : String) : TermElabM Unit := do
  let standard := FloatInfo.standardName (← summaryOf format)
  unless standard == expected do
    throwError "#float_info names the standard of {format} as {standard}, expected {expected}"

run_cmd liftTermElabM do
  checkStandard (← `(FloatFormat.binary16)) "IEEE 754-2019 binary16"
  checkStandard (← `(FloatFormat.binary64)) "IEEE 754-2019 binary64"
  checkStandard (← `(FloatFormat.binary128)) "IEEE 754-2019 binary128"
  checkStandard (← `(FloatFormat.binary256)) "IEEE 754-2019 binary256"
  checkStandard (← `(FloatFormat.ieee 16 143)) "IEEE 754-2019 binary160"
  checkStandard (← `(FloatFormat.bfloat16))
    "bfloat16, the brain floating-point format; not an IEEE 754 interchange format"
  -- 16 bits, but not binary16's 5 exponent bits.
  checkStandard (← `(FloatFormat.ieee 6 9))
    "IEEE-style layout; not an IEEE 754 interchange format"
  -- binary16's widths with a finite-only encoding.
  checkStandard (← `(FloatFormat.finite 5 10))
    "binary layout with format-specific encoding or bias"
  -- binary16's widths and encoding with a bias other than the IEEE one.
  checkStandard (← `(FloatFormat.custom 5 10 14 .ieee))
    "binary layout with format-specific encoding or bias"

/-- Whether any theorem group in `surfaces` lists `name`. -/
private def lists (surfaces : List TheoremSurface) (name : Name) : Bool :=
  surfaces.any fun surface => surface.declarations.contains name

run_cmd liftTermElabM do
  let summary ← summaryOf (← `(FloatFormat.binary32))
  let all := Backend.Operation.all.map fun operation => (operation, true)
  let configured := FloatInfo.profile summary "" "" .configured all
  -- `x + y` on `Binary32` rewrites with the notation form; the model theorem needs `toModel`.
  let [model] := configured.relatedTheorems
    | throwError "the configured report has no single section about the proof model"
  unless lists configured.theoremSurfaces ``FloatLib.Floats.ExecFloat.Proof.add_notation_eq_spec &&
      lists configured.theoremSurfaces ``FloatLib.Floats.ExecFloat.Binary.toReal_add_eq_roundAt &&
      !lists configured.theoremSurfaces ``Model.toReal_add_eq_roundAt &&
      model.type == ``Model && model.embedding == ``FloatLib.Floats.ExecFloat.Binary.toModel &&
      lists model.surfaces ``Model.toReal_add_eq_roundAt do
    throwError "the configured report does not separate Binary32 theorems from Model theorems"
  -- The rounding entry names `ExecFloat.sqrt`, so the decoding group lists its bridge.
  unless lists configured.theoremSurfaces
      ``FloatLib.Floats.ExecFloat.Binary.toModel_execFloat_sqrt do
    throwError "the configured report omits the decoding bridge of `ExecFloat.sqrt`"
  -- The proof model's own report has no related section, so its heading claims nothing.
  unless (FloatInfo.profile summary "" "").relatedTheorems.isEmpty do
    throwError "the proof model's report lists theorems about a related type"
  -- Without an installed division, the report lists no division theorem.
  let noDiv := all.map fun (operation, available) => (operation, available && operation != .div)
  let withoutDiv := FloatInfo.profile summary "" "" .configured noDiv
  if lists withoutDiv.theoremSurfaces ``FloatLib.Floats.ExecFloat.Binary.toReal_div_eq_roundAt ||
      lists withoutDiv.theoremSurfaces ``FloatLib.Floats.ExecFloat.Proof.div_eq_spec then
    throwError "the configured report lists a theorem for an operation that is not installed"
  -- A byte type has no direction or status options and no theorem about its real rounding.
  let staticByte := FloatInfo.profile summary "" "" .staticByte all
  unless (staticByte.rounding.find? (·.label == "directions and flags")).any
        (·.value.startsWith "none on this type") &&
      !lists staticByte.theoremSurfaces ``FloatLib.Floats.ExecFloat.Binary.toReal_add_eq_roundAt do
    throwError "the static-byte report claims options or theorems the byte type does not have"
  let fnuz ← summaryOf (← `(FloatFormat.e4m3fnuz))
  let spelling := FloatInfo.configuredSpelling fnuz
  unless spelling == "ExecFloat.Binary (exponentBits := 4) (fractionBits := 3) " ++
      "(encoding := .finiteUnsignedZero)" do
    throwError "unexpected configured spelling of E4M3FNUZ: {spelling}"

end Profiles

/-! ## Reports

Theorem names in a report print relative to the open namespaces, so this section opens only
`FloatLib.Floats`, as the guide does.
-/

section Reports

open FloatLib.Floats

-- The header names the inspected type, and the first theorems are the ones about its values.
/--
info: Float information: Binary32
  family: binary interchange
  standard: IEEE 754-2019 binary32
-/
#guard_msgs (substring := true) in
#float_info Binary32

/--
Theorems about Binary32 values:
  [verified] arithmetic equals its reference operation: ExecFloat.Proof.add_notation_eq_spec and 9 more
  [verified] a finite result is one nearest-even rounding of the exact result: ExecFloat.Binary.toReal_add_eq_roundAt and 5 more
-/
#guard_msgs (substring := true) in
#float_info Binary32

-- A byte type claims no rounding-direction or status options, and names the type that has them.
/--
directions and flags: none on this type; ExecFloat.Binary (exponentBits := 5) (fractionBits := 2) has the same values, with rounding-direction and status options
-/
#guard_msgs (substring := true) in
#float_info E5M2

-- The execution section names the planning policy in scope, here a non-default one.
/--
planning policy: throughput
-/
#guard_msgs (substring := true) in
open scoped ExecFloat.Backend.PlanningThroughput in
#float_info ExecFloat.Binary (exponentBits := 4) (fractionBits := 3)

-- The default plan of a 256-bit layout stores the proof model, and the layout is binary256.
/--
standard: IEEE 754-2019 binary256

Format:
  storage: BitVec 256 (the proof model itself)
-/
#guard_msgs (substring := true) in
#float_info Binary256

-- A type of an imported family that has no report is not told to import that family again.
/--
error: `#float_info` has no report for Formats.BinaryInterchange.FloatFormat. It reports FloatLib's numerical types
-/
#guard_msgs (substring := true) in
#float_info Formats.BinaryInterchange.FloatFormat

-- `#float_help` says that binary intervals over a configured type have no report, and the fallback
-- names the interval type that does.
/--
error: `#float_info` has no report for ExecFloat.Binary.Interval (format := Formats.BinaryInterchange.FloatFormat.binary32). It reports FloatLib's numerical types: ExecFloat types such as `Binary32` and `Posit32`, the proof models `Formats.BinaryInterchange.Model fmt` and `Formats.Posit.Model fmt`, the intervals `Formats.BinaryInterchange.Model.Interval fmt`
-/
#guard_msgs (substring := true) in
#float_info ExecFloat.Binary.Interval (format := Formats.BinaryInterchange.FloatFormat.binary32)

-- Every entry point that `#float_help` lists resolves after `open FloatLib.Floats`.
run_cmd do
  for (name, _, _) in FloatLib.Floats.ExecFloat.FloatHelp.Command.entryPoints do
    discard <| liftCoreM <| realizeGlobalConstNoOverload (mkIdent name.toName)

-- Every module that the fallback error recommends exists.
run_cmd do
  for (_, module) in FloatLib.Floats.ExecFloat.FloatInfo.Command.reportModules do
    unless ((← getEnv).getModuleIdx? module).isSome do
      throwError "the `#float_info` fallback recommends the missing module {module}"

end Reports
