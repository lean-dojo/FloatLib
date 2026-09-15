/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib
import FloatLibTests.Conformance
import Lean

/-!
# Public API inventory

This internal command emits a deterministic JSON inventory of declarations owned by
FloatLib modules. The root import is public while tests are private, so the environment can
distinguish declarations available to ordinary users from declarations loaded only for audits.

The classification is intentionally explicit. A newly imported module makes this command fail
until its audience and compatibility status have been reviewed.
-/

open Lean Lean.Elab Command

private structure Classification where
  group : String
  stability : String

private def classified (group stability : String) : Except String Classification :=
  .ok { group, stability }

private def hasModulePrefix (moduleName modulePrefix : String) : Bool :=
  moduleName == modulePrefix || moduleName.startsWith (modulePrefix ++ ".")

private def classifyModule (moduleName : String) : Except String Classification :=
  if hasModulePrefix moduleName "FloatLibTests" then
    classified "validation-only" "internal"
  else if hasModulePrefix moduleName "FloatLib.Floats.ExecFloat.Backends" then
    classified "internal-backend" "internal"
  else if hasModulePrefix moduleName
      "FloatLib.Floats.Formats.BinaryInterchange.Configured.Backend" ||
      hasModulePrefix moduleName
        "FloatLib.Floats.Formats.BinaryInterchange.Configured.Plan" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit.Configured.Backend" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit.Configured.Plan" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit.Arithmetic.Word" then
    classified "internal-backend" "internal"
  else if hasModulePrefix moduleName "FloatLib.Numerics.Automation" then
    classified "core-numerics" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Numerics" then
    classified "core-numerics" "stable"
  else if hasModulePrefix moduleName "FloatLib.Kernels" then
    classified "verified-kernels" "stable"
  else if hasModulePrefix moduleName "FloatLib.Floats.ExecFloat.Automation" then
    classified "exec-float" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Floats.ExecFloat" then
    classified "exec-float" "stable"
  else if hasModulePrefix moduleName
      "FloatLib.Floats.Formats.BinaryInterchange.Configured" ||
      hasModulePrefix moduleName
        "FloatLib.Floats.Formats.BinaryInterchange.StaticByte.Conversion" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.IEEE754.Native" then
    classified "configured-binary" "stable"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.BinaryInterchange.StaticByte" then
    classified "internal-backend" "internal"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.BinaryInterchange" then
    classified "descriptor-model-binary" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit.Quire.Configured" then
    classified "quire" "stable"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit.Quire" then
    classified "quire" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit.Configured" then
    classified "posit" "stable"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.Posit" then
    classified "posit" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.P3109" then
    classified "p3109" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Floats.Interval" then
    classified "interval" "stable"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats.FixedPoint.Configured" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.FixedPoint.Bounded.Configured" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.Logarithmic.Configured" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.Codebook.Configured" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.Block.Configured" ||
      hasModulePrefix moduleName "FloatLib.Floats.Formats.OCP.MX.Configured" then
    classified "specialized-formats" "stable"
  else if hasModulePrefix moduleName "FloatLib.Floats.Formats" then
    classified "specialized-formats" "experimental"
  else if moduleName == "FloatLib" || moduleName == "FloatLib.Floats" then
    classified "exec-float" "stable"
  else
    .error s!"unclassified FloatLib module: {moduleName}"

private def constantKindName : Lean.ConstantKind → String
  | .defn => "definition"
  | .thm => "theorem"
  | .axiom => "axiom"
  | .opaque => "opaque"
  | .quot => "quotient"
  | .induct => "inductive"
  | .ctor => "constructor"
  | .recursor => "recursor"

private def isFloatLibName (name : Lean.Name) : Bool :=
  let text := name.toString
  hasModulePrefix text "FloatLib" || hasModulePrefix text "FloatLibTests"

run_cmd do
  let env ← getEnv
  let rootEnv := env.setExporting true
  let declarations :=
    env.constants.toList.toArray.qsort fun left right =>
      left.1.toString < right.1.toString
  let mut entries : Array Json := #[]
  let mut failures : Array String := #[]
  for (name, info) in declarations do
    if isFloatLibName name && !isPrivateName name then
      match env.getModuleIdxFor? name with
      | none =>
          failures := failures.push s!"cannot identify declaring module for {name}"
      | some moduleIdx =>
          let moduleName := env.header.moduleNames[moduleIdx.toNat]!.toString
          match classifyModule moduleName with
          | .error message =>
              failures := failures.push message
          | .ok classification =>
              entries := entries.push <| Json.mkObj [
                ("name", toJson name.toString),
                ("module", toJson moduleName),
                ("kind", toJson (constantKindName (ConstantKind.ofConstantInfo info))),
                ("exportedFromRoot", toJson (rootEnv.contains name)),
                ("group", toJson classification.group),
                ("stability", toJson classification.stability)
              ]
  unless failures.isEmpty do
    throwError m!"public API classification failed:\n{String.intercalate "\n" failures.toList}"
  let output := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("declarations", Json.arr entries)
  ]
  liftIO <| IO.println output.compress
