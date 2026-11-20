/-
Copyright (c) 2026 FloatLib. All rights reserved.
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
  else if hasModulePrefix moduleName "FloatLib.Floats.ExecFloat.Backends.Kernel" ||
      hasModulePrefix moduleName "FloatLib.Floats.ExecFloat.Backends.Tag" then
    -- `float_decide`, `#kernel_eval` and the two backend tags are what a user writes.
    classified "exec-float" "experimental"
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
      "FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath" ||
      hasModulePrefix moduleName
        "FloatLib.Floats.Formats.BinaryInterchange.StaticByte.KernelPath" then
    classified "configured-binary" "experimental"
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
  else if moduleName == "FloatLib" || moduleName == "FloatLib.Floats" ||
      moduleName == "FloatLib.Floats.Certified" then
    classified "exec-float" "stable"
  else if hasModulePrefix moduleName "FloatLib.Tactic" ||
      hasModulePrefix moduleName "FloatLib.Util" then
    -- Tactics, commands and their helpers, as the automation modules they came from were.
    classified "core-numerics" "experimental"
  else if hasModulePrefix moduleName "FloatLib.Examples" then
    -- The worked examples, which the axiom audit loads. No module of the root imports them.
    classified "examples" "experimental"
  else
    .error s!"unclassified FloatLib module: {moduleName}"

-- Moving a declaration changes its file, not its audience or compatibility promise.
-- Keep these reviewed module classifications explicit, including opt-in commands.
private def classifyMovedModule : String → Option (String × String)
  | "FloatLib.Tactic.DirectionRule"
  | "FloatLib.Tactic.OutcomeRule"
    => some ("configured-binary", "experimental")
  | "FloatLib.Tactic.FloatInfo.IEEE754.Native"
  | "FloatLib.Tactic.NativeCapability"
  | "FloatLib.Tactic.NativeCarrier"
    => some ("configured-binary", "stable")
  | "FloatLib.Tactic.Interval"
  | "FloatLib.Tactic.Interval.Aggregates"
  | "FloatLib.Tactic.Interval.Bounds"
  | "FloatLib.Tactic.Interval.Coeff"
  | "FloatLib.Tactic.Interval.Constraints"
  | "FloatLib.Tactic.Interval.Constraints.Derive"
  | "FloatLib.Tactic.Interval.Constraints.Forms"
  | "FloatLib.Tactic.Interval.Constraints.Reify"
  | "FloatLib.Tactic.Interval.Constraints.Search"
  | "FloatLib.Tactic.Interval.Constraints.Slopes"
  | "FloatLib.Tactic.Interval.Diagnostics"
  | "FloatLib.Tactic.Interval.Functions"
  | "FloatLib.Tactic.Interval.Registry"
  | "FloatLib.Tactic.Interval.Reify"
  | "FloatLib.Tactic.Interval.Series"
  | "FloatLib.Tactic.Numerics"
  | "FloatLib.Tactic.Numerics.Attribute"
  | "FloatLib.Util.Polynomial"
    => some ("core-numerics", "experimental")
  | "FloatLib.Tactic.CompiledAs"
  | "FloatLib.Tactic.Cover"
  | "FloatLib.Tactic.FloatFormat"
  | "FloatLib.Tactic.LaneCall"
  | "FloatLib.Tactic.LaneDecide"
  | "FloatLib.Tactic.LaneTable"
  | "FloatLib.Tactic.PackedRow"
  | "FloatLib.Tactic.ReplacementProof"
  | "FloatLib.Util.Packed"
  | "FloatLib.Util.Provenance"
    => some ("core-numerics", "stable")
  | "FloatLib.Tactic.BinaryInterchangeSpec"
  | "FloatLib.Tactic.ComplexRule"
  | "FloatLib.Tactic.DescriptorBackends"
  | "FloatLib.Tactic.FloatFormat.Attribute"
  | "FloatLib.Tactic.FloatInfo.BinaryInterchange.Command"
  | "FloatLib.Tactic.FloatInfo.BinaryInterchange.Complex"
  | "FloatLib.Tactic.FloatInfo.BinaryInterchange.Interval"
  | "FloatLib.Tactic.FloatInfo.BinaryInterchange.Profile"
  | "FloatLib.Tactic.IeeeFormat"
  | "FloatLib.Tactic.InlineShort"
  | "FloatLib.Tactic.InlineStages"
  | "FloatLib.Tactic.InlineStatus"
  | "FloatLib.Tactic.KernelOperation"
  | "FloatLib.Tactic.KernelTables"
  | "FloatLib.Tactic.Roundoff"
  | "FloatLib.Tactic.Roundoff.Analyze"
  | "FloatLib.Tactic.Roundoff.Apply"
  | "FloatLib.Tactic.Roundoff.Backward"
  | "FloatLib.Tactic.Roundoff.Backward.Analyze"
  | "FloatLib.Tactic.Roundoff.Backward.Tree"
  | "FloatLib.Tactic.Roundoff.Basic"
  | "FloatLib.Tactic.Roundoff.Discharge"
  | "FloatLib.Tactic.Roundoff.Extension"
  | "FloatLib.Tactic.Roundoff.Index"
  | "FloatLib.Tactic.Roundoff.Loop"
  | "FloatLib.Tactic.Roundoff.Normalize"
  | "FloatLib.Tactic.Roundoff.Prove"
  | "FloatLib.Tactic.Roundoff.Relation"
  | "FloatLib.Tactic.Roundoff.Rules"
  | "FloatLib.Tactic.Roundoff.Sign"
  | "FloatLib.Tactic.Roundoff.Stochastic"
  | "FloatLib.Tactic.Roundoff.Tactic"
  | "FloatLib.Tactic.Roundoff.Tuple"
  | "FloatLib.Tactic.SpecializeDirections"
  | "FloatLib.Tactic.SpecializeSums"
  | "FloatLib.Tactic.StatusOperation"
    => some ("descriptor-model-binary", "experimental")
  | "FloatLib.Kernels.Selection.Portfolio"
  | "FloatLib.Tactic.CompilerBackends"
  | "FloatLib.Tactic.CompilerOptimize"
  | "FloatLib.Tactic.DirectForm"
  | "FloatLib.Tactic.ExecFloatSpec"
  | "FloatLib.Tactic.FloatDecide"
  | "FloatLib.Tactic.FormRule"
  | "FloatLib.Tactic.KernelCost"
  | "FloatLib.Tactic.KernelEval"
  | "FloatLib.Tactic.KernelInline"
  | "FloatLib.Tactic.KernelOptimize"
  | "FloatLib.Tactic.KernelProj"
  | "FloatLib.Tactic.KernelRefl"
  | "FloatLib.Tactic.KernelRules"
  | "FloatLib.Tactic.KernelShape"
  | "FloatLib.Tactic.KernelTwin"
  | "FloatLib.Util.Declaration"
  | "FloatLib.Util.KernelReduction"
    => some ("exec-float", "experimental")
  | "FloatLib.Kernels.Execution.Capability"
  | "FloatLib.Kernels.Execution.Certificate"
  | "FloatLib.Kernels.Execution.Dispatch"
  | "FloatLib.Kernels.Execution.Instances"
  | "FloatLib.Kernels.Execution.Operations"
  | "FloatLib.Kernels.Execution.Proof"
  | "FloatLib.Kernels.Execution.Spec"
  | "FloatLib.Numerics.Executable.Carrier"
  | "FloatLib.Numerics.Executable.Comparison"
  | "FloatLib.Numerics.Executable.Conversion.Core"
  | "FloatLib.Numerics.Executable.Conversion.Proof"
  | "FloatLib.Numerics.Executable.Conversion.Runtime"
  | "FloatLib.Numerics.Executable.ExactMap"
  | "FloatLib.Numerics.Executable.Packed"
  | "FloatLib.Tactic.DeclareCapability"
  | "FloatLib.Tactic.FloatInfo"
  | "FloatLib.Tactic.FloatInfo.Command"
  | "FloatLib.Tactic.FloatInfo.Inspection"
  | "FloatLib.Tactic.FloatInfo.Profile"
  | "FloatLib.Tactic.FloatInfo.Render"
  | "FloatLib.Tactic.PackedValues"
  | "FloatLib.Tactic.PortfolioCapability"
    => some ("exec-float", "stable")
  | "FloatLib.Kernels.Selection.Certified"
  | "FloatLib.Kernels.Selection.Metadata"
  | "FloatLib.Kernels.Selection.Policy"
  | "FloatLib.Kernels.Selection.Report"
  | "FloatLib.Kernels.Selection.Scoring"
  | "FloatLib.Tactic.AutomaticCapability"
  | "FloatLib.Tactic.ByteCapability"
  | "FloatLib.Tactic.ByteTableCapability"
  | "FloatLib.Tactic.CandidateSet"
  | "FloatLib.Tactic.FamilyCapability"
  | "FloatLib.Tactic.FirstOrder"
  | "FloatLib.Tactic.FixedFormat"
  | "FloatLib.Tactic.LimbCapability"
  | "FloatLib.Tactic.PlanCapability"
  | "FloatLib.Tactic.PlannedCapability"
  | "FloatLib.Tactic.TablePlanCapability"
    => some ("internal-backend", "internal")
  | "FloatLib.Tactic.FloatInfo.P3109"
    => some ("p3109", "experimental")
  | "FloatLib.Tactic.FloatInfo.Posit"
    => some ("posit", "experimental")
  | "FloatLib.Tactic.FloatInfo.Posit.Quire"
    => some ("quire", "experimental")
  | "FloatLib.Kernels.Block.Maximum"
  | "FloatLib.Numerics.Quantization.Block.Bounds"
  | "FloatLib.Numerics.Quantization.Block.Coded"
  | "FloatLib.Numerics.Quantization.Block.Dot"
  | "FloatLib.Numerics.Quantization.Block.Format"
  | "FloatLib.Numerics.Quantization.Block.Policy"
  | "FloatLib.Numerics.Quantization.Block.Transpose"
  | "FloatLib.Numerics.Quantization.Rounding"
  | "FloatLib.Tactic.FloatInfo.Block"
  | "FloatLib.Tactic.FloatInfo.Codebook"
  | "FloatLib.Tactic.FloatInfo.FixedPoint.Bounded"
  | "FloatLib.Tactic.FloatInfo.FixedPoint.Exact"
  | "FloatLib.Tactic.FloatInfo.Logarithmic.Exact"
  | "FloatLib.Tactic.FloatInfo.OCP.MX.E8M0"
  | "FloatLib.Tactic.NearestFlat"
  | "FloatLib.Tactic.ScanLoop"
    => some ("specialized-formats", "experimental")
  | "FloatLib.Tactic.FloatInfo.Codebook.Configured"
  | "FloatLib.Tactic.FloatInfo.FixedPoint.Bounded.Configured"
  | "FloatLib.Tactic.FloatInfo.FixedPoint.Configured"
  | "FloatLib.Tactic.FloatInfo.Logarithmic.Configured"
  | "FloatLib.Tactic.FloatInfo.OCP.MX.Configured"
    => some ("specialized-formats", "stable")
  | _ => none

private def classifyDeclaration (moduleName declarationName : String) :
    Except String Classification :=
  if moduleName == "FloatLib.Util.KernelReduction" &&
      hasModulePrefix declarationName "FloatLib.Numerics.Packed" then
    -- The packed-data readers share this utility with backend evaluation helpers.
    classified "core-numerics" "stable"
  else
    match classifyMovedModule moduleName with
    | some (group, stability) => classified group stability
    | none => classifyModule moduleName

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
          match classifyDeclaration moduleName name.toString with
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
