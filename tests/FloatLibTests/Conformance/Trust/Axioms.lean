/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
import all FloatLib.Floats.Formats.Posit.Model.Decode
import all FloatLib.Kernels.FixedWord.Quotient.Compiler
public import FloatLibTests.Conformance.BinaryInterchange.NativeModel
public import FloatLibTests.Conformance.Execution.Certificates
public import FloatLibTests.Conformance.Posit.Quire
public meta import Lean.Compiler.CSimpAttr
public meta import Lean.Compiler.ImplementedByAttr
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.Util.CollectAxioms

/-!
# Kernel-axiom audit

At build time, collect the transitive axioms of every loaded declaration whose originating
module belongs to `FloatLib`, including private declarations available in this environment.
Only propositional extensionality, quotient soundness, and classical choice are accepted.
The imports cover the public root and the optional binary and decimal transcendental proofs.
The quotient compiler certificate is loaded explicitly because its clients import it privately.
Unimported modules are outside this check. Symbolic certificate, quire, and native-model regression
declarations are checked separately because they belong to `FloatLibTests`.

The production traversal includes `@[csimp]` equality proofs. For the sole permitted
`@[implemented_by]` declaration, the audit also reads Lean's actual attribute and checks that its
replacement is an endpoint of the unconditional, universally quantified decoder equality theorem.
The private decoder proof is loaded explicitly for this check. Axiom collection by itself only
follows logical definitions and cannot validate a compiler substitution.

`tests/checks/trust-surface.sh` separately inventories source uses of native proof evaluation,
`@[implemented_by]`, `@[extern]`, and unchecked host imports. Neither audit verifies generated
machine code or the external numerical libraries. The explicit `NativeFPU.Unchecked` API remains
outside the configured arithmetic refinement theorems and this import closure.

The axiom traversal uses the pinned Lean implementation of `Lean.collectAxioms` in
`Lean.Util.CollectAxioms`; see also mathlib's `Mathlib.Util.AssertNoSorry`.
-/

public meta section

private def allowedKernelAxioms : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def auditedTestDeclarations : Array Lean.Name :=
  #[
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_roundtrip,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_roundtrip,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_nan_canonicalized,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.integer_conversion_spec,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.int64_to_native32_tie_down,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.int64_to_native32_tie_up,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.nat_to_native32_large_tie,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.int_to_native64_large_negative_tie,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_int8_boundary_fraction,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_int8_saturates,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_int8_negative_infinity,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_int8_nan,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_sqrt_commutes,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_sqrt_commutes,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_sqrt_negative_zero,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_sqrt_negative_one,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_add_sub_commute,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_add_overflow,
    ``FloatLibTests.Conformance.Execution.Certificates.descriptor,
    ``FloatLibTests.Conformance.Execution.Certificates.staticByte,
    ``FloatLibTests.Conformance.Execution.Certificates.ocpE4M3FN,
    ``FloatLibTests.Conformance.Execution.Certificates.ocpE5M2,
    ``FloatLibTests.Conformance.Execution.Certificates.ocpE2M1,
    ``FloatLibTests.Conformance.Execution.Certificates.ocpE2M3,
    ``FloatLibTests.Conformance.Execution.Certificates.ocpE3M2,
    ``FloatLibTests.Conformance.Execution.Certificates.onnxe4m3fnuz,
    ``FloatLibTests.Conformance.Execution.Certificates.onnxe5m2fnuz,
    ``FloatLibTests.Conformance.Execution.Certificates.posit2,
    ``FloatLibTests.Conformance.Execution.Certificates.posit8,
    ``FloatLibTests.Conformance.Execution.Certificates.posit9,
    ``FloatLibTests.Conformance.Execution.Certificates.posit16,
    ``FloatLibTests.Conformance.Execution.Certificates.posit17,
    ``FloatLibTests.Conformance.Execution.Certificates.posit32,
    ``FloatLibTests.Conformance.Execution.Certificates.posit33,
    ``FloatLibTests.Conformance.Execution.Certificates.posit64,
    ``FloatLibTests.Conformance.Execution.Certificates.posit65,
    ``FloatLibTests.Conformance.Execution.Certificates.posit128,
    ``FloatLibTests.Conformance.Execution.Certificates.posit129,
    ``FloatLibTests.Conformance.Execution.Certificates.posit256,
    ``FloatLibTests.Conformance.Execution.Certificates.posit4096,
    ``FloatLibTests.Conformance.Posit.Quire.posit2_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit3_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit4_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit5_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit6_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit7_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit8_all_quire_conversion_round_trips,
    ``FloatLibTests.Conformance.Posit.Quire.posit2_all_quire_products_refine,
    ``FloatLibTests.Conformance.Posit.Quire.posit3_all_quire_products_refine,
    ``FloatLibTests.Conformance.Posit.Quire.posit4_all_quire_products_refine,
    ``FloatLibTests.Conformance.Posit.Quire.posit5_all_quire_products_refine,
    ``FloatLibTests.Conformance.Posit.Quire.posit8_quire_shape,
    ``FloatLibTests.Conformance.Posit.Quire.posit8_quire_exact_product,
    ``FloatLibTests.Conformance.Posit.Quire.posit8_quire_positive_overflow_is_nar,
    ``FloatLibTests.Conformance.Posit.Quire.posit8_quire_nar_propagation
  ]

/-- Use the defining module, since private and generated names need not start with `FloatLib`. -/
private def isProductionDeclaration (env : Lean.Environment) (declaration : Lean.Name) : Bool :=
  match env.getModuleIdxFor? declaration with
  | some index => (`FloatLib).isPrefixOf env.header.moduleNames[index.toNat]!
  | none => false

private def checkAxioms (declaration : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  for axiomName in ← Lean.collectAxioms declaration do
    unless allowedKernelAxioms.contains axiomName do
      throwError "unapproved axiom {axiomName} occurs transitively in {declaration}"

/-- Require equality on every argument, with neither extra hypotheses nor restricted inputs. -/
private def checkReplacementEquality (logical replacement proof : Lean.Name) :
    Lean.Meta.MetaM Unit := do
  let .thmInfo info ← Lean.getConstInfo proof
    | throwError "replacement refinement {proof} is not a theorem"
  Lean.Meta.forallTelescope info.type fun arguments conclusion => do
    let some (_, lhs, rhs) := conclusion.eq?
      | throwError "replacement refinement {proof} does not conclude an equality"
    unless lhs.getAppFn.constName? == some replacement &&
        rhs.getAppFn.constName? == some logical &&
        lhs.getAppArgs == arguments && rhs.getAppArgs == arguments do
      throwError "replacement refinement {proof} must equate {replacement} and {logical} \
        on all universally quantified arguments, without additional hypotheses"

run_cmd
  let env := (← Lean.getEnv).setExporting false
  let logical := ``FloatLib.Floats.Formats.Posit.Model.toDyadic?
  let replacementName := `FloatLib.Floats.Formats.Posit.Model.toDyadicImpl?
  let proofName := `FloatLib.Floats.Formats.Posit.Model.toDyadicImpl?_eq_toDyadic?
  let mut productionCount : Nat := 0
  let mut privateCount : Nat := 0
  let mut csimpCount : Nat := 0
  let mut replacementCount : Nat := 0
  let mut replacementProof? : Option Lean.Name := none
  for (declaration, _) in env.constants do
    if isProductionDeclaration env declaration then
      productionCount := productionCount + 1
      if Lean.isPrivateName declaration then
        privateCount := privateCount + 1
      if Lean.Compiler.hasCSimpAttribute env declaration then
        csimpCount := csimpCount + 1
      if let some replacement := Lean.Compiler.getImplementedBy? env declaration then
        replacementCount := replacementCount + 1
        unless declaration == logical &&
            Lean.privateToUserName replacement == replacementName &&
            env.getModuleIdxFor? replacement == env.getModuleIdxFor? logical do
          throwError "unapproved compiler replacement: {declaration} implemented by {replacement}"
      if Lean.privateToUserName declaration == proofName &&
          env.getModuleIdxFor? declaration == env.getModuleIdxFor? logical then
        if replacementProof?.isSome then
          throwError "multiple replacement refinement theorems named {proofName}"
        replacementProof? := some declaration
      checkAxioms declaration
  if productionCount = 0 || csimpCount = 0 then
    throwError "the import closure must contain FloatLib declarations and @[csimp] proofs"
  unless replacementCount = 1 do
    throwError "expected one FloatLib compiler replacement, found {replacementCount}"
  let some replacement := Lean.Compiler.getImplementedBy? env logical
    | throwError "the posit decoder has no compiler replacement"
  let some replacementProof := replacementProof?
    | throwError "the private posit decoder refinement theorem was not loaded"
  Lean.Elab.Command.liftTermElabM do
    Lean.withoutExporting do
      checkReplacementEquality logical replacement replacementProof
  for declaration in auditedTestDeclarations do
    checkAxioms declaration
  Lean.logInfo m!"Axiom audit passed: {productionCount} loaded production declarations \
    ({privateCount} private), {csimpCount} compiler equality proofs, \
    {auditedTestDeclarations.size} test declarations, and one checked compiler replacement."
