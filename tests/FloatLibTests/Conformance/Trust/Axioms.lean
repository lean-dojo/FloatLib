/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
import all FloatLib.Floats.Formats.Posit.Model.Decode
import all FloatLib.Kernels.FixedWord.Quotient.Compiler
import all FloatLib.Kernels.FixedWord.IntegerSquareRoot.Compiler
import all FloatLib.Kernels.FixedWord.CheckedSqrt.Compiler
public import FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
public import FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded
public import FloatLibTests.Conformance.BinaryInterchange.MixedError
public import FloatLibTests.Conformance.BinaryInterchange.NativeModel
public import FloatLibTests.Conformance.BinaryInterchange.Roundoff
public import FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels
public import FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions
public import FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations
public import FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples
public import FloatLibTests.Conformance.Execution.Certificates
public import FloatLibTests.Conformance.Formats.PackedValues
public import FloatLibTests.Conformance.Numerics.Coeff
public import FloatLibTests.Conformance.Numerics.IntervalCoeff
public import FloatLibTests.Conformance.Numerics.Packed
public import FloatLibTests.Conformance.Numerics.Wiener
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
The imports cover the public root, the optional binary and decimal transcendental proofs and the
`roundoff` analysis.
The quotient, integer square root, and checked square root compiler certificates are loaded
explicitly because their clients import them privately.
Unimported modules are outside this check. Symbolic certificate, quire, native-model, packed-row and
coefficient-bound regression declarations are checked separately because they belong to
`FloatLibTests`.

The production traversal includes `@[csimp]` equality proofs. For the sole permitted
`@[implemented_by]` declaration, the audit also reads Lean's attribute and checks that its
replacement is an endpoint of the unconditional, universally quantified decoder equality theorem.
The private decoder proof is loaded explicitly for this check. Axiom collection by itself only
follows logical definitions and cannot validate a compiler substitution.

`tests/checks/trust-surface.sh` inventories source uses of native proof evaluation,
`@[implemented_by]`, `@[extern]`, and unchecked host imports. Neither audit verifies generated
machine code or the external numerical libraries. The opt-in `NativeFPU.Unchecked` API is outside
the configured arithmetic refinement theorems and this import closure.

The axiom traversal uses the pinned Lean implementation of `Lean.collectAxioms` in
`Lean.Util.CollectAxioms`. See also mathlib's `Mathlib.Util.AssertNoSorry`.
-/

public meta section

private def allowedKernelAxioms : Array Lean.Name :=
  #[``propext, ``Quot.sound, ``Classical.choice]

private def auditedTestDeclarations : Array Lean.Name :=
  #[
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.cast_fnuz_source,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.parse_tenth_real,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.sum_cancellation_real,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.dot_cancellation_real,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.rational_directed_enclosure,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.truncation_custom_range,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.truncation_custom_value,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.scaled_rational_zero,
    ``FloatLibTests.Conformance.BinaryInterchange.BoundaryCases.sterbenz_negative,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.toReal_expMinus1_tinyThreeHalves,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.exp_eightyNine_overflows,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.expMinus1_lt_zero_binary32,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.expMinus1_lt_zero_bfloat16,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.logPlus1_pos_leastSubnormal,
    ``FloatLibTests.Conformance.BinaryInterchange.MixedError.oneHot_sum_binary32,
    ``FloatLibTests.Conformance.BinaryInterchange.MixedError.oneHot_sum_bfloat16,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.horner_error,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.dot_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.horner_array_error,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.mulVec_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.expSum_nonneg,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.softmax_weight_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.fma_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.scale_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.peak_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.scaled_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions.sum_squares_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions.ping_mutual_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffRegressions.quarter_of_abs_le_one,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.round32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.ofInt32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.quantize_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.peak32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.scale32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.scale32_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.quarter_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.rotate32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.scaleSize32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.ofSmallInt32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.ofSize32_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffKernels.quantize_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.online_sum_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.online_sum_of_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.max_sum_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.online_attention_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.blocked_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.welford_squares_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.merged_squares_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.kahan_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.kahanStep_relation,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.kahan_sum_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.kahan_sum_abs_sub_le,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.kahan_product_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.max_vector_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.ema_corrected_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.kahan_list_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.kahan_list_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.kahan_array_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.kahan_vector_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.neumaierStep_relation,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.neumaierRelation_read,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.neumaier_sum_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.neumaier_sum_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.neumaier_array_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffStepRelations.kahan_squares_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTuples.square_gated_sum_mixedError,
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
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.checked32_int8_nan_metadata,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.checked32_int8_quiet_nan_metadata,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_sqrt_commutes,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_sqrt_commutes,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_sqrt_negative_zero,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_sqrt_negative_one,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_bridges_rewrite,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_isFinite_mul_rewrite,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_bridges_simp,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_sqrt_rewrite,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native64_add_sub_commute,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.native32_add_overflow,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.unpacked64_div_zero_quotient,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.unpacked64_div_zero_quotient_negative,
    ``FloatLibTests.Conformance.BinaryInterchange.NativeModel.unpacked64_mul_subnormal_tie,
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
    ``FloatLibTests.Conformance.Posit.Quire.posit8_quire_nar_propagation,
    ``FloatLibTests.Conformance.Numerics.Packed.small_eq,
    ``FloatLibTests.Conformance.Numerics.Packed.small_entries,
    ``FloatLibTests.Conformance.Numerics.Packed.small_sums,
    ``FloatLibTests.Conformance.Numerics.Packed.small_mul,
    ``FloatLibTests.Conformance.Numerics.Packed.count_checks,
    ``FloatLibTests.Conformance.Numerics.Packed.count_rev_pack,
    ``FloatLibTests.Conformance.Numerics.Packed.lanes_three_seven,
    ``FloatLibTests.Conformance.Numerics.Packed.xy_check,
    ``FloatLibTests.Conformance.Numerics.Packed.entries_xy,
    ``FloatLibTests.Conformance.Numerics.Packed.xy_values,
    ``FloatLibTests.Conformance.Numerics.Packed.window_and_rounding,
    ``FloatLibTests.Conformance.Numerics.Packed.symmetric_rows,
    ``FloatLibTests.Conformance.Numerics.Packed.rounding_spec,
    ``FloatLibTests.Conformance.Numerics.Packed.signs_spec,
    ``FloatLibTests.Conformance.Numerics.Packed.pack_spec,
    ``FloatLibTests.Conformance.Numerics.Packed.fine_autocorr,
    ``FloatLibTests.Conformance.Numerics.Packed.small_squares,
    ``FloatLibTests.Conformance.Numerics.Packed.guard_refuses,
    ``FloatLibTests.Conformance.Numerics.Packed.wrong_product,
    ``FloatLibTests.Conformance.Numerics.Packed.overflow_breaks_lanes,
    ``FloatLibTests.Conformance.Numerics.Packed.wrong_values,
    ``FloatLibTests.Conformance.Numerics.Packed.absSum_overflows,
    ``FloatLibTests.Conformance.Numerics.Packed.linked_checks,
    ``FloatLibTests.Conformance.Numerics.Coeff.sup_check,
    ``FloatLibTests.Conformance.Numerics.Coeff.sup_bound,
    ``FloatLibTests.Conformance.Numerics.Coeff.l1_value,
    ``FloatLibTests.Conformance.Numerics.Coeff.chebyshev_bound,
    ``FloatLibTests.Conformance.Numerics.Coeff.deriv_cos,
    ``FloatLibTests.Conformance.Numerics.Coeff.l1_bounds,
    ``FloatLibTests.Conformance.Numerics.Coeff.deriv_bound,
    ``FloatLibTests.Conformance.Numerics.Coeff.hilbert_bound,
    ``FloatLibTests.Conformance.Numerics.Coeff.small_hilbert_and_deriv,
    ``FloatLibTests.Conformance.Numerics.Coeff.small_product,
    ``FloatLibTests.Conformance.Numerics.Coeff.below_sup_refused,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.exact_min,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.exact_min_monomials,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.sine_ball,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.free_sine,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.ramp_ball,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.sine_exact,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.difference,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.mixed_abs,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.row_bound,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.chebyshev_min,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.chebyshev_ball,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.power_exact,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.power_lower,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.power_boxes,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.norm_ball,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.norm_upper,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.norm_lower,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.exact_min_check,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.complex_check,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.wrong_link,
    ``FloatLibTests.Conformance.Numerics.IntervalCoeff.wrong_horner,
    ``FloatLibTests.Conformance.Numerics.Wiener.check,
    ``FloatLibTests.Conformance.Numerics.Wiener.eval_f,
    ``FloatLibTests.Conformance.Numerics.Wiener.defect_inv,
    ``FloatLibTests.Conformance.Numerics.Wiener.norm_v,
    ``FloatLibTests.Conformance.Numerics.Wiener.inverse_bound,
    ``FloatLibTests.Conformance.Numerics.Wiener.eval_g,
    ``FloatLibTests.Conformance.Numerics.Wiener.norm_g,
    ``FloatLibTests.Conformance.Numerics.Wiener.defect_invSqrt,
    ``FloatLibTests.Conformance.Numerics.Wiener.invSqrt_bound,
    ``FloatLibTests.Conformance.Numerics.Wiener.wrong_inverse,
    ``FloatLibTests.Conformance.Formats.PackedValues.single_row,
    ``FloatLibTests.Conformance.Formats.PackedValues.other_rows,
    ``FloatLibTests.Conformance.Formats.PackedValues.single_value,
    ``FloatLibTests.Conformance.Formats.PackedValues.lower_bound,
    ``FloatLibTests.Conformance.Formats.PackedValues.upper_bound,
    ``FloatLibTests.Conformance.Formats.PackedValues.sine_bound,
    ``FloatLibTests.Conformance.Formats.PackedValues.wrong_denominator,
    ``FloatLibTests.Conformance.Formats.PackedValues.singleRow.link,
    ``FloatLibTests.Conformance.Formats.PackedValues.positRow.link,
    ``FloatLibTests.Conformance.Formats.PackedValues.centRow.link,
    ``FloatLibTests.Conformance.Formats.PackedValues.fractionRow.link,
    ``FloatLibTests.Conformance.Formats.PackedValues.blockRow.link
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
  let replacementName := `FloatLib.Floats.Formats.Posit.Model.Internal.toDyadic?
  let proofName := `FloatLib.Floats.Formats.Posit.Model.Internal.toDyadic?_eq
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
