/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public meta import Lean.Compiler.CSimpAttr
public meta import Lean.Compiler.ImplementedByAttr
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.Util.CollectAxioms
public import FloatLib
public import FloatLib.Examples
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.PowerProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ValueProof
public import FloatLib.Floats.Formats.BinaryInterchange.Complex.Roundoff
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.SquareRoot.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Proof
public import FloatLib.Floats.Formats.Block.Roundoff
public import FloatLib.Floats.Formats.DecimalInterchange.Reduction.Schedule.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof
public import FloatLibTests.Conformance.BinaryInterchange.BoundaryCases
public import FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded
public import FloatLibTests.Conformance.BinaryInterchange.MixedError
public import FloatLibTests.Conformance.BinaryInterchange.NativeModel
public import FloatLibTests.Conformance.Execution.Certificates
public import FloatLibTests.Conformance.Numerics.Coeff
public import FloatLibTests.Conformance.Numerics.Wiener
public import FloatLibTests.Conformance.Posit.Quire
public import FloatLibTests.Tactic.Interval.Coeff
public import FloatLibTests.Tactic.PackedValues
public import FloatLibTests.Tactic.Roundoff
public import FloatLibTests.Tactic.Roundoff.Backward
public import FloatLibTests.Tactic.Roundoff.Cases
public import FloatLibTests.Tactic.Roundoff.Closed
public import FloatLibTests.Tactic.Roundoff.Expm1x
public import FloatLibTests.Tactic.Roundoff.Kernels
public import FloatLibTests.Tactic.Roundoff.Native
public import FloatLibTests.Tactic.Roundoff.Regressions
public import FloatLibTests.Tactic.Roundoff.StepRelations
public import FloatLibTests.Tactic.Roundoff.Tightness
public import FloatLibTests.Tactic.Roundoff.Tuples

import all FloatLib.Floats.ExecFloat.Backends.Compiled.Word.NormalPair.Proof
import all FloatLib.Floats.ExecFloat.Backends.Compiled.Word.ProductRound.Proof
import all FloatLib.Floats.ExecFloat.Backends.Compiled.Word.Small.Fma.Proof
import all FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Packing.Internal
import all FloatLib.Floats.Formats.OCP.FP8.KernelTables
import all FloatLib.Floats.Formats.Posit.Model.Decode
import all FloatLib.Kernels.FixedWord.CheckedSqrt.Compiler
import all FloatLib.Kernels.FixedWord.IntegerSquareRoot.Compiler
import all FloatLib.Kernels.FixedWord.Quotient.Compiler
import all FloatLibTests.Conformance.Numerics.KernelComplex
import all FloatLibTests.Conformance.Numerics.KernelExact
import all FloatLibTests.Conformance.Numerics.Packed
import all FloatLibTests.Numerics.Stochastic
import all FloatLibTests.Numerics.StochasticBinary
import all FloatLibTests.Numerics.StochasticSequential
import all FloatLibTests.Tactic.Interval.Constraints
import all FloatLibTests.Tactic.KernelTwin
import all FloatLibTests.Tactic.Roundoff.Stochastic

/-!
# Kernel-axiom audit

At build time, collect the transitive axioms of every declaration of a `FloatLib` module that this
environment holds, private declarations included. Only propositional extensionality, quotient
soundness, and classical choice are accepted. The imports reach every module of the library but
the opt-in `NativeFPU.Unchecked`: the public root, the examples, the optional binary and decimal
transcendental proofs, the correctly rounded decimal functions, the `formatOf` square root, the
reduction schedules, the complex elementary functions and their `roundoff` rules, the `roundoff`
analysis, its block-format rules, the packed FP8 tables, and the stochastic-rounding families.
`tests/checks/trust-surface.sh` follows the imports through the sources and fails on a library
module that they miss. All four stochastic test modules and the exact-kernel
conformance modules (including complex balls, twins, packed dots and interval constraints) are
loaded with `import all` and every declaration they hold is audited separately.

This file reaches the library through public imports, so it holds what each module exports. A
declaration it does not hold is checked through the declarations that use it, whose collected
axioms include its own. The modules that every client imports privately, such as the quotient,
integer square root and checked square root compiler certificates and four backend proof modules,
are loaded with `import all` so that their declarations are checked directly, and so is the module
of the packed FP8 tables, whose table command gives proofs to the kernel by itself. A declaration
that is neither held nor used, mostly compiler-generated auxiliaries and a few unused private
lemmas, is outside this check. `tests/checks/trust-surface.sh` rejects `sorry` and `axiom` in its
source, and loads every level of every library module to check that the kernel holds no constant
of the library as an axiom. Symbolic certificate, quire, native-model,
packed-row and coefficient-bound regression declarations are checked separately because they belong
to `FloatLibTests`.

The production traversal includes `@[csimp]` equality proofs. For the sole permitted
`@[implemented_by]` declaration, the audit also reads Lean's attribute and checks, with the
library's own `Provenance.checkReplacementEquality`, that its replacement is an endpoint of the
unconditional, universally quantified decoder equality theorem registered by
`@[replacement_proof]`. The private decoder proof is loaded explicitly for this check. Axiom
collection by itself only follows logical definitions and cannot validate a compiler
substitution; `@[compiler_optimize]` runs the same replacement check at registration
(`Provenance.requireCompiled`).

Lean attaches a replacement of its own to the constructor-index function `T.ctorIdx` that it
generates for every inductive type `T` with several constructors: since Lean 4.36,
`T.ctorIdx._impl` reads the constructor tag of its argument with `getObjTagNat`. The audit accepts
exactly that generated pair after the library's `Provenance.isGeneratedCtorIdx` has checked its
names, its type and both bodies, and reports how many it found. No theorem relates the tag read
to `T.ctorIdx`; like the rest of code generation it is trusted to the compiler.

`tests/checks/trust-surface.sh` inventories source uses of native proof evaluation,
`@[implemented_by]`, `@[extern]`, and unchecked host imports. Neither audit verifies generated
machine code or the external numerical libraries. The opt-in `NativeFPU.Unchecked` API is outside
the configured arithmetic refinement theorems and outside these imports. It is the only library
module that is.

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
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.toReal_expm1_tinyThreeHalves,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.exp_eightyNine_overflows,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.expm1_lt_zero_binary32,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.expm1_lt_zero_bfloat16,
    ``FloatLibTests.Conformance.BinaryInterchange.CorrectlyRounded.logp1_pos_leastSubnormal,
    ``FloatLibTests.Conformance.BinaryInterchange.MixedError.oneHot_sum_binary32,
    ``FloatLibTests.Conformance.BinaryInterchange.MixedError.oneHot_sum_bfloat16,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.horner_error,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.dot_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.horner_array_error,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.mulVec_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.expSum_nonneg,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.softmax_weight_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.Roundoff.fma_error,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.horner_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.dot_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.dotList_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.hornerArray_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.hornerLead_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.mulVec_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.linear_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.sum_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.shared_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.quotient_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.dot_both,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.dot32_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.fma_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.wideDot_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.narrowed_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.sumSquares_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.norm_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.total_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.rows_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.countedSum_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.perceptron_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.rectifier_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.monomial_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.estrin_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.centered_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.cubes_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.productOfEntries_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.productList_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffBackward.scaledSum_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.head_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.head_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.head_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.mean_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.mean_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.activate_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.activate_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.activate_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.accumulate_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.accumulate_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.scaleBy_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.first_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.first_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffCases.nested_mixedError,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.axpy_mixedError,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.axpy_closed,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.axpy_backward,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.norm_mixedError,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.dot_mixedError,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.dot_closed,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.head_mixedError,
    ``FloatLibTests.Conformance.IEEE754.RoundoffNative.roundTrip_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness.sterbenz_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness.interval_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness.scaled_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness.scaled_backward,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffTightness.mixedAttributes_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffExpm1x.call_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffExpm1x.difference_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffExpm1x.entropy_mixedError,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffExpm1x.term_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.dot_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.horner_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.sumList_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.total_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.squarePlus_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.perceptron_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.norm_closed,
    ``FloatLibTests.Conformance.BinaryInterchange.RoundoffClosed.wideDot_closed,
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

/-- Audit all four stochastic test modules, including their private declarations. -/
private def auditedStochasticTestModules : Array Lean.Name :=
  #[`FloatLibTests.Numerics.Stochastic,
    `FloatLibTests.Numerics.StochasticBinary,
    `FloatLibTests.Tactic.Roundoff.Stochastic,
    `FloatLibTests.Numerics.StochasticSequential]

/-- Audit every declaration in the kernel conformance modules, including generated twins. -/
private def auditedKernelTestModules : Array Lean.Name :=
  #[`FloatLibTests.Conformance.Numerics.KernelExact,
    `FloatLibTests.Conformance.Numerics.KernelComplex,
    `FloatLibTests.Tactic.KernelTwin,
    `FloatLibTests.Tactic.Interval.Constraints,
    `FloatLibTests.Conformance.Numerics.Packed]

/-- Use the defining module, since private and generated names need not start with `FloatLib`. -/
private def isProductionDeclaration (env : Lean.Environment) (declaration : Lean.Name) : Bool :=
  match env.getModuleIdxFor? declaration with
  | some index => (`FloatLib).isPrefixOf env.header.moduleNames[index.toNat]!
  | none => false

private def checkAxioms (declaration : Lean.Name) : Lean.Elab.Command.CommandElabM Unit := do
  for axiomName in ← Lean.collectAxioms declaration do
    unless allowedKernelAxioms.contains axiomName do
      throwError "unapproved axiom {axiomName} occurs transitively in {declaration}"

run_cmd
  let env := (← Lean.getEnv).setExporting false
  let logical := ``FloatLib.Floats.Formats.Posit.Model.toDyadic?
  let replacementName := `FloatLib.Floats.Formats.Posit.Model.Internal.toDyadic?
  let mut productionCount : Nat := 0
  let mut privateCount : Nat := 0
  let mut stochasticTestCount : Nat := 0
  let mut exactTestCount : Nat := 0
  let mut csimpCount : Nat := 0
  let mut replacementCount : Nat := 0
  let mut ctorIdxCount : Nat := 0
  for (declaration, _) in env.constants do
    if isProductionDeclaration env declaration then
      productionCount := productionCount + 1
      if Lean.isPrivateName declaration then
        privateCount := privateCount + 1
      if Lean.Compiler.hasCSimpAttribute env declaration then
        csimpCount := csimpCount + 1
      if let some replacement := Lean.Compiler.getImplementedBy? env declaration then
        if FloatLib.Numerics.Provenance.isGeneratedCtorIdx env declaration replacement then
          ctorIdxCount := ctorIdxCount + 1
        else
          replacementCount := replacementCount + 1
          unless declaration == logical &&
              Lean.privateToUserName replacement == replacementName &&
              env.getModuleIdxFor? replacement == env.getModuleIdxFor? logical do
            throwError "unapproved compiler replacement: {declaration} implemented by {replacement}"
      checkAxioms declaration
    else if let some index := env.getModuleIdxFor? declaration then
      if auditedStochasticTestModules.contains env.header.moduleNames[index.toNat]! then
        stochasticTestCount := stochasticTestCount + 1
        checkAxioms declaration
      else if auditedKernelTestModules.contains env.header.moduleNames[index.toNat]! then
        exactTestCount := exactTestCount + 1
        checkAxioms declaration
  if productionCount = 0 || csimpCount = 0 then
    throwError "the import closure must contain FloatLib declarations and @[csimp] proofs"
  unless replacementCount = 1 do
    throwError "expected one FloatLib compiler replacement, found {replacementCount}"
  unless exactTestCount > 0 do
    throwError "the exact-kernel conformance declarations must be loaded"
  let some replacement := Lean.Compiler.getImplementedBy? env logical
    | throwError "the posit decoder has no compiler replacement"
  let some replacementProof := FloatLib.Numerics.Provenance.replacementProof? env logical
    | throwError "the posit decoder's replacement has no registered `@[replacement_proof]`"
  unless env.getModuleIdxFor? replacementProof == env.getModuleIdxFor? logical do
    throwError "the posit decoder's replacement proof is not in the decoder's module"
  checkAxioms replacementProof
  Lean.Elab.Command.liftTermElabM do
    Lean.withoutExporting do
      FloatLib.Numerics.Provenance.checkReplacementEquality logical replacement replacementProof
  for declaration in auditedTestDeclarations do
    checkAxioms declaration
  Lean.logInfo m!"Axiom audit passed: {productionCount} loaded production declarations \
    ({privateCount} private), {csimpCount} compiler equality proofs, \
    {auditedTestDeclarations.size} selected test declarations, \
    {stochasticTestCount} stochastic test declarations, {exactTestCount} kernel conformance test \
    declarations, one checked compiler replacement, and {ctorIdxCount} constructor-index tag reads \
    generated by Lean."
