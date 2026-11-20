/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Algebraic.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Classification.Runtime
public meta import FloatLib.Tactic.IeeeRecommendedKernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Adjacent
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Augmented
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.FormatOf
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.LogB
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Payload
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Power
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Reduction
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Remainder
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Root
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.ScaledProduct
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.TotalOrder.Magnitude

/-!
# Kernel rules for the named operations of IEEE 754-2019 on configured binary values

`Configured.KernelPath` gives `float_decide` the arithmetic of configured values on encodings.
This module does the same for operations that IEEE 754-2019 names and that had no rule, for
every format descriptor and storage plan:

* §5.11, the 22 comparisons: `compareQuiet_eq` and `compareSignaling_eq` state the two families
  as the predicate at the comparison code of the two encodings, with the `invalid` flag computed
  on the encodings (`KernelPath.Predicates`). The members `compareQuietEqual` to
  `compareSignalingGreaterUnordered` are unfolded to their family.
* §5.3.1 and §5.4.1: the members `roundToIntegralTiesToEven` to `roundToIntegralTowardNegative`,
  `roundToIntegralExact` and `convertToIntegerTiesToEven` to `convertToIntegerTowardNegative` are
  unfolded to `roundToIntegral` and `toInt?`, which `Configured.KernelPath` rewrites.

* §5.5.1 and §9.6: `abs`, `copySign` and the eight minimum and maximum operations (`minimum`
  to `maximumMagnitudeNumber`) are the selections of `KernelPath.Extrema` between the two
  encodings (`liftUnary_abs_eq`, `liftBinary_copySign_eq`, `liftBinary_minimum_eq` and its
  siblings), and with `status := true` the same value with the `invalid` flag of a signaling
  NaN computed on the encodings (`minimum_outcome_eq` and its siblings).

* §5.7.2: `class`, `isNormal`, `isSubnormal` and `isSignaling` read the fields of the encoding
  (`classify_eq`, `isNormal_eq`, `isSubnormal_eq`, `isSignaling_eq`, with the codes of
  `KernelPath.Classification`).

* §5.10: `totalOrderMag` is the total order of the two encodings with their sign bits cleared
  in every format that has signed zeros, and the model operation in the others
  (`totalOrderMag_eq`).

* §5.3.3: `scale` (`scaleB`) reads the significand and the exponent field off the encoding and
  rounds once at the moved exponent, in every rounding direction (`liftUnary_scale_eq`, with
  `KernelPath.scale_eq_spec`), and `logB` rounds the exponent of the leading bit, a difference
  of two natural numbers read off the encoding (`liftUnary_logB_eq`, with
  `KernelPath.logB_eq_spec`).

* §5.4.1: the values of `Model.formatOfAddition`, `formatOfSubtraction`,
  `formatOfMultiplication`, `formatOfDivision` and `formatOfFusedMultiplyAdd` on decoded
  configured values of any formats, stored in a configured format, are computed on the
  encodings (`formatOfAddition_eq` to `formatOfFusedMultiplyAdd_eq`, with
  `KernelPath.formatOfAddition_eq_spec` and its siblings): finite operands are decoded, the
  exact result is formed and rounded once into the destination.

* §5.3.1: `remainder` decodes two finite encodings with a nonzero divisor, forms the exact
  remainder and encodes it (`liftBinary_remainder_eq`, with `KernelPath.remainder_eq_spec`),
  and with `status := true` the same value with the `invalid` flag computed on the encodings
  (`remainder_outcome_eq`, with `KernelPath.remainder_status_eq`).

* §5.3.1: `nextUp` and `nextDown` step the encoding by one, with the cases of a NaN, an
  infinity, a zero and the ends of the range read off the encoding (`liftUnary_nextUp_eq`,
  `liftUnary_nextDown_eq`, with `KernelPath.nextUp_eq_spec` and `KernelPath.nextDown_eq_spec`),
  and with `status := true` the same value with the `invalid` flag of a signaling NaN
  (`nextUp_outcome_eq`, `nextDown_outcome_eq`). `copy` is unfolded to its operand.

* §9.4: `sum`, `dot`, `sumAbs` and `sumSquare` run the state machine of the reference on the
  list of the encodings: a finite encoding is pushed as its exact value, and the exact sum is
  rounded once (`sum_eq`, `dot_eq`, `sumAbs_eq`, `sumSquare_eq`, with
  `KernelPath.sum_eq_spec` and its siblings). `scaledProd`, `scaledProdSum` and
  `scaledProdDiff` fold the exact factors of the encodings and round the scaled product once
  (`scaledProd_eq`, `scaledProdSum_eq`, `scaledProdDiff_eq`, with
  `KernelPath.scaledProd_eq_spec` and `KernelPath.scaledProdOfSums_eq_spec`).

* §9.5: `augmentedAddition`, `augmentedSubtraction` and `augmentedMultiplication` decode two
  finite encodings, round the exact sum or product to nearest with ties toward zero on the
  grid of the format, and encode the head and the tail (`augmentedAddition_eq` and its
  siblings, with `KernelPath.augmentedAddition_eq_spec` and its siblings).

* §9.7: `getPayload` rounds the payload bits of a NaN word as an integer, and gives the word of
  `-1` otherwise (`liftUnary_getPayload_eq`, with `KernelPath.getPayload_eq_spec`).
  `setPayload` and `setPayloadSignaling` test on the encoding whether the operand names a
  payload and build the word of the NaN (`liftUnary_setPayload_eq`,
  `liftUnary_setPayloadSignaling_eq`, with `KernelPath.setPayload_eq_spec` and
  `KernelPath.setPayloadSignaling_eq_spec`).

* §9.2: `pown` decodes a finite nonzero encoding and rounds the quotient of the power of its
  significand and a power of two, or the reciprocal of that quotient for a negative exponent
  (`liftUnary_pown_eq`, with `KernelPath.pown_eq_spec`). `rootn` and `rSqrt` decode a finite
  nonzero encoding, take the checked integer root of its reduced fraction two bits below the
  rounding position, and round once (`liftUnary_rootn_eq`, `liftUnary_rSqrt_eq`, with
  `KernelPath.rootn_eq_spec` and `KernelPath.rSqrt_eq_spec`). `hypot` decodes two finite
  encodings, forms the exact sum of their squares and rounds its checked integer square root
  once (`liftBinary_hypot_eq`, with `KernelPath.hypot_eq_spec`).

Each rule is an equation between the operation as it is defined and a term on the encodings,
proved for all operands, so a statement checked through it is a statement about the operation.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath

variable {format : FloatFormat}

/-! ## Comparisons (IEEE 754-2019 §5.11) -/

/--
A quiet comparison of configured values is the predicate at the comparison code of the two
encodings, with `invalid` exactly when an encoding is a signaling NaN.
-/
@[kernel_optimize] theorem compareQuiet_eq {plan : StoragePlan format}
    (predicate : Numerics.IEEEComparison.Predicate)
    (x y : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.compareQuiet predicate x y =
      { value := acceptsCode predicate (KernelPath.Flat.compare format (toNat x) (toNat y))
        status :=
          { invalid := Nat.beq (signalingCode format (toNat x)) 1 ||
              Nat.beq (signalingCode format (toNat y)) 1 } } := by
  rw [← KernelPath.Value.compareQuiet_eq_lift, ← toModel_eq_natView, ← toModel_eq_natView]
  rfl

/--
A signaling comparison of configured values is the predicate at the comparison code of the two
encodings, with `invalid` exactly when an encoding is a NaN.
-/
@[kernel_optimize] theorem compareSignaling_eq {plan : StoragePlan format}
    (predicate : Numerics.IEEEComparison.Predicate)
    (x y : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.compareSignaling predicate x y =
      { value := acceptsCode predicate (KernelPath.Flat.compare format (toNat x) (toNat y))
        status :=
          { invalid := Nat.beq (nanCode format (toNat x)) 1 ||
              Nat.beq (nanCode format (toNat y)) 1 } } := by
  rw [← KernelPath.Value.compareSignaling_eq_lift, ← toModel_eq_natView, ← toModel_eq_natView]
  rfl

/-! ## Classification (§5.7.2) -/


/-- `isSignaling` of a configured value is a test on its encoding. -/
code_rule isSignaling := Nat.beq (signalingCode format (toNat x)) 1, signalingCode_eq

/-- `isNormal` of a configured value: its encoding is finite with a nonzero exponent field. -/
code_rule isNormal :=
  (Nat.beq (finiteCode format (toNat x)) 1 && !Nat.beq (expCode format (toNat x)) 0),
  normalCode_eq

/--
`isSubnormal` of a configured value: its encoding has a zero exponent field and a nonzero
fraction field.
-/
code_rule isSubnormal :=
  (Nat.beq (expCode format (toNat x)) 0 && !Nat.beq (fracCode format (toNat x)) 0),
  subnormalCode_eq

/-- IEEE 754-2019 §5.7.2 `class` of a configured value is the class of its encoding. -/
code_rule classify := classOf format (toNat x), classOf_eq

/-! ## `scaleB` and `logB` (§5.3.3) -/

/--
`scaleB` of a configured value, as the configured operation runs it through the model, is the
kernel `scaleB` on its encoding, for every rounding direction and every integer `n`.
-/
@[kernel_optimize] theorem liftUnary_scale_eq {plan : StoragePlan format} (n : Int)
    (mode : Model.IEEERoundingMode)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.scale x n mode) value = KernelPath.Value.scale mode n value := by
  rw [liftUnary_eq_natView, KernelPath.Value.scale_eq_lift]

/--
`logB` of a configured value, as the configured operation runs it through the model, is the
kernel `logB` on its encoding.
-/
@[kernel_optimize] theorem liftUnary_logB_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.logB x) value = KernelPath.Value.logB value := by
  rw [liftUnary_eq_natView, KernelPath.Value.logB_eq_lift]

/-! ## The formatOf operations (§5.4.1) -/

format_of_rule formatOfAddition := KernelPath.formatOfAddition_eq_spec

format_of_rule formatOfSubtraction := KernelPath.formatOfSubtraction_eq_spec

format_of_rule formatOfMultiplication := KernelPath.formatOfMultiplication_eq_spec

format_of_rule formatOfDivision := KernelPath.formatOfDivision_eq_spec

/--
The value of `Model.formatOfFusedMultiplyAdd` on three decoded configured values of any
formats, stored in a configured format, is the kernel operation on the three encodings, in
every rounding direction.
-/
@[kernel_optimize] theorem formatOfFusedMultiplyAdd_eq {left right addend : FloatFormat}
    {leftPlan : StoragePlan left} {rightPlan : StoragePlan right}
    {addendPlan : StoragePlan addend} {plan : StoragePlan format}
    (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat (Family left (Code leftPlan) leftPlan))
    (y : FloatLib.Floats.ExecFloat (Family right (Code rightPlan) rightPlan))
    (z : FloatLib.Floats.ExecFloat (Family addend (Code addendPlan) addendPlan)) :
    (FloatLib.Floats.ExecFloat.Binary.ofModel
        (Model.formatOfFusedMultiplyAdd format (FloatLib.Floats.ExecFloat.Binary.toModel x)
          (FloatLib.Floats.ExecFloat.Binary.toModel y)
          (FloatLib.Floats.ExecFloat.Binary.toModel z) mode).value :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.Value.ternaryInto
        (KernelPath.formatOfFusedMultiplyAdd left right addend format mode)
        (fun x y z => (Model.formatOfFusedMultiplyAdd format x y z mode).value)
        (KernelPath.formatOfFusedMultiplyAdd_eq_spec mode) x y z := by
  rw [KernelPath.Value.ternaryInto_eq, ofModel_eq_natView, toModel_eq_natView,
    toModel_eq_natView, toModel_eq_natView]

/-! ## `remainder` (§5.3.1) -/

selection_rule remainder := (fun x y => Model.remainder x y)

/--
The outcome of `remainder` of two configured values with `status := true`: the kernel remainder
of the two encodings, with `invalid` computed on the encodings (a signaling NaN, an infinite
dividend or a zero divisor) and the ternary value of an exact operation.
-/
@[kernel_optimize] theorem remainder_outcome_eq {plan : StoragePlan format}
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
        (Model.remainder (FloatLib.Floats.ExecFloat.Binary.toModel left)
          (FloatLib.Floats.ExecFloat.Binary.toModel right) (status := true)) =
      { value := KernelPath.Value.remainder left right
        status := { invalid := KernelPath.remainderInvalid format (toNat left) (toNat right) }
        ternary := .eq } := by
  change FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
    (Model.Internal.Status.remainder (FloatLib.Floats.ExecFloat.Binary.toModel left)
      (FloatLib.Floats.ExecFloat.Binary.toModel right)) = _
  rw [KernelPath.remainder_status_eq, KernelPath.Value.remainder_eq_lift]
  unfold FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel Model.outcomeWithInvalid
  rw [ofModel_eq_natView, toModel_eq_natView, toModel_eq_natView, ← KernelPath.toNat_eq,
    ← KernelPath.toNat_eq]
  generalize KernelPath.remainderInvalid format (toNat left) (toNat right) = invalid
  cases invalid <;> rfl

/-! ## `nextUp` and `nextDown` (§5.3.1) -/

/--
A model operation of one operand with the `invalid` signal of a signaling NaN, stored in a
configured format: the codec lift of the operation, with the flag computed on the encoding and
the ternary value of an exact operation.
-/
theorem ofModel_unaryWithInvalid {plan : StoragePlan format}
    (spec : Model format → Model format)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
        (Model.outcomeWithInvalid (spec (FloatLib.Floats.ExecFloat.Binary.toModel value))
          (Model.isSignaling (FloatLib.Floats.ExecFloat.Binary.toModel value))) =
      { value := NatView.liftUnary spec value
        status := { invalid := Nat.beq (signalingCode format (toNat value)) 1 }
        ternary := .eq } := by
  unfold FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel Model.outcomeWithInvalid
  rw [ofModel_eq_natView, toModel_eq_natView, ← signalingCode_eq, ← KernelPath.toNat_eq]
  generalize Nat.beq (signalingCode format (toNat value)) 1 = invalid
  cases invalid <;> rfl

/--
`nextUp` of a configured value, as the configured operation runs it through the model, is the
kernel `nextUp` on its encoding.
-/
lift_rule nextUp := (fun x => Model.nextUp x),
  KernelPath.Value.nextUp_eq_lift

/--
`nextDown` of a configured value, as the configured operation runs it through the model, is
the kernel `nextDown` on its encoding.
-/
lift_rule nextDown := (fun x => Model.nextDown x),
  KernelPath.Value.nextDown_eq_lift

quiet_rule nextUp := Model.nextUp, KernelPath.Value.nextUp_eq_lift

quiet_rule nextDown := Model.nextDown, KernelPath.Value.nextDown_eq_lift

/-! ## `getPayload` (§9.7) -/

/--
`getPayload` of a configured value, as the configured operation runs it through the model, is
the kernel `getPayload` on its encoding.
-/
@[kernel_optimize] theorem liftUnary_getPayload_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.getPayload x) value = KernelPath.Value.getPayload value := by
  rw [liftUnary_eq_natView, KernelPath.Value.getPayload_eq_lift]

/--
`setPayload` of a configured value, as the configured operation runs it through the model, is
the kernel `setPayload` on its encoding.
-/
lift_rule setPayload := (fun x => Model.setPayload x),
  KernelPath.Value.setPayload_eq_lift

/--
`setPayloadSignaling` of a configured value, as the configured operation runs it through the
model, is the kernel `setPayloadSignaling` on its encoding.
-/
lift_rule setPayloadSignaling := (fun x => Model.setPayloadSignaling x),
  KernelPath.Value.setPayloadSignaling_eq_lift

/-! ## `pown` (§9.2) -/

/--
`pown` of a configured value, as the configured operation runs it through the model, is the
kernel `pown` on its encoding, for every integer exponent.
-/
@[kernel_optimize] theorem liftUnary_pown_eq {plan : StoragePlan format} (n : Int)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.pown x n) value = KernelPath.Value.pown n value := by
  rw [liftUnary_eq_natView, KernelPath.Value.pown_eq_lift]

/-! ## `rootn`, `rSqrt` and `hypot` (§9.2) -/

selection_rule hypot := Model.hypot

/--
`rootn` of a configured value, as the configured operation runs it through the model, is the
kernel `rootn` on its encoding, for every integer degree.
-/
@[kernel_optimize] theorem liftUnary_rootn_eq {plan : StoragePlan format} (n : Int)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        (fun x => Model.rootn x n) value = KernelPath.Value.rootn n value := by
  rw [liftUnary_eq_natView, KernelPath.Value.rootn_eq_lift]

/--
`rSqrt` of a configured value, as the configured operation runs it through the model, is the
kernel `rSqrt` on its encoding.
-/
lift_rule rSqrt := (fun x => Model.rSqrt x),
  KernelPath.Value.rSqrt_eq_lift

/-! ## Augmented arithmetic (§9.5) -/

augmented_rule augmentedAddition := KernelPath.augmentedAddition_eq_spec

augmented_rule augmentedSubtraction := KernelPath.augmentedSubtraction_eq_spec

augmented_rule augmentedMultiplication := KernelPath.augmentedMultiplication_eq_spec

/-! ## Reductions (§9.4) -/

/-- The encodings of configured values are the encodings of the decoded values. -/
theorem map_toNat_eq {plan : StoragePlan format}
    (values : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan))) :
    values.toList.map toNat =
      (values.map FloatLib.Floats.ExecFloat.Binary.toModel).toList.map Model.toNatBits := by
  rw [Array.toList_map, List.map_map]
  refine List.map_congr_left fun x _ => ?_
  rw [KernelPath.toNat_eq, ← toModel_eq_natView]
  rfl

/--
The exact sum of configured values is the kernel reduction on the list of their encodings, in
every rounding direction.
-/
@[kernel_optimize] theorem sum_eq {plan : StoragePlan format}
    (values : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.Binary.sum values mode :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.ofNat (KernelPath.sum format format mode (values.toList.map toNat)) := by
  rw [map_toNat_eq, KernelPath.sum_eq_spec, ← ofModel_eq_ofNat]
  rfl

/--
The exact sum of the magnitudes of configured values is the kernel reduction on the list of
their encodings, in every rounding direction.
-/
@[kernel_optimize] theorem sumAbs_eq {plan : StoragePlan format}
    (values : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.Binary.sumAbs values mode :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.ofNat (KernelPath.sumAbs format format mode (values.toList.map toNat)) := by
  rw [map_toNat_eq, KernelPath.sumAbs_eq_spec, ← ofModel_eq_ofNat]
  rfl

/--
The exact sum of the squares of configured values is the kernel reduction on the list of their
encodings, in every rounding direction.
-/
@[kernel_optimize] theorem sumSquare_eq {plan : StoragePlan format}
    (values : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.Binary.sumSquare values mode :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.ofNat (KernelPath.sumSquare format format mode (values.toList.map toNat)) := by
  rw [map_toNat_eq, KernelPath.sumSquare_eq_spec, ← ofModel_eq_ofNat]
  rfl

/--
The exact dot product of configured values is the kernel reduction on the two lists of their
encodings, with the same length check, in every rounding direction.
-/
@[kernel_optimize] theorem dot_eq {plan : StoragePlan format}
    (left right : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.Binary.dot left right mode :
        Except Numerics.ReductionError
          (FloatLib.Floats.ExecFloat (Family format (Code plan) plan))) =
      (KernelPath.dot format format format mode (left.toList.map toNat)
        (right.toList.map toNat)).map KernelPath.ofNat := by
  rw [map_toNat_eq, map_toNat_eq, KernelPath.dot_eq_spec]
  change (Model.dot format (left.map FloatLib.Floats.ExecFloat.Binary.toModel)
    (right.map FloatLib.Floats.ExecFloat.Binary.toModel) mode).map
      FloatLib.Floats.ExecFloat.Binary.ofModel = _
  cases Model.dot format (left.map FloatLib.Floats.ExecFloat.Binary.toModel)
      (right.map FloatLib.Floats.ExecFloat.Binary.toModel) mode with
  | error reason => rfl
  | ok value => exact congrArg Except.ok (ofModel_eq_ofNat value)

/--
The scaled product of configured values is the kernel reduction on the list of their
encodings, with the product stored from its encoding, in every rounding direction.
-/
@[kernel_optimize] theorem scaledProd_eq {plan : StoragePlan format}
    (values : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.scaledProd values mode =
      (KernelPath.scaledProd format format mode (values.toList.map toNat)).map
        KernelPath.ofNat := by
  rw [map_toNat_eq, KernelPath.scaledProd_eq_spec]
  unfold FloatLib.Floats.ExecFloat.Binary.scaledProd ScaledProduct.map
  simp only [ofModel_eq_ofNat]

/--
The scaled product of the sums or differences of configured values, as the model defines it
for the two reductions, is the kernel reduction on the two lists of their encodings.
-/
theorem scaledProdOfSums_eq {plan : StoragePlan format} (subtract : Bool)
    (left right : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    (Model.Reduction.Internal.scaledProdOfSums format
        (left.map FloatLib.Floats.ExecFloat.Binary.toModel)
        (right.map FloatLib.Floats.ExecFloat.Binary.toModel) subtract mode).map
        (ScaledProduct.map (FloatLib.Floats.ExecFloat.Binary.ofModel :
          Model format → FloatLib.Floats.ExecFloat (Family format (Code plan) plan))) =
      (KernelPath.scaledProdOfSums format format format subtract mode (left.toList.map toNat)
        (right.toList.map toNat)).map (ScaledProduct.map KernelPath.ofNat) := by
  rw [map_toNat_eq, map_toNat_eq, KernelPath.scaledProdOfSums_eq_spec]
  cases Model.Reduction.Internal.scaledProdOfSums format
      (left.map FloatLib.Floats.ExecFloat.Binary.toModel)
      (right.map FloatLib.Floats.ExecFloat.Binary.toModel) subtract mode with
  | error reason => rfl
  | ok value =>
      refine congrArg Except.ok ?_
      unfold ScaledProduct.map
      simp only [ofModel_eq_ofNat]

/--
The scaled product of the sums of configured values is the kernel reduction on the two lists
of their encodings, with the same length check, in every rounding direction.
-/
@[kernel_optimize] theorem scaledProdSum_eq {plan : StoragePlan format}
    (left right : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.scaledProdSum left right mode =
      (KernelPath.scaledProdOfSums format format format false mode (left.toList.map toNat)
        (right.toList.map toNat)).map (ScaledProduct.map KernelPath.ofNat) :=
  scaledProdOfSums_eq false left right mode

/--
The scaled product of the differences of configured values is the kernel reduction on the two
lists of their encodings, with the same length check, in every rounding direction.
-/
@[kernel_optimize] theorem scaledProdDiff_eq {plan : StoragePlan format}
    (left right : Array (FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))
    (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.scaledProdDiff left right mode =
      (KernelPath.scaledProdOfSums format format format true mode (left.toList.map toNat)
        (right.toList.map toNat)).map (ScaledProduct.map KernelPath.ofNat) :=
  scaledProdOfSums_eq true left right mode

/-! ## The total order of magnitudes (§5.10) -/

/--
IEEE 754-2019 §5.10 `totalOrderMag` of configured values, for every format descriptor and
storage plan: in a format with signed zeros it is the total order of the two encodings with
their sign bits cleared, and in a format without signed zeros it is the model operation.
-/
@[kernel_optimize] theorem totalOrderMag_eq {plan : StoragePlan format}
    (x y : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.totalOrderMag x y =
      Bool.casesOn (motive := fun _ => Bool) format.supportsSignedZero
        (Model.totalOrderMag (FloatLib.Floats.ExecFloat.Binary.toModel x)
          (FloatLib.Floats.ExecFloat.Binary.toModel y))
        (Nat.beq (KernelPath.Flat.totalOrder format (KernelPath.abs format (toNat x))
          (KernelPath.abs format (toNat y))) 1) := by
  cases hformat : format.supportsSignedZero
  · rfl
  · change Model.totalOrderMag (FloatLib.Floats.ExecFloat.Binary.toModel x)
      (FloatLib.Floats.ExecFloat.Binary.toModel y) = _
    rw [Model.totalOrderMag_eq_totalOrder_abs _ _ hformat, KernelPath.toNat_eq,
      KernelPath.toNat_eq, abs_eq_spec, abs_eq_spec, KernelPath.Flat.totalOrder_eq,
      totalOrderCode_eq, ← toModel_eq_natView, ← toModel_eq_natView]

/-! ## Sign operations (§5.5.1) and minimum and maximum (§9.6) -/

/-- The absolute value of a configured value is the kernel absolute value on its encoding. -/
@[kernel_optimize] theorem liftUnary_abs_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        Model.abs value = KernelPath.Value.abs value := by
  rw [liftUnary_eq_natView, KernelPath.Value.abs_eq_lift]


selection_rule copySign := Model.copySign

selection_rule minimum := (fun x y => Model.minimum x y)

selection_rule maximum := (fun x y => Model.maximum x y)

selection_rule minimumNumber := (fun x y => Model.minimumNumber x y)

selection_rule maximumNumber := (fun x y => Model.maximumNumber x y)

selection_rule minimumMagnitude :=
  (fun x y => Model.magnitudeExtremum false (fun x y => Model.minimum x y) x y)

selection_rule maximumMagnitude :=
  (fun x y => Model.magnitudeExtremum true (fun x y => Model.maximum x y) x y)

selection_rule minimumMagnitudeNumber :=
  (fun x y => Model.magnitudeExtremum false (fun x y => Model.minimumNumber x y) x y)

selection_rule maximumMagnitudeNumber :=
  (fun x y => Model.magnitudeExtremum true (fun x y => Model.maximumNumber x y) x y)

/--
A model selection with the `invalid` signal of a signaling NaN operand, stored in a configured
format: the codec lift of the selection, with the flag computed on the two encodings and the
ternary value of an exact operation.
-/
theorem ofModel_outcomeWithInvalid {plan : StoragePlan format}
    (spec : Model format → Model format → Model format)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
        (Model.outcomeWithInvalid
          (spec (FloatLib.Floats.ExecFloat.Binary.toModel left)
            (FloatLib.Floats.ExecFloat.Binary.toModel right))
          (Model.isSignaling (FloatLib.Floats.ExecFloat.Binary.toModel left) ||
            Model.isSignaling (FloatLib.Floats.ExecFloat.Binary.toModel right))) =
      { value := NatView.liftBinary spec left right
        status :=
          { invalid := Nat.beq (signalingCode format (toNat left)) 1 ||
              Nat.beq (signalingCode format (toNat right)) 1 }
        ternary := .eq } := by
  unfold FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel Model.outcomeWithInvalid
  rw [ofModel_eq_natView, toModel_eq_natView, toModel_eq_natView, ← signalingCode_eq,
    ← signalingCode_eq, ← KernelPath.toNat_eq, ← KernelPath.toNat_eq]
  generalize (Nat.beq (signalingCode format (toNat left)) 1 ||
    Nat.beq (signalingCode format (toNat right)) 1) = invalid
  cases invalid <;> rfl


signaling_rule minimum := Model.minimum

signaling_rule maximum := Model.maximum

signaling_rule minimumNumber := Model.minimumNumber

signaling_rule maximumNumber := Model.maximumNumber

signaling_rule minimumMagnitude := Model.magnitudeExtremum false (fun x y => Model.minimum x y)

signaling_rule maximumMagnitude := Model.magnitudeExtremum true (fun x y => Model.maximum x y)

signaling_rule minimumMagnitudeNumber :=
  Model.magnitudeExtremum false (fun x y => Model.minimumNumber x y)

signaling_rule maximumMagnitudeNumber :=
  Model.magnitudeExtremum true (fun x y => Model.maximumNumber x y)

end FloatLib.Floats.Formats.BinaryInterchange.Configured

/-
The members under the names of the standard are their family at one predicate or direction:
`float_decide` unfolds them, and the rules of the family apply.
-/
ieee_tag_members [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.compareQuiet
  by predicate

ieee_tag_members [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.compareSignaling
  by predicate without unordered ordered

ieee_tag_members [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.roundToIntegral
  by direction

ieee_tag_members [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.convertToInteger
  by direction

attribute [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.roundToIntegralExact

/-
The minimum and maximum operations and the sign operations are selectors over `status` or
wrappers of one codec lift: `float_decide` unfolds them to reach the rules above.
-/
ieee_tag_members [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary by extremum

attribute [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.magnitudeExtremum
  FloatLib.Floats.ExecFloat.Binary.abs FloatLib.Floats.ExecFloat.Binary.copySign
  FloatLib.Floats.ExecFloat.Binary.scale FloatLib.Floats.ExecFloat.Binary.logB
  FloatLib.Floats.ExecFloat.Binary.getPayload FloatLib.Floats.ExecFloat.Binary.setPayload
  FloatLib.Floats.ExecFloat.Binary.setPayloadSignaling FloatLib.Floats.ExecFloat.Binary.nextUp
  FloatLib.Floats.ExecFloat.Binary.nextDown FloatLib.Floats.ExecFloat.Binary.copy
  FloatLib.Floats.ExecFloat.Binary.remainder FloatLib.Floats.ExecFloat.Binary.pown
  FloatLib.Floats.ExecFloat.Binary.rootn FloatLib.Floats.ExecFloat.Binary.rSqrt
  FloatLib.Floats.ExecFloat.Binary.hypot
