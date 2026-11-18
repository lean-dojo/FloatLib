/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Classification.Runtime
public meta import FloatLib.Tactic.IeeeRecommendedKernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Comparison.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.KernelPath
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Recommended.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.TotalOrder.Runtime
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Classification
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Extrema
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.LogB
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Payload
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

* §9.7: `getPayload` rounds the payload bits of a NaN word as an integer, and gives the word of
  `-1` otherwise (`liftUnary_getPayload_eq`, with `KernelPath.getPayload_eq_spec`).

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
  FloatLib.Floats.ExecFloat.Binary.getPayload
