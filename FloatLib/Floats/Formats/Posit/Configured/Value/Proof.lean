/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Configured.Constants
public import FloatLib.Floats.Formats.Posit.Configured.Instances
public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof
public import FloatLib.Floats.Formats.Posit.Configured.Comparison

/-!
# Correctness of the configured posit value interface

The public constructors form a lossless equivalence with the exact-width model and every in-range
word. Exact decoding and classification preserve the standardized zero and NaR observations, and
the common Boolean comparison API agrees with the configured signed-word order.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
The common comparison capability reduces to signed-word posit comparison.

This theorem is the public semantic boundary for proofs: clients need not unfold the typeclass
instance or depend on its implementation name.
-/
@[simp, grind =] theorem compare_def
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compare left right =
      some (cmp (toModel left) (toModel right)) :=
  rfl

/-- Decoding immediately after packing a posit proof model returns the original model. -/
@[simp, grind =] theorem toModel_ofModel (value : Model format) :
    toModel (ofModel (plan := plan) (code := code) value) = value :=
  Configured.Family.toModel_ofModel value

/-- Packing immediately after decoding a configured posit returns the original value. -/
@[simp, grind =] theorem ofModel_toModel
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ofModel (toModel value) = value :=
  Configured.Family.ofModel_toModel value

/-- Reconstructing a configured posit from its complete word is lossless. -/
@[simp, grind =] theorem ofNatBits_toNatBits
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ofNatBits (toNatBits value) = value := by
  apply Configured.Family.toModel_injective
  simp [ofNatBits, toNatBits, toModel, ofModel]

/-- Reading an in-range complete posit word immediately after constructing it returns that word. -/
@[simp, grind =] theorem toNatBits_ofNatBits_of_lt
    (bits : Nat) (bits_lt : bits < format.modulus) :
    toNatBits (ofNatBits (plan := plan) (code := code) bits) = bits := by
  simp [ofNatBits, toNatBits, toModel, ofModel,
    Model.toNatBits_ofNatBits_of_lt bits bits_lt]

/-- The configured zero code denotes the ordinary rational value zero. -/
@[simp, grind =] theorem decode_zero :
    decode (zero (format := format) (plan := plan) (code := code)) =
      .finite 0 := by
  change
    Model.decode
        (Configured.Family.toModel
          (Configured.Family.ofModel (Model.zero format))) =
      .finite 0
  simp

/-- The configured NaR code denotes the common exceptional Not-a-Real observation. -/
@[simp, grind =] theorem decode_nar :
    decode (nar (format := format) (plan := plan) (code := code)) =
      .exceptional .notAReal := by
  change
    Model.decode
        (Configured.Family.toModel
          (Configured.Family.ofModel (Model.nar format))) =
      .exceptional .notAReal
  simp

/-- The configured zero code is recognized as zero. -/
@[simp, grind =] theorem isZero_zero :
    isZero (zero (format := format) (plan := plan) (code := code)) = true := by
  change
    Model.isZero
        (Configured.Family.toModel
          (Configured.Family.ofModel (Model.zero format))) =
      true
  simp

/-- The configured NaR code is recognized as Not-a-Real. -/
@[simp, grind =] theorem isNaR_nar :
    isNaR (nar (format := format) (plan := plan) (code := code)) = true := by
  change
    Model.isNaR
        (Configured.Family.toModel
          (Configured.Family.ofModel (Model.nar format))) =
      true
  simp

/-- The configured zero code is not Not-a-Real. -/
@[simp, grind =] theorem isNaR_zero :
    isNaR (zero (format := format) (plan := plan) (code := code)) = false := by
  change
    Model.isNaR
        (Configured.Family.toModel
          (Configured.Family.ofModel (Model.zero format))) =
      false
  simp

/-- The configured NaR code is not the ordinary zero code. -/
@[simp, grind =] theorem isZero_nar :
    isZero (nar (format := format) (plan := plan) (code := code)) = false := by
  change
    Model.isZero
        (Configured.Family.toModel
          (Configured.Family.ofModel (Model.nar format))) =
      false
  simp

/-- The public optional rational view is absent precisely for the unique NaR value. -/
@[simp, grind =] theorem toRat?_eq_none_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toRat? value = none ↔ isNaR value = true :=
  Model.toRat?_eq_none_iff (toModel value)

/-- Boolean posit equality agrees exactly with equality of configured values. -/
@[simp, grind =] theorem compareEqual_eq_true_iff
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compareEqual left right = true ↔ left = right := by
  simp [FloatLib.Floats.ExecFloat.compareEqual,
    compare_def, cmp_eq_eq_iff]
  constructor
  · exact Configured.Family.toModel_injective
  · intro equality
    cases equality
    rfl

/-- Boolean posit inequality agrees exactly with inequality of configured values. -/
@[simp, grind =] theorem compareNotEqual_eq_true_iff
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compareNotEqual left right = true ↔ left ≠ right := by
  simp only [FloatLib.Floats.ExecFloat.compareNotEqual, Bool.not_eq_true']
  rw [← Bool.not_eq_true]
  exact not_congr (compareEqual_eq_true_iff left right)

/-- Boolean posit less-than agrees with the standard signed-word order. -/
@[simp, grind =] theorem compareLess_eq_true_iff
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compareLess left right = true ↔ left < right := by
  change
    FloatLib.Floats.ExecFloat.compareLess left right = true ↔
      toModel left < toModel right
  simp [FloatLib.Floats.ExecFloat.compareLess, compare_def, cmp_eq_lt_iff]

/-- Boolean posit less-than-or-equal agrees with the standard signed-word order. -/
@[simp, grind =] theorem compareLessEqual_eq_true_iff
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compareLessEqual left right = true ↔ left ≤ right := by
  change
    FloatLib.Floats.ExecFloat.compareLessEqual left right = true ↔
      toModel left ≤ toModel right
  rw [FloatLib.Floats.ExecFloat.compareLessEqual, compare_def]
  cases comparison : cmp (toModel left) (toModel right) <;>
    simp_all [cmp_eq_lt_iff, cmp_eq_eq_iff, cmp_eq_gt_iff]
  exact le_of_lt comparison

/-- Boolean posit greater-than agrees with the standard signed-word order. -/
@[simp, grind =] theorem compareGreater_eq_true_iff
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compareGreater left right = true ↔ left > right := by
  change
    FloatLib.Floats.ExecFloat.compareGreater left right = true ↔
      toModel right < toModel left
  simp [FloatLib.Floats.ExecFloat.compareGreater, compare_def, cmp_eq_gt_iff]

/-- Boolean posit greater-than-or-equal agrees with the standard signed-word order. -/
@[simp, grind =] theorem compareGreaterEqual_eq_true_iff
    (left right : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    FloatLib.Floats.ExecFloat.compareGreaterEqual left right = true ↔ left ≥ right := by
  change
    FloatLib.Floats.ExecFloat.compareGreaterEqual left right = true ↔
      toModel right ≤ toModel left
  rw [FloatLib.Floats.ExecFloat.compareGreaterEqual, compare_def]
  cases comparison : cmp (toModel left) (toModel right) <;>
    simp_all [cmp_eq_lt_iff, cmp_eq_eq_iff, cmp_eq_gt_iff]
  exact le_of_lt comparison

end ExecFloat.Posit
end FloatLib.Floats
