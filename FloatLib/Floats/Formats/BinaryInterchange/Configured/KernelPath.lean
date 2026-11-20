/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Value -- shake: keep
public import FloatLib.Tactic.DirectionRule
public import FloatLib.Tactic.OutcomeRule

/-!
# Kernel view of configured binary values

`ExecFloat.Binary` values store their encoding in a machine word, two words, or the exact-width
model. `Code.natView plan` reads that encoding as a natural number and stores one back, with
primitive projections and constructors for the byte, word, two-word and exact-width plans. The
limb plan goes through its model conversions.

The instance `natView` makes the kernel operations of `KernelPath.Value` and their rewrite
theorems available for every configured binary type, whatever its descriptor and storage plan.
`liftBinary_add_eq` and its siblings rewrite the mode-taking operations `ExecFloat.Binary.add`,
`sub`, `mul`, `fma`, `div` and `sqrt` in a direction other than nearest-even to the kernel
operations.

`add_outcome_eq` and its siblings rewrite an operation with `status := true` to the kernel value
with the flags and the ternary value decoded from one status number. `add_outcome_eq_with` and
its siblings, `ofRat_outcome_eq_with` and `cast_status_eq_with` take that status number at the
encoding of the kernel value, so that a statement about the value and the flags of one operation
contains the value once. They declare a kernel cost, so `float_decide` rewrites with them.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Configured

open FloatLib.Floats.ExecFloat.KernelPath
open FloatLib.Floats.Formats.BinaryInterchange.KernelPath (NatView)

variable {format : FloatFormat}

namespace Code

/-- A bound on the encoding that follows from a bound on the width. -/
theorem lt_of_width_le {n width : Nat} (hn : n < 2 ^ format.bitWidth)
    (hwidth : format.bitWidth ≤ width) : n < 2 ^ width :=
  Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) hwidth)

/-- The high word of an encoding of at most 128 bits fits a native word. -/
theorem shiftRight_lt_of_width_le {n : Nat} (hn : n < 2 ^ format.bitWidth)
    (hwidth : format.bitWidth ≤ 128) : Nat.shiftRight n 64 < 2 ^ 64 := by
  have h : n < 2 ^ 64 * 2 ^ 64 := lt_of_width_le hn hwidth
  change n >>> 64 < 2 ^ 64
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul h

/-- A natural number is its low 64 bits plus its remaining bits shifted back. -/
theorem mod_add_shiftRight_mul (n : Nat) :
    Nat.add (Nat.mod n (Nat.pow 2 64)) (Nat.mul (Nat.shiftRight n 64) (Nat.pow 2 64)) = n := by
  change n % 2 ^ 64 + (n >>> 64) * 2 ^ 64 = n
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  exact Nat.mod_add_div n (2 ^ 64)

/-- The two limbs that `natView` stores for the two-word plan have the value they came from. -/
theorem toNat_limbs (n : Nat) (hhi : Nat.shiftRight n 64 < 2 ^ 64)
    (hlo : Nat.mod n (Nat.pow 2 64) < 2 ^ 64) :
    FloatLib.Numerics.FixedWord.UInt128.toNat
      ⟨⟨⟨⟨Nat.shiftRight n 64, hhi⟩⟩⟩, ⟨⟨⟨Nat.mod n (Nat.pow 2 64), hlo⟩⟩⟩⟩ = n := by
  rw [FloatLib.Numerics.FixedWord.UInt128.toNat]
  exact mod_add_shiftRight_mul n

/-- The model conversions read back an encoding in range. -/
theorem toNatBits_toModel_ofModel {plan : StoragePlan format} {n : Nat}
    (hn : n < 2 ^ format.bitWidth) :
    (toModel (ofModel (plan := plan) (Model.ofNatBits n))).toNatBits = n := by
  rw [toModel_ofModel]
  exact Model.toNatBits_ofNatBits_of_lt n hn

/-- The natural-number view of each storage plan. -/
@[instance_reducible]
def natView : (plan : StoragePlan format) → NatView (Family format (Code plan) plan) format
  | .byte h =>
      { toNat := fun (c : Code (.byte h)) =>
          kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0) 0
        ofNat := fun n hn => (⟨⟨⟨⟨n, lt_of_width_le hn h⟩⟩⟩, hn⟩ : Code (.byte h))
        toModel := toModel (plan := .byte h)
        ofModel := ofModel (plan := .byte h)
        toNat_eq := fun c => (Model.toNatBits_ofNatBits_of_lt _ c.2).symm
        toNat_ofNat := fun _ _ => rfl
        ofModel_toModel := ofModel_toModel (plan := .byte h) }
  | .word16 h =>
      { toNat := fun (c : Code (.word16 h)) =>
          kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0) 0
        ofNat := fun n hn => (⟨⟨⟨⟨n, lt_of_width_le hn h⟩⟩⟩, hn⟩ : Code (.word16 h))
        toModel := toModel (plan := .word16 h)
        ofModel := ofModel (plan := .word16 h)
        toNat_eq := fun _ => rfl
        toNat_ofNat := fun _ _ => rfl
        ofModel_toModel := ofModel_toModel (plan := .word16 h) }
  | .word32 h =>
      { toNat := fun (c : Code (.word32 h)) =>
          kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0) 0
        ofNat := fun n hn => (⟨⟨⟨⟨n, lt_of_width_le hn h⟩⟩⟩, hn⟩ : Code (.word32 h))
        toModel := toModel (plan := .word32 h)
        ofModel := ofModel (plan := .word32 h)
        toNat_eq := fun _ => rfl
        toNat_ofNat := fun _ _ => rfl
        ofModel_toModel := ofModel_toModel (plan := .word32 h) }
  | .word64 h =>
      { toNat := fun (c : Code (.word64 h)) =>
          kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0) 0
        ofNat := fun n hn => (⟨⟨⟨⟨n, lt_of_width_le hn h⟩⟩⟩, hn⟩ : Code (.word64 h))
        toModel := toModel (plan := .word64 h)
        ofModel := ofModel (plan := .word64 h)
        toNat_eq := fun _ => rfl
        toNat_ofNat := fun _ _ => rfl
        ofModel_toModel := ofModel_toModel (plan := .word64 h) }
  | .pair hgt hle =>
      { toNat := fun (c : Code (.pair hgt hle)) =>
          Nat.add
            (kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 1) 0) 0) 0)
            (Nat.mul
              (kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0) 0) 0)
              (Nat.pow 2 64))
        ofNat := fun n hn =>
          (⟨⟨⟨⟨⟨Nat.shiftRight n 64, shiftRight_lt_of_width_le hn hle⟩⟩⟩,
              ⟨⟨⟨Nat.mod n (Nat.pow 2 64), Nat.mod_lt n (Nat.two_pow_pos 64)⟩⟩⟩⟩,
            by rw [toNat_limbs]; exact hn⟩ : Code (.pair hgt hle))
        toModel := toModel (plan := .pair hgt hle)
        ofModel := ofModel (plan := .pair hgt hle)
        toNat_eq := fun c => by
          change _ = FloatLib.Numerics.FixedWord.UInt128.toNat c.1
          rw [FloatLib.Numerics.FixedWord.UInt128.toNat]
          rfl
        toNat_ofNat := fun n _ => mod_add_shiftRight_mul n
        ofModel_toModel := ofModel_toModel (plan := .pair hgt hle) }
  | .wide =>
      { toNat := fun (c : Code (format := format) .wide) =>
          kernel_proj% (kernel_proj% (kernel_proj% c 0) 0) 0
        ofNat := fun n hn => (⟨⟨⟨n, hn⟩⟩⟩ : Code (format := format) .wide)
        toModel := toModel (plan := .wide)
        ofModel := ofModel (plan := .wide)
        toNat_eq := fun _ => rfl
        toNat_ofNat := fun _ _ => rfl
        ofModel_toModel := ofModel_toModel (plan := .wide) }
  | .limbs h =>
      { toNat := fun c => (toModel (plan := .limbs h) c).toNatBits
        ofNat := fun n _ => ofModel (plan := .limbs h) (Model.ofNatBits n)
        toModel := toModel (plan := .limbs h)
        ofModel := ofModel (plan := .limbs h)
        toNat_eq := fun _ => rfl
        toNat_ofNat := fun _ hn => toNatBits_toModel_ofModel hn
        ofModel_toModel := ofModel_toModel (plan := .limbs h) }

end Code

/-- Every configured binary type has the natural-number view of its storage plan. -/
instance natView {plan : StoragePlan format} : NatView (Family format (Code plan) plan) format :=
  Code.natView plan

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The codec lift of a binary model operation is the lift of the kernel view, in every plan. -/
theorem liftBinary_eq_natView {plan : StoragePlan format}
    (operation : Model format → Model format → Model format)
    (left right : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftBinary (Model := Model format) (plan := plan)
        operation left right =
      NatView.liftBinary operation left right := by
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The codec lift of a ternary model operation is the lift of the kernel view, in every plan. -/
theorem liftTernary_eq_natView {plan : StoragePlan format}
    (operation : Model format → Model format → Model format → Model format)
    (left right third : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftTernary (Model := Model format) (plan := plan)
        operation left right third =
      NatView.liftTernary operation left right third := by
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The codec lift of a unary model operation is the lift of the kernel view, in every plan. -/
theorem liftUnary_eq_natView {plan : StoragePlan format}
    (operation : Model format → Model format)
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.ModelCodec.liftUnary (Model := Model format) (plan := plan)
        operation value =
      NatView.liftUnary operation value := by
  cases plan <;> rfl

set_option hygiene false in
direction_rule add for format := liftBinary, liftBinary_eq_natView [left right]

direction_rule sub for format := liftBinary, liftBinary_eq_natView [left right]

direction_rule mul for format := liftBinary, liftBinary_eq_natView [left right]

direction_rule div for format := liftBinary, liftBinary_eq_natView [left right]

direction_rule fma for format := liftTernary, liftTernary_eq_natView [left right addend]

direction_rule sqrt for format := liftUnary, liftUnary_eq_natView [value]

direction_rule roundToIntegral for format := liftUnary, liftUnary_eq_natView [value]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- A scientific literal of a configured type is the kernel literal. -/
@[kernel_optimize] theorem ofScientific_eq {plan : StoragePlan format} (mantissa : Nat)
    (exponentSign : Bool) (exponent : Nat) :
    (OfScientific.ofScientific mantissa exponentSign exponent :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.Value.ofScientific mantissa exponentSign exponent := by
  rw [KernelPath.Value.ofScientific_eq_lift]
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- A natural-number literal of a configured type is the kernel literal. -/
@[kernel_optimize] theorem ofNat_eq {plan : StoragePlan format} (value : Nat) :
    (OfNat.ofNat value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.Value.ofNatural value := by
  rw [KernelPath.Value.ofNatural_eq_lift]
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The negation of a configured value is the kernel negation. -/
@[kernel_optimize] theorem neg_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    -value = KernelPath.Value.neg value := by
  rw [KernelPath.Value.neg_eq_lift]
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The decoding of a configured value is the decoding of the kernel view, in every plan. -/
theorem toModel_eq_natView {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.toModel x =
      (natView (plan := plan)).toModel x.raw := by
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The comparison of configured values is the model comparison of the decoded values. -/
instance modelComparison {plan : StoragePlan format} :
    KernelPath.Value.ModelComparison (Family format (Code plan) plan) format where
  compare_eq x y := by
    rw [← toModel_eq_natView, ← toModel_eq_natView]
    rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `x < y` on configured values is a test on the comparison code of the encodings. -/
@[kernel_optimize] theorem lt_eq {plan : StoragePlan format}
    (x y : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    (x < y) = (Nat.beq (KernelPath.Flat.compare format (toNat x) (toNat y)) 0 = true) := by
  change (FloatLib.Floats.ExecFloat.compareLess x y = true) = _
  rw [KernelPath.Value.compareLess_eq]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `x ≤ y` on configured values is a test on the comparison code of the encodings. -/
@[kernel_optimize] theorem le_eq {plan : StoragePlan format}
    (x y : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    (x ≤ y) = (Nat.ble (KernelPath.Flat.compare format (toNat x) (toNat y)) 1 = true) := by
  change (FloatLib.Floats.ExecFloat.compareLessEqual x y = true) = _
  rw [KernelPath.Value.compareLessEqual_eq]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The integer conversion of a configured value is computed on its encoding: `none` for a NaN or an
infinity, and otherwise the rounded magnitude with the sign bit.
-/
@[kernel_optimize] theorem toInt?_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan))
    (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.toInt? value mode =
      someWhen (finiteCode format (toNat value))
        (signedInt (Nat.beq (signCode format (toNat value)) 1)
          (KernelPath.Flat.intMagnitude format mode (toNat value))) := by
  rw [← KernelPath.Value.toInt?_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The packing of a model value is the packing of the kernel view, in every plan. -/
theorem ofModel_eq_natView {plan : StoragePlan format} (value : Model format) :
    (FloatLib.Floats.ExecFloat.Binary.ofModel value :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      FloatLib.Floats.ExecFloat.ofRaw ((natView (plan := plan)).ofModel value) := by
  cases plan <;> rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- A model value stored in a configured format is the stored encoding of the value. -/
theorem ofModel_eq_ofNat {plan : StoragePlan format} (value : Model format) :
    (FloatLib.Floats.ExecFloat.Binary.ofModel value :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.ofNat value.toNatBits := by
  rw [KernelPath.ofNat_eq, Model.ofNatBits_toNatBits, ofModel_eq_natView]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
A rational number rounded into a configured format in a direction is the kernel rounding of its
numerator and denominator.
-/
@[kernel_optimize] theorem ofRat_eq {plan : StoragePlan format} (q : ℚ)
    (mode : Model.IEEERoundingMode) :
    (FloatLib.Floats.ExecFloat.Binary.ofModel (Model.ofRat format q (mode := mode)) :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) =
      KernelPath.Value.ofRatio mode (decide (q.num < 0)) q.num.natAbs q.den := by
  rw [KernelPath.Value.ofRatio_eq_lift, ofModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The outcome of rounding a rational number into a configured format with `status := true`: the
kernel rounding of its numerator and denominator, with the exception flags and the ternary value
decoded from one status number.
-/
@[kernel_optimize] theorem ofRat_outcome_eq {plan : StoragePlan format} (q : ℚ)
    (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
        (Model.ofRat format q (mode := mode) (status := true)) =
      { value := KernelPath.Value.ofRatio mode (decide (q.num < 0)) q.num.natAbs q.den
        status := KernelPath.decodeStatus
          (KernelPath.Flat.ratioStatus format mode (signNat (decide (q.num < 0))) q.num.natAbs
            q.den)
        ternary := KernelPath.decodeTernary
          (KernelPath.Flat.ratioStatus format mode (signNat (decide (q.num < 0))) q.num.natAbs
            q.den) } := by
  unfold FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel
  rw [Model.value_ofRat, ofRat_eq, (KernelPath.ofRat_status_eq format mode q).1,
    (KernelPath.ofRat_status_eq format mode q).2, KernelPath.Flat.ratioStatus_eq]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The outcome of rounding a rational number into a configured format with `status := true`: the
kernel rounding of its numerator and denominator, with the exception flags and the ternary value
decoded from the status number at the word of that rounding.
-/
@[kernel_optimize (cost := 490)] theorem ofRat_outcome_eq_with {plan : StoragePlan format}
    (q : ℚ) (mode : Model.IEEERoundingMode) :
    FloatLib.Floats.ExecFloat.Binary.IEEEOutcome.ofModel (plan := plan) (code := Code plan)
        (Model.ofRat format q (mode := mode) (status := true)) =
      { value := KernelPath.Value.ofRatio mode (decide (q.num < 0)) q.num.natAbs q.den
        status := KernelPath.decodeStatus
          (KernelPath.Flat.ratioStatusWith format mode (signNat (decide (q.num < 0)))
            q.num.natAbs q.den
            (KernelPath.toNat
              (KernelPath.Value.ofRatio mode (decide (q.num < 0)) q.num.natAbs q.den :
                FloatLib.Floats.ExecFloat (Family format (Code plan) plan))))
        ternary := KernelPath.decodeTernary
          (KernelPath.Flat.ratioStatusWith format mode (signNat (decide (q.num < 0)))
            q.num.natAbs q.den
            (KernelPath.toNat
              (KernelPath.Value.ofRatio mode (decide (q.num < 0)) q.num.natAbs q.den :
                FloatLib.Floats.ExecFloat (Family format (Code plan) plan)))) } := by
  rw [ofRat_outcome_eq, KernelPath.Value.ofRatio_status_eq_with]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The reference cast of a configured value, stored in a configured format, is the kernel cast.
-/
@[kernel_optimize] theorem cast_eq {target : FloatFormat} {plan : StoragePlan format}
    {targetPlan : StoragePlan target} (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    (FloatLib.Floats.ExecFloat.Binary.ofModel
        (Model.cast format target (FloatLib.Floats.ExecFloat.Binary.toModel x) mode) :
        FloatLib.Floats.ExecFloat (Family target (Code targetPlan) targetPlan)) =
      KernelPath.Value.cast mode x := by
  rw [KernelPath.Value.cast_eq_lift, ofModel_eq_natView, toModel_eq_natView]

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The exception flags and the ternary value of the reference cast of a configured value with
`status := true` are decoded from the status number of its encoding, for every destination
descriptor.
-/
@[kernel_optimize] theorem cast_status_eq {target : FloatFormat} {plan : StoragePlan format}
    (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    (Model.cast format target (FloatLib.Floats.ExecFloat.Binary.toModel x) mode
          (status := true)).status =
        KernelPath.decodeStatus (KernelPath.Flat.castStatus format target mode (toNat x)) ∧
      (Model.cast format target (FloatLib.Floats.ExecFloat.Binary.toModel x) mode
          (status := true)).ternary =
        KernelPath.decodeTernary (KernelPath.Flat.castStatus format target mode (toNat x)) := by
  rw [toModel_eq_natView]
  exact KernelPath.Value.cast_status_eq_lift mode x

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The exception flags and the ternary value of the reference cast of a configured value with
`status := true` are decoded from the status number at the flat cast of its encoding, which is
the word of the value of the cast, for every destination descriptor.
-/
@[kernel_optimize (cost := 100)] theorem cast_status_eq_with {target : FloatFormat}
    {plan : StoragePlan format} (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    (Model.cast format target (FloatLib.Floats.ExecFloat.Binary.toModel x) mode
          (status := true)).status =
        KernelPath.decodeStatus
          (KernelPath.Flat.castStatusWith format target mode (toNat x)
            (KernelPath.Flat.cast format target mode (toNat x))) ∧
      (Model.cast format target (FloatLib.Floats.ExecFloat.Binary.toModel x) mode
          (status := true)).ternary =
        KernelPath.decodeTernary
          (KernelPath.Flat.castStatusWith format target mode (toNat x)
            (KernelPath.Flat.cast format target mode (toNat x))) := by
  rw [KernelPath.Flat.castStatusWith_cast]
  exact cast_status_eq mode x

set_option hygiene false in
outcome_rule add for format [left right]

outcome_rule sub for format [left right]

outcome_rule mul for format [left right]

outcome_rule fma for format [left right addend]

outcome_rule div for format [left right]

outcome_rule sqrt for format [value]

outcome_rule roundToIntegral for format [value]

outcome_with_rule add for format [left right] cost 270

outcome_with_rule sub for format [left right] cost 280

outcome_with_rule mul for format [left right] cost 230

outcome_with_rule fma for format [left right addend] cost 340

outcome_with_rule div for format [left right] cost 270

outcome_with_rule roundToIntegral for format [value] cost 245

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/--
The exact rational value of a configured value is built from its encoding: no value for a word
that is not finite, and `KernelPath.ratValue` otherwise.
-/
@[kernel_optimize] theorem toRat?_eq {plan : StoragePlan format}
    (value : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.toRat? value =
      someWhen (finiteCode format (toNat value)) (KernelPath.ratValue format (toNat value)) := by
  rw [← KernelPath.Value.toRat?_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The IEEE total order of configured values is a test on their encodings. -/
@[kernel_optimize] theorem totalOrder_eq {plan : StoragePlan format}
    (x y : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.totalOrder x y =
      Nat.beq (KernelPath.Flat.totalOrder format (toNat x) (toNat y)) 1 := by
  rw [← KernelPath.Value.totalOrder_eq_lift, ← toModel_eq_natView, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `isNaN` of a configured value is a test on its encoding. -/
@[kernel_optimize] theorem isNaN_eq {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.isNaN x = Nat.beq (nanCode format (toNat x)) 1 := by
  rw [KernelPath.Value.nanCode_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `isInfinite` of a configured value is a test on its encoding. -/
@[kernel_optimize] theorem isInfinite_eq {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.isInfinite x = Nat.beq (infCode format (toNat x)) 1 := by
  rw [KernelPath.Value.infCode_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `isZero` of a configured value is a test on its encoding. -/
@[kernel_optimize] theorem isZero_eq {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.isZero x = Nat.beq (zeroCode format (toNat x)) 1 := by
  rw [KernelPath.Value.zeroCode_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `isFinite` of a configured value is a test on its encoding. -/
@[kernel_optimize] theorem isFinite_eq {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.isFinite x = Nat.beq (finiteCode format (toNat x)) 1 := by
  rw [KernelPath.Value.finiteCode_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- `signBit` of a configured value is a test on its encoding. -/
@[kernel_optimize] theorem signBit_eq {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.signBit x = Nat.beq (signCode format (toNat x)) 1 := by
  rw [KernelPath.Value.signCode_eq_lift, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The interchange word of a configured value is its kernel encoding. -/
@[kernel_optimize] theorem toNatBits_eq {plan : StoragePlan format}
    (x : FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) :
    FloatLib.Floats.ExecFloat.Binary.toNatBits x = toNat x := by
  rw [KernelPath.toNat_eq, ← toModel_eq_natView]
  rfl

open FloatLib.Floats.Formats.BinaryInterchange.KernelPath in
/-- The configured value with a given interchange word is the kernel value with that encoding. -/
@[kernel_optimize] theorem ofNatBits_eq {plan : StoragePlan format} (bits : Nat) :
    (FloatLib.Floats.ExecFloat.Binary.ofNatBits bits :
        FloatLib.Floats.ExecFloat (Family format (Code plan) plan)) = ofNat bits := by
  rw [KernelPath.ofNat_eq]
  cases plan <;> rfl

end FloatLib.Floats.Formats.BinaryInterchange.Configured

/-
The mode-taking operations of configured values are selectors: `float_decide` unfolds them. A
call without a mode or status reaches `ExecFloat.add` and its peers, and a call with another
rounding direction reaches the codec lift of the model operation, which the rules above rewrite.
-/
attribute [kernel_optimize unfold] FloatLib.Floats.ExecFloat.Binary.add
    FloatLib.Floats.ExecFloat.Binary.sub
  FloatLib.Floats.ExecFloat.Binary.mul FloatLib.Floats.ExecFloat.Binary.div
  FloatLib.Floats.ExecFloat.Binary.sqrt FloatLib.Floats.ExecFloat.Binary.fma
  FloatLib.Floats.ExecFloat.Binary.roundToIntegral FloatLib.Floats.ExecFloat.Binary.ofRat

/-
The value of a reference cast with `status := true` is the cast itself, which `cast_eq` rewrites
when it is stored in a configured format.
-/
attribute [kernel_optimize] FloatLib.Floats.Formats.BinaryInterchange.Model.value_cast
