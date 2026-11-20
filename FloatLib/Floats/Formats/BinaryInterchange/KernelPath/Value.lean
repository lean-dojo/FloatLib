/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Loop -- shake: keep
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Flat
public import FloatLib.Tactic.FloatDecide -- shake: keep
public import FloatLib.Tactic.KernelOperation
public import FloatLib.Tactic.StatusOperation

/-!
# Kernel operations on stored values

For every family `F` with a `NatView F format` instance, `Value.op` is the staged, computable
operation between a read and a store of the natural-number encoding. Each one comes with

* `Value.op_eq_lift`: it is the model operation carried through the family's conversions;
* `Value.toNat_op`: its encoding is the flat operation on the encodings of the operands, so a
  nested computation stays on natural numbers;
* `Value.op_eq`: the public operation `ExecFloat.op` equals it in the nearest-even direction.
  The premise is that the family's capability has the lifted model operation as its reference,
  which instance search checks by unfolding. `add_notation_eq`, `sub_notation_eq`,
  `mul_notation_eq` and `div_notation_eq` state the same for `+`, `-`, `*` and `/`.

Addition, subtraction, multiplication, fused multiply-add, division and square root take the
rounding direction as their first argument. `Value.ofRatio mode negative num den` rounds a ratio
of naturals in a direction. `Value.neg`, `Value.ofScientific`
and `Value.ofNatural` are the negation and the two shapes of literal, with the same theorems.

`Value.add_status_eq_lift`, `Value.add_ternary_eq_lift` and their siblings for subtraction,
multiplication, fused multiply-add, division, square root and rounding to an integral value
decode the five IEEE exception flags and the ternary value of an operation with `status := true`
from one status number computed on the encodings. `Flat.ratioStatus` is the status number of a
rounded ratio of naturals (`KernelPath.ofRat_status_eq`).

`Value.add_status_eq_with` and its siblings for subtraction, multiplication, fused multiply-add,
division and rounding to an integral value, and `Value.ofRatio_status_eq_with` for a rounded
ratio, give the same status number as a function of the encoding of the kernel value
(`Flat.addStatusWith`). A statement about the value and the flags of one operation then contains
the value once, and Lean's kernel computes it once.

`Value.roundToIntegral mode x` rounds to an integer in the format, and `Value.toInt?_eq_lift`
computes the integer conversion on the encoding. `Value.cast mode x` is the cast into another
family: the reference `Model.cast` between the two descriptors, with the destination's overflow
and NaN rules. `Value.cast_status_eq_lift` decodes the flags and the ternary value of that cast
with `status := true`.

Comparisons and classification stay on encodings as well: `Value.compare_eq` and its siblings
turn `ExecFloat.compare`, the six comparison predicates and `==` into tests on the comparison
code of the two encodings, for every family with a `ModelComparison` instance, and
`Value.nanCode_eq_lift` and its siblings do the same for the classification predicates.
`Value.totalOrder_eq_lift` does it for the IEEE total order, and `Value.toRat?_eq_lift` builds
the exact rational value of a stored value from its encoding.

These are the equations the `float_decide` tactic rewrites with, and this module brings the
tactic along. The premise of `op_eq` holds up to unfolding the family's reference operation. The
term elaborator sees that, so `Value.add_eq x y` applies as it is. `simp` compares instance
arguments at restricted transparency and needs
`set_option backward.isDefEq.respectTransparency false`, which `float_decide` sets for its
rewrite step.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics


namespace Value

open FloatLib.Floats.ExecFloat (Capability)

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/-- Kernel addition of stored values, rounded in the direction `mode`. -/
kernel_operation add := binary, binary_eq, toNat_binary, NatView.liftBinary,
  NatView.liftBinary_congr
  (Flat.add, KernelPath.addShort, Model.add, KernelPath.addShort_eq_spec, Model.Spec.add,
    Model.Proof.add_eq_spec)
  for add [x y] cost 80

/-- Kernel subtraction of stored values, rounded in the direction `mode`. -/
kernel_operation sub := binary, binary_eq, toNat_binary, NatView.liftBinary,
  NatView.liftBinary_congr
  (Flat.sub, KernelPath.subShort, Model.sub, KernelPath.subShort_eq_spec, Model.Spec.sub,
    Model.Proof.sub_eq_spec)
  for sub [x y] cost 88

/-- Kernel multiplication of stored values, rounded in the direction `mode`. -/
kernel_operation mul := binary, binary_eq, toNat_binary, NatView.liftBinary,
  NatView.liftBinary_congr
  (Flat.mul, KernelPath.mulFast, Model.mul, KernelPath.mulFast_eq_spec, Model.Spec.mul,
    Model.Proof.mul_eq_spec)
  for mul [x y] cost 52

/--
Kernel fused multiply-add `x * y + z` of stored values with one rounding in the direction `mode`.
-/
kernel_operation fma := ternary, ternary_eq, toNat_ternary, NatView.liftTernary,
  NatView.liftTernary_congr
  (Flat.fma, KernelPath.fma, Model.fma, KernelPath.fma_eq_spec, Model.Spec.fma,
    Model.Proof.fma_eq_spec)
  for fma [x y z] cost 107

/-- Kernel division of stored values, rounded in the direction `mode`. -/
kernel_operation div := binary, binary_eq, toNat_binary, NatView.liftBinary,
  NatView.liftBinary_congr
  (Flat.div, KernelPath.div, Model.div, KernelPath.div_eq_spec, Model.Spec.div,
    Model.Proof.div_eq_spec)
  for div [x y] cost 66

/-- Kernel square root of a stored value, rounded in the direction `mode`. -/
kernel_operation sqrt := unary, unary_eq, toNat_unary, NatView.liftUnary,
  NatView.liftUnary_congr
  (Flat.sqrt, KernelPath.sqrt, Model.sqrt, KernelPath.sqrt_eq_spec, Model.Spec.sqrt,
    Model.Proof.sqrt_eq_spec)
  for sqrt [x] cost 62

/-- Kernel negation of a stored value. -/
def neg (x : FloatLib.Floats.ExecFloat F) : FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.neg format) Model.neg KernelPath.neg_eq_spec x

/-- The kernel negation is the model negation carried through the family's conversions. -/
theorem neg_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    neg x = NatView.liftUnary Model.neg x :=
  unary_eq _ _ _ x

/-- The encoding of a negation is the flat negation of the encoding. -/
@[kernel_optimize] theorem toNat_neg (x : FloatLib.Floats.ExecFloat F) :
    toNat (neg x) = Flat.neg format (toNat x) :=
  toNat_unary _ _ _ x

/-- The stored scientific literal with the given mantissa and decimal exponent. -/
def ofScientific (mantissa : Nat) (exponentSign : Bool) (exponent : Nat) :
    FloatLib.Floats.ExecFloat F :=
  nullary (KernelPath.ofScientific format mantissa exponentSign exponent)
    (Model.ofRat format (OfScientific.ofScientific mantissa exponentSign exponent : ℚ))
    (KernelPath.ofScientific_eq format mantissa exponentSign exponent)

/-- The kernel literal is the rounded rational carried through the family's packing. -/
theorem ofScientific_eq_lift (mantissa : Nat) (exponentSign : Bool) (exponent : Nat) :
    ofScientific (F := F) mantissa exponentSign exponent =
      FloatLib.Floats.ExecFloat.ofRaw (view.ofModel
        (Model.ofRat format (OfScientific.ofScientific mantissa exponentSign exponent : ℚ))) :=
  nullary_eq _ _ _

/-- The encoding of a scientific literal is the flat literal function. -/
@[kernel_optimize] theorem toNat_ofScientific (mantissa : Nat) (exponentSign : Bool)
    (exponent : Nat) :
    toNat (ofScientific (F := F) mantissa exponentSign exponent) =
      Flat.ofScientific format mantissa exponentSign exponent :=
  toNat_nullary _ _ _

/-- The stored natural-number literal. -/
def ofNatural (value : Nat) : FloatLib.Floats.ExecFloat F :=
  nullary (KernelPath.ofNatural format value) (Model.ofRat format (value : ℚ))
    (KernelPath.ofNatural_eq format value)

/-- The kernel literal is the rounded natural number carried through the family's packing. -/
theorem ofNatural_eq_lift (value : Nat) :
    ofNatural (F := F) value =
      FloatLib.Floats.ExecFloat.ofRaw (view.ofModel (Model.ofRat format (value : ℚ))) :=
  nullary_eq _ _ _

/-- The encoding of a natural-number literal is the flat literal function. -/
@[kernel_optimize] theorem toNat_ofNatural (value : Nat) :
    toNat (ofNatural (F := F) value) = Flat.ofNatural format value :=
  toNat_nullary _ _ _

/-! ### Rational numbers -/

/--
The stored value of `± num / den` rounded in the direction `mode`, computed on naturals: the
reference `Model.Internal.Directed.roundRat` (`ofRatio_eq_lift`).
-/
def ofRatio (mode : Model.IEEERoundingMode) (negative : Bool) (num den : Nat) :
    FloatLib.Floats.ExecFloat F :=
  nullary (KernelPath.ofRatio format mode (signNat negative) num den)
    (Model.Internal.Directed.roundRat format mode negative num den)
    (KernelPath.ofRatio_eq_directed format mode negative num den)

/-- The kernel rounding of a ratio is the reference rounding carried through the packing. -/
theorem ofRatio_eq_lift (mode : Model.IEEERoundingMode) (negative : Bool) (num den : Nat) :
    ofRatio (F := F) mode negative num den =
      FloatLib.Floats.ExecFloat.ofRaw
        (view.ofModel (Model.Internal.Directed.roundRat format mode negative num den)) :=
  nullary_eq _ _ _

/-- The encoding of a rounded ratio is the flat rounding. -/
@[kernel_optimize] theorem toNat_ofRatio (mode : Model.IEEERoundingMode) (negative : Bool)
    (num den : Nat) :
    toNat (ofRatio (F := F) mode negative num den) =
      Flat.ofRatio format mode (signNat negative) num den :=
  toNat_nullary _ _ _

/--
The status number of a rounded ratio at the encoding of its kernel rounding is the flat status
number of the ratio.
-/
theorem ofRatio_status_eq_with (mode : Model.IEEERoundingMode) (negative : Bool)
    (num den : Nat) :
    Flat.ratioStatusWith format mode (signNat negative) num den
        (toNat (ofRatio (F := F) mode negative num den)) =
      Flat.ratioStatus format mode (signNat negative) num den := by
  rw [toNat_ofRatio, Flat.ratioStatusWith_eq, Flat.ratioStatus_eq, Flat.ofRatio_eq]
  rfl

/-! ### Casts -/

section Cast

universe v

variable {G : Type v} [EncodedFormat G] {target : FloatFormat} [targetView : NatView G target]

/--
The cast of a stored value into the family `G`, rounded in the direction `mode` and computed on
encodings: the reference `Model.cast` between the two descriptors (`cast_eq_lift`).
-/
def cast (mode : Model.IEEERoundingMode) (x : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat G :=
  nullary (KernelPath.cast format target mode (toNat x))
    (Model.cast format target (view.toModel x.raw) mode)
    (by rw [toNat_eq]; exact cast_eq_spec mode _)

/-- The kernel cast is the reference cast carried through the two families' conversions. -/
theorem cast_eq_lift (mode : Model.IEEERoundingMode) (x : FloatLib.Floats.ExecFloat F) :
    (cast mode x : FloatLib.Floats.ExecFloat G) =
      FloatLib.Floats.ExecFloat.ofRaw
        (targetView.ofModel (Model.cast format target (view.toModel x.raw) mode)) :=
  nullary_eq _ _ _

/-- The encoding of a cast is the flat cast of the encoding of the operand. -/
@[kernel_optimize] theorem toNat_cast (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat F) :
    toNat (cast mode x : FloatLib.Floats.ExecFloat G) = Flat.cast format target mode (toNat x) :=
  toNat_nullary _ _ _

/--
The exception flags and the ternary value of the reference cast with `status := true` are
decoded from the flat status number of the encoding of the operand.
-/
theorem cast_status_eq_lift (mode : Model.IEEERoundingMode) (x : FloatLib.Floats.ExecFloat F) :
    (Model.cast format target (view.toModel x.raw) mode (status := true)).status =
        decodeStatus (Flat.castStatus format target mode (toNat x)) ∧
      (Model.cast format target (view.toModel x.raw) mode (status := true)).ternary =
        decodeTernary (Flat.castStatus format target mode (toNat x)) := by
  simp only [toNat_eq, Flat.castStatus_eq]
  exact And.intro (castStatus_eq mode _).1.symm (castStatus_eq mode _).2.symm

end Cast

/-! ### Status flags -/

status_operation add := Flat.addStatus, Model.add, KernelPath.addStatus_eq, Flat.addStatus_eq
  [x y]

status_operation sub := Flat.subStatus, Model.sub, KernelPath.subStatus_eq, Flat.subStatus_eq
  [x y]

status_operation mul := Flat.mulStatus, Model.mul, KernelPath.mulStatus_eq, Flat.mulStatus_eq
  [x y]

status_operation fma := Flat.fmaStatus, Model.fma, KernelPath.fmaStatus_eq, Flat.fmaStatus_eq
  [x y z]

status_operation div := Flat.divStatus, Model.div, KernelPath.divStatus_eq, Flat.divStatus_eq
  [x y]

status_operation sqrt := Flat.sqrtStatus, Model.sqrt, KernelPath.sqrtStatus_eq,
  Flat.sqrtStatus_eq [x]

status_operation roundToIntegral := Flat.roundToIntegralStatus, Model.roundToIntegral,
  KernelPath.roundToIntegralStatus_eq, Flat.roundToIntegralStatus_eq [x]

/-!
The status numbers as functions of the word of the value: a statement about the value and the
flags of one operation then makes Lean's kernel compute the value once.
-/

status_with add := Flat.addStatusWith, Flat.addStatusWith_eq, Flat.addStatus, Flat.addStatus_eq
  using [Flat.add_eq, KernelPath.addShort_eq_spec, ← KernelPath.add_eq_spec] [x y]

status_with sub := Flat.subStatusWith, Flat.subStatusWith_eq, Flat.subStatus, Flat.subStatus_eq
  using [Flat.sub_eq, KernelPath.subShort_eq_spec, ← KernelPath.sub_eq_spec] [x y]

status_with mul := Flat.mulStatusWith, Flat.mulStatusWith_eq, Flat.mulStatus, Flat.mulStatus_eq
  using [Flat.mul_eq, KernelPath.mulFast_eq_spec, ← KernelPath.mul_eq_spec] [x y]

status_with fma := Flat.fmaStatusWith, Flat.fmaStatusWith_eq, Flat.fmaStatus, Flat.fmaStatus_eq
  using [Flat.fma_eq] [x y z]

status_with div := Flat.divStatusWith, Flat.divStatusWith_eq, Flat.divStatus, Flat.divStatus_eq
  using [Flat.div_eq] [x y]

/-!
A statement that the flags of an outcome are a given record becomes one comparison of natural
numbers (`decodeStatus_eq_iff`).
-/
attribute [kernel_optimize] decodeStatus_eq_iff

/-! ### Integers -/

/--
Kernel rounding of a stored value to an integer in the direction `mode`, kept in the format.
-/
def roundToIntegral (mode : Model.IEEERoundingMode) (x : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat F :=
  unary (KernelPath.roundToIntegral format mode) (fun x => Model.roundToIntegral x mode)
    (KernelPath.roundToIntegral_eq_spec mode) x

/-- The kernel integral rounding is the reference one carried through the conversions. -/
theorem roundToIntegral_eq_lift (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat F) :
    roundToIntegral mode x = NatView.liftUnary (fun x => Model.roundToIntegral x mode) x :=
  unary_eq _ _ _ x

/-- The encoding of an integral rounding is the flat operation on the encoding. -/
@[kernel_optimize] theorem toNat_roundToIntegral (mode : Model.IEEERoundingMode)
    (x : FloatLib.Floats.ExecFloat F) :
    toNat (roundToIntegral mode x) = Flat.roundToIntegral format mode (toNat x) :=
  toNat_unary _ _ _ x

status_with roundToIntegral := Flat.roundToIntegralStatusWith,
  Flat.roundToIntegralStatusWith_eq, Flat.roundToIntegralStatus, Flat.roundToIntegralStatus_eq
  using [Flat.roundToIntegral_eq] [x]

/--
The integer that rounds a stored value in the direction `mode`, computed on its encoding: `none`
for a NaN or an infinity, and otherwise the magnitude `Flat.intMagnitude` with the sign bit.
-/
theorem toInt?_eq_lift (mode : Model.IEEERoundingMode) (x : FloatLib.Floats.ExecFloat F) :
    (Model.toDyadic? (view.toModel x.raw)).map (Model.roundDyadicToInt mode) =
      someWhen (finiteCode format (toNat x))
        (signedInt (Nat.beq (signCode format (toNat x)) 1)
          (Flat.intMagnitude format mode (toNat x))) := by
  unfold someWhen
  rw [toNat_eq, KernelPath.finiteCode_eq, KernelPath.signCode_eq, Flat.intMagnitude_eq]
  cases hfinite : Model.isFinite (view.toModel x.raw)
  · rw [toDyadic?_eq_none_of_isFinite_eq_false _ hfinite]
    rfl
  · obtain ⟨d, hd, -⟩ := toDyadic?_of_isFinite _ hfinite
    rw [hd]
    exact congrArg some (KernelPath.intMagnitude_eq mode _ d hd)

/-! ### The exact rational value -/

/--
The exact rational value of the decoded value, `Model.toRat?`, is built from the encoding: no
value for a word that is not finite, and `ratValue` otherwise.
-/
theorem toRat?_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    Model.toRat? (view.toModel x.raw) =
      someWhen (finiteCode format (toNat x)) (ratValue format (toNat x)) := by
  unfold someWhen
  rw [toNat_eq, KernelPath.finiteCode_eq]
  unfold Model.toRat?
  cases hfinite : Model.isFinite (view.toModel x.raw)
  · rw [toDyadic?_eq_none_of_isFinite_eq_false _ hfinite]
    rfl
  · obtain ⟨d, hd, -⟩ := toDyadic?_of_isFinite _ hfinite
    rw [hd]
    exact congrArg some (KernelPath.ratValue_eq _ d hd).symm

/-! ### The total order -/

/--
The IEEE total order of the decoded values is a test on the flat total-order code of the
encodings.
-/
theorem totalOrder_eq_lift (x y : FloatLib.Floats.ExecFloat F) :
    Model.totalOrder (view.toModel x.raw) (view.toModel y.raw) =
      Nat.beq (Flat.totalOrder format (toNat x) (toNat y)) 1 := by
  rw [toNat_eq, toNat_eq, Flat.totalOrder_eq, KernelPath.totalOrderCode_eq]

/-! ### Classification -/

/-- `nanCode` of the encoding of a stored value says whether the decoded value is a NaN. -/
theorem nanCode_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    Nat.beq (nanCode format (toNat x)) 1 = Model.isNaN (view.toModel x.raw) := by
  rw [toNat_eq, KernelPath.nanCode_eq]

/-- `infCode` of the encoding of a stored value says whether the decoded value is an infinity. -/
theorem infCode_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    Nat.beq (infCode format (toNat x)) 1 = Model.isInfinite (view.toModel x.raw) := by
  rw [toNat_eq, KernelPath.infCode_eq]

/-- `zeroCode` of the encoding of a stored value says whether the decoded value is a zero. -/
theorem zeroCode_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    Nat.beq (zeroCode format (toNat x)) 1 = Model.isZero (view.toModel x.raw) := by
  rw [toNat_eq, KernelPath.zeroCode_eq]

/-- `finiteCode` of the encoding of a stored value says whether the decoded value is finite. -/
theorem finiteCode_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    Nat.beq (finiteCode format (toNat x)) 1 = Model.isFinite (view.toModel x.raw) := by
  rw [toNat_eq, KernelPath.finiteCode_eq]

/-- `signCode` of the encoding of a stored value is the sign bit of the decoded value. -/
theorem signCode_eq_lift (x : FloatLib.Floats.ExecFloat F) :
    Nat.beq (signCode format (toNat x)) 1 = Model.signBit (view.toModel x.raw) := by
  rw [toNat_eq, KernelPath.signCode_eq]

/-! ### Comparison -/

/--
The comparison of the family `F` is the model comparison of the decoded values. Every binary
family defines its comparison this way, and an instance records it for the kernel path.
-/
class ModelComparison (F : Type u) [EncodedFormat F] [FloatLib.Floats.ExecFloat.Comparison F]
    (format : outParam FloatFormat) [view : NatView F format] : Prop where
  /-- The family's comparison is `Model.compare` of the decoded operands. -/
  compare_eq : ∀ x y : FloatLib.Floats.ExecFloat F,
    FloatLib.Floats.ExecFloat.compare x y =
      Model.compare (view.toModel x.raw) (view.toModel y.raw)

section Comparison

variable [FloatLib.Floats.ExecFloat.Comparison F] [ModelComparison F format]

/-- The comparison of two stored values is the comparison code of their encodings. -/
@[kernel_optimize] theorem compare_eq (x y : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.compare x y =
      decodeOrdering (Flat.compare format (toNat x) (toNat y)) := by
  rw [ModelComparison.compare_eq, toNat_eq, toNat_eq]
  exact (compareCode_eq _ _).symm

/-- `compareLess` holds exactly when the comparison code is zero. -/
@[kernel_optimize] theorem compareLess_eq (x y : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.compareLess x y =
      Nat.beq (Flat.compare format (toNat x) (toNat y)) 0 := by
  unfold FloatLib.Floats.ExecFloat.compareLess
  rw [compare_eq, decodeOrdering_beq_lt]

/-- `compareEqual` holds exactly when the comparison code is one. -/
@[kernel_optimize] theorem compareEqual_eq (x y : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.compareEqual x y =
      Nat.beq (Flat.compare format (toNat x) (toNat y)) 1 := by
  unfold FloatLib.Floats.ExecFloat.compareEqual
  rw [compare_eq, decodeOrdering_beq_eq]

/-- `compareGreater` holds exactly when the comparison code is two. -/
@[kernel_optimize] theorem compareGreater_eq (x y : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.compareGreater x y =
      Nat.beq (Flat.compare format (toNat x) (toNat y)) 2 := by
  unfold FloatLib.Floats.ExecFloat.compareGreater
  rw [compare_eq, decodeOrdering_beq_gt]

/-- `compareLessEqual` holds exactly when the comparison code is at most one. -/
@[kernel_optimize] theorem compareLessEqual_eq (x y : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.compareLessEqual x y =
      Nat.ble (Flat.compare format (toNat x) (toNat y)) 1 := by
  unfold FloatLib.Floats.ExecFloat.compareLessEqual
  rw [compare_eq]
  generalize Flat.compare format (toNat x) (toNat y) = code
  rcases code with _ | _ | _ | code <;> rfl

/-- `compareGreaterEqual` holds exactly when the comparison code is one or two. -/
@[kernel_optimize] theorem compareGreaterEqual_eq (x y : FloatLib.Floats.ExecFloat F) :
    FloatLib.Floats.ExecFloat.compareGreaterEqual x y =
      (Nat.ble 1 (Flat.compare format (toNat x) (toNat y)) &&
        Nat.ble (Flat.compare format (toNat x) (toNat y)) 2) := by
  unfold FloatLib.Floats.ExecFloat.compareGreaterEqual
  rw [compare_eq]
  generalize Flat.compare format (toNat x) (toNat y) = code
  rcases code with _ | _ | _ | code <;> rfl

/-- `x == y` holds exactly when the comparison code is one. -/
@[kernel_optimize] theorem beq_eq (x y : FloatLib.Floats.ExecFloat F) :
    (x == y) = Nat.beq (Flat.compare format (toNat x) (toNat y)) 1 :=
  compareEqual_eq x y

end Comparison

variable [FloatLib.Floats.ExecFloat.Backend.PolicyFor F]

/-- `x + y` equals the kernel addition to nearest even. -/
@[kernel_optimize] theorem add_notation_eq [cap : FloatLib.Floats.ExecFloat.Add F]
    [Capability.HasSpec cap (NatView.liftBinary (F := F) Model.Spec.add)]
    (x y : FloatLib.Floats.ExecFloat F) : x + y = add .nearest x y :=
  add_eq x y

/-- `x - y` equals the kernel subtraction to nearest even. -/
@[kernel_optimize] theorem sub_notation_eq [cap : FloatLib.Floats.ExecFloat.Sub F]
    [Capability.HasSpec cap (NatView.liftBinary (F := F) Model.Spec.sub)]
    (x y : FloatLib.Floats.ExecFloat F) : x - y = sub .nearest x y :=
  sub_eq x y

/-- `x * y` equals the kernel multiplication to nearest even. -/
@[kernel_optimize] theorem mul_notation_eq [cap : FloatLib.Floats.ExecFloat.Mul F]
    [Capability.HasSpec cap (NatView.liftBinary (F := F) Model.Spec.mul)]
    (x y : FloatLib.Floats.ExecFloat F) : x * y = mul .nearest x y :=
  mul_eq x y

/-- `x / y` equals the kernel division to nearest even. -/
@[kernel_optimize] theorem div_notation_eq [cap : FloatLib.Floats.ExecFloat.Div F]
    [Capability.HasSpec cap (NatView.liftBinary (F := F) Model.Spec.div)]
    (x y : FloatLib.Floats.ExecFloat F) : x / y = div .nearest x y :=
  div_eq x y

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath

/- `!=` and `compareNotEqual` are negations of the equality test, which `float_decide` unfolds. -/
attribute [kernel_optimize unfold] bne FloatLib.Floats.ExecFloat.compareNotEqual
