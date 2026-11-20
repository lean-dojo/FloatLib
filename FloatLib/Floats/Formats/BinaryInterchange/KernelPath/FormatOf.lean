/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Div
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Exact
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Lift
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.Proof

/-!
# The formatOf operations on encodings

IEEE 754-2019 §5.4.1 specifies its arithmetic as formatOf operations: the operands may have any
formats, and the exact result is rounded once into the destination. `Model.formatOfAddition`,
`formatOfSubtraction`, `formatOfMultiplication`, `formatOfDivision` and
`formatOfFusedMultiplyAdd` are these operations between any three or four format descriptors.

`formatOfAddition left right destination mode a b` and its siblings compute the encoding of the
delivered value from the encodings of the operands. For finite operands (and, for the division,
a nonzero dividend and divisor) the operands are decoded with `KernelPath.decode`, the exact
sum or product is formed on the decoded values, and `KernelPath.roundDyadic` rounds it once;
the quotient is rounded by `roundRatio`, the division core of `KernelPath.Div` on two
significands shifted to one width. Any other operand goes to the reference operation on the
decoded words, whose NaN and infinity rules do not depend on the kernel path.

`formatOfAddition_eq_spec` and its siblings prove each form equal to the encoding of the value
of the reference operation, for all format descriptors, every rounding direction and all
operands.

`Value.binaryInto` and `Value.ternaryInto` lift an operation on encodings to stored values of
any families, with the rules `Value.toNat_binaryInto` and `Value.toNat_ternaryInto`: the
encoding of the result is the operation on the encodings of the operands.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics
open Model.Reduction.Internal (Factor)

variable {left right addend destination : FloatFormat}

/--
Encoding of the value delivered for a finite exact result (`deliverFinite_eq`): the zero of
sign `zeroNegative` for an exact zero, and one rounding in `mode` otherwise.
-/
def deliverFinite (destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (zeroNegative : Bool) (exact : Numerics.Dyadic) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.beq exact.significand 0)
    (roundDyadic destination mode exact) (zeroWord destination zeroNegative)

/-- `deliverFinite` is the encoding of the value that the reference delivers. -/
theorem deliverFinite_eq (mode : Model.IEEERoundingMode) (zeroNegative : Bool)
    (exact : Numerics.Dyadic) :
    deliverFinite destination mode zeroNegative exact =
      ((Factor.finite exact : Factor destination).deliver mode zeroNegative).value.toNatBits := by
  unfold deliverFinite
  rw [Model.Reduction.Internal.Factor.deliver_finite_value, roundDyadic_eq]
  by_cases hzero : exact.significand = 0
  · rw [hzero, ite_eq_left rfl]
    exact zeroWord_eq destination zeroNegative
  · rw [ite_eq_right hzero, beq_zero_eq_false hzero]

/--
Encoding of `± mx / my * 2 ^ e` rounded into `fmt` in the direction `mode`, for nonzero `mx` and
`my` (`roundRatio_eq`): the two significands are shifted to one width and rounded by `divCore`.
-/
def roundRatio (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (mx my : Nat) (e : Int) : Nat :=
  (fun lx ly =>
    (fun t =>
      divCore fmt mode (signNat negative) (Nat.shiftLeft mx ly) (Nat.shiftLeft my lx)
        (Kernel.Z.toNat t) (Kernel.Z.toNat (Kernel.Z.neg t)) 0 0)
      (Kernel.Z.add (Kernel.Z.sub e (Int.ofNat ly)) (Int.ofNat lx)))
    (Numerics.Kernel.size mx) (Numerics.Kernel.size my)

/-- A nonzero number shifted left by `k` places has `k` more bits. -/
theorem shiftLeft_size_bounds {m : Nat} (hm : m ≠ 0) (k : Nat) :
    2 ^ (m.size + k - 1) ≤ m <<< k ∧ m <<< k < 2 ^ (m.size + k - 1 + 1) := by
  have hsize : 0 < m.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hm)
  have hlow : 2 ^ (m.size - 1) ≤ m := Nat.lt_size.mp (by omega)
  have hhigh : m < 2 ^ m.size := Nat.lt_size_self m
  have hexp : m.size + k - 1 = m.size - 1 + k := by omega
  have hexp' : m.size - 1 + k + 1 = m.size + k := by omega
  rw [Nat.shiftLeft_eq, hexp, hexp', Nat.pow_add, Nat.pow_add]
  exact ⟨Nat.mul_le_mul_right _ hlow, Nat.mul_lt_mul_of_pos_right hhigh (Nat.two_pow_pos _)⟩

/--
`roundRatio` computes the encoding of the reference rounding of a scaled quotient, for every
format descriptor, rounding direction and sign, and all nonzero significands.
-/
theorem roundRatio_eq (fmt : FloatFormat) (mode : Model.IEEERoundingMode) (negative : Bool)
    (mx my : Nat) (e : Int) (hmx : mx ≠ 0) (hmy : my ≠ 0) :
    roundRatio fmt mode negative mx my e =
      (Model.Internal.Directed.roundRatScaled fmt mode negative mx my e).toNatBits := by
  have hna := shiftLeft_size_bounds hmx my.size
  have hnb := shiftLeft_size_bounds hmy mx.size
  rw [Nat.add_comm my.size mx.size] at hnb
  unfold roundRatio
  simp only [Numerics.Kernel.size_eq, Nat.shiftLeft_eq', Kernel.Z.add_eq, Kernel.Z.sub_eq,
    Kernel.Z.neg_eq, Kernel.Z.toNat_eq]
  rw [divCore_eq fmt mode negative (mx.size + my.size - 1) (signNat negative) _ _ _ _ _ rfl
      (Or.inr hna) hnb,
    ite_eq_right (by have := Nat.two_pow_pos (mx.size + my.size - 1); omega),
    ← directedRat_shiftLeft fmt mode negative (mx.size + my.size - 1) mx my my.size mx.size e
      hmx hmy hna hnb]
  congr 2
  change ((e - (my.size : Int) + (mx.size : Int)).toNat : Int) -
    ((-(e - (my.size : Int) + (mx.size : Int))).toNat : Int) = _
  omega

/-- Whether the words `a` of `left` and `b` of `right` are both finite. -/
def bothFinite (left right : FloatFormat) (a b : Nat) : Bool :=
  Bool.casesOn (motive := fun _ => Bool) (Nat.beq (finiteCode left a) 1) false
    (Nat.beq (finiteCode right b) 1)

/-- `bothFinite` holds exactly when both values are finite. -/
theorem bothFinite_eq (x : Model left) (y : Model right) :
    bothFinite left right x.toNatBits y.toNatBits = (Model.isFinite x && Model.isFinite y) := by
  unfold bothFinite
  rw [finiteCode_eq, finiteCode_eq]
  cases Model.isFinite x <;> rfl

/--
Encoding in `destination` of the sum of the values that `a` encodes in `left` and `b` in
`right`, rounded once in the direction `mode` (`formatOfAddition_eq_spec`).
-/
def formatOfAddition (left right destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (bothFinite left right a b)
    (Model.formatOfAddition destination (Model.ofNatBits a : Model left)
      (Model.ofNatBits b : Model right) mode).value.toNatBits
    (deliverFinite destination mode
      (mode.zeroSumSign (Nat.beq (signCode left a) 1) (Nat.beq (signCode right b) 1))
      (addExact (decode left a) (decode right b)))

/--
Encoding in `destination` of the difference of the values that `a` encodes in `left` and `b`
in `right`, rounded once in the direction `mode`: `formatOfAddition` of the negated second
operand (`formatOfSubtraction_eq_spec`).
-/
def formatOfSubtraction (left right destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b : Nat) : Nat :=
  formatOfAddition left right destination mode a (neg right b)

/--
Encoding in `destination` of the product of the values that `a` encodes in `left` and `b` in
`right`, rounded once in the direction `mode` (`formatOfMultiplication_eq_spec`).
-/
def formatOfMultiplication (left right destination : FloatFormat)
    (mode : Model.IEEERoundingMode) (a b : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (bothFinite left right a b)
    (Model.formatOfMultiplication destination (Model.ofNatBits a : Model left)
      (Model.ofNatBits b : Model right) mode).value.toNatBits
    (deliverFinite destination mode
      (Bool.xor (Nat.beq (signCode left a) 1) (Nat.beq (signCode right b) 1))
      (mulExact (decode left a) (decode right b)))

/--
Encoding in `destination` of `x * y + z` for the values that `a`, `b` and `c` encode in `left`,
`right` and `addend`, rounded once in the direction `mode`
(`formatOfFusedMultiplyAdd_eq_spec`).
-/
def formatOfFusedMultiplyAdd (left right addend destination : FloatFormat)
    (mode : Model.IEEERoundingMode) (a b c : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat)
    (Bool.casesOn (motive := fun _ => Bool) (bothFinite left right a b) false
      (Nat.beq (finiteCode addend c) 1))
    (Model.formatOfFusedMultiplyAdd destination (Model.ofNatBits a : Model left)
      (Model.ofNatBits b : Model right) (Model.ofNatBits c : Model addend) mode).value.toNatBits
    (deliverFinite destination mode
      (mode.zeroSumSign
        (Bool.xor (Nat.beq (signCode left a) 1) (Nat.beq (signCode right b) 1))
        (Nat.beq (signCode addend c) 1))
      (addExact (mulExact (decode left a) (decode right b)) (decode addend c)))

/--
Encoding in `destination` of the quotient of the values that `a` encodes in `left` and `b` in
`right`, rounded once in the direction `mode` (`formatOfDivision_eq_spec`).
-/
def formatOfDivision (left right destination : FloatFormat) (mode : Model.IEEERoundingMode)
    (a b : Nat) : Nat :=
  (fun dx dy =>
    Bool.casesOn (motive := fun _ => Nat)
      (Bool.casesOn (motive := fun _ => Bool) (bothFinite left right a b) false
        (Bool.casesOn (motive := fun _ => Bool) (Nat.beq dx.significand 0)
          (Bool.casesOn (motive := fun _ => Bool) (Nat.beq dy.significand 0) true false)
          false))
      (Model.formatOfDivision destination (Model.ofNatBits a : Model left)
        (Model.ofNatBits b : Model right) mode).value.toNatBits
      (roundRatio destination mode
        (Bool.xor (Nat.beq (signCode left a) 1) (Nat.beq (signCode right b) 1))
        dx.significand dy.significand (Kernel.Z.sub dx.exponent dy.exponent)))
    (decode left a) (decode right b)

/--
`formatOfAddition` computes the encoding of the value of `Model.formatOfAddition`, for all
format descriptors, every rounding direction and all operands.
-/
theorem formatOfAddition_eq_spec (mode : Model.IEEERoundingMode) (x : Model left)
    (y : Model right) :
    formatOfAddition left right destination mode x.toNatBits y.toNatBits =
      (Model.formatOfAddition destination x y mode).value.toNatBits := by
  unfold formatOfAddition
  rw [bothFinite_eq, signCode_eq, signCode_eq, Model.ofNatBits_toNatBits,
    Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · rw [Model.formatOfAddition_of_toDyadic?_eq_some (toDyadic?_eq_decode x hx)
        (toDyadic?_eq_decode y hy) mode, addExact_eq]
      exact deliverFinite_eq mode _ _

/--
`formatOfSubtraction` computes the encoding of the value of `Model.formatOfSubtraction`, for
all format descriptors, every rounding direction and all operands.
-/
theorem formatOfSubtraction_eq_spec (mode : Model.IEEERoundingMode) (x : Model left)
    (y : Model right) :
    formatOfSubtraction left right destination mode x.toNatBits y.toNatBits =
      (Model.formatOfSubtraction destination x y mode).value.toNatBits := by
  unfold formatOfSubtraction Model.formatOfSubtraction
  rw [neg_eq_spec, formatOfAddition_eq_spec]

/--
`formatOfMultiplication` computes the encoding of the value of `Model.formatOfMultiplication`,
for all format descriptors, every rounding direction and all operands.
-/
theorem formatOfMultiplication_eq_spec (mode : Model.IEEERoundingMode) (x : Model left)
    (y : Model right) :
    formatOfMultiplication left right destination mode x.toNatBits y.toNatBits =
      (Model.formatOfMultiplication destination x y mode).value.toNatBits := by
  unfold formatOfMultiplication
  rw [bothFinite_eq, signCode_eq, signCode_eq, Model.ofNatBits_toNatBits,
    Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · rw [Model.formatOfMultiplication_of_toDyadic?_eq_some (toDyadic?_eq_decode x hx)
        (toDyadic?_eq_decode y hy) mode, mulExact_eq]
      exact deliverFinite_eq mode _ _

/--
`formatOfFusedMultiplyAdd` computes the encoding of the value of
`Model.formatOfFusedMultiplyAdd`, for all format descriptors, every rounding direction and all
operands.
-/
theorem formatOfFusedMultiplyAdd_eq_spec (mode : Model.IEEERoundingMode) (x : Model left)
    (y : Model right) (z : Model addend) :
    formatOfFusedMultiplyAdd left right addend destination mode x.toNatBits y.toNatBits
        z.toNatBits =
      (Model.formatOfFusedMultiplyAdd destination x y z mode).value.toNatBits := by
  unfold formatOfFusedMultiplyAdd
  rw [bothFinite_eq, finiteCode_eq, signCode_eq, signCode_eq, signCode_eq,
    Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · cases hz : Model.isFinite z
      · rfl
      · rw [Model.formatOfFusedMultiplyAdd_of_toDyadic?_eq_some (toDyadic?_eq_decode x hx)
          (toDyadic?_eq_decode y hy) (toDyadic?_eq_decode z hz) mode, addExact_eq, mulExact_eq]
        exact deliverFinite_eq mode _ _

/--
`formatOfDivision` computes the encoding of the value of `Model.formatOfDivision`, for all
format descriptors, every rounding direction and all operands.
-/
theorem formatOfDivision_eq_spec (mode : Model.IEEERoundingMode) (x : Model left)
    (y : Model right) :
    formatOfDivision left right destination mode x.toNatBits y.toNatBits =
      (Model.formatOfDivision destination x y mode).value.toNatBits := by
  unfold formatOfDivision
  simp only [bothFinite_eq, signCode_eq, Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · by_cases hx0 : (decode left x.toNatBits).significand = 0
      · rw [hx0]
        rfl
      · by_cases hy0 : (decode right y.toNatBits).significand = 0
        · rw [hy0, beq_zero_eq_false hx0]
          rfl
        · rw [beq_zero_eq_false hx0, beq_zero_eq_false hy0, Kernel.Z.sub_eq,
            Model.formatOfDivision_value_of_toDyadic?_eq_some (toDyadic?_eq_decode x hx)
              (toDyadic?_eq_decode y hy) hx0 hy0 mode]
          exact roundRatio_eq destination mode _ _ _ _ hx0 hy0

namespace Value

universe u v w t

variable {F : Type u} [EncodedFormat F] [leftView : NatView F left]
variable {G : Type v} [EncodedFormat G] [rightView : NatView G right]
variable {H : Type w} [EncodedFormat H] [addendView : NatView H addend]
variable {D : Type t} [EncodedFormat D] [view : NatView D destination]

/--
Lift an operation on encodings of two formats to stored values, with the result stored in a
third family. `h` says that `op` computes the encodings of the model operation `spec`.
-/
def binaryInto (op : Nat → Nat → Nat) (spec : Model left → Model right → Model destination)
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x : FloatLib.Floats.ExecFloat F) (y : FloatLib.Floats.ExecFloat G) :
    FloatLib.Floats.ExecFloat D :=
  nullary (op (toNat x) (toNat y)) (spec (leftView.toModel x.raw) (rightView.toModel y.raw))
    (by rw [toNat_eq, toNat_eq]; exact h _ _)

/-- A lifted operation is the model operation carried through the families' conversions. -/
theorem binaryInto_eq (op : Nat → Nat → Nat)
    (spec : Model left → Model right → Model destination)
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x : FloatLib.Floats.ExecFloat F) (y : FloatLib.Floats.ExecFloat G) :
    (binaryInto op spec h x y : FloatLib.Floats.ExecFloat D) =
      FloatLib.Floats.ExecFloat.ofRaw
        (view.ofModel (spec (leftView.toModel x.raw) (rightView.toModel y.raw))) :=
  nullary_eq _ _ _

/-- The encoding of a lifted result is the operation on the encodings of the operands. -/
@[kernel_optimize] theorem toNat_binaryInto (op : Nat → Nat → Nat)
    (spec : Model left → Model right → Model destination)
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).toNatBits)
    (x : FloatLib.Floats.ExecFloat F) (y : FloatLib.Floats.ExecFloat G) :
    toNat (binaryInto op spec h x y : FloatLib.Floats.ExecFloat D) = op (toNat x) (toNat y) :=
  toNat_nullary _ _ _

/--
Lift an operation on encodings of three formats to stored values, with the result stored in a
fourth family. `h` says that `op` computes the encodings of the model operation `spec`.
-/
def ternaryInto (op : Nat → Nat → Nat → Nat)
    (spec : Model left → Model right → Model addend → Model destination)
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x : FloatLib.Floats.ExecFloat F) (y : FloatLib.Floats.ExecFloat G)
    (z : FloatLib.Floats.ExecFloat H) : FloatLib.Floats.ExecFloat D :=
  nullary (op (toNat x) (toNat y) (toNat z))
    (spec (leftView.toModel x.raw) (rightView.toModel y.raw) (addendView.toModel z.raw))
    (by rw [toNat_eq, toNat_eq, toNat_eq]; exact h _ _ _)

/-- A lifted operation is the model operation carried through the families' conversions. -/
theorem ternaryInto_eq (op : Nat → Nat → Nat → Nat)
    (spec : Model left → Model right → Model addend → Model destination)
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x : FloatLib.Floats.ExecFloat F) (y : FloatLib.Floats.ExecFloat G)
    (z : FloatLib.Floats.ExecFloat H) :
    (ternaryInto op spec h x y z : FloatLib.Floats.ExecFloat D) =
      FloatLib.Floats.ExecFloat.ofRaw
        (view.ofModel (spec (leftView.toModel x.raw) (rightView.toModel y.raw)
          (addendView.toModel z.raw))) :=
  nullary_eq _ _ _

/-- The encoding of a lifted result is the operation on the encodings of the operands. -/
@[kernel_optimize] theorem toNat_ternaryInto (op : Nat → Nat → Nat → Nat)
    (spec : Model left → Model right → Model addend → Model destination)
    (h : ∀ x y z, op x.toNatBits y.toNatBits z.toNatBits = (spec x y z).toNatBits)
    (x : FloatLib.Floats.ExecFloat F) (y : FloatLib.Floats.ExecFloat G)
    (z : FloatLib.Floats.ExecFloat H) :
    toNat (ternaryInto op spec h x y z : FloatLib.Floats.ExecFloat D) =
      op (toNat x) (toNat y) (toNat z) :=
  toNat_nullary _ _ _

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
