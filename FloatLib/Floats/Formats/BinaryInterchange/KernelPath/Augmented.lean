/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.FormatOf
public import FloatLib.Floats.Formats.BinaryInterchange.KernelPath.Status
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Augmented.Runtime
public import FloatLib.Numerics.Kernel.ZProof

/-!
# The augmented operations on encodings

IEEE 754-2019 §9.5 `augmentedAddition`, `augmentedSubtraction` and `augmentedMultiplication`
deliver a head, the exact result rounded to nearest with ties toward zero, and a tail, the
error of that rounding. The reference `Model.augmentedAddition` and its siblings decode two
finite operands, form the exact sum or product, and run `Model.Internal.Status.augmented` on
it, which rounds the head and the tail on the grid of the format.

`augmentedWords fmt exact zeroNegative` is that step with the head and the tail as encodings:
the grid values are the reference's, and each is encoded by `KernelPath.roundDyadic`
(`augmentedWords_eq`). `augmentedAddition fmt a b`, `augmentedSubtraction fmt a b` and
`augmentedMultiplication fmt a b` decode two finite words with `KernelPath.decode` and apply it
to the exact sum or product; a word that is not finite goes to the reference operation.
`augmentedAddition_eq_spec` and its siblings prove them equal to the reference outcomes with
head and tail encoded, flags included, for every format descriptor and all operands.

`Value.augmented` lifts such an operation on encodings to stored values, with the rules
`Value.toNat_head_augmented`, `Value.toNat_tail_augmented` and `Value.status_augmented`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.KernelPath

open FloatLib.Numerics

/--
`value / 2 ^ down` rounded to the nearest natural number, a tie toward zero, for a nonzero
`down` (`shiftTiesTowardZero_eq`): the quotient, and one more when the discarded bits exceed
one half of the last place. A shift beyond the bits of `value` gives zero, and `2 ^ down` is
formed only for a shift within them, so a value far below the grid costs no more than one
near it.
-/
def shiftTiesTowardZero (value down : Nat) : Nat :=
  Bool.casesOn (motive := fun _ => Nat) (Nat.ble down (Kernel.size value))
    0
    (Nat.add (Nat.shiftRight value down)
      (Bool.casesOn (motive := fun _ => Nat)
        (Nat.ble (Nat.succ (Nat.shiftLeft 1 (Nat.sub down 1)))
          (Nat.mod value (Nat.shiftLeft 1 down)))
        0 1))

/-- `shiftTiesTowardZero` is the quotient with its correction, for every shift. -/
theorem shiftTiesTowardZero_eq (value down : Nat) :
    shiftTiesTowardZero value down =
      value >>> down +
        Bool.casesOn (motive := fun _ => Nat)
          (Nat.ble (1 <<< (down - 1) + 1) (value % 1 <<< down)) 0 1 := by
  unfold shiftTiesTowardZero
  cases hnear : Nat.ble down (Kernel.size value)
  · have hfar : Kernel.size value < down := by
      rw [← Nat.not_le]
      intro hle
      rw [Nat.ble_eq_true_of_le hle] at hnear
      exact absurd hnear (by decide)
    have hvalue : value < 2 ^ (down - 1) := by
      have hsize : value < 2 ^ Kernel.size value := by
        rw [Kernel.size_eq]
        exact Nat.lt_size_self value
      exact lt_of_lt_of_le hsize (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hpow : 2 ^ down = 2 * 2 ^ (down - 1) := by
      obtain ⟨n, rfl⟩ : ∃ n, down = n + 1 := ⟨down - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    have hble : Nat.ble (2 ^ (down - 1) + 1) (value % 2 ^ down) = false := by
      rw [Bool.eq_false_iff, Ne, Nat.ble_eq, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow, hble,
      Nat.div_eq_of_lt (show value < 2 ^ down by omega)]
  · rfl

/--
The value of the grid of `fmt` nearest to the exact dyadic `d`, a tie toward zero
(`gridTiesTowardZero_eq`): the target exponent is the exponent of the leading bit less the
fraction width, or the least subnormal exponent, and the significand is shifted to it, with the
discarded bits compared with one half of the last place (`shiftTiesTowardZero`).
-/
def gridTiesTowardZero (fmt : FloatFormat) (d : Numerics.Dyadic) : Numerics.Dyadic :=
  (fun target =>
    (fun down =>
      ⟨d.negative,
        Bool.casesOn (motive := fun _ => Nat) (Nat.beq down 0)
          (shiftTiesTowardZero d.significand down)
          (Nat.shiftLeft d.significand (Kernel.Z.toNat (Kernel.Z.sub d.exponent target))),
        target⟩)
      (Kernel.Z.toNat (Kernel.Z.sub target d.exponent)))
    (Kernel.Z.max
      (Kernel.Z.sub (Kernel.Z.add (Int.ofNat (Kernel.log2 d.significand)) d.exponent)
        (Int.ofNat fmt.fracWidth))
      (Int.subNatNat 1 (Nat.add fmt.exponentBias fmt.fracWidth)))

/--
Whether the magnitude of the exact dyadic `d` exceeds the largest finite value of `fmt`
(`magnitudeOverflows_eq`): the positions of the two leading bits decide unless they coincide,
and only then are the two significands compared on the smaller of the two exponents. So no
shift is longer than a significand, whatever the exponent range of the format.
-/
def magnitudeOverflows (fmt : FloatFormat) (d : Numerics.Dyadic) : Bool :=
  (fun top =>
    (fun shift =>
      (fun lead =>
        Bool.casesOn (motive := fun _ => Bool) (Nat.beq d.significand 0)
          (Bool.casesOn (motive := fun _ => Bool) (Int.beq' lead (Int.ofNat 0))
            (Int.blt' (Int.ofNat 0) lead)
            (Nat.ble
              (Nat.succ (Nat.shiftLeft top.significand (Kernel.Z.toNat (Kernel.Z.neg shift))))
              (Nat.shiftLeft d.significand (Kernel.Z.toNat shift))))
          false)
        (Kernel.Z.add shift
          (Kernel.Z.subNat (Kernel.log2 d.significand) (Kernel.log2 top.significand))))
      (Kernel.Z.sub d.exponent top.exponent))
    (Model.maxFiniteDyadic fmt)

/--
Two nonzero significands at exponents `shift` apart whose leading bits lie at different
positions are ordered as those positions are.
-/
theorem aligned_lt_iff_leading (m t : Nat) (hm : m ≠ 0) (ht : t ≠ 0) (shift : Int)
    (hlead : shift + ((m.log2 : Int) - (t.log2 : Int)) ≠ 0) :
    t <<< (-shift).toNat + 1 ≤ m <<< shift.toNat ↔
      0 < shift + ((m.log2 : Int) - (t.log2 : Int)) := by
  have hmb := (Nat.log2_eq_iff hm).1 rfl
  have htb := (Nat.log2_eq_iff ht).1 rfl
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  generalize ha : (-shift).toNat = a
  generalize hb : shift.toNat = b
  constructor
  · intro hle
    by_contra hneg
    have h1 : m * 2 ^ b < 2 ^ (m.log2 + 1) * 2 ^ b :=
      Nat.mul_lt_mul_of_lt_of_le hmb.2 (Nat.le_refl _) (Nat.two_pow_pos b)
    have h2 : 2 ^ (m.log2 + 1) * 2 ^ b ≤ 2 ^ t.log2 * 2 ^ a := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ t.log2 * 2 ^ a ≤ t * 2 ^ a := Nat.mul_le_mul_right _ htb.1
    exact absurd (Nat.lt_of_succ_le hle) (Nat.lt_asymm (lt_of_lt_of_le h1 (le_trans h2 h3)))
  · intro hpos
    have h1 : t * 2 ^ a < 2 ^ (t.log2 + 1) * 2 ^ a :=
      Nat.mul_lt_mul_of_lt_of_le htb.2 (Nat.le_refl _) (Nat.two_pow_pos a)
    have h2 : 2 ^ (t.log2 + 1) * 2 ^ a ≤ 2 ^ m.log2 * 2 ^ b := by
      rw [← Nat.pow_add, ← Nat.pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ m.log2 * 2 ^ b ≤ m * 2 ^ b := Nat.mul_le_mul_right _ hmb.1
    exact Nat.succ_le_of_lt (lt_of_lt_of_le h1 (le_trans h2 h3))

/-- `gridTiesTowardZero` is the grid value of the reference. -/
theorem gridTiesTowardZero_eq (fmt : FloatFormat) (d : Numerics.Dyadic) :
    gridTiesTowardZero fmt d = Model.tiesTowardZeroGrid fmt d := by
  unfold gridTiesTowardZero Model.tiesTowardZeroGrid
  simp only [Kernel.Z.max_eq, Kernel.Z.sub_eq, Kernel.Z.add_eq, Kernel.Z.toNat_eq,
    subNatNat_minSubnormalExponent, Int.ofNat_eq_natCast, Nat.add_eq, Kernel.log2_eq]
  generalize max ((d.significand.log2 : Int) + d.exponent - (fmt.fracWidth : Int))
    fmt.minSubnormalExponent = target
  congr 1
  unfold Model.roundMantissaAtExponentTiesTowardZero Model.roundMantissaAtExponentEven
  generalize hdown : (target - d.exponent).toNat = down
  by_cases hzero : down = 0
  · subst hzero
    have htie : Numerics.shiftRightIsTie d.significand 0 = false := by
      rw [Bool.eq_false_iff, Ne, Numerics.shiftRightIsTie_eq_true_iff]
      omega
    rw [htie]
    by_cases hle : d.exponent ≤ target
    · have hup : (d.exponent - target).toNat = 0 := by omega
      rw [ite_eq_left hle, hup, Numerics.roundShiftRightEven_eq_roundQuotientEven]
      simp [Numerics.roundQuotientEven, Nat.mod_one]
    · rw [ite_eq_right hle]
      rfl
  · have hbeq : Nat.beq down 0 = false := beq_zero_eq_false hzero
    have hle : d.exponent ≤ target := by omega
    have hpow : 2 ^ down = 2 * 2 ^ (down - 1) := by
      obtain ⟨n, rfl⟩ : ∃ n, down = n + 1 := ⟨down - 1, by omega⟩
      rw [Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
    rw [hbeq, ite_eq_left hle, Numerics.roundShiftRightEven_eq_roundQuotientEven]
    change shiftTiesTowardZero d.significand down = _
    rw [shiftTiesTowardZero_eq]
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.shiftRight_eq_div_pow]
    by_cases htie : Numerics.shiftRightIsTie d.significand down = true
    · have hrest := ((Numerics.shiftRightIsTie_eq_true_iff _ _).mp htie).2
      have hble : Nat.ble (2 ^ (down - 1) + 1) (d.significand % 2 ^ down) = false := by
        rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
        omega
      rw [htie, hble]
      simp
    · have hrest : d.significand % 2 ^ down ≠ 2 ^ (down - 1) := fun h =>
        htie ((Numerics.shiftRightIsTie_eq_true_iff _ _).mpr ⟨by omega, h⟩)
      rw [Bool.not_eq_true] at htie
      rw [htie]
      simp only [Bool.false_eq_true, ite_false, Numerics.roundQuotientEven]
      by_cases hhalf : 2 ^ (down - 1) + 1 ≤ d.significand % 2 ^ down
      · have hble : Nat.ble (2 ^ (down - 1) + 1) (d.significand % 2 ^ down) = true :=
          Nat.ble_eq.mpr hhalf
        rw [hble, ite_eq_right (by omega), ite_eq_left (by omega)]
      · have hble : Nat.ble (2 ^ (down - 1) + 1) (d.significand % 2 ^ down) = false := by
          rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
          exact hhalf
        rw [hble, ite_eq_left (by omega)]
        rfl

/-- `magnitudeOverflows` is the overflow test of the reference. -/
theorem magnitudeOverflows_eq (fmt : FloatFormat) (d : Numerics.Dyadic) :
    magnitudeOverflows fmt d = Model.dyadicMagnitudeOverflows fmt d := by
  have haligned : magnitudeOverflows fmt d =
      Nat.ble
        ((Model.maxFiniteDyadic fmt).significand <<<
          (-(d.exponent - (Model.maxFiniteDyadic fmt).exponent)).toNat + 1)
        (d.significand <<< (d.exponent - (Model.maxFiniteDyadic fmt).exponent).toNat) := by
    have htop : (Model.maxFiniteDyadic fmt).significand ≠ 0 := by
      have hpos := Nat.two_pow_pos fmt.fracWidth
      simp only [Model.maxFiniteDyadic, Model.pow2_eq_two_pow]
      omega
    unfold magnitudeOverflows
    simp only [Kernel.Z.sub_eq, Kernel.Z.neg_eq, Kernel.Z.toNat_eq, Kernel.Z.add_eq,
      Kernel.Z.subNat_eq, Kernel.log2_eq, Int.ofNat_eq_natCast, Nat.cast_zero,
      Nat.succ_eq_add_one, Nat.shiftLeft_eq']
    by_cases hzero : d.significand = 0
    · rw [hzero]
      simp only [Nat.zero_shiftLeft]
      change false = _
      symm
      rw [Bool.eq_false_iff, Ne, Nat.ble_eq]
      exact Nat.not_succ_le_zero _
    · rw [beq_zero_eq_false hzero]
      by_cases hlead : d.exponent - (Model.maxFiniteDyadic fmt).exponent +
          ((d.significand.log2 : Int) - ((Model.maxFiniteDyadic fmt).significand.log2 : Int)) = 0
      · rw [(Kernel.Z.beq'_iff _ _).mpr hlead]
      · have hbeq : Int.beq' (d.exponent - (Model.maxFiniteDyadic fmt).exponent +
            ((d.significand.log2 : Int) -
              ((Model.maxFiniteDyadic fmt).significand.log2 : Int))) 0 = false := by
          rw [Bool.eq_false_iff, Ne, Kernel.Z.beq'_iff]
          exact hlead
        rw [hbeq]
        change Int.blt' 0 _ = _
        rw [Bool.eq_iff_iff, Kernel.Z.blt'_iff, Nat.ble_eq]
        exact (aligned_lt_iff_leading _ _ hzero htop _ hlead).symm
  rw [haligned]
  unfold Model.dyadicMagnitudeOverflows
  generalize htop : Model.maxFiniteDyadic fmt = top
  have hnegative : top.negative = false := by
    rw [← htop]
    rfl
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  have hcompare := cmpDyadic_eq_compare { d with negative := false } top
    (d.significand <<< (d.exponent - top.exponent).toNat)
    (top.significand <<< (-(d.exponent - top.exponent)).toNat) (min d.exponent top.exponent)
    (by
      rw [toRat_mk]
      simp only [Bool.false_eq_true, ite_false, one_mul, Nat.shiftLeft_eq]
      push_cast
      rw [mul_assoc, ← zpow_natCast (2 : ℚ) (d.exponent - top.exponent).toNat,
        ← zpow_add₀ htwo]
      congr 2
      omega)
    (by
      obtain ⟨negative, significand, exponent⟩ := top
      subst hnegative
      rw [toRat_mk]
      simp only [Bool.false_eq_true, ite_false, one_mul, Nat.shiftLeft_eq]
      push_cast
      rw [mul_assoc, ← zpow_natCast (2 : ℚ) (-(d.exponent - exponent)).toNat,
        ← zpow_add₀ htwo]
      congr 2
      omega)
  rw [hcompare, Bool.eq_iff_iff, Nat.ble_eq, beq_iff_eq, Nat.compare_eq_gt]
  exact Iff.rfl

/--
Head, tail and flags of an exact dyadic result, with the head and the tail as encodings
(`augmentedWords_eq`): `Model.Internal.Status.augmented` with the grid values computed by
`gridTiesTowardZero`, the overflow decided by `magnitudeOverflows` and each rounded grid value
encoded by `KernelPath.roundDyadic`.
-/
def augmentedWords (fmt : FloatFormat) (exact : Numerics.Dyadic) (zeroNegative : Bool) :
    AugmentedOutcome Nat :=
  if exact.significand == 0 then
    { head := zeroWord fmt zeroNegative, tail := zeroWord fmt zeroNegative }
  else
    let grid := gridTiesTowardZero fmt exact
    let head := roundDyadic fmt .nearest grid
    if magnitudeOverflows fmt grid then
      { head, tail := head, status := { overflow := true, inexact := true } }
    else
      let error := subExact exact grid
      if error.significand == 0 then
        { head, tail := zeroWord fmt exact.negative }
      else
        let tailGrid := gridTiesTowardZero fmt error
        let inexact := (subExact error tailGrid).significand != 0
        { head, tail := roundDyadic fmt .nearest tailGrid
          status := { underflow := inexact, inexact } }

/-- `augmentedWords` is the reference outcome with its head and its tail encoded. -/
theorem augmentedWords_eq (fmt : FloatFormat) (exact : Numerics.Dyadic) (zeroNegative : Bool) :
    augmentedWords fmt exact zeroNegative =
      (Model.Internal.Status.augmented fmt exact zeroNegative).map Model.toNatBits := by
  unfold augmentedWords Model.Internal.Status.augmented
  simp only [roundDyadic_nearest_eq, zeroWord_eq, subExact_eq, gridTiesTowardZero_eq,
    magnitudeOverflows_eq]
  split_ifs <;> rfl

/--
Head and tail of the sum of the values that `a` and `b` encode, as encodings, with the flags
(`augmentedAddition_eq_spec`).
-/
def augmentedAddition (fmt : FloatFormat) (a b : Nat) : AugmentedOutcome Nat :=
  Bool.casesOn (motive := fun _ => AugmentedOutcome Nat) (bothFinite fmt fmt a b)
    ((Model.augmentedAddition (Model.ofNatBits a : Model fmt) (Model.ofNatBits b)).map
      Model.toNatBits)
    ((fun dx dy => augmentedWords fmt (addExact dx dy) (dx.negative && dy.negative))
      (decode fmt a) (decode fmt b))

/--
Head and tail of the difference of the values that `a` and `b` encode, as encodings, with the
flags: `augmentedAddition` of the negated second operand (`augmentedSubtraction_eq_spec`).
-/
def augmentedSubtraction (fmt : FloatFormat) (a b : Nat) : AugmentedOutcome Nat :=
  augmentedAddition fmt a (neg fmt b)

/--
Head and tail of the product of the values that `a` and `b` encode, as encodings, with the
flags (`augmentedMultiplication_eq_spec`).
-/
def augmentedMultiplication (fmt : FloatFormat) (a b : Nat) : AugmentedOutcome Nat :=
  Bool.casesOn (motive := fun _ => AugmentedOutcome Nat) (bothFinite fmt fmt a b)
    ((Model.augmentedMultiplication (Model.ofNatBits a : Model fmt) (Model.ofNatBits b)).map
      Model.toNatBits)
    ((fun dx dy => augmentedWords fmt (mulExact dx dy) (Bool.xor dx.negative dy.negative))
      (decode fmt a) (decode fmt b))

/--
`augmentedAddition` computes the outcome of `Model.augmentedAddition` with its head and its
tail encoded, for every format descriptor and all operands.
-/
theorem augmentedAddition_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    augmentedAddition fmt x.toNatBits y.toNatBits =
      (Model.augmentedAddition x y).map Model.toNatBits := by
  unfold augmentedAddition
  rw [bothFinite_eq, Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · unfold Model.augmentedAddition
      rw [toDyadic?_eq_decode x hx, toDyadic?_eq_decode y hy]
      simp only [addExact_eq]
      exact augmentedWords_eq fmt _ _

/--
`augmentedSubtraction` computes the outcome of `Model.augmentedSubtraction` with its head and
its tail encoded, for every format descriptor and all operands.
-/
theorem augmentedSubtraction_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    augmentedSubtraction fmt x.toNatBits y.toNatBits =
      (Model.augmentedSubtraction x y).map Model.toNatBits := by
  unfold augmentedSubtraction Model.augmentedSubtraction
  rw [neg_eq_spec, augmentedAddition_eq_spec]

/--
`augmentedMultiplication` computes the outcome of `Model.augmentedMultiplication` with its head
and its tail encoded, for every format descriptor and all operands.
-/
theorem augmentedMultiplication_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    augmentedMultiplication fmt x.toNatBits y.toNatBits =
      (Model.augmentedMultiplication x y).map Model.toNatBits := by
  unfold augmentedMultiplication
  rw [bothFinite_eq, Model.ofNatBits_toNatBits, Model.ofNatBits_toNatBits]
  cases hx : Model.isFinite x
  · rfl
  · cases hy : Model.isFinite y
    · rfl
    · unfold Model.augmentedMultiplication
      rw [toDyadic?_eq_decode x hx, toDyadic?_eq_decode y hy]
      simp only [mulExact_eq]
      exact augmentedWords_eq fmt _ _

namespace Value

universe u

variable {F : Type u} [EncodedFormat F] {format : FloatFormat} [view : NatView F format]

/--
Lift an augmented operation on encodings to stored values. `h` says that `op` computes the
outcome of the model operation `spec` with its head and its tail encoded.
-/
def augmented (op : Nat → Nat → AugmentedOutcome Nat)
    (spec : Model format → Model format → AugmentedOutcome (Model format))
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).map Model.toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) : AugmentedOutcome (FloatLib.Floats.ExecFloat F) :=
  { head := nullary (op (toNat x) (toNat y)).head
      (spec (view.toModel x.raw) (view.toModel y.raw)).head
      (by rw [toNat_eq, toNat_eq, h]; rfl)
    tail := nullary (op (toNat x) (toNat y)).tail
      (spec (view.toModel x.raw) (view.toModel y.raw)).tail
      (by rw [toNat_eq, toNat_eq, h]; rfl)
    status := (op (toNat x) (toNat y)).status }

/-- A lifted augmented operation is the model outcome carried through the conversions. -/
theorem augmented_eq (op : Nat → Nat → AugmentedOutcome Nat)
    (spec : Model format → Model format → AugmentedOutcome (Model format))
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).map Model.toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    augmented op spec h x y =
      (spec (view.toModel x.raw) (view.toModel y.raw)).map
        fun value => FloatLib.Floats.ExecFloat.ofRaw (view.ofModel value) := by
  unfold augmented AugmentedOutcome.map
  rw [nullary_eq, nullary_eq, toNat_eq, toNat_eq, h]
  rfl

/-- The encoding of the head of a lifted outcome is the head on the encodings. -/
@[kernel_optimize] theorem toNat_head_augmented (op : Nat → Nat → AugmentedOutcome Nat)
    (spec : Model format → Model format → AugmentedOutcome (Model format))
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).map Model.toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    toNat (augmented op spec h x y).head = (op (toNat x) (toNat y)).head :=
  view.toNat_ofNat _ _

/-- The encoding of the tail of a lifted outcome is the tail on the encodings. -/
@[kernel_optimize] theorem toNat_tail_augmented (op : Nat → Nat → AugmentedOutcome Nat)
    (spec : Model format → Model format → AugmentedOutcome (Model format))
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).map Model.toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    toNat (augmented op spec h x y).tail = (op (toNat x) (toNat y)).tail :=
  view.toNat_ofNat _ _

/-- The flags of a lifted outcome are the flags on the encodings. -/
@[kernel_optimize] theorem status_augmented (op : Nat → Nat → AugmentedOutcome Nat)
    (spec : Model format → Model format → AugmentedOutcome (Model format))
    (h : ∀ x y, op x.toNatBits y.toNatBits = (spec x y).map Model.toNatBits)
    (x y : FloatLib.Floats.ExecFloat F) :
    (augmented op spec h x y).status = (op (toNat x) (toNat y)).status :=
  rfl

end Value

end FloatLib.Floats.Formats.BinaryInterchange.KernelPath
