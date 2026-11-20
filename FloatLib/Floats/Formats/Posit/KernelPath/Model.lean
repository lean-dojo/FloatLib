/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Kernel.Plumbing
public import FloatLib.Floats.Formats.Posit.Cast.Integer.Unsigned.Proof
public import FloatLib.Floats.Formats.Posit.KernelPath.Flat
public import FloatLib.Floats.Formats.Posit.KernelPath.Integer
public import FloatLib.Floats.Formats.Posit.KernelPath.Standard
public import FloatLib.Numerics.Kernel.ZProof
public import FloatLib.Tactic.KernelOptimize

/-!
# Kernel rules for posit words

These are the equations that `float_decide` rewrites a posit computation with, so that Lean's
kernel evaluates it on natural-number encodings. Each holds for every Posit Standard (2022)
width and every operand:

* `add_eq_kernel` to `fma_eq_kernel`: the direct reference operation on two words
  (`Model.DirectDyadicArithmetic`, which the public operations of every posit carrier unfold to)
  is the word that stores the flat operation of `KernelPath.Flat` on the two encodings;
* `toNatBits_ofNatBits_kernel`: the encoding of a stored natural number is that number reduced
  to the width, so a nested computation stays on natural numbers;
* `negate_eq_kernel`, `abs_eq_kernel`, `next_eq_kernel`, `prior_eq_kernel` (§5.2) and
  `pₘToₙ_eq_kernel` (§6.1): negation, absolute value, the neighbouring words and the change of
  width;
* `compareLess_eq_kernel` and its five siblings (§5.3), `eq_iff_toNatBits_eq`,
  `lt_iff_kernel` and `le_iff_kernel`: comparisons, equality and the order of words are tests
  on the encodings;
* `roundRat_ratio_kernel`: the rounding of a ratio of natural numbers (§4.1), which the literal
  rules of `Posit.Configured.KernelPath` use;
* `ofFixedInt_eq_kernel` and `ofUnsigned_eq_kernel` (§6.4): the conversion of a signed and of an
  unsigned integer of any positive width is the flat rounding of the magnitude of its word, and
  NaR for the word with only its most significant bit set. `fixedInt_toNatBits_ofNatBits` and
  `fixedInt_toNatBits_ofInt` read the word of a fixed-width integer built from a number;
* `toFixedInt_eq_kernel` and `toUnsigned_eq_kernel` (§6.4): the conversion to a signed and to
  an unsigned integer of any positive width is the word that `Flat.toSigned` and
  `Flat.toUnsigned` compute on the encoding (`KernelPath.Integer`).
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.KernelPath

open FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- The encoding of the word that stores `a` is `a` reduced to the width, in the form that the
kernel computes. -/
@[kernel_optimize] theorem toNatBits_ofNatBits_kernel (a : Nat) :
    (Model.ofNatBits a : Model format).toNatBits = Nat.mod a (Nat.pow 2 format.bits) :=
  BitVec.toNat_ofNat ..

/-- Posit Standard (2022), §5.4: the direct addition is the flat addition on encodings. -/
@[kernel_optimize (cost := 260)] theorem add_eq_kernel (x y : Model format) :
    DirectDyadicArithmetic.add x y =
      Model.ofNatBits (Flat.add format.payloadBits 2 x.toNatBits y.toNatBits) := by
  rw [Flat.add_eq, add_eq_spec, ofNatBits_toNatBits, DirectDyadicArithmetic.add_eq_spec]

/-- Posit Standard (2022), §5.4: the direct subtraction is the flat subtraction on encodings. -/
@[kernel_optimize (cost := 260)] theorem sub_eq_kernel (x y : Model format) :
    DirectDyadicArithmetic.sub x y =
      Model.ofNatBits (Flat.sub format.payloadBits 2 x.toNatBits y.toNatBits) := by
  rw [Flat.sub_eq, sub_eq_spec, ofNatBits_toNatBits, DirectDyadicArithmetic.sub_eq_spec]

/-- Posit Standard (2022), §5.4: the direct multiplication is the flat multiplication on
encodings. -/
@[kernel_optimize (cost := 240)] theorem mul_eq_kernel (x y : Model format) :
    DirectDyadicArithmetic.mul x y =
      Model.ofNatBits (Flat.mul format.payloadBits 2 x.toNatBits y.toNatBits) := by
  rw [Flat.mul_eq, mul_eq_spec, ofNatBits_toNatBits, DirectDyadicArithmetic.mul_eq_spec]

/-- Posit Standard (2022), §5.4: the direct division is the flat division on encodings. -/
@[kernel_optimize (cost := 280)] theorem div_eq_kernel (x y : Model format) :
    DirectDyadicArithmetic.div x y =
      Model.ofNatBits (Flat.div format.payloadBits 2 x.toNatBits y.toNatBits) := by
  rw [Flat.div_eq, div_eq_spec, ofNatBits_toNatBits, DirectDyadicArithmetic.div_eq_spec]

/-- Posit Standard (2022), §5.5: the direct square root is the flat square root on encodings. -/
@[kernel_optimize (cost := 330)] theorem sqrt_eq_kernel (x : Model format) :
    DirectDyadicArithmetic.sqrt x =
      Model.ofNatBits (Flat.sqrt format.payloadBits 2 x.toNatBits) := by
  rw [Flat.sqrt_eq, sqrt_eq_spec, ofNatBits_toNatBits, DirectDyadicArithmetic.sqrt_eq_spec]

/-- FloatLib FMA extension with Posit Standard (2022), §4.1 rounding: the direct fused
multiply-add is the flat one on encodings. -/
@[kernel_optimize (cost := 330)] theorem fma_eq_kernel (x y z : Model format) :
    DirectDyadicArithmetic.fma x y z =
      Model.ofNatBits (Flat.fma format.payloadBits 2 x.toNatBits y.toNatBits z.toNatBits) := by
  rw [Flat.fma_eq, fma_eq_spec, ofNatBits_toNatBits, DirectDyadicArithmetic.fma_eq_spec]

/-! ## Negation, neighbours and change of width -/

/-- Posit Standard (2022), §5.2: negation is the two's complement of the encoding. -/
@[kernel_optimize (cost := 20)] theorem negate_eq_kernel (x : Model format) :
    Model.negate x = Model.ofNatBits (neg format.payloadBits x.toNatBits) := by
  rw [neg_eq, ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.2: the absolute value is the encoding, negated from the sign bit
on. -/
@[kernel_optimize (cost := 30)] theorem abs_eq_kernel (x : Model format) :
    Model.abs x = Model.ofNatBits (KernelPath.abs format.payloadBits x.toNatBits) := by
  rw [abs_eq, ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.2: the next word is the next encoding, wrapping. -/
@[kernel_optimize (cost := 20)] theorem next_eq_kernel (x : Model format) :
    Model.next x = Model.ofNatBits (KernelPath.next format.payloadBits x.toNatBits) := by
  rw [next_eq, ofNatBits_toNatBits]

/-- Posit Standard (2022), §5.2: the previous word is the previous encoding, wrapping. -/
@[kernel_optimize (cost := 20)] theorem prior_eq_kernel (x : Model format) :
    Model.prior x = Model.ofNatBits (KernelPath.prior format.payloadBits x.toNatBits) := by
  rw [prior_eq, ofNatBits_toNatBits]

/-- Posit Standard (2022), §6.1: the conversion between two widths is the flat change of width
on the encoding. -/
@[kernel_optimize (cost := 200)] theorem pₘToₙ_eq_kernel {source : Format} (target : Format)
    (x : Model source) :
    pₘToₙ target x = Model.ofNatBits
      (Flat.cast source.payloadBits 2 target.payloadBits 2 x.toNatBits) := by
  rw [Flat.cast_eq, cast_eq_spec, ofNatBits_toNatBits]

/-! ## Comparisons -/

/-- Posit Standard (2022), §5.3: strict less-than is `lt` on the encodings. -/
@[kernel_optimize (cost := 20)] theorem compareLess_eq_kernel (x y : Model format) :
    Model.compareLess x y = lt format.payloadBits x.toNatBits y.toNatBits :=
  (lt_eq x y).symm

/-- Posit Standard (2022), §5.3: less-or-equal is `le` on the encodings. -/
@[kernel_optimize (cost := 20)] theorem compareLessEqual_eq_kernel (x y : Model format) :
    Model.compareLessEqual x y = le format.payloadBits x.toNatBits y.toNatBits :=
  (le_eq x y).symm

/-- Posit Standard (2022), §5.3: strict greater-than is `lt` on the swapped encodings. -/
@[kernel_optimize (cost := 20)] theorem compareGreater_eq_kernel (x y : Model format) :
    Model.compareGreater x y = lt format.payloadBits y.toNatBits x.toNatBits :=
  (lt_eq y x).symm

/-- Posit Standard (2022), §5.3: greater-or-equal is `le` on the swapped encodings. -/
@[kernel_optimize (cost := 20)] theorem compareGreaterEqual_eq_kernel (x y : Model format) :
    Model.compareGreaterEqual x y = le format.payloadBits y.toNatBits x.toNatBits :=
  (le_eq y x).symm

/-- Two words are equal exactly when their encodings are. -/
@[kernel_optimize] theorem eq_iff_toNatBits_eq (x y : Model format) :
    x = y ↔ x.toNatBits = y.toNatBits :=
  ⟨fun h => h ▸ rfl, fun h => by rw [← ofNatBits_toNatBits x, h, ofNatBits_toNatBits]⟩

/-- Posit Standard (2022), §5.3: equality of words is equality of the encodings. -/
@[kernel_optimize (cost := 10)] theorem compareEqual_eq_kernel (x y : Model format) :
    Model.compareEqual x y = Nat.beq x.toNatBits y.toNatBits := by
  rw [Bool.eq_iff_iff, compareEqual_eq_true_iff, Nat.beq_eq, eq_iff_toNatBits_eq]

/-- Posit Standard (2022), §5.3: inequality of words is inequality of the encodings. -/
@[kernel_optimize (cost := 10)] theorem compareNotEqual_eq_kernel (x y : Model format) :
    Model.compareNotEqual x y = Bool.not (Nat.beq x.toNatBits y.toNatBits) := by
  rw [← compareEqual_eq_kernel]
  rfl

/-- Posit Standard (2022), §5.3: the strict order of words is `lt` on the encodings. -/
@[kernel_optimize] theorem lt_iff_kernel (x y : Model format) :
    x < y ↔ lt format.payloadBits x.toNatBits y.toNatBits = true := by
  rw [lt_eq, compareLess_eq_true_iff]

/-- Posit Standard (2022), §5.3: the order of words is `le` on the encodings. -/
@[kernel_optimize] theorem le_iff_kernel (x y : Model format) :
    x ≤ y ↔ le format.payloadBits x.toNatBits y.toNatBits = true := by
  rw [le_eq, compareLessEqual_eq_true_iff]

/-! ## Rounding a ratio -/

/-- Posit Standard (2022), §4.1: the rounding of a ratio of natural numbers with a sign is the
word that stores the flat rounding, for every nonzero denominator. -/
theorem roundRat_ratio_kernel (format : Format) (negative : Bool) (num den : Nat)
    (hden : den ≠ 0) :
    roundRat format ((if negative then -(num : Rat) else (num : Rat)) / (den : Rat)) =
      Model.ofNatBits (Flat.ofRatio format.payloadBits 2 (if negative then 1 else 0) num den) := by
  rw [Flat.ofRatio_eq, ofRatio_eq format negative num den hden]

/-! ## Integers -/

open FloatLib.Numerics.Representations in
/-- The word of a fixed-width integer built from a natural number is its remainder, by the
kernel's functions. -/
@[kernel_optimize (cost := 2)] theorem fixedInt_toNatBits_ofNatBits {width : Nat} (n : Nat) :
    (FixedInt.ofNatBits n : FixedInt width).toNatBits = Nat.mod n (Nat.pow 2 width) :=
  BitVec.toNat_ofNat ..

open FloatLib.Numerics.Representations FloatLib.Numerics.Kernel in
/-- The word of a fixed-width integer built from an integer is its remainder, by the kernel
arithmetic of `Int`. -/
@[kernel_optimize (cost := 30)] theorem fixedInt_toNatBits_ofInt {width : Nat} (i : Int) :
    (FixedInt.ofInt i : FixedInt width).toNatBits =
      Z.toNat (Z.emod i (Int.ofNat (Nat.pow 2 width))) := by
  rw [Z.toNat_eq, Z.emod_eq]
  exact BitVec.toNat_ofInt i

/-- NaR is the word of the kernel's NaR encoding. -/
theorem nar_eq_ofNatBits (format : Format) :
    Model.nar format = Model.ofNatBits (nar format.payloadBits) := by
  rw [nar_eq]
  rfl

open FloatLib.Numerics.Representations in
/-- Posit Standard (2022), §6.4: the conversion of a signed integer is NaR for the word with
only its most significant bit set, and otherwise the flat rounding of the magnitude that the
two's-complement word denotes, with its sign. It holds for every posit format and every
positive integer width. -/
@[kernel_optimize (cost := 150)] theorem ofFixedInt_eq_kernel (format : Format) {width : Nat}
    (value : FixedInt width) (hwidth : 0 < width) :
    Model.ofFixedInt format value hwidth =
      Model.ofNatBits
        (Bool.rec (motive := fun _ => Nat)
          (Bool.rec (motive := fun _ => Nat)
            (Flat.ofRatio format.payloadBits 2 0 value.toNatBits 1)
            (Flat.ofRatio format.payloadBits 2 1 (Nat.sub (Nat.pow 2 width) value.toNatBits) 1)
            (Nat.ble (Nat.pow 2 (Nat.sub width 1)) value.toNatBits))
          (nar format.payloadBits)
          (Nat.beq value.toNatBits (Nat.pow 2 (Nat.sub width 1)))) := by
  have hlt : value.toNatBits < 2 ^ width := value.toNatBits_lt_modulus
  have hpow : 2 ^ width = 2 * 2 ^ (width - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  have hint : value.toInt =
      if 2 * value.toNatBits < 2 ^ width then (value.toNatBits : Int)
      else (value.toNatBits : Int) - ((2 ^ width : Nat) : Int) :=
    BitVec.toInt_eq_toNat_cond value.bits
  unfold Model.ofFixedInt
  change _ = Model.ofNatBits
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat)
        (Flat.ofRatio format.payloadBits 2 0 value.toNatBits 1)
        (Flat.ofRatio format.payloadBits 2 1 (2 ^ width - value.toNatBits) 1)
        (Nat.ble (2 ^ (width - 1)) value.toNatBits))
      (nar format.payloadBits)
      (Nat.beq value.toNatBits (2 ^ (width - 1))))
  cases hb : Nat.beq value.toNatBits (2 ^ (width - 1))
  · have hne : value ≠ FixedInt.minCode width := fun h => by
      rw [h, integerSentinel_toNatBits hwidth, Nat.beq_refl] at hb
      cases hb
    rw [ite_eq_right hne]
    cases hs : Nat.ble (2 ^ (width - 1)) value.toNatBits
    · have ha : value.toNatBits < 2 ^ (width - 1) := Nat.lt_of_not_le fun h => by
        rw [Nat.ble_eq_true_of_le h] at hs
        cases hs
      have h := roundRat_ratio_kernel format false value.toNatBits 1 Nat.one_ne_zero
      simp only [Bool.false_eq_true, ite_false] at h
      rw [← h, hint, ite_eq_left (by omega)]
      simp
    · have ha : 2 ^ (width - 1) ≤ value.toNatBits := Nat.le_of_ble_eq_true hs
      have h := roundRat_ratio_kernel format true (2 ^ width - value.toNatBits) 1
        Nat.one_ne_zero
      simp only [ite_true] at h
      rw [← h, hint, ite_eq_right (by omega)]
      congr 1
      rw [Nat.cast_sub (Nat.le_of_lt hlt)]
      push_cast
      ring
  · have hmin : value = FixedInt.minCode width := by
      rw [← FixedInt.ofNatBits_toNatBits value, Nat.eq_of_beq_eq_true hb,
        ← integerSentinel_toNatBits hwidth, FixedInt.ofNatBits_toNatBits]
    rw [ite_eq_left hmin]
    exact nar_eq_ofNatBits format

/-- Posit Standard (2022), §6.4: the conversion of an unsigned integer is NaR for the word with
only its most significant bit set, and the flat rounding of the word otherwise. It holds for
every posit format and every positive integer width. -/
@[kernel_optimize (cost := 150)] theorem ofUnsigned_eq_kernel (format : Format) {width : Nat}
    (value : BitVec width) (hwidth : 0 < width) :
    Model.ofUnsigned format value hwidth =
      Model.ofNatBits
        (Bool.rec (motive := fun _ => Nat)
          (Flat.ofRatio format.payloadBits 2 0 value.toNat 1)
          (nar format.payloadBits)
          (Nat.beq value.toNat (Nat.pow 2 (Nat.sub width 1)))) := by
  unfold Model.ofUnsigned
  change _ = Model.ofNatBits
    (Bool.rec (motive := fun _ => Nat)
      (Flat.ofRatio format.payloadBits 2 0 value.toNat 1)
      (nar format.payloadBits)
      (Nat.beq value.toNat (2 ^ (width - 1))))
  cases hb : Nat.beq value.toNat (2 ^ (width - 1))
  · have hne : value ≠ BitVec.intMin width := fun h => by
      rw [h, BitVec.toNat_intMin_of_pos hwidth, Nat.beq_refl] at hb
      cases hb
    rw [ite_eq_right hne]
    have h := roundRat_ratio_kernel format false value.toNat 1 Nat.one_ne_zero
    simp only [Bool.false_eq_true, ite_false] at h
    rw [← h]
    simp
  · have hmin : value = BitVec.intMin width :=
      BitVec.eq_of_toNat_eq (by
        rw [Nat.eq_of_beq_eq_true hb, BitVec.toNat_intMin_of_pos hwidth])
    rw [ite_eq_left hmin]
    exact nar_eq_ofNatBits format

open FloatLib.Numerics.Representations in
/-- Posit Standard (2022), §6.4: the conversion to a signed integer is the integer of the word
that the flat conversion computes on the encoding. It holds for every posit format, every
positive integer width and every word. -/
@[kernel_optimize (cost := 150)] theorem toFixedInt_eq_kernel (width : Nat) (x : Model format)
    (hwidth : 0 < width) :
    Model.toFixedInt width x hwidth =
      FixedInt.ofNatBits (Flat.toSigned format.payloadBits 2 width x.toNatBits) := by
  rw [Flat.toSigned_eq, ← toFixedInt_toNatBits width x hwidth, FixedInt.ofNatBits_toNatBits]

/-- Posit Standard (2022), §6.4: the conversion to an unsigned integer is the word that the
flat conversion computes on the encoding. It holds for every posit format, every positive
integer width and every word. -/
@[kernel_optimize (cost := 150)] theorem toUnsigned_eq_kernel (width : Nat) (x : Model format)
    (hwidth : 0 < width) :
    Model.toUnsigned width x hwidth =
      BitVec.ofNat width (Flat.toUnsigned format.payloadBits 2 width x.toNatBits) := by
  rw [Flat.toUnsigned_eq, ← toUnsigned_toNat width x hwidth, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

end FloatLib.Floats.Formats.Posit.KernelPath
