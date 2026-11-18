/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.KernelPath.Flat
public import FloatLib.Floats.Formats.Posit.KernelPath.Standard
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
  rules of `Posit.Configured.KernelPath` use.
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

end FloatLib.Floats.Formats.Posit.KernelPath
