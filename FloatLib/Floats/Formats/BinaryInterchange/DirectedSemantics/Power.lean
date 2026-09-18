/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Dyadic.Core
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems

/-!
# Real binary-power semantics

Rational and directed rounding share this low-level real binary-power API. The file deliberately
does not import executable arithmetic, allowing native kernels to reuse the logarithm proofs
without an import cycle through `Model.Arithmetic`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats.Formats.Flocq

section

/-- Binary power as a real number. -/
noncomputable abbrev bpow (exponent : Int) : ℝ :=
  FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix exponent

/-- Every real binary power is positive. -/
theorem bpow_pos (exponent : Int) : 0 < bpow exponent :=
  FloatLib.Floats.Formats.Flocq.bpow.pos Numerics.binaryRadix exponent

/-- Every real binary power is nonnegative. -/
theorem bpow_nonneg (exponent : Int) : 0 ≤ bpow exponent :=
  FloatLib.Floats.Formats.Flocq.bpow.nonneg Numerics.binaryRadix exponent

/-- The binary power at exponent zero is one. -/
@[simp] theorem bpow_zero : bpow 0 = 1 := by
  simp [bpow, FloatLib.Floats.Formats.Flocq.bpow]

/-- The binary power at exponent one is two. -/
@[simp] theorem bpow_one : bpow 1 = 2 := by
  simp [bpow, FloatLib.Floats.Formats.Flocq.bpow,
    Numerics.binaryRadix, Numerics.Radix.toReal]

/-- The binary power at exponent minus one is one half. -/
@[simp] theorem bpow_neg_one : bpow (-1) = (2 : ℝ)⁻¹ := by
  simp [bpow, FloatLib.Floats.Formats.Flocq.bpow,
    Numerics.binaryRadix, Numerics.Radix.toReal]

/-- Binary powers turn addition of exponents into multiplication. -/
theorem bpow_add (left right : Int) :
    bpow (left + right) = bpow left * bpow right := by
  simp [bpow, FloatLib.Floats.Formats.Flocq.bpow.add_exp]

/-- Binary powers are monotone in the exponent. -/
theorem bpow_le_bpow_of_le {left right : Int} (h : left ≤ right) :
    bpow left ≤ bpow right := by
  simpa [bpow, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix,
    Numerics.Radix.toReal] using
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h

/-- A binary power at a natural exponent is the corresponding natural power of two. -/
theorem bpow_ofNat (exponent : Nat) :
    bpow (Int.ofNat exponent) = (pow2 exponent : ℝ) := by
  simpa [bpow, Numerics.binaryRadix, pow2_eq_two_pow] using
    (FloatLib.Floats.Formats.Flocq.bpow_eq_natPow
      (β := Numerics.binaryRadix) (Int.ofNat exponent) (by simp))

/-- A natural exponent coerced to an integer denotes the corresponding real power of two. -/
theorem bpow_natCast (exponent : Nat) :
    bpow (exponent : Int) = (2 : ℝ) ^ exponent := by
  rw [← Int.ofNat_eq_natCast]
  simpa [pow2_eq_two_pow] using bpow_ofNat exponent

/-- A binary power at a negative successor is the inverse natural power of two. -/
theorem bpow_negSucc (exponent : Nat) :
    bpow (Int.negSucc exponent) = ((pow2 (exponent + 1) : Nat) : ℝ)⁻¹ := by
  have hneg : Int.negSucc exponent = -(Int.ofNat (exponent + 1)) := by rfl
  rw [hneg]
  change FloatLib.Floats.Formats.Flocq.bpow Numerics.binaryRadix
      (-(Int.ofNat (exponent + 1))) =
    ((pow2 (exponent + 1) : Nat) : ℝ)⁻¹
  rw [FloatLib.Floats.Formats.Flocq.bpow.neg_exp]
  exact congrArg Inv.inv (bpow_ofNat (exponent + 1))

end

end Model
end FloatLib.Floats.Formats.BinaryInterchange
