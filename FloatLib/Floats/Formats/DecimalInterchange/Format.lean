/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import Mathlib.Data.Int.Basic

/-!
# Decimal interchange layouts

The named presets have the parameters of IEEE 754-2019, Table 3.6 and §3.5.2.
The descriptor also permits custom layouts, without identifying them as standardized
formats. Both BID and DPD represent the same datums, with an externally selected encoding.
The quantum exponent bounds concern the stored coefficient, including its trailing
zeros, rather than a normalized significand.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- A decimal layout with one sign bit, five combination bits, an exponent
continuation, and a sequence of ten-bit declets. The positive exponent width
separates NaN signaling from payload bits. Bias is unrestricted: the codec does
not require quantum zero to be representable. Precision is `3 * declets + 1`;
this is an interchange descriptor, not a descriptor for every decimal precision.
Custom layouts need not be IEEE formats. -/
structure Format where
  /-- Number of trailing groups of three decimal digits. -/
  declets : Nat
  /-- Width of the exponent continuation field in the DPD encoding. -/
  exponentBits : Nat
  /-- Bias subtracted from the encoded exponent to obtain the quantum exponent. -/
  bias : Int
  /-- At least one exponent-continuation bit separates NaN signaling from payload bits. -/
  exponentBits_pos : 0 < exponentBits
  deriving DecidableEq, Repr

namespace Format

/-- IEEE 754 decimal32 interchange parameters. -/
def decimal32 : Format := ⟨2, 6, 101, by decide⟩

/-- IEEE 754 decimal64 basic-format parameters. -/
def decimal64 : Format := ⟨5, 8, 398, by decide⟩

/-- IEEE 754 decimal128 basic-format parameters. -/
def decimal128 : Format := ⟨11, 12, 6176, by decide⟩

/-- Total number of stored bits, including the sign and combination fields. -/
def bitWidth (f : Format) : Nat := 6 + f.exponentBits + 10 * f.declets

/-- Significand precision in decimal digits. -/
def precision (f : Format) : Nat := 3 * f.declets + 1

/-- Radix of the trailing significand field. -/
def trailingBase (f : Format) : Nat := 1024 ^ f.declets

/-- Radix of the exponent continuation field. -/
def exponentBase (f : Format) : Nat := 2 ^ f.exponentBits

/-- Exclusive bound on a NaN payload or the trailing decimal digits. -/
def payloadBound (f : Format) : Nat := 1000 ^ f.declets

/-- Exclusive bound on a finite coefficient, equal to `10 ^ precision`. -/
def coefficientBound (f : Format) : Nat := 10 * f.payloadBound

/-- Exclusive bound on the biased exponent. The fourth high-bit pair is reserved. -/
def exponentBound (f : Format) : Nat := 3 * f.exponentBase

/-- Place value of the sign bit. -/
def signBase (f : Format) : Nat := 32 * f.exponentBase * f.trailingBase

/-- Smallest quantum exponent, including subnormal datums. -/
def minQuantum (f : Format) : Int := -f.bias

/-- Largest quantum exponent for a stored coefficient. -/
def maxQuantum (f : Format) : Int := (f.exponentBound : Int) - 1 - f.bias

/-- An optional arithmetic assumption: quantum zero belongs to the representable
interval. The codecs and general rounding operations do not require it. -/
class HasQuantumZero (f : Format) : Prop where
  /-- Quantum zero is not below the smallest representable quantum. -/
  bias_nonneg : 0 ≤ f.bias
  /-- Quantum zero is not above the largest representable quantum. -/
  bias_lt : f.bias < (f.exponentBound : Int)

instance : decimal32.HasQuantumZero := ⟨by decide, by decide⟩
instance : decimal64.HasQuantumZero := ⟨by decide, by decide⟩
instance : decimal128.HasQuantumZero := ⟨by decide, by decide⟩

theorem coefficientBound_eq (f : Format) : f.coefficientBound = 10 ^ f.precision := by
  change 10 * (10 ^ 3) ^ f.declets = 10 ^ (3 * f.declets + 1)
  rw [Nat.pow_add_one 10 (3 * f.declets), Nat.pow_mul, Nat.mul_comm]

theorem twice_signBase (f : Format) : 2 * f.signBase = 2 ^ f.bitWidth := by
  simp [signBase, exponentBase, trailingBase, bitWidth, Nat.pow_add, Nat.pow_mul,
    Nat.mul_assoc]
  omega

theorem trailingBase_pos (f : Format) : 0 < f.trailingBase := Nat.pow_pos (by decide)
theorem exponentBase_pos (f : Format) : 0 < f.exponentBase := Nat.pow_pos (by decide)
theorem payloadBound_pos (f : Format) : 0 < f.payloadBound := Nat.pow_pos (by decide)
theorem payloadBound_le (f : Format) : f.payloadBound ≤ f.trailingBase := by
  exact Nat.pow_le_pow_left (by decide : 1000 ≤ 1024) f.declets

theorem precision_pos (f : Format) : 0 < f.precision := by
  simp [precision]

theorem coefficientBound_pos (f : Format) : 0 < f.coefficientBound :=
  Nat.mul_pos (by decide) f.payloadBound_pos

theorem exponentBound_pos (f : Format) : 0 < f.exponentBound :=
  Nat.mul_pos (by decide) f.exponentBase_pos

theorem signBase_pos (f : Format) : 0 < f.signBase :=
  Nat.mul_pos (Nat.mul_pos (by decide) f.exponentBase_pos) f.trailingBase_pos

theorem minQuantum_nonpos (f : Format) [f.HasQuantumZero] : f.minQuantum ≤ 0 := by
  simpa [minQuantum] using HasQuantumZero.bias_nonneg (f := f)

theorem maxQuantum_nonneg (f : Format) [f.HasQuantumZero] : 0 ≤ f.maxQuantum := by
  have h := HasQuantumZero.bias_lt (f := f)
  dsimp only [maxQuantum]
  omega

theorem minQuantum_le_maxQuantum (f : Format) : f.minQuantum ≤ f.maxQuantum := by
  have h := f.exponentBound_pos
  dsimp only [minQuantum, maxQuantum]
  omega

/-- The optional bias bounds say exactly that quantum zero is representable. -/
theorem hasQuantumZero_iff (f : Format) :
    f.HasQuantumZero ↔ f.minQuantum ≤ 0 ∧ 0 ≤ f.maxQuantum := by
  constructor
  · intro h
    exact ⟨minQuantum_nonpos f, maxQuantum_nonneg f⟩
  · rintro ⟨hmin, hmax⟩
    constructor <;> dsimp only [minQuantum, maxQuantum] at * <;> omega

/-- The signaling-bit place value is a whole number of trailing significand fields. -/
theorem exponentBase_eq_two_mul (f : Format) :
    f.exponentBase = 2 * 2 ^ (f.exponentBits - 1) := by
  have h := f.exponentBits_pos
  conv_lhs => rw [exponentBase, show f.exponentBits = (f.exponentBits - 1) + 1 by omega]
  rw [Nat.pow_succ, Nat.mul_comm]

end Format

end FloatLib.Floats.Formats.DecimalInterchange
