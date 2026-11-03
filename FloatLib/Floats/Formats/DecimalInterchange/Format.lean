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
Custom layouts need not be IEEE formats.

A layout is written `{ declets := 2, exponentBits := 6, bias := 101 }`. With a numeral
`exponentBits`, `decide` supplies the proof field, and a zero width fails with the message
`a decimal format requires exponentBits ≥ 1`. -/
structure Format where
  /-- Number of trailing groups of three decimal digits. -/
  declets : Nat
  /-- Width of the exponent continuation field in the DPD encoding. -/
  exponentBits : Nat
  /-- Bias subtracted from the encoded exponent to obtain the quantum exponent. -/
  bias : Int
  /-- At least one exponent-continuation bit separates NaN signaling from payload bits. -/
  exponentBits_pos : 0 < exponentBits := by
    first
    | decide
    | fail "a decimal format requires exponentBits ≥ 1"
  deriving DecidableEq, Repr

namespace Format

/-- IEEE 754 decimal32 interchange parameters. -/
def decimal32 : Format := { declets := 2, exponentBits := 6, bias := 101 }

/-- IEEE 754 decimal64 basic-format parameters. -/
def decimal64 : Format := { declets := 5, exponentBits := 8, bias := 398 }

/-- IEEE 754 decimal128 basic-format parameters. -/
def decimal128 : Format := { declets := 11, exponentBits := 12, bias := 6176 }

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

/-- The coefficient bound is ten to the precision, so a finite coefficient has at most `precision`
decimal digits. -/
theorem coefficientBound_eq (f : Format) : f.coefficientBound = 10 ^ f.precision := by
  change 10 * (10 ^ 3) ^ f.declets = 10 ^ (3 * f.declets + 1)
  rw [Nat.pow_add_one 10 (3 * f.declets), Nat.pow_mul, Nat.mul_comm]

/-- The sign bit is the most significant bit of the word: its place value is half of
`2 ^ bitWidth`. -/
theorem twice_signBase (f : Format) : 2 * f.signBase = 2 ^ f.bitWidth := by
  simp [signBase, exponentBase, trailingBase, bitWidth, Nat.pow_add, Nat.pow_mul,
    Nat.mul_assoc]
  omega

/-- The trailing-field radix is positive. -/
theorem trailingBase_pos (f : Format) : 0 < f.trailingBase := Nat.pow_pos (by decide)

/-- The exponent-continuation radix is positive. -/
theorem exponentBase_pos (f : Format) : 0 < f.exponentBase := Nat.pow_pos (by decide)

/-- The NaN payload bound is positive, so payload zero is always representable. -/
theorem payloadBound_pos (f : Format) : 0 < f.payloadBound := Nat.pow_pos (by decide)

/-- Payloads and trailing digits fit the binary trailing field: three decimal digits use 1000 of
the 1024 patterns of a declet. -/
theorem payloadBound_le (f : Format) : f.payloadBound ≤ f.trailingBase := by
  exact Nat.pow_le_pow_left (by decide : 1000 ≤ 1024) f.declets

/-- Every layout has at least one decimal digit of precision. -/
theorem precision_pos (f : Format) : 0 < f.precision := by
  simp [precision]

/-- The coefficient bound is positive, so coefficient zero is always representable. -/
theorem coefficientBound_pos (f : Format) : 0 < f.coefficientBound :=
  Nat.mul_pos (by decide) f.payloadBound_pos

/-- The biased-exponent bound is positive, so every layout has at least one quantum. -/
theorem exponentBound_pos (f : Format) : 0 < f.exponentBound :=
  Nat.mul_pos (by decide) f.exponentBase_pos

/-- The place value of the sign bit is positive. -/
theorem signBase_pos (f : Format) : 0 < f.signBase :=
  Nat.mul_pos (Nat.mul_pos (by decide) f.exponentBase_pos) f.trailingBase_pos

/-- When quantum zero is representable, the least quantum is at most zero. -/
theorem minQuantum_nonpos (f : Format) [f.HasQuantumZero] : f.minQuantum ≤ 0 := by
  simpa [minQuantum] using HasQuantumZero.bias_nonneg (f := f)

/-- When quantum zero is representable, the largest quantum is at least zero. -/
theorem maxQuantum_nonneg (f : Format) [f.HasQuantumZero] : 0 ≤ f.maxQuantum := by
  have h := HasQuantumZero.bias_lt (f := f)
  dsimp only [maxQuantum]
  omega

/-- Every layout has a nonempty quantum range, with or without quantum zero. -/
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

/-- The exponent-continuation radix is twice `2 ^ (exponentBits - 1)`, so the signaling-bit place
value `exponentBase * trailingBase / 2` is that many whole trailing significand fields. The
positive exponent width `exponentBits_pos` keeps the subtraction exact. -/
theorem exponentBase_eq_two_mul (f : Format) :
    f.exponentBase = 2 * 2 ^ (f.exponentBits - 1) := by
  have h := f.exponentBits_pos
  conv_lhs => rw [exponentBase, show f.exponentBits = (f.exponentBits - 1) + 1 by omega]
  rw [Nat.pow_succ, Nat.mul_comm]

end Format

end FloatLib.Floats.Formats.DecimalInterchange
