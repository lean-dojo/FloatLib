/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Bounds
public import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.Logarithm

/-!
# Real meaning of square-root exponent selection

If a positive radicand has leading binary exponent `L`, its square root has leading exponent
`L / 2`, using integer floor division. Scaling the radicand by `2^(-2Q)` therefore scales its
real square root by `2^(-Q)`. These facts connect the exact integer rounder to the report's
normal and subnormal quantum formula.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.P3109.Arithmetic

open BinaryInterchange.Model

private theorem bpow_square (exponent : Int) :
    bpow exponent ^ 2 = bpow (2 * exponent) := by
  rw [pow_two, ← bpow_add]
  congr 1
  omega

/-- Floor division by two gives the leading exponent of the actual positive square root. -/
theorem sqrt_floorLog2_bounds (numerator denominator : Nat)
    (hn : numerator ≠ 0) (hd : denominator ≠ 0) :
    let exponent := RationalBinary.floorLog2 numerator denominator / 2
    bpow exponent ≤ Real.sqrt ((numerator : Real) / denominator) ∧
      Real.sqrt ((numerator : Real) / denominator) < bpow (exponent + 1) := by
  let leading := RationalBinary.floorLog2 numerator denominator
  have hbounds := floorLog2_bounds numerator denominator hn hd
  constructor
  · apply Real.le_sqrt_of_sq_le
    rw [bpow_square]
    exact (bpow_le_bpow_of_le (by omega : 2 * (leading / 2) ≤ leading)).trans hbounds.1
  · apply (Real.sqrt_lt (by positivity) (bpow_nonneg _)).mpr
    rw [bpow_square]
    exact hbounds.2.trans_le
      (bpow_le_bpow_of_le (by omega : leading + 1 ≤ 2 * (leading / 2 + 1)))

/-- Squaring the exponent scale preserves the exact real square root, including irrational roots. -/
theorem sqrt_scaled_ratio (numerator denominator : Nat) (quantum : Int) :
    let scaled := RationalBinary.scaleByPowerOfTwo numerator denominator (-2 * quantum)
    Real.sqrt ((scaled.1 : Real) / scaled.2) =
      Real.sqrt ((numerator : Real) / denominator) * bpow (-quantum) := by
  dsimp only
  rw [scaleByPowerOfTwo_real, scaledRatToReal,
    show -2 * quantum = 2 * (-quantum) by omega, ← bpow_square,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (bpow_nonneg _)]

/-- A nonnegative rational is represented by the numerator magnitude used by the root kernel. -/
theorem nonnegative_rat_eq_ratio (radicand : Rat) (h : 0 ≤ radicand) :
    ((radicand.num.natAbs : Nat) : Real) / radicand.den = (radicand : Real) := by
  have hnum : 0 ≤ radicand.num := Rat.num_nonneg.mpr h
  have hcast : ((radicand.num.natAbs : Nat) : Real) = (radicand.num : Real) := by
    rw [Nat.cast_natAbs, abs_of_nonneg hnum]
  rw [hcast, Rat.cast_def]

/-- The reference significand is the actual nonnegative root scaled by the chosen binary quantum. -/
theorem sqrt_scaled_radicand (format : Format) (radicand : Rat) (h : 0 ≤ radicand) :
    let quantum := sqrtQuantum format radicand.num.natAbs radicand.den
    let scaled :=
      RationalBinary.scaleByPowerOfTwo radicand.num.natAbs radicand.den (-2 * quantum)
    Real.sqrt ((scaled.1 : Real) / scaled.2) =
      Real.sqrt (radicand : Real) * bpow (-quantum) := by
  dsimp only
  rw [sqrt_scaled_ratio, nonnegative_rat_eq_ratio radicand h]

end FloatLib.Floats.Formats.P3109.Arithmetic
