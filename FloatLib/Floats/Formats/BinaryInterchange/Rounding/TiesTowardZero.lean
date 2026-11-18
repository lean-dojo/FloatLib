/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.TiesTowardZero
import FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Exact

/-!
# Rounding exact dyadics to nearest with ties toward zero

`roundDyadicTiesTowardZero fmt value` rounds an exact dyadic into `fmt` in the direction that
IEEE 754-2019 §9.5 names roundTiesTowardZero (see `Flocq.nearestTowardZeroChoice` for the
sources): the nearest value of the format, and of two equally near ones the one of smaller
magnitude.

It works in two steps. `tiesTowardZeroGrid` rounds the significand on the format's grid with
gradual underflow and no upper exponent bound, and returns the rounded value as an exact dyadic.
`roundDyadic` then encodes that grid value. A grid value is already representable unless it lies
above the largest finite value, so the second step rounds nothing and decides overflow on the
value rounded with an unbounded exponent range, as IEEE 754-2019 §7.4 defines it. In particular
the midpoint between the largest finite value and the next grid value rounds to the largest
finite value and does not overflow.

`roundTiesTowardZeroAt fmt x` is the real-valued specification, Flocq's `round` with the tie
choice `nearestTowardZeroChoice`. `roundTiesTowardZeroAt_dyadic` proves that the grid step computes
it for every descriptor, and `toReal_roundDyadicTiesTowardZero` that a finite result of the
executable rounding denotes it in a conventional IEEE descriptor.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Floats.Formats.Flocq
open FloatLib.Numerics

/--
Round `mantissa * 2 ^ (exponent - targetExponent)` to the nearest natural number, an exact tie
toward zero. Off a tie this is `roundMantissaAtExponentEven`.
-/
def roundMantissaAtExponentTiesTowardZero (mantissa : Nat) (exponent targetExponent : Int) :
    Nat :=
  if shiftRightIsTie mantissa (targetExponent - exponent).toNat then
    mantissa >>> (targetExponent - exponent).toNat
  else
    roundMantissaAtExponentEven mantissa exponent targetExponent

/--
The value of the grid of `fmt` nearest to an exact dyadic, a tie toward zero, as an exact dyadic.
The grid has the precision of `fmt` and its gradual underflow, and no upper exponent bound.
-/
def tiesTowardZeroGrid (fmt : FloatFormat) (value : Numerics.Dyadic) : Numerics.Dyadic :=
  let target :=
    max ((value.significand.log2 : Int) + value.exponent - fmt.fracWidth)
      fmt.minSubnormalExponent
  { negative := value.negative
    significand :=
      roundMantissaAtExponentTiesTowardZero value.significand value.exponent target
    exponent := target }

/--
Round an exact dyadic into `fmt` to nearest with ties toward zero, IEEE 754-2019 §9.5
roundTiesTowardZero. A result above the largest finite value overflows as `roundDyadic` does.
-/
def roundDyadicTiesTowardZero (fmt : FloatFormat) (value : Numerics.Dyadic) : Model fmt :=
  roundDyadic fmt (tiesTowardZeroGrid fmt value)

/--
Rounding of a real onto the precision and gradual-underflow grid of `fmt` to nearest with ties
toward zero, IEEE 754-2019 §9.5 roundTiesTowardZero. The grid has no upper exponent bound.
-/
noncomputable def roundTiesTowardZeroAt (fmt : FloatFormat) (x : ℝ) : ℝ :=
  round (β := binaryRadix) (fexp := fexpOf fmt) (nearestChoice nearestTowardZeroChoice) x

/-- Rounding with ties toward zero returns a value on the grid of `fmt`. -/
theorem genericFormat_roundTiesTowardZeroAt (fmt : FloatFormat) (x : ℝ) :
    GenericRepresentable binaryRadix (fexpOf fmt) (roundTiesTowardZeroAt fmt x) :=
  genericRepresentable_round (nearestChoice nearestTowardZeroChoice) x

/-- A tie of a right shift is a real quotient with fractional part one half. -/
private theorem natCast_div_two_pow_of_tie {mantissa shift : Nat}
    (htie : shiftRightIsTie mantissa shift = true) :
    (mantissa : ℝ) / (2 : ℝ) ^ shift = ((mantissa >>> shift : Nat) : ℝ) + 1 / 2 := by
  obtain ⟨hpos, hmod⟩ := (shiftRightIsTie_eq_true_iff mantissa shift).1 htie
  have hsplit : mantissa = 2 ^ shift * (mantissa >>> shift) + 2 ^ (shift - 1) := by
    have h := Nat.div_add_mod mantissa (2 ^ shift)
    rw [hmod, ← Nat.shiftRight_eq_div_pow] at h
    exact h.symm
  have hpow : (2 : ℝ) ^ shift = 2 * (2 : ℝ) ^ (shift - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hne : (2 : ℝ) ^ (shift - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  conv_lhs => rw [hsplit]
  push_cast
  rw [hpow]
  field_simp

/-- A real quotient by a power of two with fractional part one half is a tie of the shift. -/
private theorem tie_of_fract_natCast_div_two_pow {mantissa shift : Nat}
    (hhalf : Int.fract ((mantissa : ℝ) / ((2 ^ shift : Nat) : ℝ)) = 1 / 2) :
    shiftRightIsTie mantissa shift = true := by
  rw [Int.fract_div_natCast_eq_div_natCast_mod] at hhalf
  have hden : (((2 ^ shift : Nat) : ℝ)) ≠ 0 := by positivity
  have hnat : 2 * (mantissa % 2 ^ shift) = 2 ^ shift := by
    have h2 : (2 : ℝ) * ((mantissa % 2 ^ shift : Nat) : ℝ) = ((2 ^ shift : Nat) : ℝ) := by
      field_simp at hhalf
      linarith
    exact_mod_cast h2
  have hshift : 0 < shift := by
    rcases Nat.eq_zero_or_pos shift with rfl | hpos
    · simp [Nat.mod_one] at hnat
    · exact hpos
  have hpow : 2 ^ shift = 2 * 2 ^ (shift - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  exact (shiftRightIsTie_eq_true_iff mantissa shift).2 ⟨hshift, by omega⟩

/-- Rounding zero with ties toward zero gives zero. -/
@[simp] theorem roundTiesTowardZeroAt_zero (fmt : FloatFormat) :
    roundTiesTowardZeroAt fmt 0 = 0 :=
  round_preserves_generic _ 0 genericRepresentable_zero

/-- Rounding with ties toward zero fixes a value already on the grid of `fmt`. -/
theorem roundTiesTowardZeroAt_of_genericFormat (fmt : FloatFormat) {x : ℝ}
    (hx : GenericRepresentable binaryRadix (fexpOf fmt) x) : roundTiesTowardZeroAt fmt x = x :=
  round_preserves_generic _ x hx

/-- Ties-toward-zero rounding of a nonnegative scaled magnitude is the executable rounder. -/
theorem nearestChoice_tieTowardZero_scaledMagnitude (mantissa : Nat)
    (exponent targetExponent : Int) :
    nearestChoice nearestTowardZeroChoice
        ((mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - targetExponent)) =
      Int.ofNat (roundMantissaAtExponentTiesTowardZero mantissa exponent targetExponent) := by
  unfold roundMantissaAtExponentTiesTowardZero
  have hdown (shift : Nat) (hexp : exponent - targetExponent = -(shift : Int)) :
      (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - targetExponent) =
        (mantissa : ℝ) / (2 : ℝ) ^ shift := by
    rw [hexp, div_eq_mul_inv]
    simp [Flocq.bpow, binaryRadix, Numerics.Radix.toReal]
  by_cases htie : shiftRightIsTie mantissa (targetExponent - exponent).toNat = true
  · have hpos := ((shiftRightIsTie_eq_true_iff mantissa _).1 htie).1
    rw [ite_eq_left htie, hdown (targetExponent - exponent).toNat (by omega),
      natCast_div_two_pow_of_tie htie]
    generalize mantissa >>> (targetExponent - exponent).toNat = quotient
    have hfract : Int.fract ((quotient : ℝ) + 1 / 2) = 1 / 2 := by
      rw [Int.fract_natCast_add, Int.fract_eq_iff]
      exact ⟨by norm_num, by norm_num, 0, by norm_num⟩
    have hfloor : ⌊(quotient : ℝ) + 1 / 2⌋ = Int.ofNat quotient := by
      rw [Int.floor_eq_iff]
      simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
      constructor <;> linarith
    rw [nearestChoice_tieTowardZero_of_fract_eq_half (by positivity) hfract, hfloor]
  · have hfract : Int.fract
        ((mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - targetExponent)) ≠ 1 / 2 := by
      intro hhalf
      apply htie
      by_cases hle : exponent ≤ targetExponent
      · rw [hdown (targetExponent - exponent).toNat (by omega)] at hhalf
        apply tie_of_fract_natCast_div_two_pow
        rw [← hhalf]
        push_cast
        rfl
      · obtain ⟨k, hk⟩ : ∃ k : Nat, exponent - targetExponent = (k : Int) :=
          ⟨(exponent - targetExponent).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
        have hvalue : (mantissa : ℝ) * Flocq.bpow binaryRadix (exponent - targetExponent) =
            ((mantissa * 2 ^ k : Nat) : ℝ) := by
          rw [hk]
          simp [Flocq.bpow, binaryRadix, Numerics.Radix.toReal]
        rw [hvalue, Int.fract_natCast] at hhalf
        norm_num at hhalf
    rw [ite_eq_right htie, nearestChoice_tieTowardZero_eq_nearestEven hfract,
      nearestEven_scaledMagnitude]

/-- Ties-toward-zero rounding commutes with the sign stored in a dyadic value. -/
theorem nearestChoice_tieTowardZero_scaledDyadic (sign : Bool) (mantissa : Nat)
    (exponent targetExponent : Int) :
    nearestChoice nearestTowardZeroChoice
        ((if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
          Flocq.bpow binaryRadix (exponent - targetExponent)) =
      if sign then
        -Int.ofNat (roundMantissaAtExponentTiesTowardZero mantissa exponent targetExponent)
      else
        Int.ofNat (roundMantissaAtExponentTiesTowardZero mantissa exponent targetExponent) := by
  cases sign
  · simp [nearestChoice_tieTowardZero_scaledMagnitude]
  · simp only [ite_true]
    rw [neg_one_mul, neg_mul, nearestChoice_tieTowardZero_neg,
      nearestChoice_tieTowardZero_scaledMagnitude]

/--
The grid step computes real rounding to nearest with ties toward zero, for every binary
descriptor: custom biases and finite-only encodings included.
-/
theorem roundTiesTowardZeroAt_dyadic (fmt : FloatFormat) (d : Numerics.Dyadic) :
    roundTiesTowardZeroAt fmt d.toReal = (tiesTowardZeroGrid fmt d).toReal := by
  let target := max ((d.significand.log2 : ℤ) + d.exponent - fmt.fracWidth)
    fmt.minSubnormalExponent
  have hgrid : (tiesTowardZeroGrid fmt d).toReal =
      (if d.negative then (-1 : ℝ) else 1) *
        (roundMantissaAtExponentTiesTowardZero d.significand d.exponent target : ℝ) *
          Flocq.bpow binaryRadix target :=
    Dyadic.toReal_mk _ _ _
  rw [hgrid]
  by_cases hm : d.significand = 0
  · have hr : roundMantissaAtExponentTiesTowardZero d.significand d.exponent target = 0 := by
      have h := nearestChoice_tieTowardZero_scaledMagnitude 0 d.exponent target
      rw [Nat.cast_zero, zero_mul, ← Int.cast_zero,
        nearestChoice_intCast nearestTowardZeroChoice] at h
      simpa [hm] using (Int.ofNat_eq_zero.mp h.symm)
    have hz : d.toReal = 0 := by
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hm]
    rw [hr, hz, roundTiesTowardZeroAt_zero]
    simp
  have he : cexp binaryRadix (fexpOf fmt) d.toReal = target := cexp_dyadic fmt d hm
  have hs : scaledMantissa binaryRadix (fexpOf fmt) d.toReal =
      (if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) *
        Flocq.bpow binaryRadix (d.exponent - target) := by
    rw [scaledMantissa, he, sub_eq_add_neg, bpow.add_exp]
    cases hsign : d.negative <;>
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsign,
        Flocq.bpow, binaryRadix, Numerics.Radix.toReal] <;> ring
  rw [roundTiesTowardZeroAt, Flocq.round, hs, nearestChoice_tieTowardZero_scaledDyadic, he]
  cases d.negative <;> simp [Flocq.toReal, target]

/--
A finite result of the executable rounding denotes the real rounded to nearest with ties toward
zero, in a conventional IEEE descriptor. The finiteness hypothesis excludes overflow, which has
no value in `ℝ`.
-/
theorem toReal_roundDyadicTiesTowardZero (fmt : FloatFormat) (hfmt : fmt.isIEEE = true)
    (d : Numerics.Dyadic) (hfin : isFinite (roundDyadicTiesTowardZero fmt d) = true) :
    toReal (roundDyadicTiesTowardZero fmt d) = roundTiesTowardZeroAt fmt d.toReal := by
  unfold roundDyadicTiesTowardZero at hfin ⊢
  rw [toReal_roundDyadic_eq_roundAt fmt hfmt _ hfin, ← roundTiesTowardZeroAt_dyadic]
  exact round_preserves_generic nearestEven _ (genericFormat_roundTiesTowardZeroAt fmt _)

/-- Rounding an exact zero with ties toward zero keeps its sign. -/
theorem roundDyadicTiesTowardZero_zero (fmt : FloatFormat) (negative : Bool) (exponent : Int) :
    roundDyadicTiesTowardZero fmt ⟨negative, 0, exponent⟩ = zero fmt negative := by
  have hr (target : Int) :
      roundMantissaAtExponentTiesTowardZero 0 exponent target = 0 := by
    have h := nearestChoice_tieTowardZero_scaledMagnitude 0 exponent target
    rw [Nat.cast_zero, zero_mul, ← Int.cast_zero,
      nearestChoice_intCast nearestTowardZeroChoice] at h
    exact Int.ofNat_eq_zero.mp h.symm
  simp only [roundDyadicTiesTowardZero, tiesTowardZeroGrid, hr]
  exact Internal.Directed.roundDyadic_zero fmt .nearest negative _

end Model
end FloatLib.Floats.Formats.BinaryInterchange
