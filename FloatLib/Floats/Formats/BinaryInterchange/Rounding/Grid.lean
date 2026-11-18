/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Model.Packing.Finite
public import FloatLib.Floats.Formats.BinaryInterchange.ModelRounding.Proof
public import FloatLib.Floats.Formats.Flocq.Calculation.Round
public import FloatLib.Floats.Formats.Flocq.Theory.Format.Theorems
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Modes
public import Mathlib.Analysis.SpecialFunctions.Log.Base

import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Constants

/-!
# Real binary grid rounding

The descriptor's precision and lower exponent determine an unbounded-above dyadic grid.
This module proves membership, preservation and the integer shift-and-round formula for
nearest-even rounding on that grid, including custom biases and finite-only encodings.
Executable upper-range and exceptional-value policies are proved in `Rounding.Policy`.

The compatibility lemmas for Lean's conventional IEEE model are corollaries of the same grid
formula. Its finished-mantissa packing lemmas remain available to the accuracy development.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

open FloatLib.Floats
open FloatLib.Numerics
open FloatLib.Floats.Formats.Flocq

/-- Precision and gradual-underflow grid using the descriptor’s declared exponent bias. -/
def fexpOf (fmt : FloatFormat) : ℤ → ℤ :=
  fltExp fmt.minSubnormalExponent (fmt.fracWidth + 1)

/-- The exponent function of a format descriptor is a valid one. -/
instance (fmt : FloatFormat) : ValidExp (fexpOf fmt) :=
  validExp_flt (emin := fmt.minSubnormalExponent)
    (prec := fmt.fracWidth + 1) (by positivity)

/--
Rounding of a real onto the precision and gradual-underflow grid of `fmt`, with the descriptor's
bias, in the direction `mode`, nearest-even by default.

The real grid has no upper exponent bound. Overflow and exceptional encodings belong to the
executable operation, and its equality to `roundAt` needs the corresponding refinement hypotheses.
Nearest-even rounding and the two infinity directions unfold to Flocq's `round` with
`nearestEven`, `ceilRound`, and `floorRound`, and every direction is
`round (roundingFunction mode)` (`roundAt_eq_round`).
-/
noncomputable def roundAt (fmt : FloatFormat) (x : ℝ)
    (mode : IEEERoundingMode := .nearest) : ℝ :=
  match mode with
  | .nearest => round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) nearestEven x
  | .up => round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) ceilRound x
  | .down => round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) floorRound x
  | mode => round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) (roundingFunction mode) x

/-- Rounding in every direction is Flocq's rounding with the direction's integer rule. -/
theorem roundAt_eq_round (fmt : FloatFormat) (x : ℝ) (mode : IEEERoundingMode) :
    roundAt fmt x mode =
      round (β := Numerics.binaryRadix) (fexp := fexpOf fmt) (roundingFunction mode) x := by
  cases mode <;> rfl

/-- Every rounding direction fixes zero. -/
@[simp] theorem roundAt_zero (fmt : FloatFormat) (mode : IEEERoundingMode := .nearest) :
    roundAt fmt 0 mode = 0 := by
  rw [roundAt_eq_round]
  exact round_preserves_generic (roundingFunction mode) 0 genericRepresentable_zero

/--
Rounding a negated real gives the negation of rounding the real in the mirrored direction
`mode.negate`, which exchanges the two infinity directions and fixes the other four. Nearest-even
rounding commutes with negation.
-/
@[simp] theorem roundAt_neg (fmt : FloatFormat) (x : ℝ) (mode : IEEERoundingMode := .nearest) :
    roundAt fmt (-x) mode = -roundAt fmt x mode.negate := by
  have hrnd : negRound (roundingFunction mode) = roundingFunction mode.negate := by
    cases mode with
    | nearest =>
        funext value
        simp [IEEERoundingMode.negate, roundingFunction, negRound, nearestEven_neg]
    | nearestAway => exact negRound_nearestChoice_tieAway
    | towardZero => exact negRound_truncRound
    | up => exact negRound_ceilRound
    | down => exact negRound_floorRound
    | away => exact negRound_awayRound
  rw [roundAt_eq_round, roundAt_eq_round, round_neg, hrnd]

/-- Every rounding direction is monotone in the real input. -/
theorem roundAt_mono (fmt : FloatFormat) {x y : ℝ} (hxy : x ≤ y)
    (mode : IEEERoundingMode := .nearest) :
    roundAt fmt x mode ≤ roundAt fmt y mode := by
  rw [roundAt_eq_round, roundAt_eq_round]
  exact round_mono (roundingFunction mode) hxy

/--
Every finite decoded word belongs to its descriptor's precision and gradual-underflow grid.
The result includes custom biases, FNUZ, and finite-only encodings.
-/
theorem toReal_genericFormat_of_isFinite {fmt : FloatFormat} (x : Model fmt)
    (hfin : isFinite x = true) :
    GenericRepresentable Numerics.binaryRadix (fexpOf fmt) (toReal x) := by
  obtain ⟨d, hd⟩ := exists_toDyadic?_of_isFinite hfin
  obtain ⟨hsignificand, hexponent⟩ := toDyadic?_significand_lt_and_minSubnormalExponent_le x hd
  have hprec : (0 : ℤ) < fmt.fracWidth + 1 := by positivity
  apply (genericRepresentable_flt_iff fmt.minSubnormalExponent (fmt.fracWidth + 1) hprec _).2
  refine ⟨hprec, ⟨d.signedSignificand, d.exponent⟩, ?_, ?_, hexponent⟩
  · simp [toReal_eq, hd, Numerics.Dyadic.toReal, Flocq.toReal, bpow, Numerics.binaryRadix,
      Numerics.Radix.toReal]
  · cases hs : d.negative <;>
      simpa [Numerics.Dyadic.signedSignificand, Numerics.binaryRadix, hs] using hsignificand

/-- Rounding a finite decoded value back to its own format is the identity. -/
@[simp] theorem roundAt_toReal_eq {fmt : FloatFormat} (x : Model fmt)
    (hfin : isFinite x = true) :
    roundAt fmt (toReal x) = toReal x := by
  exact round_preserves_generic nearestEven (toReal x)
    (toReal_genericFormat_of_isFinite x hfin)

/-- Every rounding direction fixes one. -/
@[simp] theorem roundAt_one (fmt : FloatFormat) (mode : IEEERoundingMode := .nearest) :
    roundAt fmt 1 mode = 1 := by
  rw [roundAt_eq_round]
  exact round_preserves_generic (roundingFunction mode) 1
    (by simpa using toReal_genericFormat_of_isFinite (posOne fmt) (isFinite_posOne fmt))

namespace Dyadic

/-- The absolute value of a dyadic ignores its stored sign bit. -/
theorem abs_toReal (d : Numerics.Dyadic) :
    |d.toReal| = (d.significand : ℝ) * bpow Numerics.binaryRadix d.exponent := by
  have hnonneg : 0 ≤ (d.significand : ℝ) * (2 : ℝ) ^ d.exponent :=
    mul_nonneg (Nat.cast_nonneg _) (zpow_nonneg (by norm_num) _)
  cases hs : d.negative <;>
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hs, hnonneg,
      abs_of_nonneg, bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- A nonzero dyadic has the leading exponent predicted by its integer mantissa. -/
theorem magnitude_toReal (d : Numerics.Dyadic) (hm : d.significand ≠ 0) :
    magnitude Numerics.binaryRadix d.toReal =
      Int.ofNat d.significand.log2 + d.exponent + 1 := by
  have hmpos : (0 : ℝ) < d.significand := by exact_mod_cast Nat.pos_of_ne_zero hm
  calc
    magnitude Numerics.binaryRadix d.toReal =
        magnitude Numerics.binaryRadix |d.toReal| := by simp [magnitude]
    _ = magnitude Numerics.binaryRadix (d.significand : ℝ) + d.exponent := by
      rw [abs_toReal, magnitude_mul_bpow _ _ _ hmpos.ne']
    _ = Int.ofNat d.significand.log2 + d.exponent + 1 := by
      rw [magnitude_eq_int_log_add_one _ _ hmpos.ne', abs_of_pos hmpos,
        Int.log_natCast]
      simp only [binaryRadix, Nat.log2_eq_log_two, Int.ofNat_eq_natCast]
      omega

end Dyadic

/-- Canonical grid exponent of a nonzero exact dyadic, for every descriptor. -/
theorem cexp_dyadic (fmt : FloatFormat) (d : Numerics.Dyadic) (hm : d.significand ≠ 0) :
    cexp binaryRadix (fexpOf fmt) d.toReal =
      max ((d.significand.log2 : ℤ) + d.exponent - fmt.fracWidth) fmt.minSubnormalExponent := by
  rw [cexp, Dyadic.magnitude_toReal d hm]
  simp only [fexpOf, fltExp, Int.ofNat_eq_natCast]
  congr 1
  omega

/-- Lean's model and the rounded-real format choose the same exponent for a nonzero dyadic. -/
theorem cexp_toReal_eq_targetExponent (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) (hm : d.significand ≠ 0) :
    cexp Numerics.binaryRadix (fexpOf fmt) d.toReal =
      (FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent d.significand d.exponent) := by
  rw [cexp_dyadic fmt d hm, targetExponent_toModel,
    FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt]

/-- The canonical scaled mantissa of a dyadic is its signed magnitude at the target exponent. -/
theorem scaledMantissa_toReal (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) :
    scaledMantissa Numerics.binaryRadix (fexpOf fmt) d.toReal =
      (if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) *
        bpow Numerics.binaryRadix
          (d.exponent - (FloatFormat.toModel fmt).targetExponent
            (Float.Model.totalExponent d.significand d.exponent)) := by
  by_cases hm : d.significand = 0
  · simp [scaledMantissa, Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hm]
  rw [scaledMantissa, cexp_toReal_eq_targetExponent fmt d hfmt hm]
  have hpow := bpow.add_exp Numerics.binaryRadix d.exponent
    (-(FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent d.significand d.exponent))
  rw [show d.exponent - (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent d.significand d.exponent) =
      d.exponent + -(FloatFormat.toModel fmt).targetExponent
        (Float.Model.totalExponent d.significand d.exponent) by rfl]
  rw [hpow]
  cases hs : d.negative <;>
    simp only [Dyadic.toReal, Dyadic.signedSignificand, hs, Bool.false_eq_true, ↓reduceIte,
      Int.ofNat_eq_natCast, Int.cast_natCast, bpow, Radix.toReal, binaryRadix, Nat.cast_ofNat,
      zpow_neg, one_mul, Int.cast_neg, neg_mul, neg_inj] <;>
    ac_rfl

/-- Nearest-even rounding of a nonnegative dyadic agrees with executable shift-and-round. -/
theorem nearestEven_scaledMagnitude (mantissa : Nat) (exponent targetExponent : Int) :
    nearestEven
        ((mantissa : ℝ) * bpow Numerics.binaryRadix (exponent - targetExponent)) =
      Int.ofNat (roundMantissaAtExponentEven mantissa exponent targetExponent) := by
  by_cases hle : exponent ≤ targetExponent
  · let shift := (targetExponent - exponent).toNat
    have hshiftInt : (shift : Int) = targetExponent - exponent := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr hle)
    have hpow2 : (pow2 shift : ℝ) = (2 : ℝ) ^ shift := by
      simp [pow2, Nat.shiftLeft_eq]
    have hvalue :
        (mantissa : ℝ) * bpow Numerics.binaryRadix (exponent - targetExponent) =
          (mantissa : ℝ) / (pow2 shift : ℝ) := by
      rw [show exponent - targetExponent = -(shift : Int) by omega]
      rw [div_eq_mul_inv, hpow2]
      simp [bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
    rw [hvalue]
    simpa [roundMantissaAtExponentEven, hle, shift] using
      nearestEven_div_pow2_eq_roundShiftRightEven mantissa shift
  · let shift := (exponent - targetExponent).toNat
    have hshiftInt : (shift : Int) = exponent - targetExponent := by
      exact Int.toNat_of_nonneg (sub_nonneg.mpr (le_of_not_ge hle))
    have hvalue :
        (mantissa : ℝ) * bpow Numerics.binaryRadix (exponent - targetExponent) =
          (Nat.shiftLeft mantissa shift : Nat) := by
      rw [← hshiftInt]
      simp [bpow, Numerics.binaryRadix, Numerics.Radix.toReal, Nat.shiftLeft_eq]
    rw [hvalue]
    have hid :
        nearestEven ((Nat.shiftLeft mantissa shift : Nat) : ℝ) =
          Int.ofNat (Nat.shiftLeft mantissa shift) := by
      change nearestEven
          ((Int.ofNat (Nat.shiftLeft mantissa shift) : Int) : ℝ) =
        Int.ofNat (Nat.shiftLeft mantissa shift)
      exact ValidRnd.id (rnd := nearestEven)
        (Int.ofNat (Nat.shiftLeft mantissa shift))
    rw [hid]
    simp [roundMantissaAtExponentEven, hle, shift]

/-- Nearest-even rounding commutes with the sign stored in a dyadic value. -/
theorem nearestEven_scaledDyadic (sign : Bool) (mantissa : Nat)
    (exponent targetExponent : Int) :
    nearestEven
        ((if sign then (-1 : ℝ) else 1) * (mantissa : ℝ) *
          bpow Numerics.binaryRadix (exponent - targetExponent)) =
      if sign then
        -Int.ofNat (roundMantissaAtExponentEven mantissa exponent targetExponent)
      else
        Int.ofNat (roundMantissaAtExponentEven mantissa exponent targetExponent) := by
  cases sign <;>
    simp [nearestEven_scaledMagnitude,
      nearestEven_neg]

/-- The executable natural power of two has the same real value as the binary radix power. -/
theorem natCast_pow2_eq_bpow (exponent : Nat) :
    (pow2 exponent : ℝ) = bpow Numerics.binaryRadix exponent := by
  simp [pow2_eq_two_pow, bpow, Numerics.binaryRadix, Numerics.Radix.toReal]

/-- Real nearest-even grid rounding agrees with the integer significand rounder at every
binary descriptor, including custom biases and finite-only encodings. Upper packing is separate. -/
theorem roundAt_dyadic_grid (fmt : FloatFormat) (d : Numerics.Dyadic) :
    let target := max ((d.significand.log2 : ℤ) + d.exponent - fmt.fracWidth)
      fmt.minSubnormalExponent
    let rounded := roundMantissaAtExponentEven d.significand d.exponent target
    roundAt fmt d.toReal =
      (if d.negative then (-1 : ℝ) else 1) * (rounded : ℝ) *
        Flocq.bpow binaryRadix target := by
  dsimp only
  let target := max ((d.significand.log2 : ℤ) + d.exponent - fmt.fracWidth)
    fmt.minSubnormalExponent
  by_cases hm : d.significand = 0
  · have hr : roundMantissaAtExponentEven d.significand d.exponent target = 0 := by
      have h := nearestEven_scaledMagnitude 0 d.exponent target
      rw [Nat.cast_zero, zero_mul, ← Int.cast_zero, ValidRnd.id (rnd := nearestEven)] at h
      simpa [hm] using (Int.ofNat_eq_zero.mp h.symm)
    change roundAt fmt d.toReal =
      (if d.negative then (-1 : ℝ) else 1) *
        (roundMantissaAtExponentEven d.significand d.exponent target : ℝ) *
          Flocq.bpow binaryRadix target
    rw [hr]
    simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hm]
  have he : cexp binaryRadix (fexpOf fmt) d.toReal = target := cexp_dyadic fmt d hm
  have hs : scaledMantissa binaryRadix (fexpOf fmt) d.toReal =
      (if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) *
        Flocq.bpow binaryRadix (d.exponent - target) := by
    rw [scaledMantissa, he, sub_eq_add_neg, bpow.add_exp]
    cases hsign : d.negative <;>
      simp [Numerics.Dyadic.toReal, Numerics.Dyadic.signedSignificand, hsign,
        Flocq.bpow, binaryRadix, Numerics.Radix.toReal] <;> ac_rfl
  rw [roundAt, Flocq.round, hs, nearestEven_scaledDyadic, he]
  cases d.negative <;> simp [Flocq.toReal, target]

/--
Rounded-real semantics of a dyadic at a conventional IEEE descriptor.

The integer on the right is computed entirely by shifts and nearest-even rounding. The exponent is
chosen by Lean's generic logical float model and independently characterized by `fexpOf`. A zero
significand rounds to zero.
-/
theorem roundAt_dyadic_eq (fmt : FloatFormat) (d : Numerics.Dyadic)
    (hfmt : fmt.isIEEE = true) :
    let target := (FloatFormat.toModel fmt).targetExponent
      (Float.Model.totalExponent d.significand d.exponent)
    let rounded := roundMantissaAtExponentEven d.significand d.exponent target
    roundAt fmt d.toReal =
      ((if d.negative then -Int.ofNat rounded else Int.ofNat rounded) : Int) *
        bpow Numerics.binaryRadix target := by
  dsimp only
  rw [targetExponent_toModel, ← FloatFormat.minSubnormalExponent_eq_ieee fmt hfmt,
    roundAt_dyadic_grid]
  cases d.negative <;> simp

/--
Real value of a finished rounded mantissa on the subnormal grid.

The mantissa may be zero, in which case the packed value is a signed zero, or reach
`2 ^ fracWidth`, in which case it is the least normal value. Both have the stated real value.
-/
theorem toReal_ofModel_finishRoundedMantissa_minSubnormal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Float.Model.UnpackedFloat.Sign)
      (rounded : Nat)
    (hle : rounded ≤ pow2 fmt.fracWidth) :
    toReal (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, FloatFormat.ieeeMinSubnormalExponent fmt))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) *
        ((rounded : ℝ) *
          bpow Numerics.binaryRadix (FloatFormat.ieeeMinSubnormalExponent fmt)) := by
  by_cases hzero : rounded = 0
  · rw [hzero, finishRoundedMantissa_zero,
      toReal_ofModel_zero fmt (FloatFormat.supportsSignedZero_eq_true_of_isIEEE fmt hfmt)]
    simp
  · rw [finishRoundedMantissa_at_minSubnormal fmt sign rounded hzero hle,
      toReal_ofModel_finite_at_minSubnormal fmt hfmt sign rounded hzero
        (by simpa [pow2_eq_two_pow] using hle)]
    ac_rfl

/--
Real value of a finished normalized rounded mantissa with leading bit at unbiased exponent `k`.

The mantissa lies in `[2 ^ fracWidth, 2 ^ (fracWidth + 1)]`. The upper endpoint is the carry that
`finishRoundedMantissa` renormalizes to exponent `k + 1`. The finiteness hypothesis excludes IEEE
overflow, which has no value in `ℝ`.
-/
theorem toReal_ofModel_finishRoundedMantissa_normal
    (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (sign : Float.Model.UnpackedFloat.Sign)
      (rounded : Nat) (k : Int)
    (hlow : pow2 fmt.fracWidth ≤ rounded) (hhigh : rounded ≤ pow2 (fmt.fracWidth + 1))
    (hk : FloatFormat.ieeeMinNormalExponent fmt ≤ k)
    (hfin : isFinite (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign
          (rounded, k - fmt.fracWidth))) = true) :
    toReal (ofModel fmt
        (finishRoundedMantissa (FloatFormat.toModel fmt) sign (rounded, k - fmt.fracWidth))) =
      (if modelSignBit sign then (-1 : ℝ) else 1) *
        ((rounded : ℝ) * bpow Numerics.binaryRadix (k - fmt.fracWidth)) := by
  have hbiased : ∀ e : Int, FloatFormat.ieeeMinNormalExponent fmt ≤ e →
      0 < e - fmt.fracWidth + (FloatFormat.toModel fmt).exponentBias +
        (FloatFormat.toModel fmt).mantissaBitsWithoutImplicit := by
    intro e he
    change 0 < e - fmt.fracWidth + fmt.bias + fmt.fracWidth
    unfold FloatFormat.ieeeMinNormalExponent at he
    simp only [Int.ofNat_eq_natCast] at he ⊢
    omega
  by_cases hcarry : rounded = pow2 (fmt.fracWidth + 1)
  · rw [hcarry, finishRoundedMantissa_normalized_carry fmt sign k hk] at hfin ⊢
    have hpow : pow2 fmt.fracWidth ≠ 0 := by simp [pow2_eq_two_pow]
    rw [toReal_ofModel_finite_normal fmt hfmt sign (pow2 fmt.fracWidth) (k + 1 - fmt.fracWidth)
      hpow
      (by
        change (pow2 fmt.fracWidth).log2 + 1 = 1 + fmt.fracWidth
        simp [pow2_eq_two_pow, Nat.add_comm])
      (hbiased (k + 1) (by omega))
      (noOverflow_of_isFinite_ofModel_finite fmt hfmt sign (pow2 fmt.fracWidth)
        (k + 1 - fmt.fracWidth) hpow hfin)]
    rw [natCast_pow2_eq_bpow, natCast_pow2_eq_bpow, mul_assoc, ← bpow.add_exp, ← bpow.add_exp]
    congr 2
    push_cast
    omega
  · have hhighLt : rounded < pow2 (fmt.fracWidth + 1) := lt_of_le_of_ne hhigh hcarry
    have hne : rounded ≠ 0 :=
      Nat.ne_of_gt ((show 0 < pow2 fmt.fracWidth by simp [pow2_eq_two_pow]).trans_le hlow)
    rw [finishRoundedMantissa_normalized fmt sign rounded k hlow hhighLt hk] at hfin ⊢
    rw [toReal_ofModel_finite_normal fmt hfmt sign rounded (k - fmt.fracWidth) hne
      (by
        change rounded.log2 + 1 = 1 + fmt.fracWidth
        rw [log2_eq_fracWidth_of_normalized fmt rounded hlow hhighLt]
        omega)
      (hbiased k hk)
      (noOverflow_of_isFinite_ofModel_finite fmt hfmt sign rounded (k - fmt.fracWidth) hne hfin)]
    ac_rfl

end Model
end FloatLib.Floats.Formats.BinaryInterchange
