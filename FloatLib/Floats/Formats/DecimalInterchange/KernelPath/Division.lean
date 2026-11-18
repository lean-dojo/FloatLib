/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.KernelPath.Quantum

/-!
# Kernel path of decimal division

`Arithmetic.div` (IEEE 754-2019 §5.4.1) rounds the exact quotient of two finite data, a
rational number that is in general not a coefficient at an exponent, so the kernel projection
`KernelPath.project` of sums and products does not apply to it.

`projectRatio` rounds a ratio of natural numbers on the scale of the least quantum of the
format, `(num / den) × 10 ^ minQuantum`: the integer part of the ratio gives the number of
digits and so the rounding quantum, one division with remainder by the denominator at that
quantum gives the rounded coefficient, the remainder decides the increment and the `inexact`
flag, and one comparison decides whether the value is below the least normal magnitude. An exact
result is moved to the preferred exponent by `preferredCohort`, as in the specification.
`projectRatio_eq` proves it equal to `projectMagnitude` for every format, rounding direction,
numerator, nonzero denominator and preferred exponent.

`div` is the kernel form of `Arithmetic.div`: for a finite dividend and a finite nonzero
divisor the two coefficients are put on the scale of the least quantum by one power of ten, and
`projectRatio` rounds their ratio with the difference of the two quantum exponents as the
preferred exponent. `div_eq`, tagged `@[kernel_optimize]`, proves it equal to the specification
for every format, rounding direction and pair of data.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.KernelPath

open FloatLib.Numerics

/--
The outcome of the magnitude `(num / den) × 10 ^ minQuantum` of sign `negative` rounded into
`f`, with `preferred` as the preferred exponent of an exact result (`projectRatio_eq`).
-/
def projectRatio (f : Format) (mode : RoundingMode) (negative : Bool) (num den : Nat)
    (preferred : Int) : Outcome :=
  (fun shift =>
    (fun divisor =>
      (fun lower remainder =>
        deliverRounded f mode negative
          (Nat.add lower (increment mode negative lower remainder divisor)) shift
          (Nat.ble 1 remainder)
          (Nat.ble (Nat.succ num) (Nat.mul den (Nat.pow 10 (Nat.mul 3 f.declets)))) preferred)
        (Nat.div num divisor) (Nat.mod num divisor))
      (Nat.mul den (Nat.pow 10 shift)))
    (Nat.sub (decimalLength (Nat.div num den)) (Nat.succ (Nat.mul 3 f.declets)))

/--
`projectRatio` is the specified projection of the ratio on the scale of the least quantum: the
same datum and the same flags, for every format, rounding direction, sign, numerator, nonzero
denominator and preferred exponent.
-/
theorem projectRatio_eq (f : Format) (mode : RoundingMode) (negative : Bool) (num : Nat)
    {den : Nat} (hden : den ≠ 0) (preferred : Int) :
    projectRatio f mode negative num den preferred =
      projectMagnitude f mode negative ((num : ℚ) / (den : ℚ) * (10 : ℚ) ^ f.minQuantum)
        preferred := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  have hdenq : (0 : ℚ) < (den : ℚ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hden)
  have hmin : (0 : ℚ) < (10 : ℚ) ^ f.minQuantum := zpow_pos (by norm_num) _
  have hdivf : ∀ m n : Nat, Nat.div m n = m / n := fun _ _ => rfl
  have hmodf : ∀ m n : Nat, Nat.mod m n = m % n := fun _ _ => rfl
  have hprecision : 3 * f.declets + 1 = f.precision := rfl
  unfold projectRatio
  simp only [Nat.add_eq, Nat.sub_eq, Nat.mul_eq, Nat.pow_eq, Nat.succ_eq_add_one, hdivf, hmodf,
    decimalLength_eq_log, hprecision]
  obtain ⟨x, hx⟩ : ∃ x : ℚ, x = (num : ℚ) / (den : ℚ) * (10 : ℚ) ^ f.minQuantum := ⟨_, rfl⟩
  rw [← hx]
  have hscaled : x / (10 : ℚ) ^ f.minQuantum = (num : ℚ) / (den : ℚ) := by
    rw [hx, mul_div_assoc, div_self hmin.ne', mul_one]
  generalize hshift : Nat.log 10 (num / den) + 1 - f.precision = shift
  have hquantum : roundingQuantum f x = (shift : Int) - f.bias := by
    rw [roundingQuantum_eq, hscaled, scaleShift, Rat.natFloor_natCast_div_natCast, hshift,
      Format.minQuantum]
    ring
  have hdivisor : 0 < den * 10 ^ shift := Nat.mul_pos (Nat.pos_of_ne_zero hden) (by positivity)
  have hvalue : x / (10 : ℚ) ^ ((shift : Int) - f.bias) =
      (num : ℚ) / ((den * 10 ^ shift : Nat) : ℚ) := by
    have hpow : (10 : ℚ) ^ ((shift : Int) - f.bias) =
        ((10 ^ shift : Nat) : ℚ) * (10 : ℚ) ^ f.minQuantum := by
      rw [Format.minQuantum, sub_eq_add_neg, zpow_add₀ hten, zpow_natCast]
      push_cast
      rfl
    rw [hpow, hx, mul_div_mul_right _ _ hmin.ne', div_div, Nat.cast_mul]
  have hround : mode.roundAt negative x ((shift : Int) - f.bias) =
      num / (den * 10 ^ shift) +
        increment mode negative (num / (den * 10 ^ shift)) (num % (den * 10 ^ shift))
          (den * 10 ^ shift) := by
    rw [RoundingMode.roundAt, hvalue, roundMagnitude_natCast_div mode negative num _ hdivisor]
  generalize den * 10 ^ shift = D at hdivisor hvalue hround ⊢
  have hsplit := Nat.div_add_mod num D
  have hlt : num % D < D := Nat.mod_lt _ hdivisor
  generalize num / D = lower at hround hsplit ⊢
  generalize num % D = rem at hround hsplit hlt ⊢
  have hone := increment_le_one mode negative lower hlt
  have hzero : rem = 0 → increment mode negative lower rem D = 0 := fun h => by
    rw [h]
    exact increment_zero mode negative lower hdivisor
  generalize increment mode negative lower rem D = inc at hround hone hzero ⊢
  generalize hR : lower + inc = R at hround ⊢
  have hDq : (D : ℚ) ≠ 0 := (Nat.cast_pos.2 hdivisor).ne'
  have hnat : R * D = num ↔ rem = 0 := by
    subst hR
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hone with rfl | rfl
    · rw [Nat.add_zero, Nat.mul_comm]
      omega
    · have hrem : rem ≠ 0 := fun h => absurd (hzero h) (by decide)
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      omega
  have hinexact : decide (((roundedPair f mode negative x).1 : ℚ) *
      (10 : ℚ) ^ (roundedPair f mode negative x).2 ≠ x) = Nat.ble 1 rem := by
    have hval := roundedPair_value f mode negative x
    rw [hquantum, hround] at hval
    have hx' : x = (num : ℚ) / (D : ℚ) * (10 : ℚ) ^ ((shift : Int) - f.bias) := by
      rw [← hvalue, div_mul_cancel₀ _ (zpow_ne_zero _ hten)]
    have hcast : ((R : ℚ) * (D : ℚ) = (num : ℚ)) ↔ R * D = num := by norm_cast
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq, hval, ne_eq, hx',
      mul_left_inj' (zpow_ne_zero _ hten), eq_div_iff hDq, hcast, hnat]
    omega
  have htiny : decide (x < f.minNormal) = Nat.ble (num + 1) (den * 10 ^ (3 * f.declets)) := by
    have hp : f.precision - 1 = 3 * f.declets := rfl
    rw [Bool.eq_iff_iff, decide_eq_true_eq, Nat.ble_eq, Format.minNormal, ← div_lt_iff₀ hmin,
      hscaled, div_lt_iff₀ hdenq, hp, Nat.add_one_le_iff, Nat.mul_comm den]
    norm_cast
  have hpair : roundedPair f mode negative x =
      if R = f.coefficientBound then (f.payloadBound, (shift : Int) - f.bias + 1)
      else (R, (shift : Int) - f.bias) := by
    rw [roundedPair, hquantum, hround, f.carry_eq]
  rw [projectMagnitude_eq]
  dsimp only
  rw [hinexact, htiny]
  exact deliverRounded_eq f mode negative R shift _ _ preferred _ hpair

/--
The quotient of two finite data with a nonzero divisor, on natural numbers (`divFinite_eq`):
the coefficients on the scale of the least quantum, and `projectRatio` of their ratio with the
difference of the quantum exponents as the preferred exponent and the sign of the quotient.
-/
def divFinite (f : Format) (mode : RoundingMode) (sx : Bool) (cx : Nat) (qx : Int) (sy : Bool)
    (cy : Nat) (qy : Int) : Outcome :=
  (fun preferred =>
    offsets preferred f.bias fun above below =>
      projectRatio f mode (differ sx sy) (Nat.mul cx (Nat.pow 10 above))
        (Nat.mul cy (Nat.pow 10 below)) preferred)
    (Int.sub qx qy)

/-- `divFinite` is `Arithmetic.div` on two finite data with a nonzero divisor. -/
theorem divFinite_eq (f : Format) (mode : RoundingMode) (sx : Bool) (cx : Nat) (qx : Int)
    (sy : Bool) {cy : Nat} (hcy : cy ≠ 0) (qy : Int) :
    Arithmetic.div f mode (.finite sx cx qx) (.finite sy cy qy) =
      divFinite f mode sx cx qx sy cy qy := by
  have hten : (10 : ℚ) ≠ 0 := by norm_num
  have hspec : Arithmetic.div f mode (.finite sx cx qx) (.finite sy cy qy) =
      DecimalInterchange.project f mode
        (Datum.finiteValue sx cx qx / Datum.finiteValue sy cy qy) (qx - qy) (sx ^^ sy) := by
    simp only [Arithmetic.div, hcy, ↓reduceIte]
  have hsub : ∀ m n : Int, Int.sub m n = m - n := fun _ _ => rfl
  rw [hspec, divFinite]
  dsimp only
  rw [offsets_eq]
  simp only [hsub, Nat.mul_eq, Nat.pow_eq]
  generalize ha : (qx - qy + f.bias).toNat = a
  generalize hb : (-(qx - qy + f.bias)).toNat = b
  have hab : (a : Int) - (b : Int) = qx - qy + f.bias := by omega
  have hB : (0 : ℚ) < (cy : ℚ) * (10 : ℚ) ^ qy :=
    mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hcy)) (zpow_pos (by norm_num) _)
  rw [projectRatio_eq f mode _ _ (Nat.mul_ne_zero hcy (by positivity)),
    DecimalInterchange.project, differ_eq]
  congr 1
  · by_cases hcx : cx = 0
    · have hzero : Datum.finiteValue sx cx qx / Datum.finiteValue sy cy qy = 0 := by
        rw [(Datum.finiteValue_eq_zero_iff sx cx qx).2 hcx, zero_div]
      rw [ite_eq_left hzero]
    · have hA : (0 : ℚ) < (cx : ℚ) * (10 : ℚ) ^ qx :=
        mul_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hcx)) (zpow_pos (by norm_num) _)
      have hne : Datum.finiteValue sx cx qx / Datum.finiteValue sy cy qy ≠ 0 :=
        div_ne_zero (fun h => hcx ((Datum.finiteValue_eq_zero_iff sx cx qx).1 h))
          (fun h => hcy ((Datum.finiteValue_eq_zero_iff sy cy qy).1 h))
      have hpos := div_pos hA hB
      rw [ite_eq_right hne]
      cases sx <;> cases sy <;>
        simp only [Datum.finiteValue, Bool.false_eq_true, ↓reduceIte, one_mul, neg_mul, div_neg,
          neg_div, neg_neg]
      · exact decide_eq_false (not_lt.2 hpos.le)
      · exact decide_eq_true (neg_lt_zero.2 hpos)
      · exact decide_eq_true (neg_lt_zero.2 hpos)
      · exact decide_eq_false (not_lt.2 hpos.le)
  · have hexp : (10 : ℚ) ^ qx / (10 : ℚ) ^ qy =
        (10 : ℚ) ^ a / (10 : ℚ) ^ b * (10 : ℚ) ^ f.minQuantum := by
      rw [← zpow_sub₀ hten, ← zpow_natCast (10 : ℚ) a, ← zpow_natCast (10 : ℚ) b,
        ← zpow_sub₀ hten, ← zpow_add₀ hten]
      congr 1
      unfold Format.minQuantum
      omega
    rw [abs_div, Datum.finiteValue_abs, Datum.finiteValue_abs]
    push_cast
    rw [mul_div_mul_comm, hexp]
    ring

/--
Kernel form of `Arithmetic.div` (`div_eq`): a finite dividend and a finite nonzero divisor are
divided on natural numbers by `divFinite`. A zero divisor, an infinity and a NaN are left to the
specification.
-/
def div (f : Format) (mode : RoundingMode) (x y : Datum) : Outcome :=
  Datum.casesOn (motive := fun _ => Outcome) x
    (fun sx cx qx => Datum.casesOn (motive := fun _ => Outcome) y
      (fun sy cy qy =>
        Bool.casesOn (motive := fun _ => Outcome) (Nat.beq cy 0)
          (divFinite f mode sx cx qx sy cy qy) (Arithmetic.div f mode x y))
      (fun _ => Arithmetic.div f mode x y) (fun _ _ _ => Arithmetic.div f mode x y))
    (fun _ => Arithmetic.div f mode x y) (fun _ _ _ => Arithmetic.div f mode x y)

/--
IEEE 754-2019 §5.4.1 division on decimal data is its kernel form, for every format, rounding
direction and pair of data: the same datum and the same flags.
-/
@[kernel_optimize] theorem div_eq (f : Format) (mode : RoundingMode) (x y : Datum) :
    Arithmetic.div f mode x y = div f mode x y := by
  rcases x with ⟨sx, cx, qx⟩ | sx | ⟨sx, tx, px⟩ <;>
    rcases y with ⟨sy, cy, qy⟩ | sy | ⟨sy, ty, py⟩ <;> try rfl
  rcases cy with _ | cy
  · rfl
  · exact divFinite_eq f mode sx cx qx sy (Nat.succ_ne_zero cy) qy

end FloatLib.Floats.Formats.DecimalInterchange.KernelPath
