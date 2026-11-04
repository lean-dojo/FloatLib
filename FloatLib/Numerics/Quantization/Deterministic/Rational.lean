/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Quantization.Deterministic.Quotient
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rat.Floor

/-!
# Deterministic nearest-even rational rounding

This is the exact `Rat`-to-`Int` case of the shared quotient-rounding decision. It uses integer
numerator and denominator arithmetic throughout, and no floating approximation enters while a tie is
decided.

Our proofs cover both signs, the half-unit error bound, fixed points, and exact half steps, and we
keep those facts beside the executable definition so that fixed-point and mixed-precision code share
one rounding primitive with a stable contract.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- Round an exact rational to the nearest integer, breaking halfway cases toward the even result. -/
@[inline] def roundRatEven (x : Rat) : Int :=
  let magnitude := Int.ofNat (roundQuotientEven x.num.natAbs x.den)
  if x.num < 0 then -magnitude else magnitude

private theorem quotient_value (numerator denominator : Nat) :
    (numerator : ℚ) / denominator =
      (numerator / denominator : Nat) + (numerator % denominator : Nat) / denominator := by
  simpa only [Rat.floor_natCast_div_natCast, ← Int.natCast_ediv, Int.cast_natCast,
    Int.fract_div_natCast_eq_div_natCast_mod] using
    (Int.floor_add_fract ((numerator : ℚ) / denominator)).symm

/-- The floor quotient falls short of the exact quotient by the remainder fraction. -/
private theorem floor_error_eq (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    |((numerator / denominator : Nat) : ℚ) - (numerator : ℚ) / denominator| =
      (numerator % denominator : Nat) / (denominator : ℚ) := by
  have hdenominatorRatPos : (0 : ℚ) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  rw [quotient_value numerator denominator]
  rw [show
    ((numerator / denominator : Nat) : ℚ) -
        ((numerator / denominator : Nat) +
          (numerator % denominator : Nat) / denominator) =
      -((numerator % denominator : Nat) / denominator) by ring]
  rw [abs_neg, abs_of_nonneg (div_nonneg (by positivity) hdenominatorRatPos.le)]

/-- The incremented quotient exceeds the exact quotient by one minus the remainder fraction. -/
private theorem ceil_error_eq (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    |(((numerator / denominator : Nat) + 1 : Nat) : ℚ) - (numerator : ℚ) / denominator| =
      1 - (numerator % denominator : Nat) / (denominator : ℚ) := by
  have hdenominatorPos : 0 < denominator := Nat.pos_of_ne_zero hdenominator
  have hdenominatorRatPos : (0 : ℚ) < denominator := by
    exact_mod_cast hdenominatorPos
  have hremainderLe :
      (numerator % denominator : Nat) / (denominator : ℚ) ≤ 1 := by
    rw [div_le_iff₀ hdenominatorRatPos]
    norm_num
    exact_mod_cast (Nat.mod_lt numerator hdenominatorPos).le
  rw [quotient_value numerator denominator]
  push_cast
  rw [show
    (((numerator / denominator : Nat) : ℚ) + 1) -
        (((numerator / denominator : Nat) : ℚ) +
          (numerator % denominator : Nat) / denominator) =
      1 - (numerator % denominator : Nat) / denominator by ring]
  rw [abs_of_nonneg (by linarith)]

private theorem floor_error_le_half (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0)
    (hround : 2 * (numerator % denominator) ≤ denominator) :
    |((numerator / denominator : Nat) : ℚ) - (numerator : ℚ) / denominator| ≤
      (1 : ℚ) / 2 := by
  have hdenominatorRatPos : (0 : ℚ) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hroundRat :
      (2 : ℚ) * (numerator % denominator : Nat) ≤ denominator := by
    exact_mod_cast hround
  rw [floor_error_eq numerator denominator hdenominator, div_le_iff₀ hdenominatorRatPos]
  linarith

private theorem ceil_error_le_half (numerator denominator : Nat)
    (hdenominator : denominator ≠ 0)
    (hround : denominator ≤ 2 * (numerator % denominator)) :
    |(((numerator / denominator : Nat) + 1 : Nat) : ℚ) -
        (numerator : ℚ) / denominator| ≤ (1 : ℚ) / 2 := by
  have hdenominatorRatPos : (0 : ℚ) < denominator := by
    exact_mod_cast Nat.pos_of_ne_zero hdenominator
  have hroundRat :
      (denominator : ℚ) ≤ 2 * (numerator % denominator : Nat) := by
    exact_mod_cast hround
  have hhalfLeRemainder :
      (1 : ℚ) / 2 ≤ (numerator % denominator : Nat) / denominator := by
    rw [le_div_iff₀ hdenominatorRatPos]
    linarith
  rw [ceil_error_eq numerator denominator hdenominator]
  linarith

/--
Nearest-even quotient rounding differs from the exact nonnegative rational by at most one half.
-/
theorem roundQuotientEven_error_le_half
    (numerator denominator : Nat) (hdenominator : denominator ≠ 0) :
    |((roundQuotientEven numerator denominator : Nat) : ℚ) -
        (numerator : ℚ) / denominator| ≤ (1 : ℚ) / 2 := by
  unfold roundQuotientEven
  dsimp only
  split <;> rename_i hless
  · exact floor_error_le_half numerator denominator hdenominator hless.le
  split <;> rename_i hgreater
  · exact ceil_error_le_half numerator denominator hdenominator hgreater.le
  have hequal : 2 * (numerator % denominator) = denominator := by omega
  split
  · exact floor_error_le_half numerator denominator hdenominator hequal.le
  · exact ceil_error_le_half numerator denominator hdenominator hequal.ge

/-- Nearest-even rational rounding fixes every integer. -/
@[simp, grind =] theorem roundRatEven_intCast (value : Int) :
    roundRatEven (value : Rat) = value := by
  have hone : roundQuotientEven value.natAbs 1 = value.natAbs := by
    simp only [roundQuotientEven, Nat.div_one, Nat.mod_one, mul_zero,
      Nat.zero_lt_one, ite_true]
  unfold roundRatEven
  dsimp only
  by_cases hvalue : (value : Rat).num < 0
  · rw [ite_eq_left hvalue]
    simp only [Rat.num_intCast, Rat.den_intCast]
    rw [hone]
    have hvalue' : value < 0 := by
      simpa only [Rat.num_intCast] using hvalue
    simp [abs_of_neg hvalue']
  · rw [ite_eq_right hvalue]
    simp only [Rat.num_intCast, Rat.den_intCast]
    rw [hone]
    have hvalue' : ¬ value < 0 := by
      simpa only [Rat.num_intCast] using hvalue
    simp [abs_of_nonneg (Int.not_lt.mp hvalue')]

/-- Signed rational rounding has the same absolute error as rounding its magnitude. -/
theorem roundRatEven_error_eq_magnitude (x : Rat) :
    |(roundRatEven x : Rat) - x| =
      |(roundQuotientEven x.num.natAbs x.den : Rat) - (x.num.natAbs : Rat) / x.den| := by
  unfold roundRatEven
  dsimp only
  by_cases hnum : x.num < 0
  · rw [ite_eq_left hnum]
    have habsInt : Int.ofNat x.num.natAbs = -x.num := by
      simp [abs_of_neg hnum]
    have habsRat : (x.num.natAbs : Rat) = -(x.num : Rat) := by
      simpa using congrArg (fun value : Int ↦ (value : Rat)) habsInt
    rw [habsRat, neg_div, Rat.num_div_den]
    push_cast
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast]
    rw [show -(roundQuotientEven x.num.natAbs x.den : Rat) - x =
      -((roundQuotientEven x.num.natAbs x.den : Rat) + x) by ring, abs_neg]
    simp only [sub_neg_eq_add]
  · rw [ite_eq_right hnum]
    have habsInt : Int.ofNat x.num.natAbs = x.num := by
      simp [abs_of_nonneg (Int.not_lt.mp hnum)]
    have habsRat : (x.num.natAbs : Rat) = (x.num : Rat) := by
      simpa using congrArg (fun value : Int ↦ (value : Rat)) habsInt
    rw [habsRat, Rat.num_div_den]
    rfl

/-- Nearest-even rational rounding differs from its exact input by at most one half. -/
theorem roundRatEven_error_le_half (x : Rat) :
    |(roundRatEven x : Rat) - x| ≤ (1 : Rat) / 2 := by
  rw [roundRatEven_error_eq_magnitude]
  exact roundQuotientEven_error_le_half _ _ x.den_nz

/-- A candidate strictly within half a unit is the unique rounded integer. -/
theorem roundRatEven_eq_of_error_lt_half (x : Rat) (n : Int)
    (h : |(n : Rat) - x| < (1 : Rat) / 2) : roundRatEven x = n := by
  have hr := abs_le.mp (roundRatEven_error_le_half x)
  have hn := abs_lt.mp h
  have hl : n - 1 < roundRatEven x := by
    have hh : ((n - 1 : Int) : Rat) < (roundRatEven x : Rat) := by push_cast; linarith
    exact_mod_cast hh
  have hu : roundRatEven x < n + 1 := by
    have hh : (roundRatEven x : Rat) < ((n + 1 : Int) : Rat) := by push_cast; linarith
    exact_mod_cast hh
  omega

/-- The delivered integer is at least as close as every competing integer. -/
theorem roundRatEven_nearest (x : Rat) (n : Int) :
    |(roundRatEven x : Rat) - x| ≤ |(n : Rat) - x| := by
  by_cases h : |(n : Rat) - x| < (1 : Rat) / 2
  · rw [roundRatEven_eq_of_error_lt_half x n h]
  · exact (roundRatEven_error_le_half x).trans (le_of_not_gt h)

/-- An exact quotient midpoint rounds to an even natural number. -/
theorem roundQuotientEven_even_of_tie (numerator denominator : Nat)
    (htie : 2 * (numerator % denominator) = denominator) :
    roundQuotientEven numerator denominator % 2 = 0 := by
  by_cases he : numerator / denominator % 2 = 0
  · simp [roundQuotientEven, htie, he]
  · have ho : numerator / denominator % 2 = 1 := by omega
    simp [roundQuotientEven, htie, Nat.add_mod, ho]

/-- Away from a quotient midpoint the error is strictly less than half a unit. -/
theorem roundQuotientEven_error_lt_half (numerator denominator : Nat)
    (hd : denominator ≠ 0) (ht : 2 * (numerator % denominator) ≠ denominator) :
    |(roundQuotientEven numerator denominator : Rat) -
      (numerator : Rat) / denominator| < (1 : Rat) / 2 := by
  have hdp : (0 : Rat) < denominator := by exact_mod_cast Nat.pos_of_ne_zero hd
  unfold roundQuotientEven
  dsimp only
  split
  · rename_i h
    have hh : (2 : Rat) * (numerator % denominator : Nat) < denominator := by
      exact_mod_cast h
    rw [floor_error_eq numerator denominator hd, div_lt_iff₀ hdp]
    linarith
  · rename_i h
    have hg : denominator < 2 * (numerator % denominator) := by omega
    have hh : (denominator : Rat) < 2 * (numerator % denominator : Nat) := by
      exact_mod_cast hg
    have hhalf : (1 : Rat) / 2 < (numerator % denominator : Nat) / (denominator : Rat) := by
      rw [lt_div_iff₀ hdp]
      linarith
    rw [ite_eq_left hg, ceil_error_eq numerator denominator hd]
    linarith

/-- An exact quotient midpoint rounds to an even integer, regardless of its sign. -/
theorem roundRatEven_even_of_quotient_tie (x : Rat)
    (ht : 2 * (x.num.natAbs % x.den) = x.den) : roundRatEven x % 2 = 0 := by
  have he := roundQuotientEven_even_of_tie _ _ ht
  have hei : (roundQuotientEven x.num.natAbs x.den : Int) % 2 = 0 := by
    exact_mod_cast he
  unfold roundRatEven
  dsimp only
  split <;> simp only [Int.ofNat_eq_natCast] <;> omega

/-- Half-unit error can occur only when the delivered integer is even, for either sign. -/
theorem roundRatEven_even_of_error_eq_half (x : Rat)
    (h : |(roundRatEven x : Rat) - x| = (1 : Rat) / 2) : roundRatEven x % 2 = 0 := by
  apply roundRatEven_even_of_quotient_tie
  by_contra hn
  have he := roundQuotientEven_error_lt_half _ _ x.den_nz hn
  rw [← roundRatEven_error_eq_magnitude, h] at he
  exact (lt_irrefl _ he)

/-- Every half-integer rounds to its even neighbor, including negative inputs. -/
theorem roundRatEven_half_step (n : Int) :
    roundRatEven ((n : Rat) + (1 : Rat) / 2) = if n % 2 = 0 then n else n + 1 := by
  let r := roundRatEven ((n : Rat) + (1 : Rat) / 2)
  have hb := abs_le.mp (roundRatEven_error_le_half ((n : Rat) + (1 : Rat) / 2))
  have hlo : n ≤ r := by
    have hh : (n : Rat) ≤ (r : Rat) := by dsimp [r]; linarith
    exact_mod_cast hh
  have hhi : r ≤ n + 1 := by
    have hh : (r : Rat) ≤ ((n + 1 : Int) : Rat) := by dsimp [r]; push_cast; linarith
    exact_mod_cast hh
  have he : |(r : Rat) - ((n : Rat) + (1 : Rat) / 2)| = (1 : Rat) / 2 := by
    have hr : r = n ∨ r = n + 1 := by omega
    rcases hr with hr | hr <;> rw [hr] <;> push_cast <;> norm_num
  have hpar := roundRatEven_even_of_error_eq_half _ he
  change r % 2 = 0 at hpar
  change r = _
  split <;> omega

/-- The shared quotient algorithm agrees with the floor/ceiling nearest-even decision. -/
theorem roundRatEven_eq_floor_ceil (x : Rat) :
    roundRatEven x =
      if x.floor = x.ceil then x.floor
      else if x - (x.floor : Rat) < (x.ceil : Rat) - x then x.floor
      else if (x.ceil : Rat) - x < x - (x.floor : Rat) then x.ceil
      else if x.floor % 2 = 0 then x.floor else x.ceil := by
  have hl := Rat.floor_le x
  have hu : x ≤ (x.ceil : Rat) := Rat.le_ceil
  split
  · rename_i h
    have hx : x = (x.floor : Rat) := by rw [← h] at hu; exact le_antisymm hu hl
    conv_lhs => rw [hx, roundRatEven_intCast]
  · rename_i h
    have hstep : x.ceil = x.floor + 1 := by
      have hlo : x.floor ≤ x.ceil := by exact_mod_cast hl.trans hu
      have hhi : x.ceil ≤ x.floor + 1 := Rat.ceil_le_iff.mpr (Rat.lt_floor_add_one x).le
      omega
    have hstepRat : (x.ceil : Rat) = (x.floor : Rat) + 1 := by exact_mod_cast hstep
    split
    · rename_i hnear
      apply roundRatEven_eq_of_error_lt_half
      rw [abs_of_nonpos (sub_nonpos.mpr hl)]
      linarith
    · rename_i hnear
      split
      · rename_i hfar
        apply roundRatEven_eq_of_error_lt_half
        rw [abs_of_nonneg (sub_nonneg.mpr hu)]
        linarith
      · rename_i hfar
        have hx : x = (x.floor : Rat) + (1 : Rat) / 2 := by
          have hnear' := le_of_not_gt hnear
          have hfar' := le_of_not_gt hfar
          linarith
        conv_lhs => rw [hx]
        rw [roundRatEven_half_step, hstep]

end FloatLib.Numerics
