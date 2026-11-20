/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Comparison.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Rounding
public import FloatLib.Floats.Formats.DecimalInterchange.Projection.FormatProof
public import FloatLib.Floats.Formats.Flocq.Calculation.GuardSticky
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Comparison.Proof
public import FloatLib.Numerics.Enclosure.Rational.Proof
public import FloatLib.Numerics.Order.Bisection.Proof

/-!
# Decimal rounding by exact comparisons is correct rounding in every direction

`Transcendentals.roundTo f mode x` is the rounding of the real `x` in the direction `mode` on
the grid of the decimal format `f` with an unbounded exponent range: Flocq's `round` at radix
ten with the precision and the least quantum exponent of `f` (clause 4.3 of IEEE 754-2019).
To nearest-even it is `Transcendentals.roundAt`.

`RoundsTo f mode x negative outcome` says that an outcome is the rounding of `x` with its
flags. When `roundTo f mode x` is at most the largest finite magnitude, the value is a valid
finite datum with the sign `negative` that denotes `roundTo f mode x`, `inexact` is raised
exactly when that value is not `x`, `underflow` exactly when moreover `|x|` is below the least
normal magnitude, and no other flag is raised. Otherwise the outcome is the overflow result of
the direction with `overflow` and `inexact` (clause 7.4).

For a comparator that orders a real number against every rational, `ComparisonRounding.round`
meets this contract in each of the five directions, for every decimal format
(`round_roundsTo`), and gives `+0` for a comparator of zero (`round_of_eq_zero`). No premise
limits the number of comparisons or the distance of the number from a rounding boundary.
`within_eq` shows that asking through an enclosure of the number does not change a comparator,
and `deliver_roundsTo`, `unary_roundsTo` and `binary_roundsTo` carry the contract through the
rules and the operand tables.

The proof locates the magnitude: `locate_spec` shows that the two bisections find the
canonical exponent and the integer part of the scaled significand, with the guard and sticky
bits of the rest. `Flocq.round_signed_of_guardSticky`, which binary and decimal formats share,
then computes the rounding in each direction from that location.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

open FloatLib.Numerics FloatLib.Floats.Formats

namespace Transcendentals

/--
Rounding of a real number onto the decimal grid of `f`, with its precision and gradual
underflow and no upper bound on the exponent, in the direction `mode`.
-/
noncomputable def roundTo (f : Format) (mode : RoundingMode) (x : ℝ) : ℝ :=
  Flocq.round (β := decimalRadix) (fexp := fexpOf f) (Flocq.roundingFunction mode.toIEEE) x

/-- To nearest-even the rounding in a direction is `roundAt`. -/
theorem roundTo_nearest (f : Format) (x : ℝ) : roundTo f .nearest x = roundAt f x :=
  rfl

/-- Every direction fixes zero. -/
@[simp] theorem roundTo_zero (f : Format) (mode : RoundingMode) : roundTo f mode 0 = 0 :=
  Flocq.round_preserves_generic _ 0 Flocq.genericRepresentable_zero

/-- Every direction is monotone. -/
theorem roundTo_mono (f : Format) (mode : RoundingMode) {x y : ℝ} (hxy : x ≤ y) :
    roundTo f mode x ≤ roundTo f mode y :=
  Flocq.round_mono (Flocq.roundingFunction mode.toIEEE) hxy

end Transcendentals

open Transcendentals (fexpOf toReal roundTo)

/--
`outcome` is the rounding of the real `x` in the direction `mode`, with the sign `negative` and
with its flags.

`roundTo f mode x` rounds on the grid of `f` with an unbounded exponent range. When that value
is at most the largest finite magnitude, the outcome is a valid finite datum of the given sign
that denotes it, with `inexact` when it is not `x` and `underflow` when moreover `|x|` is below
the least normal magnitude. Otherwise the outcome is the overflow result of IEEE 754-2019,
clause 7.4.
-/
structure RoundsTo (f : Format) (mode : RoundingMode) (x : ℝ) (negative : Bool)
    (outcome : Outcome) : Prop where
  /-- In range, the value is a valid finite datum of the sign that denotes the grid rounding. -/
  finite : |roundTo f mode x| ≤ toReal (f.maxFinite false) →
    (∃ coefficient quantum, outcome.value = .finite negative coefficient quantum) ∧
      outcome.value.Valid f ∧ toReal outcome.value = roundTo f mode x
  /-- In range, the flags: `inexact` and `underflow` as the standard defines them, no other. -/
  flags : |roundTo f mode x| ≤ toReal (f.maxFinite false) →
    (outcome.status.inexact = true ↔ roundTo f mode x ≠ x) ∧
      (outcome.status.underflow = true ↔ |x| < (f.minNormal : ℝ) ∧ roundTo f mode x ≠ x) ∧
      outcome.status.overflow = false ∧ outcome.status.invalid = false ∧
      outcome.status.divideByZero = false
  /-- Out of range, the outcome is the overflow result of the direction. -/
  overflow : toReal (f.maxFinite false) < |roundTo f mode x| →
    outcome = KernelPath.overflow f mode negative

namespace ComparisonRounding

/-- A power of the decimal radix is a real power of ten. -/
theorem bpow_ten (e : ℤ) : Flocq.bpow decimalRadix e = (10 : ℝ) ^ e := by
  simp [Flocq.bpow, Radix.toReal, decimalRadix]

/-- The least normal magnitude is `10 ^ (minQuantum + precision - 1)`. -/
theorem cast_minNormal (f : Format) :
    ((f.minNormal : ℚ) : ℝ) = (10 : ℝ) ^ (f.minQuantum + f.precision - 1) := by
  have hp := f.precision_pos
  rw [Format.minNormal]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0), Nat.cast_sub hp]
  congr 1
  push_cast
  ring

/-- The decades above the least normal magnitude are powers of ten. -/
theorem cast_minNormal_mul_pow (f : Format) (index : ℕ) :
    ((f.minNormal * (10 : ℚ) ^ index : ℚ) : ℝ) =
      (10 : ℝ) ^ (f.minQuantum + f.precision - 1 + index) := by
  push_cast
  rw [cast_minNormal, ← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0)]

/-- The overflow bound is `10 ^ (maxQuantum + precision)`. -/
theorem cast_overflowBound (f : Format) :
    ((overflowBound f : ℚ) : ℝ) = (10 : ℝ) ^ (f.maxQuantum + f.precision) := by
  have h := f.minQuantum_le_maxQuantum
  rw [overflowBound, cast_minNormal_mul_pow]
  congr 1
  rw [Nat.cast_add, Int.toNat_of_nonneg (sub_nonneg.mpr h)]
  push_cast
  ring

/-- A bisection step accepts a candidate exactly when it is at most the located number. -/
private theorem accept_iff {compare : ℚ → Ordering} {t : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ)) (v : ℚ) :
    decide (compare v ≠ .lt) = true ↔ (v : ℝ) ≤ t := by
  rw [decide_eq_true_iff, hcompare, ne_eq, cmp_eq_lt_iff, not_lt]

/-- The span of a bisection fits its fuel. -/
private theorem lt_two_pow_log2_succ (n : ℕ) : n < 2 ^ (n.log2 + 1) := by
  rw [Nat.log2_eq_log_two]
  exact Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n

/--
For a comparator of a magnitude from the least normal magnitude up to the overflow bound, the
quantum search finds the decade: the magnitude lies in `[10 ^ (q + precision - 1),
10 ^ (q + precision))` for the quantum exponent `q` that it returns, which is a quantum
exponent of the format.
-/
theorem quantum_spec (f : Format) {compare : ℚ → Ordering} {t : ℝ}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ))
    (hlower : ((f.minNormal : ℚ) : ℝ) ≤ t)
    (hupper : t < (10 : ℝ) ^ (f.maxQuantum + f.precision)) :
    f.minQuantum ≤ quantum f compare ∧ quantum f compare ≤ f.maxQuantum ∧
      (10 : ℝ) ^ (quantum f compare + f.precision - 1) ≤ t ∧
      t < (10 : ℝ) ^ (quantum f compare + f.precision) := by
  have hrange := f.minQuantum_le_maxQuantum
  have hspan : (((f.maxQuantum - f.minQuantum).toNat : ℕ) : ℤ) = f.maxQuantum - f.minQuantum :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hrange)
  have hbracket := bisect_bracket
    (fun index => decide (compare (f.minNormal * (10 : ℚ) ^ index) ≠ .lt))
    (fun index : ℕ => (10 : ℝ) ^ (f.minQuantum + f.precision - 1 + index)) t
    (fun index => by rw [accept_iff hcompare, cast_minNormal_mul_pow])
    ((f.maxQuantum - f.minQuantum).toNat.log2 + 1) 0 ((f.maxQuantum - f.minQuantum).toNat + 1)
    (Nat.succ_pos _)
    (by simpa using Nat.succ_le_of_lt (lt_two_pow_log2_succ (f.maxQuantum - f.minQuantum).toNat))
    (by
      have h := hlower
      rw [cast_minNormal] at h
      simpa using h)
    (by
      have hexponent : f.minQuantum + f.precision - 1 +
          (((f.maxQuantum - f.minQuantum).toNat + 1 : ℕ) : ℤ) = f.maxQuantum + f.precision := by
        rw [Nat.cast_add, hspan]
        push_cast
        ring
      rw [hexponent]
      exact hupper)
  have hlt := bisect_lt_upper
    (fun index => decide (compare (f.minNormal * (10 : ℚ) ^ index) ≠ .lt))
    ((f.maxQuantum - f.minQuantum).toNat.log2 + 1) 0 ((f.maxQuantum - f.minQuantum).toNat + 1)
    (Nat.succ_pos _)
  unfold quantum
  dsimp only
  generalize bisect _ _ _ _ = index at hbracket hlt
  refine ⟨by omega, by omega, ?_, ?_⟩
  · rw [show f.minQuantum + (index : ℤ) + f.precision - 1 =
      f.minQuantum + f.precision - 1 + index by ring]
    exact hbracket.1
  · rw [show f.minQuantum + (index : ℤ) + f.precision =
      f.minQuantum + f.precision - 1 + ((index + 1 : ℕ) : ℤ) by push_cast; ring]
    exact hbracket.2

/--
For a comparator of a nonnegative magnitude below `10 ^ (q + precision)`, the coefficient
search finds the integer part of the magnitude in units of `10 ^ q`, below the coefficient
bound.
-/
theorem coefficient_spec (f : Format) {compare : ℚ → Ordering} {t : ℝ} (ht : 0 ≤ t)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ)) (q : ℤ)
    (hupper : t < (10 : ℝ) ^ (q + f.precision)) :
    coefficient f compare q < f.coefficientBound ∧
      (coefficient f compare q : ℝ) * (10 : ℝ) ^ q ≤ t ∧
      t < ((coefficient f compare q : ℝ) + 1) * (10 : ℝ) ^ q := by
  have hbound := f.coefficientBound_pos
  have hbracket := bisect_bracket
    (fun candidate => decide (compare ((candidate : ℚ) * (10 : ℚ) ^ q) ≠ .lt))
    (fun candidate : ℕ => (candidate : ℝ) * (10 : ℝ) ^ q) t
    (fun candidate => by
      rw [accept_iff hcompare]
      push_cast
      rfl)
    (f.coefficientBound.log2 + 1) 0 f.coefficientBound hbound
    (by simpa using (lt_two_pow_log2_succ f.coefficientBound).le)
    (by simpa using ht)
    (by
      rw [f.coefficientBound_eq]
      push_cast
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (10 : ℝ) ≠ 0), add_comm]
      exact hupper)
  refine ⟨bisect_lt_upper _ _ _ _ hbound, hbracket.1, ?_⟩
  have h := hbracket.2
  push_cast at h
  exact h

/--
**The comparisons locate a magnitude on the decimal grid.** For a comparator of a positive
magnitude `t` below the overflow bound, `locate` returns the canonical exponent of `t` on the
grid of the format, which is one of its quantum exponents, a coefficient below the coefficient
bound that is the integer part of the scaled significand of `t`, the guard and sticky bits of
the rest, and whether `t` is below the least normal magnitude.
-/
theorem locate_spec (f : Format) {compare : ℚ → Ordering} {t : ℝ} (ht : 0 < t)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ))
    (hrange : t < (10 : ℝ) ^ (f.maxQuantum + f.precision)) :
    Flocq.cexp decimalRadix (fexpOf f) t = (locate f compare).quantum ∧
      f.minQuantum ≤ (locate f compare).quantum ∧ (locate f compare).quantum ≤ f.maxQuantum ∧
      (locate f compare).coefficient < f.coefficientBound ∧
      Flocq.InbetweenInt ((locate f compare).coefficient : ℤ)
        (Flocq.scaledMantissa decimalRadix (fexpOf f) t)
        (Flocq.guardStickyLocation (locate f compare).guard (locate f compare).sticky) ∧
      ((locate f compare).tiny = true ↔ t < ((f.minNormal : ℚ) : ℝ)) := by
  have hten : (0 : ℝ) < 10 := by norm_num
  have htiny : (compare f.minNormal == .lt) = true ↔ t < ((f.minNormal : ℚ) : ℝ) := by
    rw [beq_iff_eq, hcompare, cmp_eq_lt_iff]
  -- The quantum exponent and the decade of the magnitude.
  obtain ⟨q, hq, hqmin, hqmax, hcexp, hdecade⟩ :
      ∃ q : ℤ, (if (compare f.minNormal == .lt) = true then f.minQuantum
          else quantum f compare) = q ∧
        f.minQuantum ≤ q ∧ q ≤ f.maxQuantum ∧
        Flocq.cexp decimalRadix (fexpOf f) t = q ∧ t < (10 : ℝ) ^ (q + f.precision) := by
    by_cases hsmall : (compare f.minNormal == .lt) = true
    · have hlt := htiny.mp hsmall
      rw [cast_minNormal] at hlt
      refine ⟨f.minQuantum, by simp [hsmall], le_rfl, f.minQuantum_le_maxQuantum, ?_, ?_⟩
      · have hmagnitude := Flocq.magnitude_le_of_abs_lt_bpow decimalRadix t
          (f.minQuantum + f.precision - 1) ht.ne' (by rwa [abs_of_pos ht, bpow_ten])
        simp only [Flocq.cexp, fexpOf, Flocq.fltExp]
        omega
      · exact hlt.trans (zpow_lt_zpow_right₀ (by norm_num) (by omega))
    · have hge : ((f.minNormal : ℚ) : ℝ) ≤ t := not_lt.mp (mt htiny.mpr hsmall)
      obtain ⟨hmin, hmax, hlow, hhigh⟩ := quantum_spec f hcompare hge hrange
      refine ⟨quantum f compare, by simp [hsmall], hmin, hmax, ?_, hhigh⟩
      have hmagnitude := Flocq.magnitude_eq_of_bpow_bounds decimalRadix t
        (quantum f compare + f.precision)
        (by rwa [abs_of_pos ht, bpow_ten])
        (by rwa [abs_of_pos ht, bpow_ten])
      simp only [Flocq.cexp, fexpOf, Flocq.fltExp, hmagnitude]
      omega
  -- The coefficient and the place of the rest.
  obtain ⟨hcoefficient, hlow, hhigh⟩ := coefficient_spec f ht.le hcompare q hdecade
  have hunit : (0 : ℝ) < (10 : ℝ) ^ q := zpow_pos hten q
  have hscaled : Flocq.scaledMantissa decimalRadix (fexpOf f) t = t / (10 : ℝ) ^ q := by
    rw [Flocq.scaledMantissa_eq_div, hcexp, bpow_ten]
  have hexact : (compare ((coefficient f compare q : ℚ) * (10 : ℚ) ^ q) == .eq) = true ↔
      t = (coefficient f compare q : ℝ) * (10 : ℝ) ^ q := by
    rw [beq_iff_eq, hcompare, cmp_eq_eq_iff]
    push_cast
    rfl
  unfold locate
  simp only [hq]
  by_cases hgrid : (compare ((coefficient f compare q : ℚ) * (10 : ℚ) ^ q) == .eq) = true
  · simp only [hgrid, ↓reduceIte]
    refine ⟨hcexp, hqmin, hqmax, hcoefficient, ?_, htiny⟩
    rw [hscaled, hexact.mp hgrid, mul_div_cancel_right₀ _ hunit.ne']
    exact .exact (by push_cast; rfl)
  · simp only [hgrid]
    refine ⟨hcexp, hqmin, hqmax, hcoefficient, ?_, htiny⟩
    have hne : t ≠ (coefficient f compare q : ℝ) * (10 : ℝ) ^ q := mt hexact.mpr hgrid
    have hhalf : compare (((coefficient f compare q : ℚ) + 1 / 2) * (10 : ℚ) ^ q) =
        cmp (t / (10 : ℝ) ^ q) ((coefficient f compare q : ℝ) + 1 / 2) := by
      rw [hcompare]
      push_cast
      simp only [cmp, cmpUsing, div_lt_iff₀ hunit, lt_div_iff₀ hunit]
    rw [hscaled, hhalf]
    exact Flocq.inbetweenInt_of_cmp_half
      ((lt_div_iff₀ hunit).mpr (lt_of_le_of_ne hlow (Ne.symm hne)))
      ((div_lt_iff₀ hunit).mpr hhigh)

/-- The real value of a finite datum: its coefficient times the power of ten, with its sign. -/
theorem toReal_finite (negative : Bool) (coefficient : ℕ) (quantum : ℤ) :
    toReal (.finite negative coefficient quantum) =
      (if negative then (-1 : ℝ) else 1) * ((coefficient : ℝ) * (10 : ℝ) ^ quantum) := by
  rw [Transcendentals.toReal_of_toRat?_eq_some (Datum.toRat?_eq _)]
  cases negative <;> simp

/-- The largest finite magnitude is one unit of the largest quantum below the coefficient
bound. -/
theorem toReal_maxFinite (f : Format) :
    toReal (f.maxFinite false) =
      ((f.coefficientBound : ℝ) - 1) * (10 : ℝ) ^ f.maxQuantum := by
  rw [Format.maxFinite, toReal_finite, Nat.cast_sub f.coefficientBound_pos]
  simp

/--
A real of magnitude at least a power of ten on the grid rounds, in every direction, to a value
of at least that magnitude.
-/
theorem pow_le_abs_roundTo (f : Format) (mode : RoundingMode) {x : ℝ} {e : ℤ}
    (he : f.minQuantum ≤ e) (hx : (10 : ℝ) ^ e ≤ |x|) : (10 : ℝ) ^ e ≤ |roundTo f mode x| := by
  have hgeneric : Flocq.GenericRepresentable decimalRadix (fexpOf f)
      (Flocq.bpow decimalRadix e) :=
    Flocq.genericRepresentable_bpow e (by
      have := f.precision_pos
      simp only [fexpOf, Flocq.fltExp]
      omega)
  have hpositive (rnd : ℝ → ℤ) [Flocq.ValidRnd rnd] {y : ℝ} (hy : (10 : ℝ) ^ e ≤ y) :
      (10 : ℝ) ^ e ≤ Flocq.round (β := decimalRadix) (fexp := fexpOf f) rnd y := by
    have hy' : Flocq.bpow decimalRadix e ≤ y := by rwa [bpow_ten]
    have h := Flocq.round_mono (β := decimalRadix) (fexp := fexpOf f) rnd hy'
    rwa [Flocq.round_preserves_generic rnd _ hgeneric, bpow_ten] at h
  rcases le_total 0 x with hnonneg | hnonpos
  · rw [abs_of_nonneg hnonneg] at hx
    exact (hpositive _ hx).trans (le_abs_self _)
  · rw [abs_of_nonpos hnonpos] at hx
    have h := hpositive (Flocq.negRound (Flocq.roundingFunction mode.toIEEE)) hx
    have hneg : roundTo f mode x = -Flocq.round (β := decimalRadix) (fexp := fexpOf f)
        (Flocq.negRound (Flocq.roundingFunction mode.toIEEE)) (-x) := by
      rw [← Flocq.round_neg, _root_.neg_neg]
      rfl
    rw [hneg, abs_neg]
    exact h.trans (le_abs_self _)

/--
**A located magnitude is rounded correctly in every direction.** For a positive magnitude `t`
whose canonical exponent is the quantum exponent `q` of the format, whose scaled significand
lies in the unit bracket above the coefficient `c` at the place of the guard and sticky bits,
and for a `tiny` that says whether `t` is below the least normal magnitude, the outcome of
`Located.round` meets the contract `RoundsTo` for `t` with the sign `negative`.
-/
theorem Located.round_roundsTo (f : Format) (mode : RoundingMode) (negative : Bool) {t : ℝ}
    (ht : 0 < t) {q : ℤ} {c : ℕ} {guard sticky tiny : Bool}
    (hcexp : Flocq.cexp decimalRadix (fexpOf f) t = q) (hqmin : f.minQuantum ≤ q)
    (hqmax : q ≤ f.maxQuantum) (hc : c < f.coefficientBound)
    (hbracket : Flocq.InbetweenInt (c : ℤ) (Flocq.scaledMantissa decimalRadix (fexpOf f) t)
      (Flocq.guardStickyLocation guard sticky))
    (htiny : tiny = true ↔ t < ((f.minNormal : ℚ) : ℝ)) :
    RoundsTo f mode (if negative then -t else t) negative
      (Located.round f mode negative ⟨q, c, guard, sticky, tiny⟩) := by
  have hten : (0 : ℝ) < 10 := by norm_num
  have hunit : (0 : ℝ) < (10 : ℝ) ^ q := zpow_pos hten q
  have hbound : (f.coefficientBound : ℝ) = 10 * (f.payloadBound : ℝ) := by
    simp [Format.coefficientBound]
  have hone : (1 : ℝ) ≤ f.coefficientBound := by exact_mod_cast f.coefficientBound_pos
  have hsign : (if negative then (-1 : ℝ) else 1) ≠ 0 := by cases negative <;> norm_num
  have habsSign : |(if negative then (-1 : ℝ) else 1)| = 1 := by cases negative <;> simp
  have hx : (if negative then -t else t) = (if negative then (-1 : ℝ) else 1) * t := by
    cases negative <;> simp
  have habs : |(if negative then -t else t)| = t := by
    rw [hx, abs_mul, habsSign, one_mul, abs_of_pos ht]
  -- The cell of the magnitude.
  have hscaled : Flocq.scaledMantissa decimalRadix (fexpOf f) t = t / (10 : ℝ) ^ q := by
    rw [Flocq.scaledMantissa_eq_div, hcexp, bpow_ten]
  rw [hscaled] at hbracket
  obtain ⟨-, hhigh⟩ := Flocq.inbetween_bounds (by push_cast; linarith) hbracket
  have hhigh' : t < ((c : ℝ) + 1) * (10 : ℝ) ^ q := by
    have := (div_lt_iff₀ hunit).mp hhigh
    simpa using this
  -- The rounded coefficient.
  have hround := Flocq.round_signed_of_guardSticky (β := decimalRadix) (fexp := fexpOf f)
    (t := t) (by rwa [hscaled]) mode.toIEEE negative
  rw [hcexp, bpow_ten] at hround
  unfold Located.round
  dsimp only
  generalize hrounded : (if (mode.toIEEE.magnitudeRounding negative).increment (c % 2 == 1)
    guard sticky then c + 1 else c) = rounded at hround ⊢
  have hvalue : roundTo f mode (if negative then -t else t) =
      (if negative then (-1 : ℝ) else 1) * ((rounded : ℝ) * (10 : ℝ) ^ q) := hround
  have hcases : rounded = c ∨ rounded = c + 1 := by
    rw [← hrounded]
    split <;> simp
  have hexact : guard = false → sticky = false → rounded = c ∧ t = (c : ℝ) * (10 : ℝ) ^ q := by
    rintro rfl rfl
    refine ⟨by simp [← hrounded], ?_⟩
    cases hbracket with
    | exact h =>
        have := (div_eq_iff hunit.ne').mp h
        simpa using this
  have hinexact : (guard || sticky) = true → (rounded : ℝ) * (10 : ℝ) ^ q ≠ t := by
    intro hflag
    have hstrict : (c : ℝ) * (10 : ℝ) ^ q < t := by
      have hlocation : ∃ order, Flocq.guardStickyLocation guard sticky = .inexact order := by
        cases guard <;> cases sticky <;> simp [Flocq.guardStickyLocation] at hflag ⊢
      obtain ⟨order, horder⟩ := hlocation
      rw [horder] at hbracket
      have := (lt_div_iff₀ hunit).mp (Flocq.inbetween_strict_bounds hbracket).1
      simpa using this
    rcases hcases with h | h
    · rw [h]
      exact hstrict.ne
    · rw [h]
      push_cast
      exact hhigh'.ne'
  have hflags : ((guard || sticky) = true ↔
      roundTo f mode (if negative then -t else t) ≠ (if negative then -t else t)) := by
    rw [hvalue, hx, ne_eq, mul_right_inj' hsign]
    constructor
    · exact hinexact
    · intro hne
      by_contra hflag
      have hboth : guard = false ∧ sticky = false := by
        cases guard <;> cases sticky <;> simp at hflag ⊢
      obtain ⟨hc', ht'⟩ := hexact hboth.1 hboth.2
      exact hne (by rw [hc', ← ht'])
  have habsValue : |roundTo f mode (if negative then -t else t)| =
      (rounded : ℝ) * (10 : ℝ) ^ q := by
    rw [hvalue, abs_mul, habsSign, one_mul,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hunit.le)]
  have hroundedLe : rounded ≤ f.coefficientBound := by
    rcases hcases with h | h <;> omega
  -- The carry.
  by_cases hcarry : rounded = f.coefficientBound
  · simp only [hcarry, ↓reduceIte]
    have hmagnitude : |roundTo f mode (if negative then -t else t)| =
        (f.payloadBound : ℝ) * (10 : ℝ) ^ (q + 1) := by
      rw [habsValue, hcarry, hbound, zpow_add_one₀ hten.ne']
      ring
    by_cases hlast : f.maxQuantum < q + 1
    · rw [ite_eq_left hlast]
      have hq : q = f.maxQuantum := by omega
      have hbeyond : toReal (f.maxFinite false) <
          |roundTo f mode (if negative then -t else t)| := by
        rw [toReal_maxFinite, habsValue, hcarry, hq]
        exact mul_lt_mul_of_pos_right (by linarith) (zpow_pos hten _)
      exact ⟨fun hin => absurd hbeyond (not_lt.mpr hin),
        fun hin => absurd hbeyond (not_lt.mpr hin), fun _ => rfl⟩
    · rw [ite_eq_right hlast]
      have hin : |roundTo f mode (if negative then -t else t)| ≤ toReal (f.maxFinite false) := by
        rw [toReal_maxFinite, hmagnitude]
        have hpayload : (f.payloadBound : ℝ) ≤ (f.coefficientBound : ℝ) - 1 := by
          have := f.payloadBound_lt_coefficientBound
          have : (f.payloadBound : ℝ) + 1 ≤ f.coefficientBound := by exact_mod_cast this
          linarith
        exact mul_le_mul hpayload (zpow_le_zpow_right₀ (by norm_num) (by omega))
          (zpow_pos hten _).le (by linarith)
      refine ⟨fun _ => ⟨⟨_, _, rfl⟩, ?_, ?_⟩, fun _ => ⟨hflags, ?_, rfl, rfl, rfl⟩,
        fun hover => absurd hover (not_lt.mpr hin)⟩
      · exact (Datum.valid_quantum_iff f negative _ _).mpr
          ⟨f.payloadBound_lt_coefficientBound, by omega, by omega⟩
      · rw [toReal_finite, hvalue, hcarry, hbound, zpow_add_one₀ hten.ne']
        ring
      · rw [habs, ← hflags]
        simp [htiny]
  · simp only [hcarry, ↓reduceIte]
    have hlt : rounded < f.coefficientBound := lt_of_le_of_ne hroundedLe hcarry
    rw [ite_eq_right (not_lt.mpr hqmax)]
    have hin : |roundTo f mode (if negative then -t else t)| ≤ toReal (f.maxFinite false) := by
      rw [toReal_maxFinite, habsValue]
      have hcoefficient : (rounded : ℝ) ≤ (f.coefficientBound : ℝ) - 1 := by
        have : (rounded : ℝ) + 1 ≤ f.coefficientBound := by exact_mod_cast hlt
        linarith
      exact mul_le_mul hcoefficient (zpow_le_zpow_right₀ (by norm_num) hqmax) hunit.le
        (by linarith)
    refine ⟨fun _ => ⟨⟨_, _, rfl⟩, ?_, ?_⟩, fun _ => ⟨hflags, ?_, rfl, rfl, rfl⟩,
      fun hover => absurd hover (not_lt.mpr hin)⟩
    · exact (Datum.valid_quantum_iff f negative _ _).mpr ⟨hlt, hqmin, hqmax⟩
    · rw [toReal_finite, hvalue]
    · rw [habs, ← hflags]
      simp [htiny]

/--
**Decimal rounding of a magnitude by exact comparisons is correct in every direction.** For a
comparator of the positive magnitude `t`, `roundMagnitude` with the sign `negative` meets the
contract `RoundsTo` for `±t`, for every decimal format and each of the five directions. No
premise restricts the magnitude: it may underflow, overflow or lie on a rounding boundary.
-/
theorem roundMagnitude_roundsTo (f : Format) (mode : RoundingMode) (negative : Bool)
    {compare : ℚ → Ordering} {t : ℝ} (ht : 0 < t)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp t (candidate : ℝ)) :
    RoundsTo f mode (if negative then -t else t) negative
      (roundMagnitude f mode negative compare) := by
  have hten : (0 : ℝ) < 10 := by norm_num
  unfold roundMagnitude
  by_cases hover : compare (overflowBound f) ≠ .lt
  · rw [ite_eq_left hover]
    have hge : (10 : ℝ) ^ (f.maxQuantum + f.precision) ≤ t := by
      rw [← cast_overflowBound]
      rwa [hcompare, ne_eq, cmp_eq_lt_iff, not_lt] at hover
    have habs : |(if negative then -t else t)| = t := by
      cases negative <;> simp [abs_of_pos ht]
    have hbeyond : toReal (f.maxFinite false) <
        |roundTo f mode (if negative then -t else t)| := by
      refine lt_of_lt_of_le ?_ (pow_le_abs_roundTo f mode
        (by have := f.minQuantum_le_maxQuantum; omega) (habs.symm ▸ hge))
      rw [toReal_maxFinite, zpow_add₀ hten.ne', f.coefficientBound_eq, mul_comm]
      push_cast
      rw [zpow_natCast]
      exact mul_lt_mul_of_pos_left (by linarith) (zpow_pos hten _)
    exact ⟨fun hin => absurd hbeyond (not_lt.mpr hin),
      fun hin => absurd hbeyond (not_lt.mpr hin), fun _ => rfl⟩
  · rw [ite_eq_right hover]
    have hlt : t < (10 : ℝ) ^ (f.maxQuantum + f.precision) := by
      rw [← cast_overflowBound]
      rwa [hcompare, ne_eq, cmp_eq_lt_iff, not_not] at hover
    obtain ⟨hcexp, hqmin, hqmax, hcoefficient, hbracket, htiny⟩ :=
      locate_spec f ht hcompare hlt
    exact Located.round_roundsTo f mode negative ht hcexp hqmin hqmax hcoefficient hbracket htiny

open BinaryInterchange.Model.ComparisonRounding in
/--
**Decimal rounding by exact comparisons is correct rounding in every direction.** For a
comparator of the nonzero real number `target`, every decimal format and each of the five
rounding directions, `round` meets the contract `RoundsTo`: a valid finite datum that denotes
`roundTo f mode target` with its `inexact` and `underflow` flags when that value is at most the
largest finite magnitude, the overflow result of the direction otherwise, and the sign of
`target`.
-/
theorem round_roundsTo (f : Format) (mode : RoundingMode) {compare : ℚ → Ordering} {target : ℝ}
    (hne : target ≠ 0)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ)) :
    RoundsTo f mode target (decide (target < 0)) (round f mode compare) := by
  have hzero := hcompare 0
  rw [Rat.cast_zero] at hzero
  unfold round
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · rw [(cmp_eq_lt_iff _ _).mpr hneg] at hzero
    simp only [hzero, decide_eq_true hneg]
    simpa using roundMagnitude_roundsTo f mode true (neg_pos.mpr hneg)
      (magnitude_compare hcompare)
  · rw [(cmp_eq_gt_iff _ _).mpr hpos] at hzero
    simp only [hzero, decide_eq_false (not_lt.mpr hpos.le)]
    simpa using roundMagnitude_roundsTo f mode false hpos hcompare

/-- A comparator of zero is rounded to `+0` with the least quantum exponent and no flag, in
every direction. -/
theorem round_of_eq_zero (f : Format) (mode : RoundingMode) {compare : ℚ → Ordering}
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp (0 : ℝ) (candidate : ℝ)) :
    round f mode compare = { value := .finite false 0 f.minQuantum } := by
  have hzero : compare 0 = .eq := by
    rw [hcompare, Rat.cast_zero]
    exact (cmp_eq_eq_iff _ _).mpr rfl
  simp [round, hzero]

/--
A comparator that is asked through an enclosure of its number answers as the comparator does:
`within` is a comparator of the same number.
-/
theorem within_eq {interval : RationalInterval} {compare : ℚ → Ordering} {target : ℝ}
    (hcontains : interval.Contains target)
    (hcompare : ∀ candidate : ℚ, compare candidate = cmp target (candidate : ℝ))
    (candidate : ℚ) : within interval compare candidate = cmp target (candidate : ℝ) := by
  unfold within
  split_ifs with hlow hhigh
  · exact ((cmp_eq_gt_iff _ _).mpr
      (lt_of_lt_of_le (by exact_mod_cast hlow) hcontains.1)).symm
  · exact ((cmp_eq_lt_iff _ _).mpr
      (lt_of_le_of_lt hcontains.2 (by exact_mod_cast hhigh))).symm
  · exact hcompare candidate

open BinaryInterchange.Model.ComparisonRounding in
/--
**A rule's decimal delivery is the correctly rounded value in every direction.** For a rule
that locates the nonzero real number `target` and an enclosure that, when there is one,
contains `target`, the outcome of `deliver` meets the contract `RoundsTo` in every decimal
format and each of the five directions.
-/
theorem deliver_roundsTo (f : Format) (mode : RoundingMode) {rule : Rule} {target : ℝ}
    (hrule : rule.Locates target) (hne : target ≠ 0)
    {enclosure : Unit → Option RationalInterval}
    (henclosure : ∀ interval, enclosure () = some interval → interval.Contains target) :
    RoundsTo f mode target (decide (target < 0)) (deliver f mode enclosure rule) := by
  cases rule with
  | zero negative => exact absurd hrule hne
  | real compare =>
      unfold deliver
      cases hinterval : enclosure () with
      | none => exact round_roundsTo f mode hne hrule
      | some interval =>
          exact round_roundsTo f mode hne (within_eq (henclosure interval hinterval) hrule)
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

open BinaryInterchange.Model.ComparisonRounding in
/--
A rule that locates zero delivers a zero with the least quantum exponent and no flag, in every
direction: the zero of the rule's sign, and `+0` for a comparator of zero.
-/
theorem deliver_of_eq_zero (f : Format) (mode : RoundingMode) {rule : Rule}
    (hrule : rule.Locates 0) {enclosure : Unit → Option RationalInterval}
    (henclosure : ∀ interval, enclosure () = some interval → interval.Contains 0) :
    ∃ negative, deliver f mode enclosure rule = { value := .finite negative 0 f.minQuantum } := by
  cases rule with
  | zero negative => exact ⟨negative, rfl⟩
  | real compare =>
      refine ⟨false, ?_⟩
      unfold deliver
      cases hinterval : enclosure () with
      | none => exact round_of_eq_zero f mode hrule
      | some interval =>
          exact round_of_eq_zero f mode (within_eq (henclosure interval hinterval) hrule)
  | infinity negative => exact absurd hrule id
  | pole negative => exact absurd hrule id
  | invalid => exact absurd hrule id

open BinaryInterchange.Model.ComparisonRounding in
/-- At a finite operand a decimal function of one operand is the outcome of its rule, with the
enclosure of that operand. -/
theorem unary_finite (f : Format) (rule : Operand → Rule) (mode : RoundingMode)
    (negative : Bool) (coefficient : ℕ) (quantum : ℤ)
    (enclosure : Operand → Unit → Option RationalInterval) :
    unary f rule mode (.finite negative coefficient quantum) enclosure =
      deliver f mode
        (enclosure (.finite negative (Datum.finiteValue negative coefficient quantum)))
        (rule (.finite negative (Datum.finiteValue negative coefficient quantum))) :=
  rfl

open BinaryInterchange.Model.ComparisonRounding in
/-- At finite operands a decimal function of two operands is the outcome of its rule, with the
enclosure of that pair. -/
theorem binary_finite (f : Format) (rule : Operand → Operand → Rule) (mode : RoundingMode)
    (negative negative' : Bool) (coefficient coefficient' : ℕ) (quantum quantum' : ℤ)
    (enclosure : Operand → Operand → Unit → Option RationalInterval) :
    binary f rule mode (.finite negative coefficient quantum)
        (.finite negative' coefficient' quantum') enclosure =
      deliver f mode
        (enclosure (.finite negative (Datum.finiteValue negative coefficient quantum))
          (.finite negative' (Datum.finiteValue negative' coefficient' quantum')))
        (rule (.finite negative (Datum.finiteValue negative coefficient quantum))
          (.finite negative' (Datum.finiteValue negative' coefficient' quantum'))) :=
  rfl

end ComparisonRounding

end FloatLib.Floats.Formats.DecimalInterchange
