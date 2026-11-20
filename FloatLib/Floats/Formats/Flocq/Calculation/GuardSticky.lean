/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Calculation.Round
public import FloatLib.Floats.Formats.Flocq.Theory.Rounding.Modes

/-!
# Rounding a magnitude from its guard and sticky bits, in any radix

A nonnegative magnitude is located on a grid by the integer part `m` of its scaled significand,
a guard bit that says whether the discarded part is at least a half, and a sticky bit that says
whether it is neither zero nor exactly a half. `round_of_guardSticky` computes the rounding of
such a magnitude in each rounding direction: the integer part or the next integer, as
`MagnitudeRounding.increment` decides from the parity of `m` and the two bits, in units of the
radix power of the canonical exponent. `round_signed_of_guardSticky` is the statement for a
magnitude with a sign: the negative value rounds its magnitude in the mirrored direction.

The radix and the exponent function are parameters, so binary and decimal formats share these
two theorems. `negRound_roundingFunction` is the rule of negation for the six integer rounding
rules, and `inbetweenInt_of_cmp_half` reads the two bits of a magnitude strictly inside a cell
off its ordering against the midpoint.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq

open FloatLib.Numerics
open FloatLib.Floats.Formats.BinaryInterchange.Model (IEEERoundingMode)

/-- The bracket location that a guard bit and a sticky bit name. -/
def guardStickyLocation (guard sticky : Bool) : Location :=
  match guard, sticky with
  | false, false => .exact
  | false, true => .inexact .lt
  | true, false => .inexact .eq
  | true, true => .inexact .gt

/-- Nearest-even integer rounding commutes with negation. -/
theorem negRound_nearestEven : negRound nearestEven = nearestEven := by
  have heven : nearestEven = nearestChoice nearestEvenChoice :=
    funext fun x => (nearestChoice_even_eq x).symm
  rw [heven, negRound_nearestChoice]
  congr 1
  funext f
  by_cases hf : Even f <;> simp [nearestEvenChoice, hf]

/-- Conjugating the integer rule of a direction by negation gives the rule of the mirrored
direction. -/
theorem negRound_roundingFunction (mode : IEEERoundingMode) :
    negRound (roundingFunction mode) = roundingFunction mode.negate := by
  cases mode with
  | nearest => exact negRound_nearestEven
  | nearestAway => exact negRound_nearestChoice_tieAway
  | towardZero => exact negRound_truncRound
  | up => exact negRound_ceilRound
  | down => exact negRound_floorRound
  | away => exact negRound_awayRound

/--
A real strictly inside the unit bracket above the natural number `m` is located by its
ordering against the midpoint: the guard bit says that it is not below the midpoint, and the
sticky bit that it is not the midpoint.
-/
theorem inbetweenInt_of_cmp_half {m : ℕ} {w : ℝ} (hlower : (m : ℝ) < w)
    (hupper : w < (m : ℝ) + 1) :
    InbetweenInt (m : ℤ) w
      (guardStickyLocation (cmp w ((m : ℝ) + 1 / 2) != .lt)
        (cmp w ((m : ℝ) + 1 / 2) != .eq)) := by
  have hlocation (order : Ordering) :
      guardStickyLocation (order != .lt) (order != .eq) = .inexact order := by
    cases order <;> rfl
  rw [hlocation]
  refine .inexact _ ⟨by simpa using hlower, by push_cast; linarith⟩ ?_
  congr 1
  push_cast
  ring

variable {β : Numerics.Radix} {fexp : ℤ → ℤ} [ValidExp fexp]

/--
**Every direction rounds a located magnitude from its guard and sticky bits.** For a real `t`
whose scaled significand lies in the unit bracket above the natural number `mantissa`, at the
place that the guard and sticky bits name, the rounding of `t` in the direction `mode` is
`mantissa` or `mantissa + 1`, as `MagnitudeRounding.increment` decides from the parity of
`mantissa` and the two bits, times the radix power of the canonical exponent of `t`.
-/
theorem round_of_guardSticky {t : ℝ} {mantissa : ℕ} {guard sticky : Bool}
    (hbracket : InbetweenInt (mantissa : ℤ) (scaledMantissa β fexp t)
      (guardStickyLocation guard sticky))
    (mode : IEEERoundingMode) :
    round (β := β) (fexp := fexp) (roundingFunction mode) t =
      ((if (mode.magnitudeRounding false).increment (mantissa % 2 == 1) guard sticky
        then mantissa + 1 else mantissa : ℕ) : ℝ) * bpow β (cexp β fexp t) := by
  have hparity : nearestEvenChoice (mantissa : ℤ) = (mantissa % 2 == 1) := by
    rcases Nat.mod_two_eq_zero_or_one mantissa with hm | hm <;>
      simp [nearestEvenChoice, Int.even_natCast, Nat.even_iff, hm]
  have haway : nearestAwayChoice (mantissa : ℤ) = true := by simp [nearestAwayChoice]
  have hnonneg : ¬(mantissa : ℤ) < 0 := not_lt.mpr (Int.natCast_nonneg mantissa)
  cases mode with
  | nearest =>
      rw [show roundingFunction .nearest = nearestEven from rfl,
        round_nearestEven_of_scaledBracket t hbracket]
      rcases Nat.mod_two_eq_zero_or_one mantissa with hm | hm <;>
        cases guard <;> cases sticky <;>
        simp [guardStickyLocation, Flocq.toReal, conditionalIncrement, roundNearestLocation,
          hparity, IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment, hm]
  | nearestAway =>
      rw [show roundingFunction .nearestAway = nearestChoice nearestAwayChoice from rfl,
        round_nearestChoice_of_scaledBracket nearestAwayChoice t hbracket]
      cases guard <;> cases sticky <;>
        simp [guardStickyLocation, Flocq.toReal, conditionalIncrement, roundNearestLocation,
          haway, IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment]
  | towardZero =>
      rw [show roundingFunction .towardZero = truncRound from rfl,
        round_trunc_of_scaledBracket t hbracket, ite_eq_right hnonneg]
      simp [Flocq.toReal, IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment]
  | up =>
      rw [show roundingFunction .up = ceilRound from rfl,
        round_ceil_of_scaledBracket t hbracket]
      cases guard <;> cases sticky <;>
        simp [guardStickyLocation, Flocq.toReal, conditionalIncrement, roundUpLocation,
          IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment]
  | down =>
      rw [show roundingFunction .down = floorRound from rfl,
        round_floor_of_scaledBracket t hbracket]
      simp [Flocq.toReal, IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment]
  | away =>
      rw [show roundingFunction .away = awayRound from rfl,
        round_away_of_scaledBracket t hbracket, ite_eq_right hnonneg]
      cases guard <;> cases sticky <;>
        simp [guardStickyLocation, Flocq.toReal, conditionalIncrement, roundUpLocation,
          IEEERoundingMode.magnitudeRounding, MagnitudeRounding.increment]

/--
A located magnitude with either sign: the rounding of `-t` in the direction `mode` is the
negation of the rounding of the magnitude `t` under the rule that the direction applies to a
negative value.
-/
theorem round_signed_of_guardSticky {t : ℝ} {mantissa : ℕ} {guard sticky : Bool}
    (hbracket : InbetweenInt (mantissa : ℤ) (scaledMantissa β fexp t)
      (guardStickyLocation guard sticky))
    (mode : IEEERoundingMode) (negative : Bool) :
    round (β := β) (fexp := fexp) (roundingFunction mode) (if negative then -t else t) =
      (if negative then (-1 : ℝ) else 1) *
        (((if (mode.magnitudeRounding negative).increment (mantissa % 2 == 1) guard sticky
          then mantissa + 1 else mantissa : ℕ) : ℝ) * bpow β (cexp β fexp t)) := by
  cases negative with
  | false => simpa using round_of_guardSticky hbracket mode
  | true =>
      have hmirror := round_of_guardSticky hbracket mode.negate
      rw [IEEERoundingMode.magnitudeRounding_negate, Bool.not_false] at hmirror
      simp only [↓reduceIte]
      rw [round_neg, negRound_roundingFunction, hmirror]
      ring

end FloatLib.Floats.Formats.Flocq
