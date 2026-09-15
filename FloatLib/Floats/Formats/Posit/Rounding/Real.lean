/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Rounding.Runtime
public import FloatLib.Floats.Formats.Posit.Rounding.Proof
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Real-valued posit rounding specification

The exact rational posit rounding specification has a noncomputable interpretation in `ℝ`. This
interpretation belongs to the semantic proof layer: executable arithmetic continues to use the
rational, dyadic, native-word, and fixed-limb kernels.

The real specification lets refinement theorems state correctness against conventional analytic
operations such as `Real.sqrt`, without adding real-number evaluation to a runtime dependency.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model.RealRounding

/--
Real value of the posit word with unsigned code `code`.

The intended domain is `code < format.signMaskNat`. In general the code is reduced modulo the
format's modulus before decoding; zero and NaR map to zero, and other words retain their sign.
-/
noncomputable def nonnegativeRealAt (format : Format) (code : Nat) : ℝ :=
  (Model.nonnegativeRatAt format code : ℝ)

/-- For a nonnegative target, the greatest code whose real denotation does not exceed it. -/
noncomputable def lowerCode (format : Format) (target : ℝ) : Nat :=
  Model.lowerCodeByBisection
    (fun code => decide (nonnegativeRealAt format code ≤ target))
    format.bits 0 format.signMaskNat

/-- Exact smallest positive real value of a posit format. -/
noncomputable def minPositive (format : Format) : ℝ :=
  nonnegativeRealAt format 1

/-- Exact appended-bit rounding threshold interpreted in the reals. -/
noncomputable def roundingThreshold (format : Format) (lowerCode : Nat) : ℝ :=
  nonnegativeRealAt format.nextPrecision (2 * lowerCode + 1)

/-- Round a real to a nonnegative posit code, sending nonpositive targets to zero. -/
noncomputable def roundPositiveCode (format : Format) (target : ℝ) : Nat :=
  if target ≤ 0 then
    0
  else if target < minPositive format then
    1
  else
    let lower := lowerCode format target
    let upper := lower + 1
    if upper < format.signMaskNat then
      let threshold := roundingThreshold format lower
      if target < threshold then
        lower
      else if threshold < target then
        upper
      else if lower % 2 = 0 then
        lower
      else
        upper
    else
      lower

/-- Model-valued rounding of a nonnegative real target. -/
noncomputable def roundPositive (format : Format) (target : ℝ) : Model format :=
  Model.ofNatBits (roundPositiveCode format target)

/-- Round a signed real by the standard whole-word negation symmetry. -/
noncomputable def round (format : Format) (target : ℝ) : Model format :=
  if target < 0 then Model.neg (roundPositive format (-target))
  else roundPositive format target

/-- Real lower-code search agrees with rational lower-code search after exact coercion. -/
theorem lowerCode_ratCast (format : Format) (target : Rat) :
    lowerCode format (target : ℝ) =
      Model.lowerCodeForPositive format target := by
  unfold lowerCode Model.lowerCodeForPositive
  congr 1
  funext code
  simp [nonnegativeRealAt]

/-- Real lower-code search is monotone in its target. -/
theorem lowerCode_mono (format : Format) :
    Monotone (lowerCode format) := by
  intro left right hle
  unfold lowerCode
  apply Model.lowerCodeByBisection_mono_accept
  intro code hleft
  simp only [decide_eq_true_eq] at hleft ⊢
  exact hleft.trans hle

/-- The minimum positive value has lower code one. -/
theorem lowerCode_minPositive (format : Format) :
    lowerCode format (minPositive format) = 1 := by
  unfold minPositive nonnegativeRealAt
  rw [lowerCode_ratCast,
    Model.lowerCodeForPositive_nonnegativeRatAt
      format 1 format.one_lt_signMaskNat]

/--
Interior positive rounding selects either its lower code or its immediate successor.
-/
theorem roundPositiveCode_bounds
    (format : Format) (target : ℝ)
    (hpositive : 0 < target)
    (hminimum : minPositive format ≤ target) :
    lowerCode format target ≤ roundPositiveCode format target ∧
      roundPositiveCode format target ≤ lowerCode format target + 1 := by
  unfold roundPositiveCode
  rw [ite_eq_right (not_le_of_gt hpositive),
    ite_eq_right (not_lt_of_ge hminimum)]
  dsimp only
  split
  · split
    · constructor <;> omega
    · split
      · constructor <;> omega
      · split <;> constructor <;> omega
  · constructor <;> omega

/-- An interior target below its appended-bit boundary selects the lower code. -/
theorem roundPositiveCode_eq_lower_of_lt_threshold
    (format : Format) (target : ℝ)
    (hpositive : 0 < target)
    (hminimum : minPositive format ≤ target)
    (hupper :
      lowerCode format target + 1 < format.signMaskNat)
    (hbelow :
      target <
        roundingThreshold format (lowerCode format target)) :
    roundPositiveCode format target = lowerCode format target := by
  simp [roundPositiveCode, not_le_of_gt hpositive,
    not_lt_of_ge hminimum, hupper, hbelow]

/-- An interior target above its appended-bit boundary selects the successor code. -/
theorem roundPositiveCode_eq_succ_of_threshold_lt
    (format : Format) (target : ℝ)
    (hpositive : 0 < target)
    (hminimum : minPositive format ≤ target)
    (hupper :
      lowerCode format target + 1 < format.signMaskNat)
    (habove :
      roundingThreshold format (lowerCode format target) < target) :
    roundPositiveCode format target =
      lowerCode format target + 1 := by
  simp [roundPositiveCode, not_le_of_gt hpositive,
    not_lt_of_ge hminimum, hupper, habove,
    not_lt_of_ge habove.le]

/-- A saturated interior lower code is already the final rounded code. -/
theorem roundPositiveCode_eq_lower_of_not_succ_lt
    (format : Format) (target : ℝ)
    (hpositive : 0 < target)
    (hminimum : minPositive format ≤ target)
    (hupper :
      ¬lowerCode format target + 1 < format.signMaskNat) :
    roundPositiveCode format target = lowerCode format target := by
  simp [roundPositiveCode, not_le_of_gt hpositive,
    not_lt_of_ge hminimum, hupper]

/-- Exact real-valued positive rounding is monotone. -/
theorem roundPositiveCode_mono (format : Format) :
    Monotone (roundPositiveCode format) := by
  intro left right hle
  have hlower := lowerCode_mono format hle
  have hminimum :
      ¬right < minPositive format → 1 ≤ lowerCode format right := fun h =>
    (lowerCode_minPositive format).symm.trans_le
      (lowerCode_mono format (not_lt.mp h))
  unfold roundPositiveCode
  dsimp only
  rcases hlower.lt_or_eq with hlt | heq
  · split_ifs <;> first | omega | (exfalso; linarith)
  · rw [heq]
    split_ifs <;>
      first | omega | (exfalso; linarith) | (have := hminimum ‹_›; omega)

/-- Real rounding agrees with rational rounding after exact coercion. -/
theorem roundPositiveCode_ratCast (format : Format) (target : Rat) :
    roundPositiveCode format (target : ℝ) =
      Model.roundPositiveCode format target := by
  unfold roundPositiveCode Model.roundPositiveCode
  simp only [minPositive, roundingThreshold, nonnegativeRealAt,
    Model.minPositiveRat, Model.roundingThreshold,
    Rat.cast_nonpos, Rat.cast_lt, lowerCode_ratCast]
  rfl

/-- Model-valued real rounding agrees with rational rounding after exact coercion. -/
theorem roundPositive_ratCast (format : Format) (target : Rat) :
    roundPositive format (target : ℝ) =
      Model.roundPositiveRat format target := by
  simp [roundPositive, Model.roundPositiveRat, roundPositiveCode_ratCast]

/-- Signed real rounding extends the executable exact-rational specification. -/
theorem round_ratCast (format : Format) (target : Rat) :
    round format (target : ℝ) = Model.roundRat format target := by
  by_cases hzero : target = 0
  · subst target
    simp [round, roundPositive, roundPositiveCode, Model.roundRat, Model.zero]
  · simp only [round, Model.roundRat, ite_eq_right hzero, Rat.cast_lt_zero]
    split
    · rw [← Rat.cast_neg, roundPositive_ratCast]
    · rw [roundPositive_ratCast]

end FloatLib.Floats.Formats.Posit.Model.RealRounding
