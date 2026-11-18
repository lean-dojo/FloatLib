/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Floats.Formats.P3109.Block.Root.Proof
public import FloatLib.Floats.Formats.P3109.Arithmetic.Sqrt.Report
public import FloatLib.Floats.Formats.P3109.Projection.Saturation

/-!
# Independent report formula for signed block roots

P3109 Interim Report v4.1, §§4.7.4–4.7.5, 5.4.2 and 5.7
(unapproved draft). The exact signed-root implementation delivers the
independent logarithmic real rounding formula, including negative finite
result scales and all supplied stochastic words. Exceptional scale rules
remain the separate closed-domain contracts.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.P3109.BlockRoot

open FloatLib.Numerics

/-- P3109 interim report v4.1, §4.7.4: reversing directed magnitude rounding gives the signed
    fractional decision. -/
theorem roundAway_magnitudeMode (mode : RoundingMode) (negative lowerEven : Bool)
    (fraction : ℝ) :
    RoundingFormula.roundAway (magnitudeMode negative mode) false lowerEven fraction =
      RoundingFormula.roundAway mode negative lowerEven fraction := by
  cases negative <;> cases mode <;> simp [magnitudeMode, RoundingFormula.roundAway]

/-- P3109 interim report v4.1, §4.7.4: restoring a rounded magnitude's sign gives the signed
    report value.
The equality is numerical because the report canonicalizes a rounded zero. -/
theorem reportRounded_signed_toRat (format : Format) (mode : RoundingMode)
    (negative : Bool) (magnitude : ℝ) (h : 0 ≤ magnitude) :
    (if negative then
      (ComparisonRounding.reportRounded format (magnitudeMode negative mode) magnitude).neg
    else ComparisonRounding.reportRounded format (magnitudeMode negative mode) magnitude).toRat =
      (ComparisonRounding.reportRounded format mode
        (if negative then -magnitude else magnitude)).toRat := by
  cases negative with
  | false => cases mode <;> rfl
  | true =>
      change (ComparisonRounding.reportRounded format (magnitudeMode true mode)
        magnitude).neg.toRat =
        (ComparisonRounding.reportRounded format mode (-magnitude)).toRat
      by_cases hz : magnitude = 0
      · simp [hz, ComparisonRounding.reportRounded]
      have hp : 0 < magnitude := lt_of_le_of_ne h (Ne.symm hz)
      simp only [ComparisonRounding.reportRounded, hz,
        neg_eq_zero, ite_false, not_lt_of_ge h, decide_false,
        neg_lt_zero.mpr hp, decide_true, abs_of_nonneg h, abs_neg]
      rw [roundAway_magnitudeMode]
      split_ifs <;> simp [Numerics.Dyadic.neg, Numerics.Dyadic.toRat,
        Numerics.Dyadic.signedSignificand]

/-- P3109 interim report v4.1, §§4.7.4–4.7.5: signed exact-root rounding and saturation deliver
    the real report datum. -/
theorem sameDatum_value_report (format : Format) (policy : ProjectionPolicy)
    (negative : Bool) (radicand : Rat) (h : 0 ≤ radicand) :
    Format.SameDatum (value format policy ⟨negative, .finite radicand⟩)
      (ComparisonRounding.reportValue format policy
        (if negative then -Real.sqrt (radicand : ℝ) else Real.sqrt (radicand : ℝ))) := by
  simp only [value, rounded, Arithmetic.sqrtRounded, not_lt_of_ge h, ite_false,
    Arithmetic.roundSqrtRatToPrecision_eq_report format
      (magnitudeMode negative policy.rounding) radicand h,
    applySign, ComparisonRounding.reportValue]
  exact format.sameDatum_saturate_finite policy.saturation policy.rounding
    (reportRounded_signed_toRat format policy.rounding negative _ (Real.sqrt_nonneg _))

/-- P3109 interim report v4.1, §§4.7.4–4.7.5 and 5.7: encoding a signed root preserves its
    independent report datum. -/
theorem decode_project_report (format : Format) (policy : ProjectionPolicy)
    (negative : Bool) (radicand : Rat) (h : 0 ≤ radicand) :
    Format.SameDatum
      (ExecFloat.P3109.decode (project format policy ⟨negative, .finite radicand⟩))
      (ComparisonRounding.reportValue format policy
        (if negative then -Real.sqrt (radicand : ℝ) else Real.sqrt (radicand : ℝ))) :=
  (decode_project format policy _).trans (sameDatum_value_report format policy negative radicand h)

/-- P3109 interim report v4.1, §§5.4.2 and 5.7: a finite nonzero result scale divides the exact
    real root before
the independent report rounding, for either scale sign and every lane policy. -/
theorem decode_project_normalize_report (format : Format) (policy : ProjectionPolicy)
    (scale radicand : Rat) (hs : scale ≠ 0) (hq : 0 ≤ radicand) :
    Format.SameDatum
      (ExecFloat.P3109.decode
        (project format policy (normalize (.finite scale) (.finite radicand))))
      (ComparisonRounding.reportValue format policy
        (Real.sqrt (radicand : ℝ) / (scale : ℝ))) := by
  rw [normalize_finite scale radicand hs hq]
  have hn : 0 ≤ radicand / (scale * scale) := div_nonneg hq (mul_self_nonneg _)
  have hnormalized := normalize_finite_real scale radicand hs hq
  have hreal :
      (if decide (scale < 0) then -Real.sqrt ((radicand / (scale * scale) : Rat) : ℝ)
       else Real.sqrt ((radicand / (scale * scale) : Rat) : ℝ)) =
        Real.sqrt (radicand : ℝ) / (scale : ℝ) := by
    simpa only [decide_eq_true_eq, ite_mul, neg_one_mul, one_mul] using hnormalized
  rw [← hreal]
  exact decode_project_report format policy _ _ hn

end FloatLib.Floats.Formats.P3109.BlockRoot

namespace FloatLib.Floats.Formats.P3109.Block

open FloatLib.Numerics FloatLib.Floats.ExecFloat Arithmetic

/-- P3109 interim report v4.1, §§5.4.2 and 5.7: each finite root lane is divided by its finite
    nonzero
decoded result scale, then rounded and saturated by the independent real report formula. -/
theorem decode_projectRoots_report {length : ℕ+}
    {Scale Exact : Type} [ExactDecoder Scale Exact] [ExactMap Exact Rat]
    (format : Format) (policy : BlockPolicy length) (scale : Scale)
    (radicands : Vector (NumericalValue Rat) length) (lane : Fin (length : Nat))
    (s q : Rat) (hs : Mixed.decode scale = .finite s) (hs0 : s ≠ 0)
    (hq : radicands[lane.val] = .finite q) (hq0 : 0 ≤ q) :
    Format.SameDatum
      (ExecFloat.P3109.decode (projectRoots format policy scale radicands).values[lane.val])
      (ComparisonRounding.reportValue format (policy.at lane)
        (Real.sqrt (q : ℝ) / (s : ℝ))) := by
  simpa only [projectRoots, Vector.getElem_ofFn, hs, hq] using
    BlockRoot.decode_project_normalize_report format (policy.at lane) s q hs0 hq0

end FloatLib.Floats.Formats.P3109.Block
