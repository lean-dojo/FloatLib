/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import
  FloatLib.Floats.Formats.BinaryInterchange.DirectedSemantics.Rational.RoundingSemantics.Executable
public import FloatLib.Floats.Formats.BinaryInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Numerics.Enclosure.Rational.Proof

/-!
# Soundness of binary enclosure acceptance

Finite rational rounding agrees with `roundAt`. Monotonicity extends agreement of rounded endpoints
to every real target in the enclosure, including subnormal results and underflow to zero.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Enclosure

open FloatLib.Numerics

private theorem signedScaledRatToReal_eq_cast (value : ℚ) :
    signedScaledRatToReal (decide (value < 0)) value.num.natAbs value.den 0 =
      (value : ℝ) := by
  have hmagnitude : (value.num.natAbs : ℝ) / value.den = |(value : ℝ)| := by
    simp [Rat.cast_def, abs_div]
  simp only [signedScaledRatToReal, scaledRatToReal, bpow_zero, mul_one, hmagnitude]
  by_cases hnegative : value < 0
  · have hreal : (value : ℝ) < 0 := by exact_mod_cast hnegative
    simp [hnegative, abs_of_neg hreal]
  · have hreal : 0 ≤ (value : ℝ) := by exact_mod_cast le_of_not_gt hnegative
    simp [hnegative, abs_of_nonneg hreal]

/-- Finite endpoint rounding agrees with nearest-even rounding on the independent real grid. -/
theorem toReal_roundEndpoint (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (value : ℚ)
    (hfinite : isFinite (roundEndpoint fmt value) = true) :
    toReal (roundEndpoint fmt value) = roundAt fmt (value : ℝ) := by
  by_cases hzero : value = 0
  · simp [hzero, roundEndpoint]
  · have hnumerator : value.num.natAbs ≠ 0 := by simpa using hzero
    rw [roundEndpoint, roundRat, toReal_roundRatScaled_eq_roundAt
      fmt (decide (value < 0)) value.num.natAbs value.den 0
      hfmt hnumerator value.den_nz hfinite, signedScaledRatToReal_eq_cast]

/-- Acceptance proves both the descriptor restriction and endpoint finiteness and agreement. -/
theorem accepted {fmt : FloatFormat} {interval : RationalInterval} {result : Model fmt}
    (hresult : round? fmt interval = some result) :
    fmt.isIEEE = true ∧ isFinite result = true ∧
      roundEndpoint fmt interval.lo = result ∧ roundEndpoint fmt interval.hi = result := by
  unfold round? at hresult
  split at hresult
  · rename_i hfmt
    dsimp only at hresult
    split at hresult
    · rename_i hsame
      have hvalue := Option.some.inj hresult
      exact ⟨hfmt, hvalue ▸ hsame.1, hvalue, hsame.2.symm.trans hvalue⟩
    · simp at hresult
  · simp at hresult

/-- An accepted encoding is finite; overflow can never pass the endpoint check. -/
theorem isFinite_of_round?_eq_some {fmt : FloatFormat}
    {interval : RationalInterval} {result : Model fmt}
    (hresult : round? fmt interval = some result) : isFinite result = true :=
  (accepted hresult).2.1

/-- Every accepted result is the correctly rounded value of every real target in the enclosure. -/
theorem toReal_eq_roundAt_of_round?_eq_some {fmt : FloatFormat}
    {interval : RationalInterval} {target : ℝ} {result : Model fmt}
    (htarget : interval.Contains target) (hresult : round? fmt interval = some result) :
    toReal result = roundAt fmt target := by
  obtain ⟨hfmt, hfinite, hlower, hupper⟩ := accepted hresult
  have hlo : toReal result = roundAt fmt (interval.lo : ℝ) := by
    rw [← hlower] at hfinite ⊢
    exact toReal_roundEndpoint fmt hfmt interval.lo hfinite
  have hhi : toReal result = roundAt fmt (interval.hi : ℝ) := by
    rw [← hupper] at hfinite ⊢
    exact toReal_roundEndpoint fmt hfmt interval.hi hfinite
  exact le_antisymm
    (hlo.trans_le (roundAt_mono fmt htarget.1))
    ((roundAt_mono fmt htarget.2).trans_eq hhi.symm)

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Enclosure
