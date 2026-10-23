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
to every real target in the enclosure, including subnormal results and underflow to zero. The
binary scale of `roundScaled?` multiplies every target by the same power of two.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Enclosure

open FloatLib.Numerics

private theorem signedScaledRatToReal_eq_cast (value : ℚ) (scale : ℤ) :
    signedScaledRatToReal (decide (value < 0)) value.num.natAbs value.den scale =
      (value : ℝ) * 2 ^ scale := by
  have hmagnitude : (value.num.natAbs : ℝ) / value.den = |(value : ℝ)| := by
    simp [Rat.cast_def, abs_div]
  have hpow : bpow scale = (2 : ℝ) ^ scale := by
    simp [bpow, FloatLib.Floats.Formats.Flocq.bpow, Numerics.binaryRadix, Numerics.Radix.toReal]
  simp only [signedScaledRatToReal, scaledRatToReal, hpow, hmagnitude]
  by_cases hnegative : value < 0
  · have hreal : (value : ℝ) < 0 := by exact_mod_cast hnegative
    simp [hnegative, abs_of_neg hreal]
  · have hreal : 0 ≤ (value : ℝ) := by exact_mod_cast le_of_not_gt hnegative
    simp [hnegative, abs_of_nonneg hreal]

/-- Finite endpoint rounding agrees with nearest-even rounding on the independent real grid. -/
theorem toReal_roundEndpoint (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (value : ℚ)
    (scale : ℤ) (hfinite : isFinite (roundEndpoint fmt value scale) = true) :
    toReal (roundEndpoint fmt value scale) = roundAt fmt ((value : ℝ) * 2 ^ scale) := by
  rw [roundEndpoint, toReal_roundRatScaled_eq_roundAt_of_isFinite
    fmt (decide (value < 0)) value.num.natAbs value.den scale hfmt value.den_nz hfinite,
    signedScaledRatToReal_eq_cast]

/-- Acceptance proves both the descriptor restriction and endpoint finiteness and agreement. -/
theorem accepted {fmt : FloatFormat} {interval : RationalInterval} {scale : ℤ}
    {result : Model fmt} (hresult : roundScaled? fmt interval scale = some result) :
    fmt.isIEEE = true ∧ isFinite result = true ∧
      roundEndpoint fmt interval.lo scale = result ∧
        roundEndpoint fmt interval.hi scale = result := by
  unfold roundScaled? at hresult
  split at hresult
  · rename_i hfmt
    dsimp only at hresult
    split at hresult
    · rename_i hsame
      have hvalue := Option.some.inj hresult
      exact ⟨hfmt, hvalue ▸ hsame.1, hvalue, hsame.2.symm.trans hvalue⟩
    · simp at hresult
  · simp at hresult

/-- A scaled accepted encoding is finite, because overflow can never pass the endpoint check. -/
theorem isFinite_of_roundScaled?_eq_some {fmt : FloatFormat}
    {interval : RationalInterval} {scale : ℤ} {result : Model fmt}
    (hresult : roundScaled? fmt interval scale = some result) : isFinite result = true :=
  (accepted hresult).2.1

/--
Every scaled accepted result is the correctly rounded value of every real target in the enclosure
times the binary scale.
-/
theorem toReal_eq_roundAt_of_roundScaled?_eq_some {fmt : FloatFormat}
    {interval : RationalInterval} {scale : ℤ} {target : ℝ} {result : Model fmt}
    (htarget : interval.Contains target) (hresult : roundScaled? fmt interval scale = some result) :
    toReal result = roundAt fmt (target * 2 ^ scale) := by
  obtain ⟨hfmt, hfinite, hlower, hupper⟩ := accepted hresult
  have hlo : toReal result = roundAt fmt ((interval.lo : ℝ) * 2 ^ scale) := by
    rw [← hlower] at hfinite ⊢
    exact toReal_roundEndpoint fmt hfmt interval.lo scale hfinite
  have hhi : toReal result = roundAt fmt ((interval.hi : ℝ) * 2 ^ scale) := by
    rw [← hupper] at hfinite ⊢
    exact toReal_roundEndpoint fmt hfmt interval.hi scale hfinite
  have hpow : (0 : ℝ) < 2 ^ scale := zpow_pos (by norm_num) scale
  exact le_antisymm
    (hlo.trans_le (roundAt_mono fmt (mul_le_mul_of_nonneg_right htarget.1 hpow.le)))
    ((roundAt_mono fmt (mul_le_mul_of_nonneg_right htarget.2 hpow.le)).trans_eq hhi.symm)

/-- An accepted encoding is finite, because overflow can never pass the endpoint check. -/
theorem isFinite_of_round?_eq_some {fmt : FloatFormat}
    {interval : RationalInterval} {result : Model fmt}
    (hresult : round? fmt interval = some result) : isFinite result = true :=
  isFinite_of_roundScaled?_eq_some hresult

/-- Every accepted result is the correctly rounded value of every real target in the enclosure. -/
theorem toReal_eq_roundAt_of_round?_eq_some {fmt : FloatFormat}
    {interval : RationalInterval} {target : ℝ} {result : Model fmt}
    (htarget : interval.Contains target) (hresult : round? fmt interval = some result) :
    toReal result = roundAt fmt target := by
  simpa using toReal_eq_roundAt_of_roundScaled?_eq_some htarget hresult

end FloatLib.Floats.Formats.BinaryInterchange.Model.Transcendentals.Enclosure
