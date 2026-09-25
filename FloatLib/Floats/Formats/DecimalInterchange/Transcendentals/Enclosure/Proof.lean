/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure.Runtime
public import FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Rounding
public import FloatLib.Numerics.Enclosure.Rational.Proof

/-!
# Real correctness of decimal enclosure acceptance

Finite endpoint projections equal real nearest-even rounding. Flocq monotonicity then forces
every enclosed real value to have the same rounded result. Success proves destination validity
and finiteness as well as the equality to the real specification.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure

open FloatLib.Numerics

/-- A finite datum has an exact rational interpretation. -/
theorem exists_toRat?_of_isFinite {datum : Datum} (hfinite : datum.isFinite = true) :
    ∃ value : ℚ, datum.toRat? = some value := by
  cases datum with
  | finite s c q => simp only [Datum.toRat?_eq]; exact ⟨_, rfl⟩
  | infinity s => simp [Datum.isFinite] at hfinite
  | nan s t p => simp [Datum.isFinite] at hfinite

/-- Finite endpoint projection equals real nearest-even rounding at every decimal descriptor. -/
theorem toReal_roundEndpoint (f : Format) (value : ℚ)
    (hfinite : (roundEndpoint f value).isFinite = true) :
    toReal (roundEndpoint f value) = roundAt f (value : ℝ) := by
  obtain ⟨rounded, hrounded⟩ := exists_toRat?_of_isFinite hfinite
  rw [toReal_of_toRat?_eq_some hrounded]
  exact project_nearestEven_eq_roundAt f value f.minQuantum false hrounded

/-- Acceptance records finiteness and equality of the two endpoint datums. -/
theorem accepted {f : Format} {interval : RationalInterval} {result : Datum}
    (hresult : round? f interval = some result) :
    result.isFinite = true ∧ roundEndpoint f interval.lo = result ∧
      roundEndpoint f interval.hi = result := by
  dsimp only [round?] at hresult
  split at hresult
  · rename_i hsame
    have hvalue := Option.some.inj hresult
    exact ⟨hvalue ▸ hsame.1, hvalue, hsame.2.symm.trans hvalue⟩
  · simp at hresult

/-- No infinity or NaN can pass the endpoint test. -/
theorem isFinite_of_round?_eq_some {f : Format} {interval : RationalInterval} {result : Datum}
    (hresult : round? f interval = some result) : result.isFinite = true :=
  (accepted hresult).1

/-- Every accepted datum is representable in the destination format. -/
theorem valid_of_round?_eq_some {f : Format} {interval : RationalInterval} {result : Datum}
    (hresult : round? f interval = some result) : result.Valid f := by
  rw [← (accepted hresult).2.1]
  exact project_valid f .nearestEven interval.lo f.minQuantum false

/-- Endpoint agreement certifies real nearest-even rounding of every enclosed target. -/
theorem toReal_eq_roundAt_of_round?_eq_some {f : Format}
    {interval : RationalInterval} {target : ℝ} {result : Datum}
    (htarget : interval.Contains target) (hresult : round? f interval = some result) :
    toReal result = roundAt f target := by
  obtain ⟨hfinite, hlower, hupper⟩ := accepted hresult
  have hlo : toReal result = roundAt f (interval.lo : ℝ) := by
    rw [← hlower] at hfinite ⊢
    exact toReal_roundEndpoint f interval.lo hfinite
  have hhi : toReal result = roundAt f (interval.hi : ℝ) := by
    rw [← hupper] at hfinite ⊢
    exact toReal_roundEndpoint f interval.hi hfinite
  exact le_antisymm (hlo.trans_le (roundAt_mono f htarget.1))
    ((roundAt_mono f htarget.2).trans_eq hhi.symm)

/-- An accepted datum is within half a decimal ULP of the enclosed real target. -/
theorem error_le_half_ulp_of_round?_eq_some {f : Format}
    {interval : RationalInterval} {target : ℝ} {result : Datum}
    (htarget : interval.Contains target) (hresult : round? f interval = some result) :
    |toReal result - target| ≤ Flocq.ulp decimalRadix (fexpOf f) target / 2 := by
  rw [toReal_eq_roundAt_of_round?_eq_some htarget hresult]
  exact roundAt_error_le_half_ulp f target

end FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Enclosure
