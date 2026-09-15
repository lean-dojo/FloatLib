/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Real
public import FloatLib.Floats.Formats.Posit.Semantics.OnePointOption

/-!
# Explicit projective views of posit quires

These adapters apply `Option.toOnePoint` to the exact optional semantics. They map the unique
quire NaR word to the added point and then to mathlib's projective line, preserving the distinction
between NaR and finite values. This geometric interpretation supplies no signed or ordered
infinity semantics for quire arithmetic.

## References

* Mathlib, `OnePoint.equivProjectivization`.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace FloatLib.Floats.Formats.Posit.Quire.Model

variable {format : Format}

/--
One-point view of quire meanings over `Rat`.

The added point represents quire NaR in this view.
-/
@[inline] def toProjectiveRat (value : Model format) : OnePoint Rat :=
  value.toRat?.toOnePoint

/-- The zero quire embeds as finite zero in projective rational semantics. -/
@[simp] theorem toProjectiveRat_zero (format : Format) :
    (zero format).toProjectiveRat = ((0 : Rat) : OnePoint Rat) := by
  simp [toProjectiveRat]

/-- The NaR quire embeds as the projective rational point at infinity. -/
@[simp] theorem toProjectiveRat_nar (format : Format) :
    (nar format).toProjectiveRat = OnePoint.infty := by
  simp [toProjectiveRat]

/-- Finite one-point coordinates agree exactly with the primary rational semantics. -/
theorem toProjectiveRat_eq_coe_iff
    (value : Model format) (rational : Rat) :
    value.toProjectiveRat = (rational : OnePoint Rat) ↔
      value.toRat? = some rational :=
  Option.toOnePoint_eq_coe_iff _ _

/-- The rational one-point view reaches its added point exactly for quire NaR. -/
theorem toProjectiveRat_eq_infty_iff (value : Model format) :
    value.toProjectiveRat = OnePoint.infty ↔ value.isNaR = true :=
  (Option.toOnePoint_eq_infty_iff _).trans (toRat?_eq_none_iff value)

/-- Canonical rational projective-line point associated with the quire one-point view. -/
@[inline] def toProjectiveRatLine (value : Model format) : ℙ Rat (Fin 2 → Rat) :=
  OnePoint.equivProjectivization Rat value.toProjectiveRat

/-- Rational projective-line point representing quire NaR. -/
def projectiveRatNaR : ℙ Rat (Fin 2 → Rat) :=
  OnePoint.equivProjectivization Rat OnePoint.infty

/-- The rational projective line reaches its distinguished NaR point exactly for quire NaR. -/
theorem toProjectiveRatLine_eq_nar_iff (value : Model format) :
    value.toProjectiveRatLine = projectiveRatNaR ↔ value.isNaR = true :=
  (OnePoint.equivProjectivization_eq_iff Rat _ _).trans
    (toProjectiveRat_eq_infty_iff value)

/-- Real one-point view of quire meanings. -/
@[inline] noncomputable def toProjectiveReal (value : Model format) : OnePoint ℝ :=
  value.toReal?.toOnePoint

/-- The zero quire embeds as finite zero in projective real semantics. -/
@[simp] theorem toProjectiveReal_zero (format : Format) :
    (zero format).toProjectiveReal = ((0 : ℝ) : OnePoint ℝ) := by
  simp [toProjectiveReal]

/-- The NaR quire embeds as the projective real point at infinity. -/
@[simp] theorem toProjectiveReal_nar (format : Format) :
    (nar format).toProjectiveReal = OnePoint.infty := by
  simp [toProjectiveReal]

/-- The real one-point view reaches its added point exactly for quire NaR. -/
theorem toProjectiveReal_eq_infty_iff (value : Model format) :
    value.toProjectiveReal = OnePoint.infty ↔ value.isNaR = true :=
  (Option.toOnePoint_map_eq_infty_iff _ _).trans (toRat?_eq_none_iff value)

/-- Canonical real projective-line point associated with the real quire one-point view. -/
@[inline] noncomputable def toProjectiveRealLine
    (value : Model format) : ℙ ℝ (Fin 2 → ℝ) :=
  OnePoint.equivProjectivization ℝ value.toProjectiveReal

/-- Real projective-line point representing quire NaR. -/
noncomputable def projectiveRealNaR : ℙ ℝ (Fin 2 → ℝ) :=
  OnePoint.equivProjectivization ℝ OnePoint.infty

/-- The real projective line reaches its distinguished NaR point exactly for quire NaR. -/
theorem toProjectiveRealLine_eq_nar_iff (value : Model format) :
    value.toProjectiveRealLine = projectiveRealNaR ↔ value.isNaR = true :=
  (OnePoint.equivProjectivization_eq_iff ℝ _ _).trans
    (toProjectiveReal_eq_infty_iff value)

end FloatLib.Floats.Formats.Posit.Quire.Model
