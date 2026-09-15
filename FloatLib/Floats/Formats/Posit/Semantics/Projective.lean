/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.OnePointOption
public import FloatLib.Floats.Formats.Posit.Semantics.Real

/-!
# Optional projective semantics of posits

The primary posit semantics remains `NumericalValue Rat`: every ordinary word denotes an exact
dyadic rational, while the single NaR word denotes `ExceptionalValue.notAReal`.

For applications that intentionally want a one-point completion, `Model.toProjectiveRat` is
`Option.toOnePoint` applied to the exact optional semantics: it maps all finite values to their
canonical rational point and NaR to the added point. The theorem `toProjectiveRat_eq_infty_iff`
identifies NaR exactly; it remains distinct from every finite point. Mathlib supplies the
canonical equivalence from `OnePoint Rat` to the projective line over `Rat`.

Finite rational values map canonically into `OnePoint Real` and the real projective line. This
adapter provides coordinates for topology and projective proofs. It does not change the
arithmetic interpretation of NaR.

## References

* Posit Working Group, *Standard for Posit Arithmetic (2022)*, March 2, 2022,
  Sections 3--5, <https://posithub.org/docs/posit_standard-2.pdf>.
* Mathlib, `OnePoint.equivProjectivization`,
  <https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Topology/Compactification/OnePoint/ProjectiveLine.lean>.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace FloatLib.Floats.Formats.Posit

namespace Model

variable {format : Format}

/--
Intentional one-point projection of posit meanings.

It sends NaR to the added point called `∞` by `OnePoint`, distinct from all finite values.
The name of that point does not give NaR an ordered or signed-infinity interpretation.
-/
@[inline] def toProjectiveRat (value : Model format) : OnePoint Rat :=
  value.toRat?.toOnePoint

/-- The rational one-point projection sends the canonical zero word to zero. -/
@[simp] theorem toProjectiveRat_zero (format : Format) :
    toProjectiveRat (zero format) = ((0 : Rat) : OnePoint Rat) := by
  simp [toProjectiveRat]

/-- The rational one-point projection sends the unique NaR word to its added point. -/
@[simp] theorem toProjectiveRat_nar (format : Format) :
    toProjectiveRat (nar format) = OnePoint.infty := by
  simp [toProjectiveRat]

/--
The one-point projection agrees with the exact rational view on every ordinary posit.

Together with `toProjectiveRat_eq_infty_iff`, this characterizes the complete projection:
finite points correspond exactly to `some` rational, and
the added point corresponds exactly to NaR.
-/
theorem toProjectiveRat_eq_coe_iff (value : Model format) (rational : Rat) :
    value.toProjectiveRat = (rational : OnePoint Rat) ↔
      value.toRat? = some rational :=
  Option.toOnePoint_eq_coe_iff _ _

/-- The projective view reaches its added point exactly for the NaR encoding. -/
theorem toProjectiveRat_eq_infty_iff (value : Model format) :
    value.toProjectiveRat = OnePoint.infty ↔ value.isNaR = true :=
  (Option.toOnePoint_eq_infty_iff _).trans (toRat?_eq_none_iff value)

/-- Canonical rational projective-line point associated with the rational one-point view. -/
@[inline] def toProjectiveRatLine (value : Model format) : ℙ Rat (Fin 2 → Rat) :=
  OnePoint.equivProjectivization Rat value.toProjectiveRat

/-- Rational projective-line point chosen for NaR by the one-point view. -/
def projectiveRatNaR : ℙ Rat (Fin 2 → Rat) :=
  OnePoint.equivProjectivization Rat OnePoint.infty

/-- The rational projective-line projection sends the canonical zero word to zero. -/
@[simp] theorem toProjectiveRatLine_zero (format : Format) :
    toProjectiveRatLine (zero format) =
      OnePoint.equivProjectivization Rat ((0 : Rat) : OnePoint Rat) := by
  simp [toProjectiveRatLine]

/-- The rational projective-line projection sends NaR to its distinguished added point. -/
@[simp] theorem toProjectiveRatLine_nar (format : Format) :
    toProjectiveRatLine (nar format) = projectiveRatNaR := by
  simp [toProjectiveRatLine, projectiveRatNaR]

/--
Equality of finite projective-line points is exactly equality of their rational coordinates.

The equivalence is inherited from mathlib's `OnePoint.equivProjectivization`; no separate posit
notion of projective equality is introduced.
-/
theorem toProjectiveRatLine_eq_finite_iff
    (value : Model format) (rational : Rat) :
    value.toProjectiveRatLine =
        OnePoint.equivProjectivization Rat (rational : OnePoint Rat) ↔
      value.toRat? = some rational :=
  (OnePoint.equivProjectivization_eq_iff Rat _ _).trans
    (toProjectiveRat_eq_coe_iff value rational)

/-- The rational projective-line view is its NaR point exactly for the NaR encoding. -/
theorem toProjectiveRatLine_eq_nar_iff (value : Model format) :
    value.toProjectiveRatLine = projectiveRatNaR ↔ value.isNaR = true :=
  (OnePoint.equivProjectivization_eq_iff Rat _ _).trans
    (toProjectiveRat_eq_infty_iff value)

/-! ## Mathlib real and real-projective views -/

/--
Intentional real one-point projection of posit meanings.

The finite branch is the canonical injection `Rat → Real`; NaR alone maps to the added point.
This view is useful for topology and analysis. Its type distinguishes this geometric
interpretation from the `notAReal` exception used by `decodeReal`.
-/
@[inline] noncomputable def toProjectiveReal (value : Model format) : OnePoint ℝ :=
  value.toReal?.toOnePoint

/-- The real one-point projection sends the canonical zero word to zero. -/
@[simp] theorem toProjectiveReal_zero (format : Format) :
    toProjectiveReal (zero format) = ((0 : ℝ) : OnePoint ℝ) := by
  simp [toProjectiveReal]

/-- The real one-point projection sends the unique NaR word to its added point. -/
@[simp] theorem toProjectiveReal_nar (format : Format) :
    toProjectiveReal (nar format) = OnePoint.infty := by
  simp [toProjectiveReal]

/-- A finite rational coordinate is preserved exactly by the real one-point projection. -/
theorem toProjectiveReal_eq_coe_iff (value : Model format) (rational : Rat) :
    value.toProjectiveReal = ((rational : ℝ) : OnePoint ℝ) ↔
      value.toRat? = some rational :=
  Option.toOnePoint_map_eq_coe_iff Rat.cast_injective _ _

/-- The real one-point projection reaches its added point exactly for NaR. -/
theorem toProjectiveReal_eq_infty_iff (value : Model format) :
    value.toProjectiveReal = OnePoint.infty ↔ value.isNaR = true :=
  (Option.toOnePoint_map_eq_infty_iff _ _).trans (toRat?_eq_none_iff value)

/-- Canonical real projective-line point associated with the real one-point view. -/
@[inline] noncomputable def toProjectiveRealLine
    (value : Model format) : ℙ ℝ (Fin 2 → ℝ) :=
  OnePoint.equivProjectivization ℝ value.toProjectiveReal

/-- Real projective-line point chosen for NaR by the one-point view. -/
noncomputable def projectiveRealNaR : ℙ ℝ (Fin 2 → ℝ) :=
  OnePoint.equivProjectivization ℝ OnePoint.infty

/-- The real projective-line projection sends the canonical zero word to zero. -/
@[simp] theorem toProjectiveRealLine_zero (format : Format) :
    toProjectiveRealLine (zero format) =
      OnePoint.equivProjectivization ℝ ((0 : ℝ) : OnePoint ℝ) := by
  simp [toProjectiveRealLine]

/-- The real projective-line projection sends NaR to its distinguished added point. -/
@[simp] theorem toProjectiveRealLine_nar (format : Format) :
    toProjectiveRealLine (nar format) = projectiveRealNaR := by
  simp [toProjectiveRealLine, projectiveRealNaR]

/-- Finite real projective coordinates agree exactly with the embedded rational semantics. -/
theorem toProjectiveRealLine_eq_finite_iff
    (value : Model format) (rational : Rat) :
    value.toProjectiveRealLine =
        OnePoint.equivProjectivization ℝ ((rational : ℝ) : OnePoint ℝ) ↔
      value.toRat? = some rational :=
  (OnePoint.equivProjectivization_eq_iff ℝ _ _).trans
    (toProjectiveReal_eq_coe_iff value rational)

/-- The real projective-line view is its NaR point exactly for the NaR encoding. -/
theorem toProjectiveRealLine_eq_nar_iff (value : Model format) :
    value.toProjectiveRealLine = projectiveRealNaR ↔ value.isNaR = true :=
  (OnePoint.equivProjectivization_eq_iff ℝ _ _).trans
    (toProjectiveReal_eq_infty_iff value)

end Model
end FloatLib.Floats.Formats.Posit
