/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Projective
public import FloatLib.Floats.Formats.Posit.Configured

/-!
# Optional projective views of configured posits

Configured posits normally decode NaR as an exceptional value with no real meaning. These
adapters map it, on purpose, to the added point of Mathlib's one-point completion and projective
line. They are views for proofs and carry no executable posit semantics. We keep them out of the
basic configured API so that ordinary programs don't pick up topology and projective-geometry
dependencies.
-/

@[expose] public section

open scoped LinearAlgebra.Projectivization

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit

namespace ExecFloat.Posit

variable {format : Format} {plan : Configured.StoragePlan format} {code : Type}
    [codec : FloatLib.Floats.ExecFloat.ModelCodec plan (Model format) code]

/--
Opt-in one-point view of a configured posit.

This view maps NaR to `OnePoint.infty` and so reads it as the added projective point.
The primary denotation returned by `decode` keeps NaR as `ExceptionalValue.notAReal`.
-/
@[inline] def toProjectiveRat
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    OnePoint Rat :=
  Model.toProjectiveRat (toModel value)

/-- Canonical mathlib rational projective-line view of a configured posit. -/
@[inline] def toProjectiveRatLine
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ℙ Rat (Fin 2 → Rat) :=
  Model.toProjectiveRatLine (toModel value)

/-- Opt-in real one-point view, which embeds the exact rational finite values. -/
@[inline] noncomputable def toProjectiveReal
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    OnePoint ℝ :=
  Model.toProjectiveReal (toModel value)

/-- Canonical mathlib real projective-line view of a configured posit. -/
@[inline] noncomputable def toProjectiveRealLine
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    ℙ ℝ (Fin 2 → ℝ) :=
  Model.toProjectiveRealLine (toModel value)

/-- A configured posit maps to the rational point at infinity if and only if it is NaR. -/
@[simp, grind =] theorem toProjectiveRat_eq_infty_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toProjectiveRat value = OnePoint.infty ↔ isNaR value = true :=
  Model.toProjectiveRat_eq_infty_iff (toModel value)

/-- Equality with a finite rational point is equivalent to the exact optional rational view. -/
@[simp, grind =] theorem toProjectiveRat_eq_coe_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan))
    (rational : Rat) :
    toProjectiveRat value = (rational : OnePoint Rat) ↔
      toRat? value = some rational :=
  Model.toProjectiveRat_eq_coe_iff (toModel value) rational

/-- On finite rational points, the rational projective-line view agrees with `toRat?`. -/
@[grind =]
theorem toProjectiveRatLine_eq_finite_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan))
    (rational : Rat) :
    toProjectiveRatLine value =
        OnePoint.equivProjectivization Rat (rational : OnePoint Rat) ↔
      toRat? value = some rational :=
  Model.toProjectiveRatLine_eq_finite_iff (toModel value) rational

/-- Posit NaR, and nothing else, maps to the distinguished rational projective point. -/
@[simp, grind =] theorem toProjectiveRatLine_eq_nar_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toProjectiveRatLine value = Model.projectiveRatNaR ↔ isNaR value = true :=
  Model.toProjectiveRatLine_eq_nar_iff (toModel value)

/-- A configured posit maps to the real point at infinity if and only if it is NaR. -/
@[simp, grind =] theorem toProjectiveReal_eq_infty_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toProjectiveReal value = OnePoint.infty ↔ isNaR value = true :=
  Model.toProjectiveReal_eq_infty_iff (toModel value)

/-- Equality with an embedded rational real point agrees with the exact rational view. -/
@[simp, grind =] theorem toProjectiveReal_eq_coe_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan))
    (rational : Rat) :
    toProjectiveReal value = ((rational : ℝ) : OnePoint ℝ) ↔
      toRat? value = some rational :=
  Model.toProjectiveReal_eq_coe_iff (toModel value) rational

/-- On embedded finite rational points, the real projective-line view agrees with `toRat?`. -/
@[grind =]
theorem toProjectiveRealLine_eq_finite_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan))
    (rational : Rat) :
    toProjectiveRealLine value =
        OnePoint.equivProjectivization ℝ ((rational : ℝ) : OnePoint ℝ) ↔
      toRat? value = some rational :=
  Model.toProjectiveRealLine_eq_finite_iff (toModel value) rational

/-- Posit NaR, and nothing else, maps to the distinguished real projective point. -/
@[simp, grind =] theorem toProjectiveRealLine_eq_nar_iff
    (value : FloatLib.Floats.ExecFloat (Configured.Family format code plan)) :
    toProjectiveRealLine value = Model.projectiveRealNaR ↔ isNaR value = true :=
  Model.toProjectiveRealLine_eq_nar_iff (toModel value)

end ExecFloat.Posit
end FloatLib.Floats
