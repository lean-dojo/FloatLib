/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Semantics.Projective

/-!
# Optional mathematical views of configured posit quires

These wrappers expose real and projective-line denotations through the configured API. They are
kept outside `Configured.Runtime` because executable rational quire arithmetic does not require
classical real-number or projective-geometry dependencies.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Floats.Formats.Posit
open scoped LinearAlgebra.Projectivization

namespace ExecFloat.Posit.Quire

variable {format : Format}

/-- Complete real quire semantics obtained from the exact rational denotation. -/
@[inline] noncomputable def decodeReal
    (value : Formats.Posit.Quire.Model format) :
    FloatLib.Numerics.NumericalValue ℝ :=
  Formats.Posit.Quire.Model.decodeReal value

/-- Mathlib rational projective-line view of a configured quire. -/
@[inline] def toProjectiveRatLine
    (value : Formats.Posit.Quire.Model format) :
    ℙ Rat (Fin 2 → Rat) :=
  Formats.Posit.Quire.Model.toProjectiveRatLine value

/-- Mathlib real projective-line view of a configured quire. -/
@[inline] noncomputable def toProjectiveRealLine
    (value : Formats.Posit.Quire.Model format) :
    ℙ ℝ (Fin 2 → ℝ) :=
  Formats.Posit.Quire.Model.toProjectiveRealLine value

end ExecFloat.Posit.Quire
end FloatLib.Floats
