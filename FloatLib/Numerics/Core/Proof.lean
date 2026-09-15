/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System

/-!
# Proof-indexed views of numerical systems

Every `NumericalSystem` has one runtime carrier, `S.Code`. The abbreviations in this module attach
an erased proof of what a stored code denotes; they do not introduce another representation.

`S.At value` tracks the complete `NumericalValue`, including infinity and exceptional encodings.
`S.AtFinite x` is the ordinary finite specialization.
-/

@[expose] public section

namespace FloatLib.Numerics
namespace NumericalSystem

/-- A runtime code bundled with an erased proof of its complete denotation. -/
abbrev At (S : NumericalSystem) (value : NumericalValue S.Scalar) :=
  { code : S.Code // S.denote code = value }

/-- A runtime code bundled with an erased proof of its ordinary finite value. -/
abbrev AtFinite (S : NumericalSystem) (value : S.Scalar) :=
  S.At (.finite value)

namespace At

/-- Attach the denotation computed by a numerical system to an existing runtime code. -/
@[inline] def ofCode (S : NumericalSystem) (code : S.Code) : S.At (S.denote code) :=
  ⟨code, rfl⟩

/-- The bundled runtime code has its indexed complete denotation. -/
@[simp, grind =] theorem denote {S : NumericalSystem} {value : NumericalValue S.Scalar}
    (code : S.At value) :
    S.denote code.1 = value :=
  code.2

end At

namespace AtFinite

/-- Attach an existing finite representation proof to its runtime code. -/
@[inline] def ofRepresents {S : NumericalSystem} {value : S.Scalar}
    (code : S.Code) (hcode : S.Represents code value) : S.AtFinite value :=
  ⟨code, hcode⟩

/-- The bundled runtime code represents its indexed finite value. -/
@[simp, grind .] theorem represents {S : NumericalSystem} {value : S.Scalar}
    (code : S.AtFinite value) :
    S.Represents code.1 value :=
  code.2

end AtFinite
end NumericalSystem
end FloatLib.Numerics
