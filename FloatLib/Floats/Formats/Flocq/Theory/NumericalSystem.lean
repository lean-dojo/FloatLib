/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Flocq.Theory.Core
public import FloatLib.Numerics.Core.Proof

/-!
# Radix-parametric floats as numerical systems

For any radix `β ≥ 2`, a `FloatRep β` becomes a numerical system here, with denotation
`m * β^e`. The carrier is a mantissa and an exponent and nothing else, and no bit layout
constrains either.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Flocq.FloatRep

open FloatLib.Numerics

/-- Real semantics of an integer-mantissa, integer-exponent float at arbitrary radix. -/
noncomputable def numericalSystem (β : Numerics.Radix) : NumericalSystem where
  Code := FloatRep β
  Scalar := ℝ
  denote x := .finite (toReal x)

/-- An integer-mantissa float with an erased proof of its complete real denotation. -/
abbrev At (β : Numerics.Radix) (value : NumericalValue ℝ) :=
  (numericalSystem β).At value

/-- An integer-mantissa float with an erased proof of its finite real value. -/
abbrev AtFinite (β : Numerics.Radix) (value : ℝ) :=
  (numericalSystem β).AtFinite value

/-- Representation in the generic numerical-system interface is equality of real denotations. -/
@[simp] theorem numericalSystem_represents_iff {β : Numerics.Radix} (x : FloatRep β) (r : ℝ) :
    (numericalSystem β).Represents x r ↔ toReal x = r := by
  simp [NumericalSystem.Represents, numericalSystem]

end FloatLib.Floats.Formats.Flocq.FloatRep
