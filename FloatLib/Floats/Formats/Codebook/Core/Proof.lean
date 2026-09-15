/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Codebook.Core.Runtime
public import FloatLib.Numerics.Core.Proof

/-!
# Proof-indexed views of exact finite codebooks

The views in this module attach erased denotation proofs to the same exact-width runtime bit
vector. They introduce no additional executable representation.
-/

@[expose] public section

open FloatLib.Numerics

namespace FloatLib.Floats.Formats.Codebook

universe u

variable {width : Nat} {α : Type u}

/-- A codebook word bundled with an erased proof of its complete denotation. -/
abbrev At (book : Codebook width α) (value : NumericalValue α) :=
  book.numericalSystem.At value

/-- A codebook word bundled with an erased proof of its finite denotation. -/
abbrev AtFinite (book : Codebook width α) (value : α) :=
  book.numericalSystem.AtFinite value

/-- The numerical-system wrapper preserves the codebook's denotation definitionally. -/
theorem numericalSystem_denote (book : Codebook width α) (code : Code book) :
    book.numericalSystem.denote code = book.denote code :=
  rfl

end FloatLib.Floats.Formats.Codebook
