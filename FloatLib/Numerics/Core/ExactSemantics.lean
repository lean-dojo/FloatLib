/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Proof

/-!
# Exact semantics with representation metadata

`ExactSemantics` supplements a `NumericalSystem` with a decoder that can retain signed zero,
NaN metadata, tags, or block structure. It is used in proofs; executable arithmetic calls the
concrete family functions directly.
-/

@[expose] public section

namespace FloatLib.Numerics

universe u

/-- A richer exact interpretation that forgets coherently to a numerical system's denotation. -/
structure ExactSemantics (S : NumericalSystem) where
  /-- Representation-specific exact semantic domain. -/
  Exact : Type u
  /-- Exact interpretation of one runtime code. -/
  decode : S.Code → Exact
  /-- Forget representation-specific distinctions. -/
  forget : Exact → NumericalValue S.Scalar
  /-- Exact decoding agrees with the common numerical interpretation. -/
  forget_decode : ∀ code, forget (decode code) = S.denote code

namespace ExactSemantics

variable {S : NumericalSystem} (E : ExactSemantics S)

/-- A runtime code bundled with an erased proof of its richer exact interpretation. -/
abbrev At (value : E.Exact) :=
  { code : S.Code // E.decode code = value }

/-- Attach the exact interpretation computed from an existing runtime code. -/
@[inline] def ofCode (code : S.Code) : E.At (E.decode code) :=
  ⟨code, rfl⟩

/-- The bundled runtime code has its indexed exact interpretation. -/
@[simp, grind =] theorem decode_eq {value : E.Exact} (code : E.At value) :
    E.decode code.1 = value :=
  code.2

/-- Forget exact distinctions while retaining the same runtime code. -/
@[inline] def toAt {value : E.Exact} (code : E.At value) :
    S.At (E.forget value) :=
  ⟨code.1, by
    rw [← E.forget_decode code.1, code.2]⟩

/-- Use a system's complete denotation as its exact interpretation. -/
def ofDenote (S : NumericalSystem) : ExactSemantics S where
  Exact := NumericalValue S.Scalar
  decode := S.denote
  forget := id
  forget_decode _ := rfl

end ExactSemantics
end FloatLib.Numerics
