/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Semantics.Exact.Proof

/-!
# Ordinary posit values as exact rationals

The NaR encoding has no rational denotation. Excluding it gives a subtype on which exact rational
decoding is total.

No alternate encoding is introduced: `Model.Ordinary format` is a proof-carrying view of the same
encoded word. The full posit order still belongs to `Model format`; the rational coordinate here
is available for every value of the subtype.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Model

variable {format : Format}

/-- A posit word accompanied by proof that it is not the unique NaR encoding. -/
abbrev Ordinary (format : Format) :=
  { value : Model format // value.isNaR = false }

namespace Ordinary

/-- The optional exact semantics of an ordinary posit is inhabited. -/
theorem toRat_isSome (value : Ordinary format) :
    value.1.toRat?.isSome := by
  rw [Option.isSome_iff_ne_none]
  intro equality
  have hnar := (toRat?_eq_none_iff value.1).mp equality
  rw [value.2] at hnar
  contradiction

/--
Total exact rational semantics of an ordinary posit.

The proof argument to `Option.get` is erased at runtime. It records that the only absent rational
meaning belongs to NaR, which the subtype excludes.
-/
@[inline] def toRat (value : Ordinary format) : Rat :=
  value.1.toRat?.get (toRat_isSome value)

/-- Forgetting the subtype and decoding recovers exactly the total rational coordinate. -/
@[simp] theorem model_toRat?_eq_some (value : Ordinary format) :
    value.1.toRat? = some value.toRat := by
  exact (Option.some_get (toRat_isSome value)).symm

/-- Ordinary zero, retaining proof that the zero word is not NaR. -/
def zero (format : Format) : Ordinary format :=
  ⟨Model.zero format, by simp⟩

/-- The posit zero denotes the rational zero. -/
@[simp] theorem toRat_zero (format : Format) :
    (zero format).toRat = 0 := by
  apply Option.some.inj
  rw [← model_toRat?_eq_some]
  exact Model.toRat?_zero format

end Ordinary

end FloatLib.Floats.Formats.Posit.Model
