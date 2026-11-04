/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Model.Core

/-!
# Executable exact semantics of a posit quire

Every ordinary quire word denotes an exact rational fixed-point value, while the reserved quire NaR
word denotes `ExceptionalValue.notAReal` and has no rational or dyadic coordinate.

Quire arithmetic and the configured wrappers execute against these definitions, while correctness
theorems, real embeddings, and projective views come from other modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

/-- Exact rational value of an ordinary quire, with `none` kept for quire NaR alone. -/
@[inline] def toRat? (value : Model format) : Option Rat :=
  if value.isNaR then
    none
  else
    some
      (Rat.ofInt value.coefficient *
        (2 : Rat) ^ scaleExponent format)

/-- Complete exact semantics, retaining quire NaR as an exceptional numerical observation. -/
@[inline] def decode (value : Model format) : NumericalValue Rat :=
  match value.toRat? with
  | some rational => .finite rational
  | none => .exceptional .notAReal

/--
Exact shared-dyadic view of an ordinary quire.

`qToP` executes through this view. The coefficient and fixed scale go to the certified posit
dyadic rounder as they are, and no rational is ever built.
-/
@[inline] def toDyadic?
    (value : Model format) : Option FloatLib.Numerics.Dyadic :=
  if value.isNaR then
    none
  else
    some
      (FloatLib.Numerics.Dyadic.ofScaledInt
        value.coefficient (scaleExponent format))

end FloatLib.Floats.Formats.Posit.Quire.Model
