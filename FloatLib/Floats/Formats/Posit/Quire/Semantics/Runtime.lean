/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.Posit.Quire.Model.Core

/-!
# Executable exact semantics of a posit quire

Every ordinary quire word denotes an exact rational fixed-point value. The reserved quire NaR word
denotes `ExceptionalValue.notAReal` and has no rational or dyadic coordinate.

The definitions in this module are the execution boundary used by quire arithmetic and configured
wrappers. Correctness theorems, real embeddings, and projective views live in separate modules.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.Posit.Quire.Model

open FloatLib.Numerics

variable {format : Format}

/-- Exact rational value represented by an ordinary quire, or `none` exactly for quire NaR. -/
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

This is the execution bridge used by `qToP`: the coefficient and fixed scale pass directly to the
certified posit dyadic rounder without constructing a rational.
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
