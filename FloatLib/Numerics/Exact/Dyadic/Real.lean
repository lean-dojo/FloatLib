/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Exact.Dyadic.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Real values of exact dyadics

A dyadic denotes its signed integer significand times an integral power of two. Its rational
and real interpretations agree, so exact arithmetic identities can be transported by casting.
These definitions do not depend on any floating-point format.
-/

@[expose] public section

namespace FloatLib.Numerics.Dyadic

/-- Interpret an exact dyadic `(-1)^sign * significand * 2^exponent` as a real. -/
noncomputable def toReal (d : Dyadic) : ℝ :=
  (d.signedSignificand : ℝ) * (2 : ℝ) ^ d.exponent

/-- The exact rational and real interpretations of a dyadic agree. -/
@[simp, norm_cast] theorem cast_toRat (d : Dyadic) :
    (d.toRat : ℝ) = d.toReal := by
  simp [toRat, toReal, Rat.cast_zpow]

/-- Casting the signed significand separates its sign from its natural magnitude. -/
@[simp] theorem cast_signedSignificand (d : Dyadic) :
    (d.signedSignificand : ℝ) =
      (if d.negative then (-1 : ℝ) else 1) * (d.significand : ℝ) := by
  cases hnegative : d.negative <;>
    simp [signedSignificand, hnegative]

/-- A nonnegative dyadic constructor has the expected unsigned real denotation. -/
@[simp] theorem toReal_mk_false (significand : Nat) (exponent : Int) :
    (Dyadic.mk false significand exponent).toReal =
      (significand : ℝ) * (2 : ℝ) ^ exponent := by
  simp [toReal]

end FloatLib.Numerics.Dyadic
