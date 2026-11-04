/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Order.Basic

/-!
# Intervals with arbitrary endpoint representations

An interval here is just a pair of endpoints, with no order, radix, infinity representation, or
rounding policy imposed on it. `Contains` reads finite endpoints through a partial decoder that you
pass in, and failed decoding excludes NaNs, NaRs, and any other value outside the chosen scalar
interpretation.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- An endpoint pair. Building one doesn't assert that the bounds are ordered. -/
structure Interval (α : Type*) where
  /-- Lower endpoint. -/
  lo : α
  /-- Upper endpoint. -/
  hi : α
  deriving DecidableEq, Repr

namespace Interval

variable {α β γ : Type*}

/-- A point interval preserves its endpoint representation exactly. -/
def point (x : α) : Interval α := ⟨x, x⟩

/-- Change both endpoint representations by the same function. -/
def map (f : α → β) (I : Interval α) : Interval β := ⟨f I.lo, f I.hi⟩

/-- Decode both finite endpoints, failing if either endpoint has no scalar interpretation. -/
def decode? (decode : α → Option β) (I : Interval α) : Option (Interval β) := do
  let lo ← decode I.lo
  let hi ← decode I.hi
  pure ⟨lo, hi⟩

/-- Scalar membership requires successful decoding and both endpoint inequalities. -/
def Contains [LE β] (decode : α → Option β) (I : Interval α) (x : β) : Prop :=
  ∃ lo hi, decode I.lo = some lo ∧ decode I.hi = some hi ∧ lo ≤ x ∧ x ≤ hi

/-- Keep finite ordered bounds. Special values and reversed bounds return `none`. -/
def ofBounds? [LinearOrder β] (decode : α → Option β) (lo hi : α) : Option (Interval α) :=
  match decode lo, decode hi with
  | some a, some b => if a ≤ b then some ⟨lo, hi⟩ else none
  | _, _ => none

end Interval

/--
Partial outward rounding for any endpoint carrier and ordered scalar interpretation.

Success certifies finite decoded bounds, and failure can report overflow or an unavailable
enclosure. So bounded formats don't need to represent infinities to use this interface.
-/
structure OutwardRounding (α β : Type*) [LE β] where
  /-- Finite scalar interpretation of an encoded endpoint. -/
  decode : α → Option β
  /-- Try to bracket an exact scalar by representable endpoints. -/
  enclose? : β → Option (Interval α)
  /-- Every successful result encloses the exact scalar. -/
  sound : ∀ {x I}, enclose? x = some I → I.Contains decode x

end FloatLib.Numerics
