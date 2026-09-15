/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
module

public import FloatLib.Numerics.Representations.FixedInt.Core
public import Mathlib.Algebra.Field.Rat

/-!
# Integer destination ranges

A range check follows exact rational-to-integer rounding. The caller supplies
the integer rounder and the policy for failure, allowing IEEE invalid results
and Posit integer sentinels to share the same numerical range calculation.
Signed and unsigned words are instances of an inclusive integer interval.
-/

@[expose] public section

namespace FloatLib.Numerics

open Representations

/-- An inclusive integer interval. Empty intervals are permitted and reject every result. -/
structure IntegerRange where
  /-- Inclusive lower endpoint of the accepted integer interval. -/
  lower : Int
  /-- Inclusive upper endpoint; an endpoint below `lower` gives an empty interval. -/
  upper : Int
  deriving DecidableEq, Repr

/-- Membership in the inclusive destination interval. -/
def IntegerRange.Contains (range : IntegerRange) (value : Int) : Prop :=
  range.lower ≤ value ∧ value ≤ range.upper

instance (range : IntegerRange) (value : Int) : Decidable (range.Contains value) :=
  inferInstanceAs (Decidable (range.lower ≤ value ∧ value ≤ range.upper))

/-- Round first, then test the resulting integer against the destination interval. -/
def IntegerRange.round? (range : IntegerRange) (round : ℚ → Int) (value : ℚ) : Option Int :=
  let rounded := round value
  if range.Contains rounded then some rounded else none

/-- Signedness and width specify the ordinary numerical range of a word.
Reserved bit patterns are a separate format-specific conversion policy. -/
inductive IntegerFormat where
  /-- Two's-complement numerical range, with width zero containing only zero. -/
  | signed (width : Nat)
  /-- Unsigned numerical range from zero through `2 ^ width - 1`. -/
  | unsigned (width : Nat)
  deriving DecidableEq, Repr

/-- Smallest integer accepted by the word format. -/
def IntegerFormat.minValue : IntegerFormat → Int
  | .signed width => FixedInt.minValue width
  | .unsigned _ => 0

/-- Largest integer accepted by the word format. -/
def IntegerFormat.maxValue : IntegerFormat → Int
  | .signed width => FixedInt.maxValue width
  | .unsigned width => (2 : Int) ^ width - 1

/-- Inclusive numerical range; width zero denotes only zero for either signedness. -/
def IntegerFormat.range (destination : IntegerFormat) : IntegerRange :=
  ⟨destination.minValue, destination.maxValue⟩

/-- Numerical representability, independently of any reserved bit pattern. -/
abbrev IntegerFormat.InRange (destination : IntegerFormat) (value : Int) : Prop :=
  destination.range.Contains value

end FloatLib.Numerics
