/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import Mathlib.Data.Ordering.Basic
public import FloatLib.Numerics.IEEEStatus

/-!
# IEEE comparison predicates

The truth tables in IEEE 754-2019 Tables 5.1–5.2 depend only on four possible relations:
less, equal, greater, and unordered. This module shares those tables between numerical
formats. Operand decoding and the invalid-operation flag belong to each format's API.
-/

@[expose] public section

namespace FloatLib.Numerics.IEEEComparison

/-- A predicate's truth value and the exceptions raised while evaluating it. -/
structure Result where
  /-- The Boolean answer, including the predicate's unordered case. -/
  value : Bool
  /-- Exceptions raised by this comparison. -/
  status : IEEEStatus := {}
  deriving DecidableEq, Repr

/-- Truth sets named by the IEEE quiet and signaling comparison operations. -/
inductive Predicate where
  | equal | notEqual | greater | greaterEqual | less | lessEqual
  | unordered | ordered | lessUnordered | notGreater | notLess | greaterUnordered
  deriving DecidableEq, Repr

/-- Whether a predicate accepts a relation; `none` denotes unordered operands. -/
def Predicate.accepts : Predicate → Option Ordering → Bool
  | .equal, r => r == some .eq
  | .notEqual, r => r != some .eq
  | .greater, r => r == some .gt
  | .greaterEqual, r => r == some .gt || r == some .eq
  | .less, r => r == some .lt
  | .lessEqual, r => r == some .lt || r == some .eq
  | .unordered, r => r == none
  | .ordered, r => r != none
  | .lessUnordered, r => r == none || r == some .lt
  | .notGreater, r => r != some .gt
  | .notLess, r => r != some .lt
  | .greaterUnordered, r => r == none || r == some .gt

/-- Inequality is the complement of equality, including unordered inputs. -/
theorem accepts_notEqual (relation : Option Ordering) :
    Predicate.notEqual.accepts relation = !Predicate.equal.accepts relation := rfl

/-- Ordered and unordered are complementary predicates. -/
theorem accepts_ordered (relation : Option Ordering) :
    Predicate.ordered.accepts relation = !Predicate.unordered.accepts relation := rfl

/-- Not-greater includes unordered inputs and is the complement of greater-than. -/
theorem accepts_notGreater (relation : Option Ordering) :
    Predicate.notGreater.accepts relation = !Predicate.greater.accepts relation := rfl

/-- Not-less includes unordered inputs and is the complement of less-than. -/
theorem accepts_notLess (relation : Option Ordering) :
    Predicate.notLess.accepts relation = !Predicate.less.accepts relation := rfl

/-- Less-or-unordered complements greater-or-equal across all four relations. -/
theorem accepts_lessUnordered (relation : Option Ordering) :
    Predicate.lessUnordered.accepts relation = !Predicate.greaterEqual.accepts relation := by
  cases relation with
  | none => rfl
  | some relation => cases relation <;> rfl

/-- Greater-or-unordered complements less-or-equal across all four relations. -/
theorem accepts_greaterUnordered (relation : Option Ordering) :
    Predicate.greaterUnordered.accepts relation = !Predicate.lessEqual.accepts relation := by
  cases relation with
  | none => rfl
  | some relation => cases relation <;> rfl

end FloatLib.Numerics.IEEEComparison
