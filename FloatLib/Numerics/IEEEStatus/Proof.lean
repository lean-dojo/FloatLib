/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.IEEEStatus
public import Mathlib.Data.Bool.Basic
public import Mathlib.Tactic.Ext

/-!
# Laws for shared IEEE exception flags

These results quantify over every flag state and selected group. They are independent
of number format, numerical value, rounding direction, and runtime storage.
-/

public section

namespace FloatLib.Numerics.IEEEStatus

/-- Two flag states are equal when every exception has the same state. -/
@[ext] theorem ext_isSet {left right : IEEEStatus}
    (h : ∀ exception, left.isSet exception = right.isSet exception) : left = right := by
  cases left
  cases right
  have hi := h .invalid
  have hd := h .divideByZero
  have ho := h .overflow
  have hu := h .underflow
  have he := h .inexact
  simp only [isSet] at hi hd ho hu he
  cases hi
  cases hd
  cases ho
  cases hu
  cases he
  rfl

/-- Constructing a flag group preserves its membership predicate. -/
@[simp] theorem isSet_ofPredicate (selected : IEEEException → Bool) (exception : IEEEException) :
    (ofPredicate selected).isSet exception = selected exception := by
  cases exception <;> rfl

/-- The default flag state has no exceptions raised. -/
@[simp] theorem isSet_empty (exception : IEEEException) :
    isSet ({} : IEEEStatus) exception = false := by
  cases exception <;> rfl

/-- A singleton selects precisely its named exception. -/
@[simp] theorem isSet_singleton (selected exception : IEEEException) :
    (singleton selected).isSet exception = decide (exception = selected) := by
  simp [singleton]

/-- The all-flags group selects every exception. -/
@[simp] theorem isSet_allFlags (exception : IEEEException) :
    allFlags.isSet exception = true := by
  simp [allFlags]

/-- A flag in a union is raised exactly when either input raises it. -/
@[simp] theorem isSet_union (left right : IEEEStatus) (exception : IEEEException) :
    (left.union right).isSet exception =
      (left.isSet exception || right.isSet exception) := by
  cases exception <;> rfl

/-- Accumulating exceptions is associative, so operation grouping does not affect flags. -/
theorem union_assoc (first second third : IEEEStatus) :
    (first.union second).union third = first.union (second.union third) := by
  ext exception
  simp [Bool.or_assoc]

/-- Flag accumulation is independent of the order in which the same exceptions are raised. -/
theorem union_comm (left right : IEEEStatus) : left.union right = right.union left := by
  ext exception
  simp [Bool.or_comm]

/-- Raising an already raised flag changes nothing. -/
@[simp] theorem union_self (flags : IEEEStatus) : flags.union flags = flags := by
  ext exception
  simp

/-- An operation with no exceptions preserves the accumulated flags. -/
@[simp] theorem union_empty (flags : IEEEStatus) : flags.union {} = flags := by
  ext exception
  simp

/-- Existing flags remain raised when another operation contributes exceptions. -/
theorem isSet_union_of_left (left right : IEEEStatus) (exception : IEEEException)
    (h : left.isSet exception = true) : (left.union right).isSet exception = true := by
  simp [h]

/-- A newly raised exception appears in the accumulated state. -/
theorem isSet_union_of_right (left right : IEEEStatus) (exception : IEEEException)
    (h : right.isSet exception = true) : (left.union right).isSet exception = true := by
  simp [h]

/-- Raising a group affects exactly its members. -/
theorem isSet_raiseFlags (flags group : IEEEStatus) (exception : IEEEException) :
    (flags.raiseFlags group).isSet exception =
      (flags.isSet exception || group.isSet exception) := by
  simp [raiseFlags]

/-- Clearing a group removes precisely the selected flags. -/
theorem isSet_lowerFlags (flags group : IEEEStatus) (exception : IEEEException) :
    (flags.lowerFlags group).isSet exception =
      (flags.isSet exception && !group.isSet exception) := by
  simp [lowerFlags]

/-- Testing a group succeeds exactly when it contains a raised exception. -/
theorem testFlags_iff (flags group : IEEEStatus) :
    flags.testFlags group = true ↔
      ∃ exception, flags.isSet exception = true ∧ group.isSet exception = true := by
  simp only [testFlags, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  constructor
  · rintro (h | h | h | h | h)
    · exact ⟨.invalid, h⟩
    · exact ⟨.divideByZero, h⟩
    · exact ⟨.overflow, h⟩
    · exact ⟨.underflow, h⟩
    · exact ⟨.inexact, h⟩
  · rintro ⟨exception, h⟩
    cases exception <;> simp_all [isSet]

/-- A saved-state test has the same existential meaning as a current-state test. -/
theorem testSavedFlags_iff (saved group : IEEEStatus) :
    saved.testSavedFlags group = true ↔
      ∃ exception, saved.isSet exception = true ∧ group.isSet exception = true :=
  testFlags_iff saved group

/-- Restoration chooses saved state inside the group and current state outside it. -/
theorem isSet_restoreFlags (flags saved group : IEEEStatus) (exception : IEEEException) :
    (flags.restoreFlags saved group).isSet exception =
      if group.isSet exception then saved.isSet exception else flags.isSet exception := by
  simp [restoreFlags]

/-- Clearing all exceptions resets the state. -/
@[simp] theorem lowerFlags_allFlags (flags : IEEEStatus) :
    flags.lowerFlags allFlags = {} := by
  ext exception
  simp [isSet_lowerFlags]

/-- Restoring the complete saved group recovers the snapshot exactly. -/
@[simp] theorem restoreFlags_allFlags (flags saved : IEEEStatus) :
    flags.restoreFlags saved.saveAllFlags allFlags = saved := by
  ext exception
  simp [isSet_restoreFlags, saveAllFlags]

/-- An empty selection never reports an exception. -/
@[simp] theorem testFlags_empty (flags : IEEEStatus) : flags.testFlags {} = false := by
  simp [testFlags]

/-- An empty selection leaves all flags unchanged when clearing. -/
@[simp] theorem lowerFlags_empty (flags : IEEEStatus) : flags.lowerFlags {} = flags := by
  ext exception
  simp [isSet_lowerFlags]

/-- An empty selection leaves all flags unchanged when restoring. -/
@[simp] theorem restoreFlags_empty (flags saved : IEEEStatus) :
    flags.restoreFlags saved {} = flags := by
  ext exception
  simp [isSet_restoreFlags]

end FloatLib.Numerics.IEEEStatus
