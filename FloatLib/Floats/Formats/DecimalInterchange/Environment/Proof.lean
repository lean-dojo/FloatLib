/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Environment.Runtime
public import FloatLib.Numerics.IEEEStatus.Proof

/-!
# Sticky flags and scoped rounding laws

Flags raised by an operation remain set after later operations. Raising, clearing and restoring
affect exactly the requested group and keep the rounding direction. Scoped rounding restores the
caller's direction while preserving the flags produced by the inner computation.
-/

public section

namespace FloatLib.Floats.Formats.DecimalInterchange

namespace Environment

/-- Restoring every flag from a snapshot replaces the flags and keeps the rounding direction. -/
theorem restoreFlags_allFlags (environment : Environment) (saved : Numerics.IEEEStatus) :
    environment.restoreFlags saved.saveAllFlags Numerics.IEEEStatus.allFlags =
      { environment with flags := saved } := by
  simp [restoreFlags]

/-- Raising a group sets its flags and leaves every other flag unchanged. -/
theorem isSet_flags_raiseFlags (environment : Environment) (group : Numerics.IEEEStatus)
    (exception : Numerics.IEEEException) :
    (environment.raiseFlags group).flags.isSet exception =
      (environment.flags.isSet exception || group.isSet exception) :=
  Numerics.IEEEStatus.isSet_raiseFlags _ _ _

/-- Clearing a group clears exactly its flags and leaves every other flag unchanged. -/
theorem isSet_flags_lowerFlags (environment : Environment) (group : Numerics.IEEEStatus)
    (exception : Numerics.IEEEException) :
    (environment.lowerFlags group).flags.isSet exception =
      (environment.flags.isSet exception && !group.isSet exception) :=
  Numerics.IEEEStatus.isSet_lowerFlags _ _ _

/-- Restoring a group takes the saved flags inside it and keeps the current flags outside it. -/
theorem isSet_flags_restoreFlags (environment : Environment) (saved group : Numerics.IEEEStatus)
    (exception : Numerics.IEEEException) :
    (environment.restoreFlags saved group).flags.isSet exception =
      if group.isSet exception then saved.isSet exception
      else environment.flags.isSet exception :=
  Numerics.IEEEStatus.isSet_restoreFlags _ _ _ _

/-- Raising flags keeps the rounding direction. -/
@[simp] theorem rounding_raiseFlags (environment : Environment) (group : Numerics.IEEEStatus) :
    (environment.raiseFlags group).rounding = environment.rounding := rfl

/-- Clearing flags keeps the rounding direction. -/
@[simp] theorem rounding_lowerFlags (environment : Environment) (group : Numerics.IEEEStatus) :
    (environment.lowerFlags group).rounding = environment.rounding := rfl

/-- Restoring flags keeps the rounding direction. -/
@[simp] theorem rounding_restoreFlags (environment : Environment)
    (saved group : Numerics.IEEEStatus) :
    (environment.restoreFlags saved group).rounding = environment.rounding := rfl

/-- Exception accumulation never changes the operation's delivered datum. -/
@[simp] theorem accept_value (environment : Environment) (outcome : Outcome) :
    (environment.accept outcome).1 = outcome.value := rfl

/-- An operation preserves the ambient rounding direction. -/
@[simp] theorem run_rounding (environment : Environment) (operation : RoundingMode → Outcome) :
    (environment.run operation).2.rounding = environment.rounding := rfl

/-- A flag after execution is the disjunction of its previous and newly raised states. -/
theorem run_isSet (environment : Environment) (operation : RoundingMode → Outcome)
    (exception : Numerics.IEEEException) :
    (environment.run operation).2.flags.isSet exception =
      (environment.flags.isSet exception ||
        (operation environment.rounding).status.isSet exception) := by
  simp [run, accept]

/-- Two operations accumulate the union of both outcomes and the initial flags. -/
theorem accept_accept_flags (environment : Environment) (first second : Outcome) :
    ((environment.accept first).2.accept second).2.flags =
      environment.flags.union (first.status.union second.status) :=
  Numerics.IEEEStatus.union_assoc _ _ _

/-- Scoped rounding restores the caller's direction, regardless of the inner computation. -/
@[simp] theorem withRounding_rounding {α : Type*} (environment : Environment)
    (rounding : RoundingMode) (computation : Environment → α × Environment) :
    (environment.withRounding rounding computation).2.rounding = environment.rounding := rfl

/-- Scoped rounding preserves the inner computation's resulting exception flags. -/
theorem withRounding_flags {α : Type*} (environment : Environment)
    (rounding : RoundingMode) (computation : Environment → α × Environment) :
    (environment.withRounding rounding computation).2.flags =
      (computation { environment with rounding }).2.flags := rfl

end Environment

end FloatLib.Floats.Formats.DecimalInterchange
