/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.DecimalInterchange.Projection.Runtime

/-!
# Explicit decimal rounding attributes and sticky exception flags

An arithmetic `Outcome` records the exceptions raised by one operation. An `Environment`
accumulates those exceptions until a caller clears or restores the selected flags. Because
this state is an ordinary value, exception behavior is available in pure Lean programs and proofs.
Flag operations are defined in `FloatLib.Numerics.IEEEStatus`, shared with binary formats.

The flag operations implement the default-handling state of IEEE 754-2019 §§5.7.4 and 7.
They do not change the host floating-point environment. A scoped rounding attribute changes
the direction used inside a computation while preserving the exceptions raised there.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.DecimalInterchange

/-- Rounding direction and accumulated exception flags of a decimal computation. -/
structure Environment where
  /-- The rounding direction used by computations in this environment. -/
  rounding : RoundingMode := .nearestEven
  /-- Exceptions accumulated until a caller clears or restores them. -/
  flags : Numerics.IEEEStatus := {}
  deriving DecidableEq, Repr

namespace Environment

/-- Set the selected sticky flags without changing the rounding direction. -/
def raiseFlags (environment : Environment) (group : Numerics.IEEEStatus) : Environment :=
  { environment with flags := environment.flags.raiseFlags group }

/-- Clear the selected sticky flags without changing the rounding direction. -/
def lowerFlags (environment : Environment) (group : Numerics.IEEEStatus) : Environment :=
  { environment with flags := environment.flags.lowerFlags group }

/-- Test whether any selected current flag is raised. -/
def testFlags (environment : Environment) (group : Numerics.IEEEStatus) : Bool :=
  environment.flags.testFlags group

/-- Save the current flags for a later test or restoration. -/
def saveAllFlags (environment : Environment) : Numerics.IEEEStatus := environment.flags.saveAllFlags

/-- Restore selected flags from a saved snapshot, including saved clear flags. -/
def restoreFlags (environment : Environment) (saved group : Numerics.IEEEStatus) : Environment :=
  { environment with flags := environment.flags.restoreFlags saved group }

/-- Record an operation's result and accumulate its exceptions in the current flags. -/
def accept (environment : Environment) (outcome : Outcome) : Datum × Environment :=
  (outcome.value, { environment with flags := environment.flags.union outcome.status })

/-- Evaluate one operation under the current rounding direction. -/
def run (environment : Environment) (operation : RoundingMode → Outcome) :
    Datum × Environment :=
  environment.accept (operation environment.rounding)

/-- Evaluate a computation under a scoped rounding direction.
The outer direction is restored and the computation's final flags are kept. -/
def withRounding {α : Type*} (environment : Environment) (rounding : RoundingMode)
    (computation : Environment → α × Environment) : α × Environment :=
  let result := computation { environment with rounding }
  (result.1, { result.2 with rounding := environment.rounding })

end Environment

end FloatLib.Floats.Formats.DecimalInterchange
