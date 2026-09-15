/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

/-!
# Shared IEEE exception indicators

Binary and decimal operations signal the same five exceptions. Their numerical conditions,
including tininess detection, belong to each format; the flag record and sticky accumulation
do not depend on radix, precision, storage, or rounding direction.
-/

@[expose] public section

namespace FloatLib.Numerics

/-- The five default exception indicators of IEEE 754-2019 §7. -/
structure IEEEStatus where
  /-- An operand or operation was invalid. -/
  invalid : Bool := false
  /-- An exact infinite result was obtained from finite operands. -/
  divideByZero : Bool := false
  /-- The precision-rounded result exceeded the finite exponent range. -/
  overflow : Bool := false
  /-- A tiny result was inexact. -/
  underflow : Bool := false
  /-- The delivered result differs from the exact result. -/
  inexact : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- The five IEEE floating-point exceptions, individually addressable as flags. -/
inductive IEEEException where
  | invalid
  | divideByZero
  | overflow
  | underflow
  | inexact
  deriving DecidableEq, Repr

namespace IEEEStatus

/-- Accumulate exceptions, preserving every flag raised by either computation. -/
def union (earlier raised : IEEEStatus) : IEEEStatus where
  invalid := earlier.invalid || raised.invalid
  divideByZero := earlier.divideByZero || raised.divideByZero
  overflow := earlier.overflow || raised.overflow
  underflow := earlier.underflow || raised.underflow
  inexact := earlier.inexact || raised.inexact

/-- Read one exception flag. -/
def isSet (flags : IEEEStatus) : IEEEException → Bool
  | .invalid => flags.invalid
  | .divideByZero => flags.divideByZero
  | .overflow => flags.overflow
  | .underflow => flags.underflow
  | .inexact => flags.inexact

/-- Construct a flag group by specifying its members. -/
def ofPredicate (selected : IEEEException → Bool) : IEEEStatus :=
  { invalid := selected .invalid
    divideByZero := selected .divideByZero
    overflow := selected .overflow
    underflow := selected .underflow
    inexact := selected .inexact }

/-- A group containing exactly one exception. -/
def singleton (exception : IEEEException) : IEEEStatus :=
  ofPredicate fun candidate => decide (candidate = exception)

/-- The group of all five exceptions. -/
def allFlags : IEEEStatus := ofPredicate fun _ => true

/-- Set each flag in a group, preserving all other flags. -/
def raiseFlags (flags group : IEEEStatus) : IEEEStatus := flags.union group

/-- Clear each flag in a group, preserving all other flags. -/
def lowerFlags (flags group : IEEEStatus) : IEEEStatus :=
  ofPredicate fun exception => flags.isSet exception && !group.isSet exception

/-- Whether at least one selected flag is raised. -/
def testFlags (flags group : IEEEStatus) : Bool :=
  (flags.invalid && group.invalid) ||
  (flags.divideByZero && group.divideByZero) ||
  (flags.overflow && group.overflow) ||
  (flags.underflow && group.underflow) ||
  (flags.inexact && group.inexact)

/-- Save all flags as an immutable value. -/
def saveAllFlags (flags : IEEEStatus) : IEEEStatus := flags

/-- Test a saved snapshot without changing the current environment. -/
def testSavedFlags (saved group : IEEEStatus) : Bool := saved.testFlags group

/-- Restore the selected flags from a saved value, preserving flags outside the group. -/
def restoreFlags (flags saved group : IEEEStatus) : IEEEStatus :=
  ofPredicate fun exception =>
    if group.isSet exception then saved.isSet exception else flags.isSet exception

end IEEEStatus
end FloatLib.Numerics
