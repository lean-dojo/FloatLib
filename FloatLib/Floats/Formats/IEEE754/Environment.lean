/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Mode
public import FloatLib.Floats.Formats.DecimalInterchange.Rounding.Runtime

/-!
# Conformance predicates and dynamic modes of IEEE 754-2019

Two groups of operations of IEEE 754-2019 concern the programming environment and no datum.

`is754version1985`, `is754version2008` and `is754version2019` (§5.7.1) say whether the
environment conforms to a version of the standard. The text of the standard is not public. The
clause number and the name `is754version2019` are from the 754 working group's list of changes
from 754-2008 (<https://grouper.ieee.org/groups/msc/ANSI_IEEE-Std-754-2019/background/>: "5.7.1
new predicate operation is754version2019 is required"). FloatLib answers `false` to all three:
it is a library of operations with proofs and makes no claim that a programming environment
built on it conforms to a version of the standard as a whole.

The dynamic modes of §9.3 are the rounding directions of binary and of decimal arithmetic.
FloatLib's operations take the direction as an argument, so the modes are a value, `Modes`, that
a computation carries: `getBinaryRoundingDirection`, `setBinaryRoundingDirection`,
`getDecimalRoundingDirection`, `setDecimalRoundingDirection`, `saveModes`, `restoreModes` and
`defaultModes`. The names are those of ISO/IEC 9899:2024 (C23, working draft N3220) Annex F,
Table F.2 and paragraph F.3 (18), which bind them to `fegetround`, `fesetround`,
`fe_dec_getround`, `fe_dec_setround`, `fegetmode` and `fesetmode` (7.6.5.1 to 7.6.5.6). The
default direction of both radices is roundTiesToEven. The decimal `Environment` carries the
decimal direction together with the status flags.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.IEEE754

/-- The versions of IEEE 754 that the conformance predicates of IEEE 754-2019 §5.7.1 name. -/
inductive Version where
  /-- IEEE 754-1985, as named by IEEE 754-2019 §5.7.1. -/
  | v1985
  /-- IEEE 754-2008, as named by IEEE 754-2019 §5.7.1. -/
  | v2008
  /-- IEEE 754-2019, as named by IEEE 754-2019 §5.7.1. -/
  | v2019
  deriving Repr

/--
Whether the programming environment conforms to a version named by IEEE 754-2019 §5.7.1. FloatLib
makes no such
claim for any version, so the answer is `false`.
-/
def conformsTo (_ : Version) : Bool := false

/--
IEEE 754-2019 §5.7.1 `is754version1985`: whether the programming environment conforms to
IEEE 754-1985, `conformsTo .v1985`.
-/
def is754version1985 : Bool := conformsTo .v1985

/--
IEEE 754-2019 §5.7.1 `is754version2008`: whether the programming environment conforms to
IEEE 754-2008, `conformsTo .v2008`.
-/
def is754version2008 : Bool := conformsTo .v2008

/--
IEEE 754-2019 §5.7.1 `is754version2019`: whether the programming environment conforms to
IEEE 754-2019, `conformsTo .v2019`.
-/
def is754version2019 : Bool := conformsTo .v2019

/--
The dynamic modes of IEEE 754-2019 §9.3: the rounding direction of binary arithmetic and the
rounding direction of decimal arithmetic, each roundTiesToEven by default.
-/
structure Modes where
  /-- The rounding direction of operations on binary formats. -/
  binaryRounding : BinaryInterchange.Model.IEEERoundingMode := .nearest
  /-- The rounding direction of operations on decimal formats. -/
  decimalRounding : DecimalInterchange.RoundingMode := .nearest
  deriving DecidableEq

namespace Modes

/-- IEEE 754-2019 §9.3 `getBinaryRoundingDirection` (C23 `fegetround`, N3220 7.6.5.2). -/
def getBinaryRoundingDirection (modes : Modes) : BinaryInterchange.Model.IEEERoundingMode :=
  modes.binaryRounding

/--
IEEE 754-2019 §9.3 `setBinaryRoundingDirection` (C23 `fesetround`, N3220 7.6.5.5): the modes
with the binary direction replaced. The decimal direction is kept.
-/
def setBinaryRoundingDirection (modes : Modes)
    (direction : BinaryInterchange.Model.IEEERoundingMode) : Modes :=
  { modes with binaryRounding := direction }

/-- IEEE 754-2019 §9.3 `getDecimalRoundingDirection` (C23 `fe_dec_getround`, N3220 7.6.5.3). -/
def getDecimalRoundingDirection (modes : Modes) : DecimalInterchange.RoundingMode :=
  modes.decimalRounding

/--
IEEE 754-2019 §9.3 `setDecimalRoundingDirection` (C23 `fe_dec_setround`, N3220 7.6.5.6): the
modes with the decimal direction replaced. The binary direction is kept.
-/
def setDecimalRoundingDirection (modes : Modes)
    (direction : DecimalInterchange.RoundingMode) : Modes :=
  { modes with decimalRounding := direction }

/-- IEEE 754-2019 §9.3 `saveModes` (C23 `fegetmode`, N3220 7.6.5.1): all dynamic modes. -/
def saveModes (modes : Modes) : Modes := modes

/--
IEEE 754-2019 §9.3 `restoreModes` (C23 `fesetmode`, N3220 7.6.5.4): the saved modes replace
the current ones.
-/
def restoreModes (_current saved : Modes) : Modes := saved

/--
IEEE 754-2019 §9.3 `defaultModes` (C23 `fesetmode(FE_DFL_MODE)`, N3220 7.6.5.4): both
directions roundTiesToEven.
-/
def defaultModes : Modes := {}

/-- A binary direction that was set is the one read. -/
@[simp] theorem getBinaryRoundingDirection_setBinaryRoundingDirection (modes : Modes)
    (direction : BinaryInterchange.Model.IEEERoundingMode) :
    (modes.setBinaryRoundingDirection direction).getBinaryRoundingDirection = direction :=
  rfl

/-- A decimal direction that was set is the one read. -/
@[simp] theorem getDecimalRoundingDirection_setDecimalRoundingDirection (modes : Modes)
    (direction : DecimalInterchange.RoundingMode) :
    (modes.setDecimalRoundingDirection direction).getDecimalRoundingDirection = direction :=
  rfl

/-- Setting the binary direction leaves the decimal direction as it was. -/
@[simp] theorem getDecimalRoundingDirection_setBinaryRoundingDirection (modes : Modes)
    (direction : BinaryInterchange.Model.IEEERoundingMode) :
    (modes.setBinaryRoundingDirection direction).getDecimalRoundingDirection =
      modes.getDecimalRoundingDirection :=
  rfl

/-- Setting the decimal direction leaves the binary direction as it was. -/
@[simp] theorem getBinaryRoundingDirection_setDecimalRoundingDirection (modes : Modes)
    (direction : DecimalInterchange.RoundingMode) :
    (modes.setDecimalRoundingDirection direction).getBinaryRoundingDirection =
      modes.getBinaryRoundingDirection :=
  rfl

/-- Restoring saved modes brings back both directions, whatever was set in between. -/
@[simp] theorem restoreModes_saveModes (current modes : Modes) :
    current.restoreModes modes.saveModes = modes :=
  rfl

/-- The default binary direction is roundTiesToEven. -/
@[simp] theorem getBinaryRoundingDirection_defaultModes :
    defaultModes.getBinaryRoundingDirection = .nearest :=
  rfl

/-- The default decimal direction is roundTiesToEven. -/
@[simp] theorem getDecimalRoundingDirection_defaultModes :
    defaultModes.getDecimalRoundingDirection = .nearest :=
  rfl

end Modes
end FloatLib.Floats.Formats.IEEE754
