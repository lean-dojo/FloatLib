/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.System

/-!
# Booleans as a numerical system

Boolean masks have no exceptional encodings: every runtime `Bool` denotes itself.
-/

@[expose] public section

namespace FloatLib.Numerics.Representations.Boolean

/-- Mathematical interpretation of a Boolean code. -/
def numericalSystem : NumericalSystem :=
  NumericalSystem.exact Bool

/-- Every Boolean code represents itself. -/
@[simp, grind .] theorem represents (value : Bool) :
    numericalSystem.Represents value value := by
  simp [numericalSystem]

end FloatLib.Numerics.Representations.Boolean
