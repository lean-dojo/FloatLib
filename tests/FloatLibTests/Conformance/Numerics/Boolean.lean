/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.Boolean.Automation

/-!
# Boolean numerical-system regression checks

These examples exercise the same proof-indexed operation interface used by arithmetic formats.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Boolean

open FloatLib.Numerics.Representations.Boolean

example {x : Bool} (value : numericalSystem.AtFinite x) :
    numericalSystem.AtFinite (!x) :=
  numerics_refine (FloatLib.Numerics.Representations.Boolean.not value.1)

example {x y : Bool} (left : numericalSystem.AtFinite x)
    (right : numericalSystem.AtFinite y) :
    numericalSystem.AtFinite (x && y) :=
  numerics_refine (FloatLib.Numerics.Representations.Boolean.and left.1 right.1)

example {x y : Bool} (left : numericalSystem.AtFinite x)
    (right : numericalSystem.AtFinite y) :
    numericalSystem.AtFinite (x || y) :=
  numerics_refine (FloatLib.Numerics.Representations.Boolean.or left.1 right.1)

example {x y : Bool} (left : numericalSystem.AtFinite x)
    (right : numericalSystem.AtFinite y) :
    numericalSystem.AtFinite (Bool.xor x y) :=
  numerics_refine (FloatLib.Numerics.Representations.Boolean.xor left.1 right.1)

example : FloatLib.Numerics.Representations.Boolean.xor true false = true := by
  numerics_reduce

end FloatLibTests.Conformance.Numerics.Boolean
