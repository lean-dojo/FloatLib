/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Representations.FixedInt.Automation
public meta import FloatLib.Numerics.Representations.FixedInt.Core

/-!
# Fixed-width signed-integer refinement checks

The symbolic examples exercise wrapping and saturating addition through `numerics_refine`, and
checked addition through its proof-indexed interface with an explicit range hypothesis.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.FixedInt

open FloatLib.Numerics
open FloatLib.Numerics.Representations.FixedInt

example {left right : Int}
    (x : AtFinite 8 left) (y : AtFinite 8 right) :
    AtFinite 8 ((left + right).bmod 256) :=
  numerics_refine (wrapAdd x.1 y.1)

example {left right : Int}
    (hresult : InRange 8 (left + right))
    (x : AtFinite 8 left) (y : AtFinite 8 right) :
    (numericalSystem 8).At (.finite (left + right)) :=
  Operation.Checked2On.applyAt (checkedAdd_refines (by decide)) hresult x y

example {left right : Int}
    (x : AtFinite 8 left) (y : AtFinite 8 right) :
    AtFinite 8 (clamp 8 (left + right)) :=
  numerics_refine (saturatingAdd x.1 y.1)

end FloatLibTests.Conformance.Numerics.FixedInt
