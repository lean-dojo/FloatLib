/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.FixedPoint.Bounded.Automation
public meta import FloatLib.Floats.Formats.FixedPoint.Bounded.Core

/-!
# Bounded fixed-point refinement checks

The symbolic examples exercise wrapping and saturating addition through `numerics_refine`, and
checked addition through its proof-indexed interface with an explicit coefficient-range hypothesis.
-/

@[expose] public section

open FloatLib.Numerics
open FloatLib.Numerics.Representations

namespace FloatLibTests.Conformance.Numerics.FixedPointChecks

open FloatLib.Floats.Formats.FixedPoint.Bounded

example {left right : ℚ}
    (x : AtFinite binaryRadix 4 8 left)
    (y : AtFinite binaryRadix 4 8 right) :
    AtFinite binaryRadix 4 8 (wrapAddValue binaryRadix 4 8 left right) :=
  numerics_refine (wrapAdd x.1 y.1)

example {left right : ℚ}
    (hresult :
      FixedInt.InRange 8
        (coefficientOf binaryRadix 4 left + coefficientOf binaryRadix 4 right))
    (x : AtFinite binaryRadix 4 8 left)
    (y : AtFinite binaryRadix 4 8 right) :
    (numericalSystem binaryRadix 4 8).At (.finite (left + right)) :=
  Operation.Checked2On.applyAt (checkedAdd_refines (by decide)) hresult x y

example {left right : ℚ}
    (x : AtFinite binaryRadix 4 8 left)
    (y : AtFinite binaryRadix 4 8 right) :
    AtFinite binaryRadix 4 8
      (saturatingAddValue binaryRadix 4 8 left right) :=
  numerics_refine (saturatingAdd x.1 y.1)

end FloatLibTests.Conformance.Numerics.FixedPointChecks
