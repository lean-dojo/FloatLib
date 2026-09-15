/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Core.Declaration

/-!
# Static format declaration regression

This compile-time regression ensures that `float_format` preserves an arbitrary code type exactly
and installs the requested denotation without a descriptor wrapper.
-/

@[expose] public section

namespace FloatLibTests.Conformance.Numerics.Declaration

open FloatLib.Numerics

float_format ExampleByte where
  Code := UInt8
  Scalar := UInt8
  denote := fun code => .finite code

/-- The declared format's persistent code is exactly the requested machine byte. -/
example : FormatCode ExampleByte = UInt8 := rfl

/-- The generated semantics is the supplied denotation. -/
example (code : UInt8) :
    denoteFormat ExampleByte code = NumericalValue.finite code := rfl

end FloatLibTests.Conformance.Numerics.Declaration
