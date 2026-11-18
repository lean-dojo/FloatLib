/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Numerics.Executable.Carrier
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Core

/-!
# Configured bounded fixed-point identity

The public `ExecFloat.BoundedFixedPoint` type comes from the encoded bounded fixed-point family. At
runtime a value is a `FixedInt width` and nothing more. The overflow policy isn't stored anywhere,
because each operation names its own.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat
namespace BoundedFixedPoint

/-- Type-level identity of a bounded fixed-point grid. -/
inductive Family (radix : Radix) (fractionalDigits width : Nat) where
  /-- The only value: the family names a format in types and carries no data. -/
  | format

instance (radix : Radix) (fractionalDigits width : Nat) :
    EncodedFormat (Family radix fractionalDigits width) where
  Code := Formats.FixedPoint.Bounded.Code radix fractionalDigits width
  Scalar := ℚ

instance (radix : Radix) (fractionalDigits width : Nat) :
    FormatSemantics (Family radix fractionalDigits width) :=
  FormatSemantics.ofFinite _ fun code ↦
    Formats.FixedPoint.Bounded.toRat radix fractionalDigits code

end BoundedFixedPoint

/-- Fixed-width radix-parametric fixed point, where every operation names its overflow policy. -/
abbrev BoundedFixedPoint (radix : Radix) (fractionalDigits width : Nat) :=
  FloatLib.Floats.ExecFloat
    (BoundedFixedPoint.Family radix fractionalDigits width)

end ExecFloat

end FloatLib.Floats
