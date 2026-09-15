/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.FixedPoint.Bounded.Core

/-!
# Configured bounded fixed-point identity

The encoded bounded fixed-point family supplies the public `ExecFloat.BoundedFixedPoint` type.
Its runtime carrier is exactly `FixedInt width`; overflow policy belongs to explicitly named
operations.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat
namespace BoundedFixedPoint

/-- Type-level identity of a bounded fixed-point grid. -/
inductive Family (radix : Radix) (fractionalDigits width : Nat) where
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

/-- Fixed-width radix-parametric fixed point with explicit overflow-policy operations. -/
abbrev BoundedFixedPoint (radix : Radix) (fractionalDigits width : Nat) :=
  FloatLib.Floats.ExecFloat
    (BoundedFixedPoint.Family radix fractionalDigits width)

end ExecFloat

end FloatLib.Floats
