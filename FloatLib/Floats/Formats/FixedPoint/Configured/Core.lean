/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.FixedPoint.Exact.Runtime

/-!
# Configured exact fixed-point identity

This module defines the public `ExecFloat.FixedPoint` type from the encoded exact fixed-point
family, and nothing else. The executable operations, refinement proofs, planner metadata, and
dispatch instances all live in modules that import it.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat
namespace FixedPoint

/-- Type-level identity of an exact fixed-point grid. -/
inductive Family (radix : Radix) (fractionalDigits : Nat) where
  | format

instance (radix : Radix) (fractionalDigits : Nat) :
    EncodedFormat (Family radix fractionalDigits) where
  Code := Formats.FixedPoint.Code radix fractionalDigits
  Scalar := ℚ

instance (radix : Radix) (fractionalDigits : Nat) :
    FormatSemantics (Family radix fractionalDigits) :=
  FormatSemantics.ofFinite _ fun code ↦ code.toRat

end FixedPoint

/-- Exact radix-parametric fixed point on the common executable carrier. -/
abbrev FixedPoint (radix : Radix) (fractionalDigits : Nat) :=
  FloatLib.Floats.ExecFloat (FixedPoint.Family radix fractionalDigits)

end ExecFloat

end FloatLib.Floats
