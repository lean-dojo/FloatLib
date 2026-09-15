/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Carrier
public import FloatLib.Floats.Formats.Logarithmic.Exact.Proof

/-!
# Configured exact logarithmic identity

The encoded logarithmic family supplies the public `ExecFloat.Logarithmic` type. The
representation contains only zero or a sign with an unbounded integer exponent; it does not
impose a bit layout.
-/

@[expose] public section

namespace FloatLib.Floats

open FloatLib.Numerics

namespace ExecFloat
namespace Logarithmic

/-- Type-level identity of an exact logarithmic format at one radix. -/
inductive Family (radix : Radix) where
  | format

instance (radix : Radix) : EncodedFormat (Family radix) where
  Code := Formats.Logarithmic.Code radix
  Scalar := ℝ

noncomputable instance (radix : Radix) : FormatSemantics (Family radix) :=
  FormatSemantics.ofFinite _ fun code ↦ code.toReal

end Logarithmic

/-- Exact zero and signed integral powers of `radix`, using the common `ExecFloat` carrier. -/
abbrev Logarithmic (radix : Radix) :=
  FloatLib.Floats.ExecFloat (Logarithmic.Family radix)

end ExecFloat

end FloatLib.Floats
