/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Descriptor.Carrier
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Division
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.Dyadic
public import FloatLib.Floats.Formats.BinaryInterchange.Spec.SquareRoot

/-!
# Reference operations for binary descriptors

These definitions lift the binary model specifications through the representation-preserving
descriptor codec. Executable backend implementations and their refinement proofs live separately
in `Descriptor.Backends`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange

open FloatLib.Floats.ExecFloat

namespace Descriptor.Spec

/--
Reference addition on a binary descriptor: `Model.Spec.add`, the exact dyadic sum rounded once to
nearest-even, with NaN, infinity, and zero results following the descriptor's encoding.
-/
def add {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.add

/--
Reference subtraction on a binary descriptor: `Model.Spec.sub`, addition of the negated right
operand, so a NaN taken from the right operand has its sign bit flipped.
-/
def sub {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.sub

/--
Reference multiplication on a binary descriptor: `Model.Spec.mul`, the exact dyadic product
rounded once to nearest-even; a zero times a finite value is the format's zero with the XOR of
the operand signs.
-/
def mul {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.mul

/--
Reference division on a binary descriptor: `Model.Spec.div`, the exact rational quotient rounded
once to nearest-even, with NaN, infinity, and zero results following the descriptor's encoding.
-/
def div {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.div

/--
Reference square root on a binary descriptor: `Model.Spec.sqrt`, the exact square root rounded
once to nearest-even.
-/
def sqrt {format : FloatFormat} :=
  ModelCodec.liftUnary (F := Descriptor format) (plan := ()) Model.Spec.sqrt

/--
Reference fused multiply-add on a binary descriptor: `Model.Spec.fma`, the exact `x * y + z`
rounded once to nearest-even, with no rounding of the product.
-/
def fma {format : FloatFormat} :=
  ModelCodec.liftTernary (F := Descriptor format) (plan := ()) Model.Spec.fma

end Descriptor.Spec

end FloatLib.Floats.Formats.BinaryInterchange
