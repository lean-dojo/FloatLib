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

/-- Descriptor-aware reference addition. -/
def add {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.add

/-- Descriptor-aware reference subtraction. -/
def sub {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.sub

/-- Descriptor-aware reference multiplication. -/
def mul {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.mul

/-- Descriptor-aware reference division. -/
def div {format : FloatFormat} :=
  ModelCodec.liftBinary (F := Descriptor format) (plan := ()) Model.Spec.div

/-- Descriptor-aware reference square root. -/
def sqrt {format : FloatFormat} :=
  ModelCodec.liftUnary (F := Descriptor format) (plan := ()) Model.Spec.sqrt

/-- Descriptor-aware reference fused multiply-add. -/
def fma {format : FloatFormat} :=
  ModelCodec.liftTernary (F := Descriptor format) (plan := ()) Model.Spec.fma

end Descriptor.Spec

end FloatLib.Floats.Formats.BinaryInterchange
