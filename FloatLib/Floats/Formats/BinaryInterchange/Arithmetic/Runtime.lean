/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Add.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Div.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Fma.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Sqrt.Runtime

/-!
# Format-parameterized binary arithmetic runtime

The six model operations use the structural dispatchers selected for a validated format
descriptor. This module contains only executable definitions; their refinement theorems live in
`Arithmetic.Proof`.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model

/-- Automatically dispatched addition for any validated format descriptor. -/
def add {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  AddBackend.word x y

/-- Automatically dispatched subtraction for any validated format descriptor. -/
def sub {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  AddBackend.subWord x y

/-- Automatically dispatched multiplication for any validated format descriptor. -/
def mul {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  MulBackend.word x y

/-- Automatically dispatched division for any validated format descriptor. -/
def div {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  DivBackend.word x y

/-- Automatically dispatched square root for any validated format descriptor. -/
def sqrt {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  SqrtBackend.dispatch x

/-- Automatically dispatched fused multiply-add for any validated format descriptor. -/
def fma {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  FmaBackend.dispatch x y z

end Model
end FloatLib.Floats.Formats.BinaryInterchange
