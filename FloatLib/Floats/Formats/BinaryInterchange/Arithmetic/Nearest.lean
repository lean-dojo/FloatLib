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
# Nearest-even binary arithmetic kernels

The six nearest-even kernels behind the default `Model.add`, `Model.sub`, `Model.mul`,
`Model.div`, `Model.sqrt`, and `Model.fma` call the structural dispatchers selected for a
validated format descriptor. They sit below the directed and status kernels, which reuse them
for nearest-even rounding, and the public operations in `Arithmetic.Runtime` select among the
three.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Internal.Nearest

/-- Automatically dispatched nearest-even addition for any validated format descriptor. -/
def add {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  AddBackend.word x y

/-- Automatically dispatched nearest-even subtraction for any validated format descriptor. -/
def sub {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  AddBackend.subWord x y

/-- Automatically dispatched nearest-even multiplication for any validated format descriptor. -/
def mul {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  MulBackend.word x y

/-- Automatically dispatched nearest-even division for any validated format descriptor. -/
def div {fmt : FloatFormat} (x y : Model fmt) : Model fmt :=
  DivBackend.word x y

/-- Automatically dispatched nearest-even square root for any validated format descriptor. -/
def sqrt {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  SqrtBackend.dispatch x

/-- Automatically dispatched nearest-even fused multiply-add for any validated format descriptor. -/
def fma {fmt : FloatFormat} (x y z : Model fmt) : Model fmt :=
  FmaBackend.dispatch x y z

end Internal.Nearest
end Model
end FloatLib.Floats.Formats.BinaryInterchange
