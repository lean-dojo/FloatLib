/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Add.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Div.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Fma.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Mul.Proof
public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Sqrt.Proof

/-!
# Refinement of format-parameterized binary arithmetic

The executable model operations agree with the independent descriptor-aware specifications for
every validated `FloatFormat`.

These theorems connect the arithmetic dispatchers to the format's specifications before a result
is transported to configured storage. Each dispatcher proof covers its optimized backends and
generic fallback.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange
namespace Model
namespace Proof

/-- Public addition agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem add_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    add x y = Spec.add x y :=
  AddBackend.word_eq_spec x y

/-- Public subtraction agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem sub_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    sub x y = Spec.sub x y :=
  AddBackend.subWord_eq_spec x y

/-- Public multiplication agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem mul_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    mul x y = Spec.mul x y :=
  MulBackend.word_eq_spec x y

/-- Public division agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem div_eq_spec {fmt : FloatFormat} (x y : Model fmt) :
    div x y = Spec.div x y :=
  DivBackend.word_eq_spec x y

/-- Public square root agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem sqrt_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    sqrt x = Spec.sqrt x :=
  SqrtBackend.dispatch_eq_spec x

/-- Public FMA agrees with its descriptor-aware specification for every `FloatFormat`. -/
@[grind =] theorem fma_eq_spec {fmt : FloatFormat} (x y z : Model fmt) :
    fma x y z = Spec.fma x y z :=
  FmaBackend.dispatch_eq_spec x y z

end Proof
end Model
end FloatLib.Floats.Formats.BinaryInterchange
