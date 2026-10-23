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

The `Internal.Directed.add_eq` family and its status counterparts state that each kernel computes
the public operation with the same options, so proofs that unfold a kernel can return to the
public form.
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

/-! ## Kernels of the public operations -/

namespace Internal.Directed

/-- The directed addition kernel computes `add` in every rounding direction. -/
theorem add_eq {fmt : FloatFormat} (mode : IEEERoundingMode) (x y : Model fmt) :
    add mode x y = Model.add x y (mode := mode) := by
  cases mode <;> rfl

/-- The directed subtraction kernel computes `sub` in every rounding direction. -/
theorem sub_eq {fmt : FloatFormat} (mode : IEEERoundingMode) (x y : Model fmt) :
    sub mode x y = Model.sub x y (mode := mode) := by
  cases mode
  case nearest =>
    change Nearest.add x (neg y) = Nearest.sub x y
    rw [show Nearest.add x (neg y) = Spec.add x (neg y) from AddBackend.word_eq_spec x (neg y),
      show Nearest.sub x y = Spec.sub x y from AddBackend.subWord_eq_spec x y]
    rfl
  all_goals rfl

/-- The directed multiplication kernel computes `mul` in every rounding direction. -/
theorem mul_eq {fmt : FloatFormat} (mode : IEEERoundingMode) (x y : Model fmt) :
    mul mode x y = Model.mul x y (mode := mode) := by
  cases mode <;> rfl

/-- The directed division kernel computes `div` in every rounding direction. -/
theorem div_eq {fmt : FloatFormat} (mode : IEEERoundingMode) (x y : Model fmt) :
    div mode x y = Model.div x y (mode := mode) := by
  cases mode <;> rfl

/-- The directed square-root kernel computes `sqrt` in every rounding direction. -/
theorem sqrt_eq {fmt : FloatFormat} (mode : IEEERoundingMode) (x : Model fmt) :
    sqrt mode x = Model.sqrt x (mode := mode) := by
  cases mode <;> rfl

/-- The directed FMA kernel computes `fma` in every rounding direction. -/
theorem fma_eq {fmt : FloatFormat} (mode : IEEERoundingMode) (x y z : Model fmt) :
    fma mode x y z = Model.fma x y z (mode := mode) := by
  cases mode <;> rfl

end Internal.Directed

namespace Internal.Status

/-- The status addition kernel is `add` with `status := true`. -/
theorem add_eq {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    add x y mode = Model.add x y (mode := mode) (status := true) :=
  rfl

/-- The status subtraction kernel is `sub` with `status := true`. -/
theorem sub_eq {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    sub x y mode = Model.sub x y (mode := mode) (status := true) :=
  rfl

/-- The status multiplication kernel is `mul` with `status := true`. -/
theorem mul_eq {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    mul x y mode = Model.mul x y (mode := mode) (status := true) :=
  rfl

/-- The status division kernel is `div` with `status := true`. -/
theorem div_eq {fmt : FloatFormat} (x y : Model fmt) (mode : IEEERoundingMode) :
    div x y mode = Model.div x y (mode := mode) (status := true) :=
  rfl

/-- The status square-root kernel is `sqrt` with `status := true`. -/
theorem sqrt_eq {fmt : FloatFormat} (x : Model fmt) (mode : IEEERoundingMode) :
    sqrt x mode = Model.sqrt x (mode := mode) (status := true) :=
  rfl

/-- The status FMA kernel is `fma` with `status := true`. -/
theorem fma_eq {fmt : FloatFormat} (x y z : Model fmt) (mode : IEEERoundingMode) :
    fma x y z mode = Model.fma x y z (mode := mode) (status := true) :=
  rfl

end Internal.Status

end Model
end FloatLib.Floats.Formats.BinaryInterchange
