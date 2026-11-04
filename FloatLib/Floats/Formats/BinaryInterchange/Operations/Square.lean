/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Backends.Dispatch.Square.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Runtime

/-!
# Once-rounded binary squares

`Model.square` decodes its operand once for the specialized product kernels and returns the same
complete encoding as `Model.mul x x`. So the descriptor's rounding, overflow, zero and NaN
policies apply at every width.
-/

@[expose] public section

namespace FloatLib.Floats.Formats.BinaryInterchange.Model

/-- Square with one nearest-even rounding, preserving multiplication's NaN sign and payload. -/
@[inline] def square {fmt : FloatFormat} (x : Model fmt) : Model fmt :=
  SquareBackend.dispatch x

/-- Squaring and multiplying equal operands produce identical complete encodings. -/
theorem square_eq_mul {fmt : FloatFormat} (x : Model fmt) :
    square x = mul x x :=
  SquareBackend.dispatch_eq_mul x

/-- Squaring refines the exact dyadic product and the descriptor's exceptional-value policy. -/
theorem square_eq_spec {fmt : FloatFormat} (x : Model fmt) :
    square x = Spec.mul x x :=
  SquareBackend.dispatch_eq_spec x

end FloatLib.Floats.Formats.BinaryInterchange.Model
