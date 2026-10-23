/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats.ExecFloat.Core.Operations

/-!
# Static dispatch for public `ExecFloat` operations

Same-format arithmetic entry points of the format-independent execution layer. Capability
dictionaries are resolved from the static format type. Each function is marked `inline`, and the
checks under `benchmarks/scripts/checks/` verify that specialization erases the dictionary lookup.
-/

@[expose] public section

namespace FloatLib.Floats
namespace ExecFloat

open FloatLib.Numerics

universe u

variable {F : Type u} [EncodedFormat F] [Backend.PolicyFor F]

/--
Add two values in the same format using the certified implementation selected for `F`.

This is the function behind `left + right`. In proofs, `ExecFloat.Proof.add_eq_spec` rewrites it to
the reference definition.
-/
@[inline] def add [Add F] (left right : ExecFloat F) : ExecFloat F :=
  Add.run left right

/--
Subtract two values in the same format using the certified implementation selected for `F`.

This is the function behind `left - right`. In proofs, `ExecFloat.Proof.sub_eq_spec` rewrites it to
the reference definition.
-/
@[inline] def sub [Sub F] (left right : ExecFloat F) : ExecFloat F :=
  Sub.run left right

/--
Multiply two values in the same format using the certified implementation selected for `F`.

This is the function behind `left * right`. In proofs, `ExecFloat.Proof.mul_eq_spec` rewrites it to
the reference definition.
-/
@[inline] def mul [Mul F] (left right : ExecFloat F) : ExecFloat F :=
  Mul.run left right

/--
Divide two values in the same format using the certified implementation selected for `F`.

This is the function behind `left / right`. In proofs, `ExecFloat.Proof.div_eq_spec` rewrites it to
the reference definition.
-/
@[inline] def div [Div F] (left right : ExecFloat F) : ExecFloat F :=
  Div.run left right

/--
Compute square root using the certified implementation selected for `F`.

Write `ExecFloat.sqrt value`, or `value.sqrt` for a format without its own `sqrt`. On a configured
binary value, `value.sqrt` is `ExecFloat.Binary.sqrt`, whose default call is this function. In
proofs, `ExecFloat.Proof.sqrt_eq_spec` rewrites it to the reference definition.
-/
@[inline] def sqrt [Sqrt F] (value : ExecFloat F) : ExecFloat F :=
  Sqrt.run value

/--
Compute `left * right + addend` with one final rounding using the certified implementation
selected for `F`.

In proofs, `ExecFloat.Proof.fma_eq_spec` rewrites it to the reference definition.
-/
@[inline] def fma [Fma F] (left right addend : ExecFloat F) : ExecFloat F :=
  Fma.run left right addend

end ExecFloat
end FloatLib.Floats
