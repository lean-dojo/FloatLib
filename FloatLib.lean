/-
Copyright (c) 2026 FloatLib. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats

/-!
# FloatLib

FloatLib is a Lean library for floating-point arithmetic with machine-checked proofs. We built it
so that the code you run is the code you prove things about. You pick a format, write ordinary
arithmetic on `ExecFloat` values, and the theorems `ExecFloat.Proof.*_eq_spec` relate those same
calls to the format's reference semantics. Here is binary32 addition, run on two numbers and
proved for all of them:

```lean
open FloatLib.Floats

#float_info Binary32

def x : Binary32 := 1.5
def y : Binary32 := 2.25

#eval x + y

example : x + y = ExecFloat.Spec.add x y :=
  ExecFloat.Proof.add_eq_spec x y
```

The sum is `3.75`. `add_eq_spec` holds for any two operands, and it fixes the whole result word,
signed zeros and NaN encodings included, so you can rewrite with it inside a larger proof.
`#float_info` shows which representation and backends a format got and which theorems come with
them. `float_decide` proves a statement about a concrete computation by evaluating it in Lean's
kernel, and `#kernel_eval` runs a term there and prints its value and its time.

`import FloatLib` brings in the configured numerical types, their arithmetic and refinement
theorems, the inspection commands, and intervals. Four parts of the library need an import of
their own. Binary elementary functions come from
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`, which provides operations
such as `ExecFloat.Binary.exp`, `Model.exp`, and `Model.pow` and the `MathFunctions` instances
for configured and model binary values. The `MathFunctions` class itself, with its host `Float`
and real instances, is already in the default import.

The named import `FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded` adds
total `exp`, `log`, `expm1`, `logp1`, and weighted `exp x * w`. On an IEEE format their
finite results on finite inputs are correctly rounded, and an overflowing result is the infinity
with the sign of the exact result. The same import has the other functions that IEEE 754-2019
§9.2 recommends, under their names in the standard and with their flags (`exp2`, `log10`,
`sinPi`, `atan2`, `powr`, `compound`, ...), in every rounding direction. The `MathFunctions`
instances keep the approximations, so
generic code doesn't pick these up by itself. If you want it to, import `Configured.Transcendentals`
too and open the scope `FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath`, which
gives generic code the correctly rounded `exp` and `log` on IEEE formats.

The complex elementary functions on `ExecComplex` are under
`FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary`: `Algebraic` has `sqrt` and
`rsqrt`, `Logarithm` has `log`, `log1p`, `atanh` and `atan`, `Exponential` has `exp`, `expm1`,
`sinh`, `cosh`, `sin` and `cos`, `Tangent` has `tanh` and `tan`, `Inverse` has `asinh`, `asin`,
`acosh` and `acos`, and `Power` has `pow`. They are C's `<complex.h>` functions with the special
values specified by C23 Annex G. For the eighteen unary functions, the module of the same
name with `Proof` appended proves correct rounding of each finite component in every direction.
`PowerProof` proves the corresponding result for `pow` under its comparison certificates;
those certificates are not established for every finite argument.

Error bounds have their own import as well. With
`FloatLib.Tactic.Roundoff` you get the `roundoff` tactic and
the `roundoff theorem` and `roundoff mixed theorem` commands, which infer the error bound of a
configured computation from its code. `FloatLib.Floats.Formats.Block.Roundoff` adds the rules for
block-scaled formats: quantization of an element, and accumulation in a narrow accumulator.

If you'd rather import less, the library comes in three layers. `FloatLib.Floats` holds the format
families and the `ExecFloat` carrier they share. `FloatLib.Numerics` is the mathematics that
doesn't depend on an encoding, such as exact dyadic and rational values, rounding, enclosures and
error bounds, and `FloatLib.Kernels` has the integer and fixed-word algorithms the backends run.
Worked examples live under `FloatLib.Examples`, and tests and benchmarks have separate Lake
workspaces.
-/

@[expose] public section
