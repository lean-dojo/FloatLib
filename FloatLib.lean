/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/

module

public import FloatLib.Floats

/-!
# FloatLib

Import `FloatLib` for configured numerical types, arithmetic, refinement theorems, inspection
commands, and intervals.
Programs operate on `ExecFloat` values, and proofs use `ExecFloat.Proof.*_eq_spec` to relate
those same calls to the selected format's reference semantics.

Binary elementary functions require the additional import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`. It provides operations
such as `ExecFloat.Binary.exp`, `Model.exp`, and `Model.pow`, together with the `MathFunctions`
instances for configured and model binary values. The `MathFunctions` class and its host `Float`
and real instances are available from the default import. The named import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded` adds total `exp`, `log`,
`expMinus1`, `logPlus1`, and weighted `exp x * w`. For an IEEE format, their finite results on
finite inputs are correctly rounded, and an overflowing result is the infinity with the sign of
the exact result. The `MathFunctions` instances keep the approximations. With
`Configured.Transcendentals` imported too, open the scope
`FloatLib.Floats.Formats.BinaryInterchange.CorrectlyRoundedMath` to give generic code the
correctly rounded `exp` and `log` on IEEE formats.

The `roundoff` tactic and the `roundoff theorem` and `roundoff mixed theorem` commands, which infer
error bounds of configured computations from their code, come with the named import
`FloatLib.Floats.Formats.BinaryInterchange.Automation.Roundoff`.

For smaller imports, choose a module under `FloatLib.Numerics`, `FloatLib.Kernels`, or
`FloatLib.Floats`. Worked examples live under `FloatLib.Examples`, and tests and benchmarks
have separate Lake workspaces.
-/

@[expose] public section
