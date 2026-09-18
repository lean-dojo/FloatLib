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
Programs operate on `ExecFloat` values; proofs use `ExecFloat.Proof.*_eq_spec` to relate those
same calls to the selected format's reference semantics.

Binary elementary functions require the additional import
`FloatLib.Floats.Formats.BinaryInterchange.Configured.Transcendentals`. It provides operations
such as `ExecFloat.Binary.exp`, `Model.exp`, and `Model.pow`, together with the `MathFunctions`
instances for configured and model binary values. The `MathFunctions` class and its host `Float`
and real instances are available from the default import.

For smaller imports, choose a module under `FloatLib.Numerics`, `FloatLib.Kernels`, or
`FloatLib.Floats`. Worked examples live under `FloatLib.Examples`; tests and benchmarks
have separate Lake workspaces.
-/

@[expose] public section
