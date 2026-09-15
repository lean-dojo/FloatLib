/-
Copyright (c) 2026 FloatLib
Released under MIT license as described in the file LICENSE.
Authors: FloatLib Team
-/
import Lake
open Lake DSL

/-!
# FloatLib package

The reusable numerical library. Validation and benchmarks have separate workspaces under
`tests/` and `benchmarks/`. The checked website lives under `site/`.
-/

package floatlib where
  version := v!"0.1.0"
  description := "Executable numerical representations with proof-backed semantics in Lean 4."
  keywords := #["numerics", "floating-point", "IEEE-754", "quantization", "verification", "mathlib"]
  license := "MIT"
  readmeFile := "README.md"
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["FloatLib"]
  fixedToolchain := true
  buildDir :=
    (get_config? buildDir).map System.FilePath.mk |>.getD <|
      run_io do
        -- Lake does not pass root `-K` options to a package loaded as a dependency. Repository
        -- scripts export this path so nested workspaces share the configured build directory.
        return (← IO.getEnv "FLOATLIB_BUILD_DIR")
          |>.map System.FilePath.mk
          |>.getD defaultBuildDir
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

/--
Reusable semantics and refinement proofs for numerical representations.

The family-independent interface lives under `FloatLib.Numerics`; concrete format families,
executable backends, and proof packages live under `FloatLib.Floats`.
-/
@[default_target]
lean_lib FloatLib where
  roots := #[`FloatLib]
