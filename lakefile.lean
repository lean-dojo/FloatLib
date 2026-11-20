/-
Copyright (c) 2026 FloatLib. All rights reserved.
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

/--
The modules whose import closures the linter reads: the root, and the opt-in entry points that
`import FloatLib` leaves out. Together they reach every library module, and
`tests/checks/architecture.sh` fails when a module is in no closure.
-/
def lintRoots : Array String := #[
  "FloatLib",
  "FloatLib.Examples",
  "FloatLib.Floats.Formats.BinaryInterchange.Analysis.MixedError.Rounding",
  "FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.PowerProof",
  "FloatLib.Floats.Formats.BinaryInterchange.Complex.Elementary.ValueProof",
  "FloatLib.Floats.Formats.BinaryInterchange.Complex.Roundoff",
  "FloatLib.Floats.Formats.BinaryInterchange.Configured.NativeFPU.Unchecked",
  "FloatLib.Floats.Formats.BinaryInterchange.Operations.FormatOf.SquareRoot.Proof",
  "FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.KernelPath",
  "FloatLib.Floats.Formats.BinaryInterchange.Reduction.Schedule.Proof",
  "FloatLib.Floats.Formats.BinaryInterchange.Rounding.Policy.StochasticSupport",
  "FloatLib.Floats.Formats.Block.Roundoff",
  "FloatLib.Floats.Formats.DecimalInterchange.Reduction.Schedule.Proof",
  "FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.Certified.Proof",
  "FloatLib.Floats.Formats.DecimalInterchange.Transcendentals.CorrectlyRounded.Proof",
  "FloatLib.Floats.Formats.OCP.FP8.KernelTables",
  "FloatLib.Numerics.Quantization.Stochastic.Boundary",
  "FloatLib.Numerics.Quantization.Stochastic.Network",
  "FloatLib.Numerics.Quantization.Stochastic.Requantize",
  "FloatLib.Tactic.PackedRow",
  "FloatLib.Tactic.PackedValues"]

/--
The linters every library module is built with: Mathlib's standard set and the options listed
here, each of which Lean, Batteries or Mathlib registers and leaves off by default.
`tests/checks/linters.sh` fails on a warning. The `weak.` prefix lets a module that does not
import a linter accept its option.
-/
def linterOptions : Array LeanOption := #[
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.header.license,
    "Released under MIT license as described in the file LICENSE."⟩,
  -- No file over 1,500 lines: the standard set applies no limit outside Mathlib.
  ⟨`weak.linter.style.longFile, .ofNat 1500⟩,
  -- A docstring on every definition, constructor and structure field.
  ⟨`weak.linter.missingDocs, true⟩,
  -- No name that nothing refers to, also inside tactic proofs.
  ⟨`weak.linter.unusedVariables.analyzeTactics, true⟩,
  -- No `private` or `public` that changes nothing.
  ⟨`weak.linter.redundantVisibility, true⟩,
  -- No `omit`: a `variable` is declared where the theorems that need it begin.
  ⟨`weak.linter.omit, true⟩,
  -- Lean's extra linters: unreachable tactics, needless `<;>`, repeated namespaces, and
  -- `Decidable` hypotheses that a statement does not use.
  ⟨`weak.linter.extra, true⟩,
  ⟨`weak.linter.style.admit, true⟩,
  -- A docstring on every declaration whose name ends in a prime.
  ⟨`weak.linter.docPrime, true⟩]

package floatlib where
  version := v!"4.1.0"
  description := "Executable numerical representations with proof-backed semantics in Lean 4."
  keywords := #["numerics", "floating-point", "IEEE-754", "quantization", "verification", "mathlib"]
  license := "MIT"
  readmeFile := "README.md"
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
    ⟨`relaxedAutoImplicit, false⟩] ++ linterOptions

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

/--
Reusable semantics and refinement proofs for numerical representations.

The family-independent interface lives under `FloatLib.Numerics`; concrete format families,
executable backends, and proof packages live under `FloatLib.Floats`.
-/
@[default_target]
lean_lib FloatLib where
  roots := #[`FloatLib]

/--
`lake lint` runs the Batteries linter on each module of `lintRoots`, one process per module, so
that it holds one environment at a time (about 4.5 GB; combining the environments needs more
than 16 GB). Arguments after `--` go to every run. After the default linters of a root it runs
`docBlameThm`, which Batteries registers and leaves off: every theorem has a docstring. The file
of that run imports `Batteries.Tactic.Lint` next to the root, because a root that loads no
package does not bring the `#lint` command.
-/
@[lint_driver]
script lint (args) do
  let lake ← getLake
  let sources := (← getWorkspace).root.buildDir / "lint"
  IO.FS.createDirAll sources
  for root in lintRoots do
    let child ← IO.Process.spawn
      { cmd := lake.toString, args := #["exe", "runLinter"] ++ args.toArray ++ #[root] }
    let code ← child.wait
    if code != 0 then
      return code
    let source := sources / s!"{root}.lean"
    IO.FS.writeFile source
      s!"import {root}\nimport Batteries.Tactic.Lint\n#lint- only docBlameThm in FloatLib\n"
    let child ← IO.Process.spawn
      { cmd := lake.toString, args := #["env", "lean", source.toString] }
    let code ← child.wait
    if code != 0 then
      return code
    IO.println s!"-- Every theorem of {root} has a docstring."
  return 0
