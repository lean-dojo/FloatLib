import Lake

open Lake DSL

/-!
# Tests

`lake -d tests test` checks the Lean proofs and native regressions. The `oracle` executable
exchanges vectors with independent numerical tools; see `tests/README.md` for commands.
-/

package floatlibTests where
  packagesDir := "../.lake/packages"
  testDriver := "check"
  buildDir :=
    (get_config? buildDir).map System.FilePath.mk |>.getD <|
      run_io do
        return (← IO.getEnv "FLOATLIB_BUILD_DIR")
          |>.map System.FilePath.mk
          |>.getD defaultBuildDir
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require floatlib from ".."

@[default_target]
lean_lib FloatLibTests where
  roots := #[`FloatLibTests]

lean_exe check where
  root := `Check

lean_exe oracle where
  root := `Oracle
