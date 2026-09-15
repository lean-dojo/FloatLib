import Lake

open Lake DSL

/-!
# Native executable for the standalone transcendental comparison

This deliberately separate Lake file lets `transcendental_compare.sh` compile the vector emitter
without adding a development-only executable to the main tests workspace.
-/

package floatlibTranscendentalHarness where
  srcDir := "FloatLibTests/Oracle"
  packagesDir := "../.lake/packages"
  buildDir :=
    (get_config? buildDir).map System.FilePath.mk |>.getD defaultBuildDir
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require floatlib from ".."

lean_exe transcendentalEmitter where
  root := `Transcendentals
