import Lake

open Lake DSL

def floatLibRoot : System.FilePath :=
  run_io do
    let some root ← IO.getEnv "FLOATLIB_ROOT"
      | throw <| IO.userError "FLOATLIB_ROOT is not set"
    pure root

/-!
# Native runner for the SMT-LIB oracle

This small workspace exists because Lean's interpreter cannot execute every native-only
declaration imported by the conversion runtime. It reuses the repository dependency checkout and
local build directory while exposing only the standalone SMT stream runner as an executable.
-/

package floatlibSMTFP where
  packagesDir := floatLibRoot / ".lake" / "packages"
  buildDir :=
    (get_config? buildDir).map System.FilePath.mk |>.getD <|
      run_io do
        return (← IO.getEnv "FLOATLIB_BUILD_DIR")
          |>.map System.FilePath.mk
          |>.getD defaultBuildDir
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require floatlib from floatLibRoot

lean_exe smtFpRunner where
  root := `FloatLibTests.Oracle.SMT
  srcDir := floatLibRoot / "tests"
