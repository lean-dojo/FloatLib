import Lake

open Lake DSL

/-! Native entry points for the standard community suites, sharing the repository's packages. -/

package floatlibCommunity where
  packagesDir := "../../.lake/packages"
  buildDir :=
    (get_config? buildDir).map System.FilePath.mk |>.getD defaultBuildDir
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require floatlib from "../.."
require floatlibTests from "../../tests"

lean_exe suiteCorrectRounding where
  srcDir := "../correct-rounding"
  root := `Runtime

lean_exe suiteTestFloat where
  srcDir := "generated"
  root := `TestFloatAdapter
