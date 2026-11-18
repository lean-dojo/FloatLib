import Lake

open Lake DSL

/-!
# Tests

`lake -d tests test` checks the Lean proofs and native regressions. The `oracle` executable
exchanges vectors with independent numerical tools; see `tests/README.md` for commands.
-/

/--
The linters the test modules are built with: those of the library (`linterOptions` in the root
`lakefile.lean`), without four that ask a test for what it is not.
-/
def linterOptions : Array LeanOption := #[
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`weak.linter.style.header.license,
    "Released under MIT license as described in the file LICENSE."⟩,
  ⟨`weak.linter.style.longFile, .ofNat 1500⟩,
  ⟨`weak.linter.unusedVariables.analyzeTactics, true⟩,
  ⟨`weak.linter.redundantVisibility, true⟩,
  ⟨`weak.linter.omit, true⟩,
  ⟨`weak.linter.extra, true⟩,
  ⟨`weak.linter.style.admit, true⟩,
  ⟨`weak.linter.docPrime, true⟩,
  -- A test module exports nothing: its declarations are fixtures of the checks beside them.
  ⟨`weak.linter.missingDocs, false⟩,
  ⟨`weak.linter.privateModule, false⟩,
  -- The tests print values and run compiled code on purpose. `checks/trust-surface.sh` counts
  -- every `native_decide`.
  ⟨`weak.linter.hashCommand, false⟩,
  ⟨`weak.linter.style.native, false⟩]

package floatlibTests where
  packagesDir := "../.lake/packages"
  testDriver := "check"
  buildDir :=
    (get_config? buildDir).map System.FilePath.mk |>.getD <|
      run_io do
        return (← IO.getEnv "FLOATLIB_BUILD_DIR")
          |>.map System.FilePath.mk
          |>.getD defaultBuildDir
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩] ++ linterOptions

require floatlib from ".."

@[default_target]
lean_lib FloatLibTests where
  roots := #[`FloatLibTests]

lean_exe check where
  root := `Check

lean_exe oracle where
  root := `Oracle

/-- `oracle ieee2019` alone, which `tests/oracles/ieee2019.sh` runs in Lean's interpreter. -/
lean_exe oracleIEEE2019 where
  root := `OracleIEEE2019

/-- Exhaustive small-width observations for the independent SoftPosit checker. -/
lean_exe positStandard where
  root := `FloatLibTests.Oracle.Standards.PositStandard

/-- Complete small posit function inputs and selected standard quire boundaries. -/
lean_exe positFunctions where
  root := `FloatLibTests.Oracle.Standards.PositFunctions

/-- Exact precision, integer and decimal observations through all small posit words. -/
lean_exe positConversions where
  root := `FloatLibTests.Oracle.Standards.PositConversions

/-- Posit/IEEE conversions, including signed zeros and each deterministic rounding mode. -/
lean_exe positIEEE where
  root := `FloatLibTests.Oracle.Standards.PositIEEE

/-- OFP8 conversion observations over complete 16-bit inputs and binary32 boundaries. -/
lean_exe ofp8Standard where
  root := `FloatLibTests.Oracle.Standards.OFP8

/-- Existing block oracle with a narrow import graph for standards comparisons. -/
lean_exe blockStandard where
  root := `FloatLibTests.Oracle.Standards.BlockStandard

/-- General N1169 exact-value observations for the independent Fraction checker. -/
lean_exe embeddedFixedPoint where
  root := `FloatLibTests.Oracle.Standards.EmbeddedFixedPoint

/-- Exact C-locale text observations from a JSON input corpus. -/
lean_exe embeddedText where
  root := `FloatLibTests.Oracle.Standards.EmbeddedText

/-- Complete fixed-point constant grammar and translation from a JSON corpus. -/
lean_exe embeddedConstant where
  root := `FloatLibTests.Oracle.Standards.EmbeddedConstant

/-- Fixed decimal output and width-limited numeric input from a JSON corpus. -/
lean_exe embeddedFormatted where
  root := `FloatLibTests.Oracle.Standards.EmbeddedFormatted

/-- Exact boundary observations for every P3109 rounding policy and small descriptor. -/
lean_exe p3109Comparison where
  root := `FloatLibTests.Oracle.Standards.P3109Comparison

/-- Exhaustive elementary functions with independent source and destination descriptors. -/
lean_exe p3109Functions where
  root := `FloatLibTests.Oracle.Standards.P3109Functions

/-- Shared policy observations for the scalar and block elementary-function oracles. -/
lean_lib P3109OracleSupport where
  roots := #[`FloatLibTests.Oracle.Standards.P3109FunctionSupport]

/-- Chapter 5 elementary functions with independent scales and three-lane blocks. -/
lean_exe p3109BlockFunctions where
  root := `FloatLibTests.Oracle.Standards.P3109BlockFunctions

/-- Exact P3109 query observations for independent gfloat comparisons. -/
lean_exe p3109Queries where
  root := `FloatLibTests.Oracle.Standards.P3109Queries

/-- Mixed-descriptor chapter 5 scalar and block observations. -/
lean_exe p3109Blocks where
  root := `FloatLibTests.Oracle.Standards.P3109Blocks
