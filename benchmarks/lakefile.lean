import Lake

open Lake DSL

/-!
# Benchmark workspace

Benchmarks depend on the library through its public package boundary. This workspace owns
performance experiments and generated code probes. Repository scripts reuse the library's
external build directory, and correctness checks have their own workspace under `tests/`.
-/

package floatlibBenchmarks where
  srcDir := "lean"
  packagesDir := "../.lake/packages"
  buildDir := (get_config? buildDir).map System.FilePath.mk |>.getD defaultBuildDir
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require floatlib from ".."
require floatlibTests from "../tests"

lean_lib FloatLibBenchmarks where
  globs := #[.submodules `FloatLibBenchmarks]

/-- All six arithmetic operations over the shared static precision catalog. -/
@[default_target]
lean_exe execFloatSweep where
  root := `FloatLibBenchmarks.Public.Precision

/-- Compare all supported FP8 nominal byte carriers with the same exact descriptor formats. -/
lean_exe execFloatFP8Bench where
  root := `FloatLibBenchmarks.Public.FP8

/-- Sweep all six public posit operations across representative static total widths. -/
lean_exe execFloatPositBench where
  root := `FloatLibBenchmarks.Public.Posit

lean_exe execFloatFormatComparison where
  root := `FloatLibBenchmarks.Public.FormatComparison

/-- Matched P3109 inputs and timing protocol shared with the FLoPS adapter. -/
lean_exe execFloatP3109Comparison where
  root := `FloatLibBenchmarks.Public.P3109Comparison

/-- Matched scalar casts shared with TensorLib's Float32 conversion adapter. -/
lean_exe execFloatTensorLibComparison where
  root := `FloatLibBenchmarks.Public.TensorLibComparison

lean_exe execFloatPositVectors where
  root := `FloatLibBenchmarks.Public.PositVectors

/-- Report the certified backend selected for every benchmark format and operation. -/
lean_exe execFloatSelectionMatrix where
  root := `FloatLibBenchmarks.Public.SelectionMatrix

/-- Measure cold-start and warm costs of every admissible tiny-descriptor backend candidate. -/
lean_exe execFloatBackendCalibration where
  root := `FloatLibBenchmarks.Kernels.BackendCalibration

/-- Explain the configured-binary FMA crossover across encoded widths four through eight. -/
lean_exe execFloatConfiguredLowBitCalibration where
  root := `FloatLibBenchmarks.Kernels.ConfiguredLowBitCalibration

/-- Measure cold-start and warm costs of every admissible byte-sized posit backend candidate. -/
lean_exe execFloatPositBackendCalibration where
  root := `FloatLibBenchmarks.Kernels.PositBackendCalibration

/-- Audit and time the width-generic direct quotient-prefix and square-root-prefix kernels. -/
lean_exe execFloatPositDirectStages where
  root := `FloatLibBenchmarks.Diagnostics.PositDirectStages

/-- Measure residual dispatch cost for the ordinary configured binary32 and binary64 user types. -/
lean_exe execFloatConfiguredBinaryBench where
  root := `FloatLibBenchmarks.Kernels.ConfiguredBinary
  -- These paired functions have instruction-for-instruction equivalent hot paths. Giving every
  -- benchmark function the same page offset also controls front-end and page-placement effects,
  -- which are otherwise large enough to masquerade as dispatch cost at 5--8 ns/op.
  moreLeancArgs := #["-falign-functions=4096", "-falign-loops=64"]

/-- Six-operation public arithmetic workload used by the performance-regression budget gate. -/
lean_exe execFloatPerformanceRegression where
  root := `FloatLibBenchmarks.Public.PerformanceRegression

/-- Run certified binary `exp`, `log`, `expm1`, and `logp1` on encoded inputs. -/
lean_exe execFloatCertifiedExpLog where
  root := `FloatLibBenchmarks.Public.CertifiedExpLog

/-- Compiled time of the IEEE 754-2019 clause 9 operations and of the decimal additions. -/
lean_exe execFloatIEEE2019 where
  root := `FloatLibBenchmarks.Public.IEEE2019

/-- Exhaustive 16-bit arithmetic and binary32 square root with IEEE flags. -/
lean_exe execFloatExhaustive where
  root := `FloatLibBenchmarks.Public.Exhaustive

/-- IEEE results and flags for listed operands, used to check other libraries. -/
lean_exe execFloatOracleList where
  root := `FloatLibBenchmarks.Public.OracleList

/-- Time the public binary and posit operations on listed operands. -/
lean_exe execFloatTimeList where
  root := `FloatLibBenchmarks.Public.TimeList

/-- Time the public operations beyond the six nearest-even kernels on mixed operands. -/
lean_exe execFloatTimeOps where
  root := `FloatLibBenchmarks.Public.TimeOps

/-- Compiled times of the exact-arithmetic operations, next to their kernel times. -/
lean_exe exactCompiled where
  root := `FloatLibBenchmarks.Exact.Compiled

/-- Compare MX finite bisection with its exhaustive argmin specification. -/
lean_exe mxCompiled where
  root := `FloatLibBenchmarks.Standards.MXCompiled

/-- Native complete-block NVFP4 observations with exact rational scale arithmetic. -/
lean_exe nvfp4Compiled where
  root := `FloatLibBenchmarks.Standards.NVFP4

/-- Standard-spelled N1169 operations at eight arbitrary value widths. -/
lean_exe fixedPointMatrix where
  root := `FloatLibBenchmarks.Standards.FixedPointMatrix

/-- Every Posit Standard operation at eight static widths, with full-word observations. -/
lean_exe positMatrix where
  root := `FloatLibBenchmarks.Standards.PositMatrix

/-- P3109 scalar, block and scaled standard operations at eight static widths. -/
lean_exe p3109Matrix where
  root := `FloatLibBenchmarks.Standards.P3109Matrix

/-- OFP8 SAT/NONSAT conversions with complete outcomes and exact-decoder observations. -/
lean_exe ofp8Matrix where
  root := `FloatLibBenchmarks.Standards.OFP8Matrix

/-- Complete MX block outputs, stored dots and exponent-only scale operations. -/
lean_exe mxMatrix where
  root := `FloatLibBenchmarks.Standards.MXMatrix

/-- Complete stored NVFP4 tensors with independent scale and reduction policies. -/
lean_exe nvfp4Matrix where
  root := `FloatLibBenchmarks.Standards.NVFP4Matrix
