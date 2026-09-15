# Checks across the floating-point ecosystem

We built and exercised tools for error analysis, expression rewriting, testing,
and reproducible arithmetic. Where we had an adapter, we also compared their
results with FloatLib.

Daisy, FPTaylor, Herbie, OpenLibm, RLIBM,
ReproBLAS, ExBLAS, FPBench, Verificarlo, CORE-MATH, and FLiT mostly run their
own upstream checks in our pinned environment. The SMT QF_FP campaign and the
direct transcendental campaign call FloatLib and an outside implementation on
the same generated inputs. The `evidence` column records which kind of result
each row contains.

## What we pinned

We used the upstream repositories below and recorded the complete revisions,
runner scripts, package versions, and job descriptions under `provenance/`.

| Suite | Upstream source | Retained revision | What this run establishes |
| --- | --- | --- | --- |
| Daisy | <https://github.com/malyzajko/daisy> | `6a6f47abdd231d3009444e9e1b8ce9febc28c27e` | Upstream analysis tests |
| FPTaylor | <https://github.com/soarlab/FPTaylor> | `b5a77cae348400f21f83512210d9f43c4bffb381` | Upstream error-analysis tests |
| Herbie | <https://github.com/herbie-fp/herbie> | `52cba77bdd002d6a71feecc2e57631c8d462b4b2` | Upstream tests and workloads |
| OpenLibm | <https://github.com/JuliaMath/openlibm> | `5fe399749f9276eaa0b8403e507470da05cbbb3f` | Upstream tests and direct observations |
| RLIBM-All | <https://github.com/rutgers-apl/rlibm-all> | `90431a000071e415abf0f403b6125c385551e346` | Upstream format configurations and direct observations |
| ReproBLAS | <https://github.com/peterahrens/ReproBLAS> | `dfb815058dd34b88caba2513cce63bc2e89f951f` | Upstream reproducible-reduction tests |
| ExBLAS | <https://github.com/riakymch/exblas> | `856130ebcfe906f519a623d57d1359e744e29042` | Upstream exact and expansion tests |
| FPBench | <https://github.com/FPBench/FPBench> | `a6621d5f86276859bc01cc7b9c238dee73ff5dbe` | Maintained upstream workflow |
| Verificarlo | <https://github.com/verificarlo/verificarlo> | `c5d1bf798a5ec617c138aa5e6629e1923411d3c8` | Upstream installation test |
| CORE-MATH | <https://gitlab.inria.fr/core-math/core-math> | `68b034fbe9512781352d28f2dc9795c1686fe8e9` | Upstream exhaustive rounding checks and direct observations |
| FLiT | <https://github.com/PRUNERS/FLiT> | `27b6061b9d2302fa8c3252fe770287bb4d07905b` | Upstream tests plus compiler-variation litmus runs |
| SMT QF_FP | <https://github.com/Z3Prover/z3> | Ubuntu package version retained in the raw log | Direct FloatLib/Z3 generated-case comparison |

## Reading the status column

- `pass` means the maintained gate completed without an unexpected failure.
- `qualified-pass` means the useful part passed, with a documented unsupported,
  obsolete, or narrower component left visible in the raw log.
- `observational-complete` means every planned comparison ran, but differences
  are measurements rather than conformance failures.
- `external-limitation`, `diagnostic-failure`, and `upstream-failure` are
  retained when the outside project cannot supply the requested comparison.

The results include:

- Daisy passed 682 tests, ignored five upstream-marked cases, and its
  supplemental Z3 run retained 33 unknown or timed-out queries.
- FPTaylor passed all 670 maintained tests.
- Herbie ran 26,464 unit tests and 89 workloads; four ground-truth convergence
  warnings remain observational.
- RLIBM exercised 1,610 format configurations directly. The five-rounding-mode
  interpretation is reported separately, and unsupported functions stay in the
  availability table.
- ReproBLAS passed 66,338 maintained checks. Its obsolete accuracy target fails
  before execution because the expected binary is no longer built.
- ExBLAS passed all four exact-superaccumulator cases and three of four
  expansion configurations; the compiler compatibility patch is retained.
- The generated SMT campaign compared 147,876 FloatLib and Z3 cases with no
  mismatches.
- The direct transcendental campaign retained every exact agreement and
  difference against MPFR, CORE-MATH, OpenLibm, and the supported RLIBM
  functions. FloatLib does not claim correctly rounded transcendentals, so
  that row is deliberately observational.
- FPBench's maintained workflow passed. Its old standalone filter script still
  exits 1, which accounts for the qualification on that row.
- Verificarlo's install check passed with one upstream expected failure.
- CORE-MATH completed all 169 available function gates. Of those, 166 passed.
  The three compound-interest functions are retained as build limitations
  because MPFR 4.2.1 does not export the `mpfr_compound` symbol they require.
- FLiT completed 140 GCC and Clang configurations in each of base, OpenMPI, and
  MPICH mode. Timing was disabled on purpose: this run checks output variation,
  and the package keeps every final comparison CSV and each imported database.
  FLiT's generated Makefile treats the earlier `*-out` files as intermediate
  prerequisites, so GNU Make removes them after producing the comparison CSVs.
  This follows FLiT's documented workflow, which imports those final CSVs.

Each raw directory contains its own metadata and logs. `provenance/` keeps
the scripts, job descriptions, and pinned revisions, including the details of
runs that needed a retry.
