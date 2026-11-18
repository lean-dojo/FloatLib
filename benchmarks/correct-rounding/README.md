# Correctly rounded elementary functions

The experiment checks the FloatLib native Lean result encoding against MPFR,
CORE-MATH and, when supplied by the corpus, the published expected result.
All available references must agree before a row enters the Lean comparison.
NaNs are compared by class; other results, including signed zeros, are
compared by encoding. Exception flags are covered by the separate TestFloat
suite, not this experiment.

Sources:

- [CORE-MATH](https://gitlab.inria.fr/core-math/core-math), commit
  `fd1314b125ea8a6871f68030161eb08839c8caa7`; MIT notices in the source files.
- [Vincent Lefèvre's hard cases](https://www.vinc17.net/research/testlibm/):
  `testlibm-data.xz` dated 2020-11-27 and `hrcases-explog.xz` dated 2015-12-25.
  Download checksums and URLs are in `lefevre-source.json`. The data are
  fetched rather than redistributed because no separate redistribution
  license was identified. The associated `hrtests` software is GPL-3.0-or-later.
- Lefèvre and Muller, ARITH 1997/2001; Lefèvre et al., IEEE Transactions on
  Computers 1998. See DOI
  [10.1109/ARITH.1997.614888](https://doi.org/10.1109/ARITH.1997.614888),
  [10.1109/12.736435](https://doi.org/10.1109/12.736435),
  [10.1109/ARITH.2001.930110](https://doi.org/10.1109/ARITH.2001.930110).

```sh
FLOATLIB_CR_SAMPLES=1024 \
  bash benchmarks/suites/run.sh correct-rounding
```

Sampling chooses the smallest SHA-256 ranks of source path and line number,
separately per supported source group. `coverage.csv` reports full source
counts and actual selected counts. A sampled run is not an exhaustive check.
Only exact source inputs representable in the stated format are accepted.
For published input/output pairs, both encodings must be representable before
the case is eligible. A failed expected-output conversion refuses the whole case.
Unsupported functions and source rounding modes remain in the inventory.

The current runtime adapter covers nearest-even `exp`, `log`, `expm1` and
`log1p` on binary32 and binary64. Complex rows use the same arguments for
each requested component but require a complex analytic API. Scalar calls
on components are not substituted for a complex exponential or logarithm.
Each checkout probes the corresponding `ExecComplex` entry points under
the benchmark imports. Missing tested names get capability refusals with
compiler evidence. If an entry point becomes available, the row instead
reports the missing validated complex reference/encoding adapter; API
presence alone never becomes a correctness verdict.

CORE-MATH's unary binary32 validation uses an exhaustive input space rather
than worst-case files. An optional numerical screen ranks normal-output
candidates by distance to binary32 rounding midpoints:

```sh
python3 benchmarks/correct-rounding/screen.py /absolute/path/to/screen exp \
  --start 0 --end 0x100000000 --keep 32 --timeout 450
FLOATLIB_CR_SCREEN=/absolute/path/to/screen \
  bash benchmarks/suites/run.sh correct-rounding
```

Run screening through the same external resource wrapper as other jobs.
Enumeration limits and retained input bits are exact JSON integers. Ranking
uses CORE-MATH binary64 values and independently recomputes selected distances
with MPFR at 256 and 512 bits. This selects difficult tests; it is not a
certificate of global hardness, and excludes subnormal output magnitudes.

`elapsed_ns` measures the native Lean function call. Reference construction,
compilation and process startup have separate timing records. Exact-value
calibrations of the reference and Lean runner are separate from corpus counts.

## Results on Lean v4.36.0

The suite ran on 2026-11-17.
[`../results/suites/README.md`](../results/suites/README.md) has the table and
[`correct-rounding.csv`](../results/suites/correct-rounding.csv) the counts and the median times per
source, format and function.

The real functions give **107,199 matching real cases and 16 translation refusals**. For every
real argument `x`
of the selection, `complex_reference.py` asks for `exp`, `expm1`, `log` and `log1p` at `z = x + i x`,
to nearest-even, and compares both parts of the result word with GNU MPC through `gmpy2`:
**214,396 matching parts**, 32 translation refusals and 2 parts
left out at the origin, where the comparison with MPC does not apply.
