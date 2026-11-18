# Berkeley TestFloat

Sources: Berkeley [TestFloat Release 3](https://github.com/ucb-bar/berkeley-testfloat-3),
commit `a9c849f1b0eb0264b626d9686ffae167d996e3be`, and
[SoftFloat Release 3](https://github.com/ucb-bar/berkeley-softfloat-3), commit
`a0c6494cdc11865811dec815d5c0049fba9d82a8`; BSD-3-Clause.
The manifests pin the source and file hashes.

The matrix has 210 campaigns. It covers binary16/32/64/128 arithmetic, square root,
FMA, remainder, round-to-integer, floating conversions and comparisons;
bfloat16 coverage follows the upstream conversion support. Widenings and
rounding-independent operations use one mode. `coverage-exclusions.csv`
records formats, operations and modes for which the reference or adapter
does not provide a campaign.

```sh
FLOATLIB_SUITE_OFFSET=0 FLOATLIB_SUITE_LIMIT=10 bash benchmarks/suites/run.sh testfloat
```

Level 1, seed 1 and tininess-after are the defaults. The runner
requires a complete generated level-1 vector file, then checks it with the
compiled Lean adapter. Generation and checking are serial, and the vector
file is deleted afterward. Its checksum, byte count, command and complete
checker summary remain.

Each successful row requires nonzero case count, no parse errors, no value
mismatches and no flag mismatches. A timeout without the final summary is
not conformance evidence. Complete level-1 coverage is a finite standard
test campaign, not a claim about every possible input tuple.

`adapter.py` derives the adapter from the test checker without changing it. Generator and native Lean checking times are reported separately.
The checker executes the library's `logicalModel` operations. These observations
therefore concern that implementation path, rather than every configurable
`ExecFloat` backend.
No imported expected output is a Lean theorem.

## Results on Lean v4.36.0

The full level-1 matrix ran on 2026-11-17,
eight campaigns at a time: **210 campaigns, 127,741,704 vectors,
0 value mismatches and 0 flag mismatches**.
[`../results/suites/README.md`](../results/suites/README.md) has the table by group and
[`testfloat.csv`](../results/suites/testfloat.csv) one row per campaign with its vector count, its
generation time and its checking time.
