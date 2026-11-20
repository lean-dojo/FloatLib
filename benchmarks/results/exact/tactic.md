# The `interval` tactic

Time to elaborate one `example` closed by `interval`: reification, the kernel check and the addition to the environment (Lean 4.36.0, `benchmarks/exact/Tactic.lean`). Written by `benchmarks/exact/run.sh tactic`.


## interval

| row | time |
| --- | --- |
| `x * (1 - x) ≤ 13/50 on [0, 1]` | 78.8 ms |
| `x ^ 3 - 2 * x ≤ 1/100 on [0, 7/5]` | 64.4 ms |
| `exp x ≤ 11/4 on [0, 1]` | 23.6 ms |
| `x * exp (-x) ≤ 2/5 on [0, 3]` | 260 ms |
| `log x ≤ 7/10 on [1, 2]` | 33.5 ms |
| `sqrt x ≤ 3/2 on [1, 2]` | 23.4 ms |
| `sin x ≤ x on [0, 1]` | 413 ms |
| `x * y - x ^ 2 ≤ 1/3 on [0, 1]²` | 78.5 ms |
