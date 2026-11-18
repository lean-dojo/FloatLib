# The `interval` tactic

Time to elaborate one `example` closed by `interval`: reification, the kernel check and the addition to the environment (Lean 4.36.0, `benchmarks/exact/Tactic.lean`). Written by `benchmarks/exact/run.sh tactic`.


## interval

| row | time |
| --- | --- |
| `x * (1 - x) ≤ 13/50 on [0, 1]` | 80.1 ms |
| `x ^ 3 - 2 * x ≤ 1/100 on [0, 7/5]` | 69.8 ms |
| `exp x ≤ 11/4 on [0, 1]` | 24.9 ms |
| `x * exp (-x) ≤ 2/5 on [0, 3]` | 283 ms |
| `log x ≤ 7/10 on [1, 2]` | 35.3 ms |
| `sqrt x ≤ 3/2 on [1, 2]` | 24.7 ms |
| `sin x ≤ x on [0, 1]` | 437 ms |
| `x * y - x ^ 2 ≤ 1/3 on [0, 1]²` | 83 ms |
