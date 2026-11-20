# The kernel against `native_decide`

Each row times the same closed statement with `decide +kernel` and `native_decide`. Both columns include elaboration. The native column also includes compilation. `native_decide` trusts the compiler and introduces an axiom for its result. A `failed` cell means the statement did not compile with `native_decide`. Run `benchmarks/exact/run.sh native` to generate the statements and repeat the comparison.

| statement | `decide +kernel` | `native_decide` |
| --- | --- | --- |
| 3 ^ (p - 1) % p = 1 for p = 2 ^ 255 - 19 | 13.2 ms | 14.2 ms |
| 3 ^ (p - 1) % p = 1 for p = 2 ^ 1279 - 1 | 30 ms | 17.7 ms |
| the square root of 2 ^ 2001 + 12345, checked | 11.5 ms | 13.1 ms |
| sum of 1 / k ^ 2 for k ≤ 40 below 1.63, on fractions | 4.12 ms | 3.34 ms |
| exp (7/5) ≤ 4.0553 on the grid, degree 20, 64 bits | 9.29 ms | 4.53 ms |
| packed row product of 256 lanes with its guards and norm | 6.13 ms | failed |
