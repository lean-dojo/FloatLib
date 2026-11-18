# FloatLib's own exact layer in the kernel

Lean 4.36.0, `Lean.Kernel.whnf`, one operation in a fresh kernel state. The benchmark file `benchmarks/exact/Baseline.lean` uses the library's exact layer as the library's own proofs do. Written by `benchmarks/exact/run.sh baseline`.


## dyadic

| row | time |
| --- | --- |
| `core a + b`, 64 bits | 1.54 ms |
| `core a + b`, 1,024 bits | 1.48 ms |
| `core a + b`, 4,096 bits | 1.55 ms |
| `core a * b`, 64 bits | 1.49 ms |
| `core a * b`, 1,024 bits | 1.44 ms |
| `core a * b`, 4,096 bits | 1.52 ms |
| `FloatLib add`, 64 bits | 541 µs |
| `FloatLib add`, 1,024 bits | 536 µs |
| `FloatLib add`, 4,096 bits | 542 µs |
| `FloatLib add`, 16,384 bits | 542 µs |
| `FloatLib mul`, 64 bits | 20.8 µs |
| `FloatLib mul`, 1,024 bits | 20.9 µs |
| `FloatLib mul`, 4,096 bits | 22.9 µs |
| `FloatLib mul`, 16,384 bits | 38 µs |
| `FloatLib isLess`, 64 bits | 554 µs |
| `FloatLib isLess`, 1,024 bits | 552 µs |
| `FloatLib isLess`, 4,096 bits | 553 µs |
| `FloatLib isLess`, 16,384 bits | 553 µs |


## grid

| row | time |
| --- | --- |
| `add`, 64 bits | 41.8 µs |
| `add`, 1,024 bits | 41.7 µs |
| `add`, 4,096 bits | 42 µs |
| `add`, 16,384 bits | 42.5 µs |
| `sub`, 64 bits | 34.4 µs |
| `sub`, 1,024 bits | 34.7 µs |
| `sub`, 4,096 bits | 34.8 µs |
| `sub`, 16,384 bits | 35.5 µs |
| `mul`, 64 bits | 147 µs |
| `mul`, 1,024 bits | 149 µs |
| `mul`, 4,096 bits | 157 µs |
| `mul`, 16,384 bits | 225 µs |
| `square`, 64 bits | 73.7 µs |
| `square`, 1,024 bits | 74 µs |
| `square`, 4,096 bits | 78.4 µs |
| `square`, 16,384 bits | 113 µs |
| `abs`, 64 bits | 62.1 µs |
| `abs`, 1,024 bits | 62.1 µs |
| `abs`, 4,096 bits | 61.6 µs |
| `abs`, 16,384 bits | 62.8 µs |
| `div?`, 64 bits | 446 µs |
| `div?`, 1,024 bits | 446 µs |
| `div?`, 4,096 bits | 450 µs |
| `div?`, 16,384 bits | 457 µs |
| `pow 7`, 64 bits | 459 µs |
| `pow 7`, 1,024 bits | 467 µs |
| `pow 7`, 4,096 bits | 525 µs |
| `divideNat`, 64 bits | 31.7 µs |
| `divideNat`, 1,024 bits | 32 µs |
| `divideNat`, 4,096 bits | 32.1 µs |
| `divideNat`, 16,384 bits | 33.3 µs |
| `enclose`, 64 bits | 182 µs |
| `enclose`, 1,024 bits | 183 µs |
| `enclose`, 4,096 bits | 233 µs |


## elementary

| row | time |
| --- | --- |
| `grid exp`, 64 bits | 5.18 ms |
| `grid exp`, 256 bits | 7.07 ms |
| `grid exp`, 1,024 bits | 16.3 ms |
| `grid exp`, 4,096 bits | 56.4 ms |
| `grid log`, 64 bits | 11.1 ms |
| `grid log`, 256 bits | 12.6 ms |
| `grid log`, 1,024 bits | 19.3 ms |
| `grid log`, 4,096 bits | 50.8 ms |
| `rational exp (1/3), degree 12` | 1.47 ms |
| `rational exp (1/3), degree 20` | 1.99 ms |
| `rational exp (1/3), degree 40` | 3.43 ms |
| `rational log (4/3), degree 12` | 3.2 ms |
| `rational log (4/3), degree 20` | 4.61 ms |
| `rational log (4/3), degree 40` | 8.52 ms |
| `rational sin (1/3), degree 12` | 1.16 ms |
| `rational sin (1/3), degree 20` | 1.51 ms |
| `rational sin (1/3), degree 40` | 2.45 ms |
| `rational cos (1/3), degree 20` | 1.44 ms |
| `rational atan (1/3), degree 12` | 1.92 ms |
| `rational atan (1/3), degree 20` | 2.61 ms |
| `sqrt bounds`, 64 bits | 1.08 ms |
| `sqrt bounds`, 256 bits | 2.62 ms |
| `sqrt bounds`, 1,024 bits | 9.57 ms |
| `pi`, 64 bits | 5.89 ms |
| `pi`, 256 bits | 16.8 ms |
| `pi`, 1,024 bits | 67.1 ms |
| `log 2`, 64 bits | 11.5 ms |
| `log 2`, 256 bits | 43.6 ms |
| `log 2`, 1,024 bits | 202 ms |


## backend

| row | time |
| --- | --- |
| `exp` | 2.25 ms |
| `log` | 8.75 ms |
| `sin` | 2.06 ms |
| `cos` | 1.89 ms |
| `sqrt` | 1.46 ms |
| `atan` | 2.76 ms |
| `tan` | 3.97 ms |
| `sinh` | 4.04 ms |
| `cosh` | 4.91 ms |
| `tanh` | 2.58 ms |
| `sin, argument near 10` | 7.57 ms |
| `log, argument near 10` | 9.1 ms |


## root

| row | time |
| --- | --- |
| `IntegerRoot.newton 2`, 64 bits | 220 µs |
| `IntegerRoot.newton 2`, 1,024 bits | 353 µs |
| `IntegerRoot.newton 2`, 4,096 bits | 423 µs |
| `IntegerRoot.newton 3`, 64 bits | 230 µs |
| `IntegerRoot.newton 3`, 1,024 bits | 364 µs |
| `IntegerRoot.newton 3`, 4,096 bits | 437 µs |


## bound

| row | time |
| --- | --- |
| `log (7/5) ≤ 0.3365, degree 18, 64 bits` | 7.65 ms |
| `log (7/5), degree 40, 192 bits` | 8.31 ms |
| `exp (7/5) ≤ 4.0553, degree 20, 64 bits` | 6.14 ms |
| `exp (7/5), degree 40, 192 bits` | 8.8 ms |


## checker

| row | time |
| --- | --- |
| `the whole check, depth 8 (35 boxes)` | 32.9 ms |
| `one evaluation of the expression`, 60 bits | 941 µs |
| `one box`, 60 bits | 1.38 ms |
| `one bisection`, 60 bits | 789 µs |
