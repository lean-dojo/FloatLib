# FloatLib's own exact layer in the kernel

Lean 4.36.0, `Lean.Kernel.whnf`, one operation in a fresh kernel state. The benchmark file `benchmarks/exact/Baseline.lean` uses the library's exact layer as the library's own proofs do. Written by `benchmarks/exact/run.sh baseline`.


## dyadic

| row | time |
| --- | --- |
| `core a + b`, 64 bits | 1.52 ms |
| `core a + b`, 1,024 bits | 1.48 ms |
| `core a + b`, 4,096 bits | 1.55 ms |
| `core a * b`, 64 bits | 1.48 ms |
| `core a * b`, 1,024 bits | 1.43 ms |
| `core a * b`, 4,096 bits | 1.5 ms |
| `FloatLib add`, 64 bits | 534 µs |
| `FloatLib add`, 1,024 bits | 536 µs |
| `FloatLib add`, 4,096 bits | 537 µs |
| `FloatLib add`, 16,384 bits | 539 µs |
| `FloatLib mul`, 64 bits | 20.8 µs |
| `FloatLib mul`, 1,024 bits | 20.7 µs |
| `FloatLib mul`, 4,096 bits | 22.8 µs |
| `FloatLib mul`, 16,384 bits | 37.9 µs |
| `FloatLib isLess`, 64 bits | 549 µs |
| `FloatLib isLess`, 1,024 bits | 546 µs |
| `FloatLib isLess`, 4,096 bits | 547 µs |
| `FloatLib isLess`, 16,384 bits | 548 µs |


## grid

| row | time |
| --- | --- |
| `add`, 64 bits | 42.8 µs |
| `add`, 1,024 bits | 43 µs |
| `add`, 4,096 bits | 43.1 µs |
| `add`, 16,384 bits | 43.8 µs |
| `sub`, 64 bits | 34.1 µs |
| `sub`, 1,024 bits | 34.2 µs |
| `sub`, 4,096 bits | 34.6 µs |
| `sub`, 16,384 bits | 35 µs |
| `mul`, 64 bits | 146 µs |
| `mul`, 1,024 bits | 148 µs |
| `mul`, 4,096 bits | 156 µs |
| `mul`, 16,384 bits | 223 µs |
| `square`, 64 bits | 73.3 µs |
| `square`, 1,024 bits | 73.9 µs |
| `square`, 4,096 bits | 77.8 µs |
| `square`, 16,384 bits | 112 µs |
| `abs`, 64 bits | 62.2 µs |
| `abs`, 1,024 bits | 62 µs |
| `abs`, 4,096 bits | 62 µs |
| `abs`, 16,384 bits | 62.5 µs |
| `div?`, 64 bits | 445 µs |
| `div?`, 1,024 bits | 442 µs |
| `div?`, 4,096 bits | 445 µs |
| `div?`, 16,384 bits | 451 µs |
| `pow 7`, 64 bits | 453 µs |
| `pow 7`, 1,024 bits | 463 µs |
| `pow 7`, 4,096 bits | 523 µs |
| `divideNat`, 64 bits | 31.4 µs |
| `divideNat`, 1,024 bits | 31.5 µs |
| `divideNat`, 4,096 bits | 31.5 µs |
| `divideNat`, 16,384 bits | 32.9 µs |
| `enclose`, 64 bits | 182 µs |
| `enclose`, 1,024 bits | 183 µs |
| `enclose`, 4,096 bits | 232 µs |


## elementary

| row | time |
| --- | --- |
| `grid exp`, 64 bits | 5.08 ms |
| `grid exp`, 256 bits | 7.08 ms |
| `grid exp`, 1,024 bits | 16.3 ms |
| `grid exp`, 4,096 bits | 55.3 ms |
| `grid log`, 64 bits | 10.9 ms |
| `grid log`, 256 bits | 12.4 ms |
| `grid log`, 1,024 bits | 19.3 ms |
| `grid log`, 4,096 bits | 49.5 ms |
| `rational exp (1/3), degree 12` | 1.41 ms |
| `rational exp (1/3), degree 20` | 1.96 ms |
| `rational exp (1/3), degree 40` | 3.39 ms |
| `rational log (4/3), degree 12` | 3.15 ms |
| `rational log (4/3), degree 20` | 4.58 ms |
| `rational log (4/3), degree 40` | 8.24 ms |
| `rational sin (1/3), degree 12` | 1.15 ms |
| `rational sin (1/3), degree 20` | 1.51 ms |
| `rational sin (1/3), degree 40` | 2.41 ms |
| `rational cos (1/3), degree 20` | 1.42 ms |
| `rational atan (1/3), degree 12` | 2.01 ms |
| `rational atan (1/3), degree 20` | 2.66 ms |
| `sqrt bounds`, 64 bits | 947 µs |
| `sqrt bounds`, 256 bits | 2.52 ms |
| `sqrt bounds`, 1,024 bits | 9.07 ms |
| `pi`, 64 bits | 5.68 ms |
| `pi`, 256 bits | 15.6 ms |
| `pi`, 1,024 bits | 62.5 ms |
| `log 2`, 64 bits | 11.1 ms |
| `log 2`, 256 bits | 40.3 ms |
| `log 2`, 1,024 bits | 185 ms |


## backend

| row | time |
| --- | --- |
| `exp` | 2.2 ms |
| `log` | 8.49 ms |
| `sin` | 1.98 ms |
| `cos` | 1.85 ms |
| `sqrt` | 1.39 ms |
| `atan` | 2.69 ms |
| `tan` | 3.96 ms |
| `sinh` | 3.98 ms |
| `cosh` | 4.52 ms |
| `tanh` | 2.49 ms |
| `sin, argument near 10` | 7.31 ms |
| `log, argument near 10` | 8.72 ms |


## root

| row | time |
| --- | --- |
| `IntegerRoot.newton 2`, 64 bits | 208 µs |
| `IntegerRoot.newton 2`, 1,024 bits | 298 µs |
| `IntegerRoot.newton 2`, 4,096 bits | 417 µs |
| `IntegerRoot.newton 3`, 64 bits | 212 µs |
| `IntegerRoot.newton 3`, 1,024 bits | 308 µs |
| `IntegerRoot.newton 3`, 4,096 bits | 428 µs |


## bound

| row | time |
| --- | --- |
| `log (7/5) ≤ 0.3365, degree 18, 64 bits` | 7.09 ms |
| `log (7/5), degree 40, 192 bits` | 7.92 ms |
| `exp (7/5) ≤ 4.0553, degree 20, 64 bits` | 5.78 ms |
| `exp (7/5), degree 40, 192 bits` | 8.26 ms |


## checker

| row | time |
| --- | --- |
| `the whole check, depth 8 (35 boxes)` | 31.3 ms |
| `one evaluation of the expression`, 60 bits | 938 µs |
| `one box`, 60 bits | 1.37 ms |
| `one bisection`, 60 bits | 780 µs |
