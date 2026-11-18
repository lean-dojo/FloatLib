# Kernel checks of other projects

Lean 4.36.0, `Lean.Kernel.whnf`, one check in a fresh kernel state. Each project's check is copied as its authors wrote it and timed next to the same check on `FloatLib.Numerics.Kernel`. The section `packed` times FloatLib's packed rows against the same norm computed entry by entry. Written by `benchmarks/exact/run.sh workloads`.


## primecert

| row | time |
| --- | --- |
| `61/powModK` | 950 µs |
| `61/powMod` | 331 µs |
| `127/powModK` | 1.94 ms |
| `127/powMod` | 549 µs |
| `255/powModK` | 3.93 ms |
| `255/powMod` | 1.09 ms |
| `256/powModK` | 3.78 ms |
| `256/powMod` | 1.1 ms |
| `384/powModK` | 6.01 ms |
| `384/powMod` | 1.84 ms |
| `521/powModK` | 8.35 ms |
| `521/powMod` | 2.95 ms |
| `1279/powModK` | 24.1 ms |
| `1279/powMod` | 17.3 ms |
| `2203/powModK` | 53.6 ms |
| `2203/powMod` | 32.6 ms |
| `4423/powModK` | 796 ms |
| `4423/powMod` | 136 ms |


## ecrank

| row | time |
| --- | --- |
| `checkPoint curve1 (Int)` | 769 µs |
| `checkPoint curve1 (Z)` | 464 µs |
| `checkPoint (Int)`, 64 bits | 513 µs |
| `checkPoint (Int)`, 256 bits | 509 µs |
| `checkPoint (Int)`, 1,024 bits | 519 µs |
| `checkPoint (Z)`, 64 bits | 225 µs |
| `checkPoint (Z)`, 256 bits | 226 µs |
| `checkPoint (Z)`, 1,024 bits | 236 µs |
| `qrMask 23` | 100 µs |
| `qrMask 523` | 1.93 ms |
| `F2 inverse 12 (checkInv)` | 1.97 ms |
| `F2 inverse 12 (packed)` | 552 µs |
| `F2 inverse 32 (checkInv)` | 12.6 ms |
| `F2 inverse 32 (packed)` | 1.35 ms |
| `F2 inverse 64 (checkInv)` | 53.1 ms |
| `F2 inverse 64 (packed)` | 2.82 ms |


## ha

| row | time |
| --- | --- |
| `expChildren step`, 64 bits | 14.2 µs |
| `expChildren step`, 128 bits | 13.7 µs |
| `expChildren step`, 256 bits | 13.9 µs |


## packed

| row | time |
| --- | --- |
| `row product 32 lanes (entry by entry)` | 238 ms |
| `row product 32 lanes (packed)` | 337 µs |
| `row product 256 lanes (packed)` | 455 µs |
| `row product 2048 lanes (packed)` | 2.22 ms |
| `guard and norm 32 lanes` | 229 µs |
| `guard and norm 256 lanes` | 292 µs |
| `guard and norm 2048 lanes` | 582 µs |
