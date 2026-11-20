# Kernel checks of other projects

Lean 4.36.0, `Lean.Kernel.whnf`, one check in a fresh kernel state. Each project's check is copied as its authors wrote it and timed next to the same check on `FloatLib.Numerics.Kernel`. The section `packed` times FloatLib's packed rows against the same norm computed entry by entry. Written by `benchmarks/exact/run.sh workloads`.


## primecert

| row | time |
| --- | --- |
| `61/powModK` | 947 µs |
| `61/powMod` | 329 µs |
| `127/powModK` | 1.91 ms |
| `127/powMod` | 558 µs |
| `255/powModK` | 3.84 ms |
| `255/powMod` | 1.09 ms |
| `256/powModK` | 3.72 ms |
| `256/powMod` | 1.1 ms |
| `384/powModK` | 5.79 ms |
| `384/powMod` | 1.81 ms |
| `521/powModK` | 8.17 ms |
| `521/powMod` | 2.98 ms |
| `1279/powModK` | 22.5 ms |
| `1279/powMod` | 17 ms |
| `2203/powModK` | 53.3 ms |
| `2203/powMod` | 32.1 ms |
| `4423/powModK` | 771 ms |
| `4423/powMod` | 136 ms |


## ecrank

| row | time |
| --- | --- |
| `checkPoint curve1 (Int)` | 753 µs |
| `checkPoint curve1 (Z)` | 462 µs |
| `checkPoint (Int)`, 64 bits | 511 µs |
| `checkPoint (Int)`, 256 bits | 509 µs |
| `checkPoint (Int)`, 1,024 bits | 521 µs |
| `checkPoint (Z)`, 64 bits | 225 µs |
| `checkPoint (Z)`, 256 bits | 225 µs |
| `checkPoint (Z)`, 1,024 bits | 235 µs |
| `qrMask 23` | 98.5 µs |
| `qrMask 523` | 1.96 ms |
| `F2 inverse 12 (checkInv)` | 1.89 ms |
| `F2 inverse 12 (packed)` | 544 µs |
| `F2 inverse 32 (checkInv)` | 11.9 ms |
| `F2 inverse 32 (packed)` | 1.34 ms |
| `F2 inverse 64 (checkInv)` | 52.5 ms |
| `F2 inverse 64 (packed)` | 2.77 ms |


## ha

| row | time |
| --- | --- |
| `expChildren step`, 64 bits | 14.2 µs |
| `expChildren step`, 128 bits | 13.6 µs |
| `expChildren step`, 256 bits | 13.8 µs |


## packed

| row | time |
| --- | --- |
| `row product 32 lanes (entry by entry)` | 212 ms |
| `row product 32 lanes (packed)` | 331 µs |
| `row product 256 lanes (packed)` | 440 µs |
| `row product 2048 lanes (packed)` | 2.04 ms |
| `guard and norm 32 lanes` | 237 µs |
| `guard and norm 256 lanes` | 279 µs |
| `guard and norm 2048 lanes` | 574 µs |
