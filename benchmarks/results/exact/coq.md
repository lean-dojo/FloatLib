# Coq 8.20.1 on the same operand sizes

`vm_compute` in the image `leanfloat-flocq-bench:4.2.2`, one container with 8 GB and two cores. Each cell is the time Coq printed for a loop divided by its number of iterations. `Z` and `Q` are Coq's binary integers and rationals, `BigZ` is the `bignums` library on 63-bit machine words. An empty cell was not run. Written by `benchmarks/exact/run.sh coq`.

| operation | 64 bits | 256 bits | 512 bits | 1,024 bits | 4,096 bits | 16,384 bits |
| --- | --- | --- | --- | --- | --- | --- |
| `Z.add` | 9.3 µs |  |  | 59.6 µs | 249 µs | 1.01 ms |
| `Z.mul+Z.modulo` | 314 µs |  |  | 74.8 ms | 1.2 s | 19.2 s |
| `Z.leb` | 1.55 µs |  |  | 23.3 µs | 95.6 µs | 376 µs |
| `Z.gcd` | < 1 ms |  |  | 22 ms | 356 ms | 5.72 s |
| `Z.log2` | < 1 ms |  |  | < 1 ms | < 1 ms | 1 ms |
| `BigZ.add` | 400 ns |  |  | 4 µs | 17.1 µs | 442 µs |
| `BigZ.mul+BigZ.modulo` | 8 µs |  |  | 246 µs | 2.44 ms | 94.5 ms |
| `Q: x + b < c, unreduced` | 225 µs |  |  | 39.5 ms | 626 ms | 9.9 s |
| `Qred` | < 1 ms |  |  | 31 ms | 596 ms | 11 s |
| `Zpow_mod` | 29 ms | 1.95 s | 14.4 s |  |  |  |
