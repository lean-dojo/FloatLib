# The kernel against compiled code

One call of the same definition in Lean's kernel (`Lean.Kernel.whnf`, fresh state) and in the compiled program `exactCompiled` (`benchmarks/lean/FloatLibBenchmarks/Exact/Compiled.lean`, Lean's C backend and GMP). The compiled time includes about 0.35 µs of loop around each call. `IntegerRoot.Seeded.newton` is what compiled code runs for `IntegerRoot.newton`. Written by `benchmarks/exact/run.sh compiled`.

| operation | bits | kernel | compiled | kernel / compiled |
| --- | --- | --- | --- | --- |
| `nat/Nat.add` | 64 | 1.31 µs | 424 ns | 3.1x |
| `nat/Nat.mul` | 64 | 1.32 µs | 380 ns | 3.5x |
| `nat/Nat.div (2n by n bits)` | 64 | 2.07 µs | 496 ns | 4.2x |
| `nat/Nat.gcd` | 64 | 1.34 µs | 274 ns | 4.9x |
| `nat/Kernel.size` | 64 | 43.6 µs | 6.12 µs | 7.1x |
| `nat/Kernel.isqrt` | 64 | 129 µs | 18.7 µs | 6.9x |
| `root/IntegerRoot.newton 3` | 64 | 212 µs | 11 µs | 19.3x |
| `root/IntegerRoot.Seeded.newton 3` | 64 | n/a | 2.57 µs | n/a |
| `int/Signed.mul` | 64 | 19.2 µs | 1.56 µs | 12.3x |
| `rat/a + b < c (Rat)` | 64 | 878 µs | 2.92 µs | 300.6x |
| `rat/a + b < c (Frac)` | 64 | 36 µs | 2.42 µs | 14.8x |
| `dyad/Dyad.add` | 64 | 28.9 µs | 910 ns | 31.7x |
| `ball/Ball.mul` | 64 | 21.2 µs | 1.82 µs | 11.6x |
| `nat/Nat.add` | 1,024 | 1.33 µs | 437 ns | 3.0x |
| `nat/Nat.mul` | 1,024 | 1.51 µs | 644 ns | 2.4x |
| `nat/Nat.div (2n by n bits)` | 1,024 | 2.48 µs | 1.08 µs | 2.3x |
| `nat/Nat.gcd` | 1,024 | 7.79 µs | 6.21 µs | 1.3x |
| `nat/Kernel.size` | 1,024 | 97.5 µs | 6.42 µs | 15.2x |
| `nat/Kernel.isqrt` | 1,024 | 280 µs | 62.2 µs | 4.5x |
| `root/IntegerRoot.newton 3` | 1,024 | 308 µs | 71.7 µs | 4.3x |
| `root/IntegerRoot.Seeded.newton 3` | 1,024 | n/a | 10.3 µs | n/a |
| `int/Signed.mul` | 1,024 | 19.6 µs | 988 ns | 19.8x |
| `rat/a + b < c (Rat)` | 1,024 | 838 µs | 21.1 µs | 39.7x |
| `rat/a + b < c (Frac)` | 1,024 | 37.4 µs | 3.7 µs | 10.1x |
| `dyad/Dyad.add` | 1,024 | 29 µs | 1.04 µs | 27.7x |
| `ball/Ball.mul` | 1,024 | 21.5 µs | 2.21 µs | 9.7x |
| `nat/Nat.add` | 4,096 | 1.37 µs | 513 ns | 2.7x |
| `nat/Nat.mul` | 4,096 | 3.31 µs | 2.46 µs | 1.3x |
| `nat/Nat.div (2n by n bits)` | 4,096 | 5.99 µs | 6.12 µs | 1.0x |
| `nat/Nat.gcd` | 4,096 | 35.9 µs | 35.5 µs | 1.0x |
| `nat/Kernel.size` | 4,096 | 170 µs | 19.6 µs | 8.7x |
| `nat/Kernel.isqrt` | 4,096 | 401 µs | 296 µs | 1.4x |
| `root/IntegerRoot.newton 3` | 4,096 | 428 µs | 199 µs | 2.1x |
| `root/IntegerRoot.Seeded.newton 3` | 4,096 | n/a | 19.9 µs | n/a |
| `int/Signed.mul` | 4,096 | 21.9 µs | 2.86 µs | 7.7x |
| `rat/a + b < c (Rat)` | 4,096 | 956 µs | 123 µs | 7.8x |
| `rat/a + b < c (Frac)` | 4,096 | 51.2 µs | 16.3 µs | 3.1x |
| `dyad/Dyad.add` | 4,096 | 29.1 µs | 1.21 µs | 24.1x |
| `ball/Ball.mul` | 4,096 | 23.4 µs | 4.36 µs | 5.4x |
| `nat/Nat.add` | 16,384 | 1.64 µs | 1.19 µs | 1.4x |
| `nat/Nat.mul` | 16,384 | 17.9 µs | 17.7 µs | 1.0x |
| `nat/Nat.div (2n by n bits)` | 16,384 | 43 µs | 60.6 µs | 0.7x |
| `nat/Nat.gcd` | 16,384 | 218 µs | 247 µs | 0.9x |
| `nat/Kernel.size` | 16,384 | 206 µs | 90.6 µs | 2.3x |
| `nat/Kernel.isqrt` | 16,384 | 574 µs | 1.08 ms | 0.5x |
| `root/IntegerRoot.newton 3` | 16,384 | n/a | 837 µs | n/a |
| `root/IntegerRoot.Seeded.newton 3` | 16,384 | n/a | 99.7 µs | n/a |
| `int/Signed.mul` | 16,384 | 37.9 µs | 18.8 µs | 2.0x |
| `rat/a + b < c (Rat)` | 16,384 | 1.64 ms | 793 µs | 2.1x |
| `rat/a + b < c (Frac)` | 16,384 | 153 µs | 114 µs | 1.3x |
| `dyad/Dyad.add` | 16,384 | 30.7 µs | 2.84 µs | 10.8x |
| `ball/Ball.mul` | 16,384 | 39.6 µs | 21.8 µs | 1.8x |
| `nat/Nat.add` | 100,000 | 3.77 µs | 4.59 µs | 0.8x |
| `nat/Nat.mul` | 100,000 | 211 µs | 218 µs | 1.0x |
| `nat/Nat.div (2n by n bits)` | 100,000 | 642 µs | 850 µs | 0.8x |
| `nat/Nat.gcd` | 100,000 | 3.55 ms | 3.62 ms | 1.0x |
| `nat/Kernel.size` | 100,000 | 254 µs | 77.3 µs | 3.3x |
| `nat/Kernel.isqrt` | 100,000 | 3.13 ms | 8.42 ms | 0.4x |
| `root/IntegerRoot.newton 3` | 100,000 | n/a | 6.87 ms | n/a |
| `root/IntegerRoot.Seeded.newton 3` | 100,000 | n/a | 1.95 ms | n/a |
| `int/Signed.mul` | 100,000 | 242 µs | 222 µs | 1.1x |
| `rat/a + b < c (Rat)` | 100,000 | n/a | 11.4 ms | n/a |
| `rat/a + b < c (Frac)` | 100,000 | 1.53 ms | 1.58 ms | 1.0x |
| `dyad/Dyad.add` | 100,000 | 36.8 µs | 9.75 µs | 3.8x |
| `ball/Ball.mul` | 100,000 | 242 µs | 244 µs | 1.0x |
| `mod/powModWindow 0 (binary)` | 64 | 818 µs | 40.5 µs | 20.2x |
| `mod/powModWindow 0 (binary)` | 256 | 3.21 ms | 245 µs | 13.1x |
| `mod/powModWindow 0 (binary)` | 1,024 | 14.7 ms | 1.41 ms | 10.5x |
| `mod/powModWindow 0 (binary)` | 4,096 | 102 ms | 51.2 ms | 2.0x |
