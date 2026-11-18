# The kernel against compiled code

One call of the same definition in Lean's kernel (`Lean.Kernel.whnf`, fresh state) and in the compiled program `exactCompiled` (`benchmarks/lean/FloatLibBenchmarks/Exact/Compiled.lean`, Lean's C backend and GMP). The compiled time includes about 0.35 µs of loop around each call. `IntegerRoot.Seeded.newton` is what compiled code runs for `IntegerRoot.newton`. Written by `benchmarks/exact/run.sh compiled`.

| operation | bits | kernel | compiled | kernel / compiled |
| --- | --- | --- | --- | --- |
| `nat/Nat.add` | 64 | 1.3 µs | 386 ns | 3.4x |
| `nat/Nat.mul` | 64 | 1.35 µs | 365 ns | 3.7x |
| `nat/Nat.div (2n by n bits)` | 64 | 2.05 µs | 489 ns | 4.2x |
| `nat/Nat.gcd` | 64 | 1.4 µs | 283 ns | 5.0x |
| `nat/Kernel.size` | 64 | 46 µs | 5.55 µs | 8.3x |
| `nat/Kernel.isqrt` | 64 | 148 µs | 10.1 µs | 14.7x |
| `root/IntegerRoot.newton 3` | 64 | 230 µs | 11.3 µs | 20.4x |
| `root/IntegerRoot.Seeded.newton 3` | 64 | n/a | 2.02 µs | n/a |
| `int/Signed.mul` | 64 | 19.5 µs | 700 ns | 27.8x |
| `rat/a + b < c (Rat)` | 64 | 890 µs | 2.67 µs | 333.2x |
| `rat/a + b < c (Frac)` | 64 | 36.3 µs | 3.06 µs | 11.8x |
| `dyad/Dyad.add` | 64 | 28.7 µs | 1.14 µs | 25.1x |
| `ball/Ball.mul` | 64 | 21.4 µs | 1.79 µs | 12.0x |
| `nat/Nat.add` | 1,024 | 1.33 µs | 444 ns | 3.0x |
| `nat/Nat.mul` | 1,024 | 1.53 µs | 635 ns | 2.4x |
| `nat/Nat.div (2n by n bits)` | 1,024 | 2.48 µs | 1.09 µs | 2.3x |
| `nat/Nat.gcd` | 1,024 | 7.94 µs | 6.18 µs | 1.3x |
| `nat/Kernel.size` | 1,024 | 137 µs | 118 µs | 1.2x |
| `nat/Kernel.isqrt` | 1,024 | 316 µs | 257 µs | 1.2x |
| `root/IntegerRoot.newton 3` | 1,024 | 364 µs | 252 µs | 1.4x |
| `root/IntegerRoot.Seeded.newton 3` | 1,024 | n/a | 10.3 µs | n/a |
| `int/Signed.mul` | 1,024 | 19.6 µs | 1.31 µs | 14.9x |
| `rat/a + b < c (Rat)` | 1,024 | 847 µs | 28.2 µs | 30.0x |
| `rat/a + b < c (Frac)` | 1,024 | 37.5 µs | 7.41 µs | 5.1x |
| `dyad/Dyad.add` | 1,024 | 29 µs | 2.1 µs | 13.8x |
| `ball/Ball.mul` | 1,024 | 21.7 µs | 4.77 µs | 4.6x |
| `nat/Nat.add` | 4,096 | 1.35 µs | 851 ns | 1.6x |
| `nat/Nat.mul` | 4,096 | 3.37 µs | 3.02 µs | 1.1x |
| `nat/Nat.div (2n by n bits)` | 4,096 | 6.12 µs | 7.83 µs | 0.8x |
| `nat/Nat.gcd` | 4,096 | 35.9 µs | 37 µs | 1.0x |
| `nat/Kernel.size` | 4,096 | 168 µs | 103 µs | 1.6x |
| `nat/Kernel.isqrt` | 4,096 | 390 µs | 277 µs | 1.4x |
| `root/IntegerRoot.newton 3` | 4,096 | 437 µs | 275 µs | 1.6x |
| `root/IntegerRoot.Seeded.newton 3` | 4,096 | n/a | 19.9 µs | n/a |
| `int/Signed.mul` | 4,096 | 22 µs | 2.83 µs | 7.7x |
| `rat/a + b < c (Rat)` | 4,096 | 961 µs | 124 µs | 7.8x |
| `rat/a + b < c (Frac)` | 4,096 | 51.8 µs | 16.4 µs | 3.2x |
| `dyad/Dyad.add` | 4,096 | 28.9 µs | 1.25 µs | 23.1x |
| `ball/Ball.mul` | 4,096 | 23.5 µs | 4.27 µs | 5.5x |
| `nat/Nat.add` | 16,384 | 1.62 µs | 1.16 µs | 1.4x |
| `nat/Nat.mul` | 16,384 | 18 µs | 17.8 µs | 1.0x |
| `nat/Nat.div (2n by n bits)` | 16,384 | 43.3 µs | 57.6 µs | 0.8x |
| `nat/Nat.gcd` | 16,384 | 219 µs | 224 µs | 1.0x |
| `nat/Kernel.size` | 16,384 | 206 µs | 87 µs | 2.4x |
| `nat/Kernel.isqrt` | 16,384 | 559 µs | 958 µs | 0.6x |
| `root/IntegerRoot.newton 3` | 16,384 | n/a | 828 µs | n/a |
| `root/IntegerRoot.Seeded.newton 3` | 16,384 | n/a | 99.6 µs | n/a |
| `int/Signed.mul` | 16,384 | 38.1 µs | 18.8 µs | 2.0x |
| `rat/a + b < c (Rat)` | 16,384 | 1.65 ms | 792 µs | 2.1x |
| `rat/a + b < c (Frac)` | 16,384 | 154 µs | 114 µs | 1.4x |
| `dyad/Dyad.add` | 16,384 | 30.6 µs | 2.77 µs | 11.0x |
| `ball/Ball.mul` | 16,384 | 39.7 µs | 22.1 µs | 1.8x |
| `nat/Nat.add` | 100,000 | 3.77 µs | 5.82 µs | 0.6x |
| `nat/Nat.mul` | 100,000 | 214 µs | 280 µs | 0.8x |
| `nat/Nat.div (2n by n bits)` | 100,000 | 646 µs | 981 µs | 0.7x |
| `nat/Nat.gcd` | 100,000 | 3.55 ms | 4.1 ms | 0.9x |
| `nat/Kernel.size` | 100,000 | 250 µs | 80.4 µs | 3.1x |
| `nat/Kernel.isqrt` | 100,000 | 3.16 ms | 9.01 ms | 0.4x |
| `root/IntegerRoot.newton 3` | 100,000 | n/a | 7.11 ms | n/a |
| `root/IntegerRoot.Seeded.newton 3` | 100,000 | n/a | 2.52 ms | n/a |
| `int/Signed.mul` | 100,000 | 247 µs | 240 µs | 1.0x |
| `rat/a + b < c (Rat)` | 100,000 | n/a | 12.2 ms | n/a |
| `rat/a + b < c (Frac)` | 100,000 | 1.53 ms | 1.56 ms | 1.0x |
| `dyad/Dyad.add` | 100,000 | 37.1 µs | 9.65 µs | 3.8x |
| `ball/Ball.mul` | 100,000 | 244 µs | 235 µs | 1.0x |
| `mod/powModWindow 0 (binary)` | 64 | 837 µs | 31.6 µs | 26.5x |
| `mod/powModWindow 0 (binary)` | 256 | 3.28 ms | 162 µs | 20.3x |
| `mod/powModWindow 0 (binary)` | 1,024 | 16 ms | 1.44 ms | 11.1x |
| `mod/powModWindow 0 (binary)` | 4,096 | 114 ms | 35.3 ms | 3.2x |
