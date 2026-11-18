# Kernel cost of one exact operation

Lean 4.36.0, `Lean.Kernel.whnf`. Each cell is `cold / warm`: one operation in a fresh kernel state, and one more operation in a state that has already done one. The column is the size of the operands in bits. Written by `benchmarks/exact/run.sh operations`.


## nat

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Nat.add` | 1.3 µs / 1.43 µs | 1.33 µs / 1.54 µs | 1.35 µs / 1.65 µs | 1.62 µs / 2.05 µs | 3.77 µs / 5.92 µs |
| `a + b` | 11.9 µs / 3.73 µs | 11.9 µs / 3.91 µs | 11.9 µs / 4.01 µs | 12.2 µs / 4.47 µs | 14.5 µs / 8.34 µs |
| `Nat.mul` | 1.35 µs / 1.48 µs | 1.53 µs / 1.79 µs | 3.37 µs / 3.65 µs | 18 µs / 18.6 µs | 214 µs / 219 µs |
| `a * b` | 11.9 µs / 4.33 µs | 12.2 µs / 4.19 µs | 14.1 µs / 6.1 µs | 28.9 µs / 21.5 µs | 228 µs / 228 µs |
| `Nat.div (2n by n bits)` | 2.05 µs / 2.21 µs | 2.48 µs / 2.79 µs | 6.12 µs / 6.49 µs | 43.3 µs / 43.5 µs | 646 µs / 651 µs |
| `Nat.gcd` | 1.4 µs / 1.31 µs | 7.94 µs / 7.48 µs | 35.9 µs / 35.9 µs | 219 µs / 219 µs | 3.55 ms / 3.56 ms |
| `Nat.ble` | 1.08 µs / 2 µs | 1.07 µs / 1.91 µs | 1.09 µs / 1.96 µs | 1.11 µs / 1.99 µs | 1.35 µs / 2.11 µs |
| `decide (a ≤ b)` | 4.24 µs / 5.42 µs | 4.2 µs / 5.5 µs | 4.21 µs / 5.43 µs | 4.22 µs / 5.48 µs | 4.22 µs / 5.49 µs |
| `Nat.log2` | 446 µs / 452 µs | 8.24 ms / 9.64 ms | 40.5 ms / 47.3 ms |  |  |
| `Kernel.size` | 46 µs / 19.4 µs | 137 µs / 82.6 µs | 168 µs / 111 µs | 206 µs / 141 µs | 250 µs / 190 µs |
| `Nat.testBit` | 53.7 µs / 19 µs | 54.2 µs / 19.2 µs | 54.6 µs / 19.2 µs | 54.8 µs / 20 µs | 56 µs / 21.3 µs |
| `Kernel.testBit` | 8.52 µs / 4.74 µs | 8.83 µs / 5.24 µs | 8.92 µs / 5.2 µs | 9.24 µs / 5.51 µs | 10.7 µs / 7.32 µs |
| `(Nat.digits 2 n).sum` | 4.27 ms / 4.5 ms | 84.2 ms / 97.8 ms |  |  |  |
| `Kernel.popCount` | 40.6 µs / 25.5 µs | 293 µs / 228 µs | 327 µs / 261 µs | 375 µs / 304 µs | 509 µs / 456 µs |
| `Nat.sqrt` | 873 µs / 763 µs | 9.23 ms / 10.1 ms | 42.4 ms / 46.7 ms |  |  |
| `Kernel.isqrt` | 148 µs / 118 µs | 316 µs / 268 µs | 390 µs / 341 µs | 559 µs / 520 µs | 3.16 ms / 3.19 ms |
| `Kernel.isRoot 3` | 14 µs / 12.2 µs | 15.8 µs / 14 µs | 30.5 µs / 29.4 µs | 143 µs / 141 µs | 1.75 ms / 1.77 ms |


## int

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `a + b` | 75.9 µs / 40.7 µs | 76.3 µs / 41.5 µs | 76.3 µs / 42 µs | 77.7 µs / 43.3 µs | 83.6 µs / 52.3 µs |
| `Z.add` | 16.3 µs / 16.7 µs | 17 µs / 17.6 µs | 16.9 µs / 17.8 µs | 17.7 µs / 19 µs | 22.3 µs / 26.8 µs |
| `a * b` | 67.1 µs / 40.1 µs | 67.2 µs / 40.4 µs | 69.8 µs / 43.7 µs | 87.9 µs / 61.7 µs | 303 µs / 285 µs |
| `Z.mul` | 17.4 µs / 18 µs | 17.6 µs / 18.5 µs | 19.6 µs / 20.9 µs | 35.8 µs / 38.3 µs | 242 µs / 256 µs |
| `decide (a ≤ b)` | 90 µs / 51.1 µs | 89.4 µs / 50.9 µs | 90.2 µs / 50.8 µs | 89.9 µs / 50.6 µs | 90.6 µs / 50.9 µs |
| `Int.ble'` | 6.62 µs / 7.77 µs | 6.61 µs / 7.79 µs | 6.61 µs / 7.73 µs | 6.62 µs / 7.7 µs | 6.65 µs / 7.7 µs |
| `a / b` | 85.2 µs / 44.4 µs | 85.7 µs / 45.5 µs | 90.1 µs / 50.2 µs | 137 µs / 94 µs | 764 µs / 732 µs |
| `Z.ediv` | 39.5 µs / 26.2 µs | 40.2 µs / 27.5 µs | 44.7 µs / 31.8 µs | 89.7 µs / 75.2 µs | 718 µs / 715 µs |
| `Signed.mul` | 19.5 µs / 17.1 µs | 19.6 µs / 17.8 µs | 22 µs / 20.1 µs | 38.1 µs / 37 µs | 247 µs / 259 µs |
| `y² = x³ + a x + b (Int)` | 308 µs / 235 µs | 308 µs / 233 µs | 320 µs / 253 µs |  |  |
| `y² = x³ + a x + b (Z)` | 65.6 µs / 68.2 µs | 67.1 µs / 70.4 µs | 77.4 µs / 82.6 µs |  |  |


## rat

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `mkRat (two operands)` | 120 µs / 96.3 µs | 144 µs / 117 µs | 210 µs / 182 µs | 594 µs / 562 µs |  |
| `a + b < c (Rat)` | 890 µs / 764 µs | 847 µs / 717 µs | 961 µs / 842 µs | 1.65 ms / 1.55 ms |  |
| `a * b < c (Rat)` | 638 µs / 501 µs | 695 µs / 561 µs | 823 µs / 697 µs | 1.6 ms / 1.49 ms |  |
| `a + b < c (Frac)` | 36.3 µs / 35.1 µs | 37.5 µs / 37.3 µs | 51.8 µs / 51.4 µs | 154 µs / 153 µs | 1.53 ms / 1.56 ms |
| `a * b < c (Frac)` | 34.7 µs / 32.3 µs | 36 µs / 33.7 µs | 47.7 µs / 46 µs | 133 µs / 132 µs | 1.32 ms / 1.33 ms |
| `Frac.normalize` | 15.3 µs / 13 µs | 23.1 µs / 20.7 µs | 53.3 µs / 50.3 µs | 243 µs / 238 µs | 3.6 ms / 3.6 ms |
| `Q.mk (two operands)` | 33.2 µs / 33 µs | 48.7 µs / 49.3 µs | 109 µs / 108 µs | 488 µs / 487 µs | 7.24 ms / 7.24 ms |
| `a + b < c (Q)` | 143 µs / 148 µs | 185 µs / 187 µs | 335 µs / 338 µs | 1.38 ms / 1.4 ms | 18 ms / 18.1 ms |
| `a * b < c (Q)` | 122 µs / 127 µs | 160 µs / 163 µs | 305 µs / 310 µs | 1.33 ms / 1.34 ms | 17.7 ms / 17.7 ms |
| `a ^ 21 (Rat)` | 141 µs / 92.1 µs | 161 µs / 109 µs |  |  |  |
| `a ^ 21 (Q)` | 26.5 µs / 24 µs | 46.7 µs / 45.1 µs | 178 µs / 176 µs |  |  |
| `SignedRat a + b` | 215 µs / 177 µs | 247 µs / 205 µs |  |  |  |
| `SignedRat a * b` | 230 µs / 188 µs | 292 µs / 247 µs |  |  |  |


## dyad

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Dyad.add` | 28.7 µs / 23.4 µs | 29 µs / 23.9 µs | 28.9 µs / 24.4 µs | 30.6 µs / 25.5 µs | 37.1 µs / 36.1 µs |
| `Dyad.mul` | 14.6 µs / 12.4 µs | 14.6 µs / 12.8 µs | 16.7 µs / 15 µs | 32.2 µs / 30.8 µs | 232 µs / 237 µs |
| `Dyad.lt` | 25.5 µs / 21.2 µs | 25.7 µs / 21.5 µs | 25.8 µs / 22 µs | 26.9 µs / 23.1 µs | 32.1 µs / 29.8 µs |
| `Dyad.roundDown` | 25.2 µs / 17.3 µs | 25.5 µs / 18.2 µs | 25.7 µs / 18.4 µs | 26.7 µs / 19.3 µs | 31.3 µs / 27.2 µs |
| `Dyad.trimDown 53` | 80.5 µs / 41.5 µs | 176 µs / 112 µs | 210 µs / 142 µs | 248 µs / 177 µs | 302 µs / 236 µs |


## ball

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Ball.add` | 30.5 µs / 25.4 µs | 30.9 µs / 25.9 µs | 31 µs / 26.2 µs | 32.4 µs / 27.4 µs | 38.7 µs / 37.6 µs |
| `Ball.mul` | 21.4 µs / 19.4 µs | 21.7 µs / 19.7 µs | 23.5 µs / 22 µs | 39.7 µs / 38.6 µs | 244 µs / 249 µs |
| `Ball.mul, round 64` | 48.1 µs / 43.8 µs | 49.7 µs / 43.3 µs | 52.1 µs / 47.2 µs | 72.4 µs / 66.3 µs | 290 µs / 301 µs |
| `Ball.le` | 42.8 µs / 35.1 µs | 43.1 µs / 35.6 µs | 43.1 µs / 35.9 µs | 44.6 µs / 37.8 µs | 49.9 µs / 45 µs |
| `Ball.inv, near one, as many digits` | 42 µs / 31 µs | 42.6 µs / 33 µs | 48.5 µs / 37.8 µs | 99.2 µs / 86.7 µs | 928 µs / 928 µs |
| `Ball.div, near one, as many digits` | 62.9 µs / 51.8 µs | 64.8 µs / 54.2 µs | 72.2 µs / 61.5 µs | 146 µs / 133 µs | 1.18 ms / 1.2 ms |
| `Ball.apart` | 10.6 µs / 9.37 µs | 11.2 µs / 9.98 µs | 11.4 µs / 10 µs | 12 µs / 10.7 µs | 14.8 µs / 13.9 µs |


## complex

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `CBall.add` | 37.5 µs / 33.3 µs | 37.6 µs / 34.3 µs | 37.9 µs / 34.9 µs | 39 µs / 36.4 µs | 43.3 µs / 44.4 µs |
| `CBall.mul` | 87.6 µs / 80.6 µs | 88.2 µs / 83.3 µs | 92.9 µs / 88.4 µs | 128 µs / 124 µs | 549 µs / 573 µs |
| `CBall.mul, round 64` | 106 µs / 100 µs | 107 µs / 102 µs | 112 µs / 108 µs | 150 µs / 148 µs | 579 µs / 612 µs |
| `CFix.mul, as many digits` | 57.8 µs / 47.5 µs | 59.6 µs / 50.8 µs | 68.8 µs / 60.1 µs |  |  |


## list

| operation | 64 bits | 1,024 bits |
| --- | --- | --- |
| `(List.range 256).map, length` | 22.7 ms / 21.5 ms | 22.3 ms / 21.2 ms |
| `Seq.tabulate 256, Seq.len` | 3.19 ms / 3.93 ms | 3.19 ms / 3.98 ms |
| `(List.range 256).map, getD 200` | 23.1 ms / 21.4 ms | 23.2 ms / 21.3 ms |
| `Seq.tabulate 256, Seq.getD 200` | 3.59 ms / 4.47 ms | 3.58 ms / 4.34 ms |
| `Split.cover of 1 to 64` | 3.73 ms / 2.85 ms |  |


## search

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Kernel.bisect, square root` | 414 µs / 362 µs | 6.03 ms / 6.63 ms | 29.7 ms / 34 ms |  |  |
| `Kernel.isqrt` | 151 µs / 122 µs | 316 µs / 270 µs | 395 µs / 344 µs |  |  |
| `strict (a * b), then successor` | 10.3 µs / 9.1 µs | 10.6 µs / 9.71 µs | 12.7 µs / 12.2 µs | 28.6 µs / 28.7 µs | 235 µs / 247 µs |


## mod

| operation | 64 bits | 256 bits | 1,024 bits | 4,096 bits |
| --- | --- | --- | --- | --- |
| `powMod` | 298 µs / 250 µs | 997 µs / 1.01 ms | 8.06 ms / 8.32 ms | 91.8 ms / 99.6 ms |
| `powModWindow 0 (binary)` | 837 µs / 777 µs | 3.28 ms / 3.4 ms | 16 ms / 17.7 ms | 114 ms / 130 ms |
| `invMod` | 530 µs / 505 µs | 1.96 ms / 2.12 ms | 9.06 ms / 10.6 ms | 45.6 ms / 54.1 ms |
| `isInvMod` | 7.34 µs / 5.47 µs | 7.41 µs / 5.58 µs | 7.88 µs / 6.15 µs | 12.7 µs / 11.1 µs |
