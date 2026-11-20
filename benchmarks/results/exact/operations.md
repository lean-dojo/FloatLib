# Kernel cost of one exact operation

Lean 4.36.0, `Lean.Kernel.whnf`. Each cell is `cold / warm`: one operation in a fresh kernel state, and one more operation in a state that has already done one. The column is the size of the operands in bits. Written by `benchmarks/exact/run.sh operations`.


## nat

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Nat.add` | 1.31 µs / 1.43 µs | 1.33 µs / 1.55 µs | 1.37 µs / 1.63 µs | 1.64 µs / 2.04 µs | 3.77 µs / 5.88 µs |
| `a + b` | 11.8 µs / 3.72 µs | 11.8 µs / 3.9 µs | 11.9 µs / 4 µs | 12.2 µs / 4.46 µs | 14.2 µs / 8.39 µs |
| `Nat.mul` | 1.32 µs / 1.47 µs | 1.51 µs / 1.77 µs | 3.31 µs / 3.64 µs | 17.9 µs / 18.6 µs | 211 µs / 215 µs |
| `a * b` | 11.9 µs / 3.83 µs | 12.2 µs / 4.18 µs | 14.1 µs / 6.13 µs | 28.8 µs / 21.1 µs | 223 µs / 219 µs |
| `Nat.div (2n by n bits)` | 2.07 µs / 2.2 µs | 2.48 µs / 2.79 µs | 5.99 µs / 6.37 µs | 43 µs / 43.3 µs | 642 µs / 648 µs |
| `Nat.gcd` | 1.34 µs / 1.21 µs | 7.79 µs / 7.33 µs | 35.9 µs / 35.7 µs | 218 µs / 218 µs | 3.55 ms / 3.55 ms |
| `Nat.ble` | 1.11 µs / 1.92 µs | 1.05 µs / 1.91 µs | 1.06 µs / 1.91 µs | 1.06 µs / 1.91 µs | 1.25 µs / 2.06 µs |
| `decide (a ≤ b)` | 4.23 µs / 5.4 µs | 4.21 µs / 5.46 µs | 4.23 µs / 5.4 µs | 4.23 µs / 5.47 µs | 4.22 µs / 5.38 µs |
| `Nat.log2` | 446 µs / 448 µs | 7.93 ms / 8.61 ms | 36.5 ms / 43.2 ms |  |  |
| `Kernel.size` | 43.6 µs / 17 µs | 97.5 µs / 57.9 µs | 170 µs / 111 µs | 206 µs / 146 µs | 254 µs / 192 µs |
| `Nat.testBit` | 53.8 µs / 18.7 µs | 54 µs / 19.2 µs | 54.1 µs / 19 µs | 54.6 µs / 19.5 µs | 56 µs / 21.1 µs |
| `Kernel.testBit` | 8.42 µs / 4.64 µs | 8.78 µs / 5.12 µs | 8.82 µs / 5.14 µs | 9.14 µs / 5.4 µs | 10.6 µs / 7.15 µs |
| `(Nat.digits 2 n).sum` | 4.23 ms / 4.21 ms | 75.8 ms / 85.5 ms |  |  |  |
| `Kernel.popCount` | 39.8 µs / 24.8 µs | 228 µs / 188 µs | 324 µs / 256 µs | 371 µs / 301 µs | 501 µs / 438 µs |
| `Nat.sqrt` | 893 µs / 767 µs | 8.91 ms / 8.97 ms | 37.7 ms / 42.4 ms |  |  |
| `Kernel.isqrt` | 129 µs / 97.6 µs | 280 µs / 241 µs | 401 µs / 348 µs | 574 µs / 515 µs | 3.13 ms / 3.12 ms |
| `Kernel.isRoot 3` | 13.6 µs / 12 µs | 15.3 µs / 13.7 µs | 30.4 µs / 29 µs | 142 µs / 141 µs | 1.74 ms / 1.75 ms |


## int

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `a + b` | 75.5 µs / 40.1 µs | 76.5 µs / 41.1 µs | 76.4 µs / 41.3 µs | 77 µs / 42.7 µs | 82.1 µs / 49.9 µs |
| `Z.add` | 16 µs / 16.6 µs | 16.9 µs / 17.5 µs | 16.8 µs / 17.6 µs | 17.6 µs / 18.7 µs | 22.2 µs / 25.7 µs |
| `a * b` | 66.8 µs / 39.6 µs | 67.1 µs / 40.4 µs | 69.6 µs / 43.1 µs | 87.4 µs / 60.5 µs | 300 µs / 275 µs |
| `Z.mul` | 17.3 µs / 17.9 µs | 17.6 µs / 18.4 µs | 19.7 µs / 20.8 µs | 35.9 µs / 37.4 µs | 239 µs / 250 µs |
| `decide (a ≤ b)` | 89.8 µs / 51.3 µs | 89.2 µs / 50.7 µs | 89.8 µs / 50.4 µs | 89.4 µs / 50.4 µs | 89.5 µs / 50.8 µs |
| `Int.ble'` | 6.58 µs / 7.73 µs | 6.56 µs / 7.68 µs | 6.58 µs / 7.69 µs | 6.58 µs / 7.7 µs | 6.56 µs / 7.78 µs |
| `a / b` | 84.9 µs / 43.7 µs | 85.7 µs / 45 µs | 91 µs / 49.9 µs | 137 µs / 92.9 µs | 762 µs / 724 µs |
| `Z.ediv` | 39.5 µs / 26.2 µs | 40.1 µs / 27.3 µs | 44.8 µs / 31.7 µs | 89.3 µs / 74 µs | 715 µs / 706 µs |
| `Signed.mul` | 19.2 µs / 16.9 µs | 19.6 µs / 17.8 µs | 21.9 µs / 19.9 µs | 37.9 µs / 36.5 µs | 242 µs / 251 µs |
| `y² = x³ + a x + b (Int)` | 306 µs / 228 µs | 307 µs / 229 µs | 319 µs / 243 µs |  |  |
| `y² = x³ + a x + b (Z)` | 65.1 µs / 67.9 µs | 66.7 µs / 69.6 µs | 76.7 µs / 81.5 µs |  |  |


## rat

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `mkRat (two operands)` | 119 µs / 95.9 µs | 144 µs / 116 µs | 209 µs / 180 µs | 591 µs / 560 µs |  |
| `a + b < c (Rat)` | 878 µs / 744 µs | 838 µs / 704 µs | 956 µs / 823 µs | 1.64 ms / 1.5 ms |  |
| `a * b < c (Rat)` | 635 µs / 494 µs | 692 µs / 555 µs | 821 µs / 683 µs | 1.59 ms / 1.46 ms |  |
| `a + b < c (Frac)` | 36 µs / 34.9 µs | 37.4 µs / 37.2 µs | 51.2 µs / 51.4 µs | 153 µs / 152 µs | 1.53 ms / 1.53 ms |
| `a * b < c (Frac)` | 34.4 µs / 32.2 µs | 35 µs / 33.8 µs | 46.5 µs / 45.9 µs | 131 µs / 130 µs | 1.31 ms / 1.31 ms |
| `Frac.normalize` | 15.3 µs / 12.9 µs | 23 µs / 21 µs | 53.1 µs / 50.1 µs | 241 µs / 237 µs | 3.59 ms / 3.59 ms |
| `Q.mk (two operands)` | 33.4 µs / 32.7 µs | 48.9 µs / 49.1 µs | 109 µs / 108 µs | 488 µs / 487 µs | 7.19 ms / 7.21 ms |
| `a + b < c (Q)` | 143 µs / 147 µs | 184 µs / 187 µs | 333 µs / 336 µs | 1.38 ms / 1.39 ms | 17.9 ms / 18 ms |
| `a * b < c (Q)` | 122 µs / 126 µs | 160 µs / 164 µs | 305 µs / 308 µs | 1.32 ms / 1.33 ms | 17.6 ms / 17.6 ms |
| `a ^ 21 (Rat)` | 142 µs / 94.6 µs | 164 µs / 114 µs |  |  |  |
| `a ^ 21 (Q)` | 26.2 µs / 24 µs | 47 µs / 44.8 µs | 178 µs / 175 µs |  |  |
| `SignedRat a + b` | 214 µs / 177 µs | 246 µs / 205 µs |  |  |  |
| `SignedRat a * b` | 228 µs / 187 µs | 291 µs / 247 µs |  |  |  |


## dyad

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Dyad.add` | 28.9 µs / 23.7 µs | 29 µs / 24.3 µs | 29.1 µs / 24.6 µs | 30.7 µs / 25.6 µs | 36.8 µs / 35.1 µs |
| `Dyad.mul` | 14.4 µs / 12.2 µs | 14.5 µs / 12.6 µs | 16.6 µs / 14.8 µs | 32 µs / 30.2 µs | 229 µs / 232 µs |
| `Dyad.lt` | 25.5 µs / 21 µs | 25.5 µs / 21.5 µs | 25.8 µs / 21.7 µs | 26.9 µs / 22.8 µs | 32.1 µs / 29.1 µs |
| `Dyad.roundDown` | 25.1 µs / 17.3 µs | 25.5 µs / 18.1 µs | 25.6 µs / 18.3 µs | 26.6 µs / 19.1 µs | 30.7 µs / 26.5 µs |
| `Dyad.trimDown 53` | 76.1 µs / 39.1 µs | 133 µs / 84.3 µs | 212 µs / 141 µs | 249 µs / 174 µs | 303 µs / 237 µs |


## ball

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Ball.add` | 30.5 µs / 25.3 µs | 31 µs / 25.7 µs | 30.9 µs / 26.2 µs | 32.6 µs / 27.3 µs | 39.1 µs / 37.3 µs |
| `Ball.mul` | 21.2 µs / 19.1 µs | 21.5 µs / 19.5 µs | 23.4 µs / 21.7 µs | 39.6 µs / 38 µs | 242 µs / 245 µs |
| `Ball.mul, round 64` | 47.7 µs / 43.8 µs | 48.1 µs / 44 µs | 50.2 µs / 47 µs | 69.8 µs / 65.5 µs | 284 µs / 289 µs |
| `Ball.le` | 44 µs / 35.6 µs | 43 µs / 35.8 µs | 42.8 µs / 35.9 µs | 44.3 µs / 37 µs | 49.7 µs / 44 µs |
| `Ball.inv, near one, as many digits` | 41.9 µs / 30.9 µs | 42.6 µs / 32.9 µs | 47 µs / 37.5 µs | 99.2 µs / 86.2 µs | 923 µs / 917 µs |
| `Ball.div, near one, as many digits` | 62.9 µs / 51.5 µs | 64.6 µs / 54.2 µs | 71.9 µs / 61.8 µs | 144 µs / 132 µs | 1.18 ms / 1.18 ms |
| `Ball.apart` | 10.7 µs / 9.36 µs | 11.2 µs / 9.97 µs | 11.4 µs / 10.1 µs | 12.1 µs / 10.6 µs | 14.9 µs / 13.9 µs |


## complex

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `CBall.add` | 37.7 µs / 32.5 µs | 37.4 µs / 33 µs | 37.6 µs / 33.2 µs | 39 µs / 34.6 µs | 43.5 µs / 42.9 µs |
| `CBall.mul` | 87.1 µs / 82.4 µs | 90.7 µs / 83.6 µs | 95.6 µs / 88.2 µs | 131 µs / 124 µs | 547 µs / 556 µs |
| `CBall.mul, round 64` | 105 µs / 100 µs | 107 µs / 102 µs | 112 µs / 108 µs | 149 µs / 145 µs | 571 µs / 593 µs |
| `CFix.mul, as many digits` | 56.9 µs / 47.3 µs | 59.3 µs / 50.3 µs | 69.2 µs / 60.1 µs |  |  |


## list

| operation | 64 bits | 1,024 bits |
| --- | --- | --- |
| `(List.range 256).map, length` | 20.1 ms / 18.9 ms | 20.3 ms / 20 ms |
| `Seq.tabulate 256, Seq.len` | 3.17 ms / 3.7 ms | 3.17 ms / 3.61 ms |
| `(List.range 256).map, getD 200` | 20.5 ms / 19.4 ms | 20.6 ms / 19.5 ms |
| `Seq.tabulate 256, Seq.getD 200` | 3.54 ms / 4.1 ms | 3.54 ms / 4.04 ms |
| `Split.cover of 1 to 64` | 3.69 ms / 2.57 ms |  |


## search

| operation | 64 bits | 1,024 bits | 4,096 bits | 16,384 bits | 100,000 bits |
| --- | --- | --- | --- | --- | --- |
| `Kernel.bisect, square root` | 409 µs / 358 µs | 5.9 ms / 5.72 ms | 26.3 ms / 29.6 ms |  |  |
| `Kernel.isqrt` | 128 µs / 98.1 µs | 279 µs / 243 µs | 403 µs / 349 µs |  |  |
| `strict (a * b), then successor` | 10.3 µs / 9.02 µs | 10.5 µs / 9.57 µs | 12.6 µs / 11.8 µs | 28.5 µs / 28.3 µs | 231 µs / 239 µs |


## mod

| operation | 64 bits | 256 bits | 1,024 bits | 4,096 bits |
| --- | --- | --- | --- | --- |
| `powMod` | 295 µs / 253 µs | 996 µs / 979 µs | 7.81 ms / 8.06 ms | 88 ms / 94 ms |
| `powModWindow 0 (binary)` | 818 µs / 776 µs | 3.21 ms / 3.3 ms | 14.7 ms / 15.6 ms | 102 ms / 110 ms |
| `invMod` | 522 µs / 492 µs | 1.94 ms / 2.03 ms | 8.36 ms / 9.3 ms | 38.3 ms / 47.6 ms |
| `isInvMod` | 7.36 µs / 5.45 µs | 7.38 µs / 5.58 µs | 7.86 µs / 6.16 µs | 12.7 µs / 11.1 µs |
