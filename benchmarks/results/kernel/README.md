# Kernel time of floating-point operations

These tables record what Lean's kernel, the proof checker, spends on one operation and on whole theorems, as written and on the kernel path. They are written by the timing mode of `benchmarks/plots/figures.py` on one shared machine (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs), so read them as ratios; `../figures/measured.json` has the exit code and the time of every section. Nothing here times compiled code. The figures `kernel-binary`, `kernel-operands`, `kernel-extras`, `kernel-loops` and `kernel-all-pairs` of [`../FIGURES.md`](../FIGURES.md) draw them.

- As written: the public operations of FloatLib (`+`, `-`, `*`, `/`, `ExecFloat.sqrt`, `ExecFloat.fma`), as the kernel reduces them without the kernel path. The kernel path does not change these operations. For E4M3 and E5M2 these rows are the reference operations `ExecFloat.Spec.*`, because the kernel cannot evaluate their public operations: they look answers up in tables of 65,536 entries, and building one table in the kernel ran out of 16 GB after about 220 seconds.
- Kernel path: the operations `KernelPath.Value.*` in the nearest-even direction, rewritten as `float_decide` rewrites a goal (the rules tagged `@[kernel_optimize]`), so a cell is the operation that the kernel checks in a proof by `float_decide`.
- A cell is (time of the operation over the operand table - time of a no-operation over the same table) / number of triples, the fastest run of `Lean.Kernel.whnf`, in microseconds. `benchmarks/kernel/run.sh` produces the cells.
- Square roots are taken of positive operands in the normal and subnormal classes. The special class mixes zeros, the smallest subnormal, one, the largest finite value, infinities and NaNs.
- The operand tables are hard on sums: the two operands of a sum have exponents within four binades of each other and their signs alternate, so half of the sums cancel leading bits or carry. The step of an accumulation loop, a sum of two values of one sign that keeps the exponent of the larger operand, is cheaper: see the loop theorems below.

## Eight triples per cell

`benchmarks/kernel/run.sh public 8 3` (as written, at `e58d3251`, 2026-11-18, Lean v4.36.0), `spec 8 3 e4m3 e5m2` (at `e58d3251`, 2026-11-18, Lean v4.36.0) and `kernel 8 3` (kernel path, at `e58d3251`, 2026-11-18, Lean v4.36.0). The as-written cells read and store encodings with the public conversions of each format, the kernel-path cells with `KernelPath.ofNat` and `KernelPath.toNat`. One-time work (format constants) is spread over eight operations only. The ratio is as written over kernel path.

| format | operands | | add | sub | mul | div | sqrt | fma |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| binary16 | normal | as written | 5,100 | 3,674 | 3,334 | 6,119 | 4,613 | 4,545 |
| binary16 | normal | kernel path | 161 | 120 | 82 | 98 | 91 | 139 |
| binary16 | normal | ratio | 32x | 31x | 41x | 62x | 51x | 33x |
| binary16 | subnormal | as written | 3,814 | 4,031 | 2,692 | 3,221 | 5,011 | 5,386 |
| binary16 | subnormal | kernel path | 106 | 115 | 146 | 121 | 114 | 135 |
| binary16 | subnormal | ratio | 36x | 35x | 18x | 27x | 44x | 40x |
| binary16 | special | as written | 2,363 | 1,982 | 2,138 | 2,290 | 2,331 | 2,941 |
| binary16 | special | kernel path | 294 | 265 | 262 | 250 | 163 | 275 |
| binary16 | special | ratio | 8x | 7x | 8x | 9x | 14x | 11x |
| bfloat16 | normal | as written | 3,402 | 3,375 | 3,858 | 5,024 | 4,669 | 4,879 |
| bfloat16 | normal | kernel path | 103 | 119 | 82 | 112 | 90 | 140 |
| bfloat16 | normal | ratio | 33x | 28x | 47x | 45x | 52x | 35x |
| bfloat16 | subnormal | as written | 3,483 | 3,604 | 2,247 | 2,758 | 4,088 | 5,610 |
| bfloat16 | subnormal | kernel path | 105 | 116 | 154 | 122 | 112 | 136 |
| bfloat16 | subnormal | ratio | 33x | 31x | 15x | 23x | 36x | 41x |
| bfloat16 | special | as written | 2,440 | 2,140 | 2,153 | 2,209 | 2,272 | 2,949 |
| bfloat16 | special | kernel path | 291 | 264 | 264 | 247 | 163 | 278 |
| bfloat16 | special | ratio | 8x | 8x | 8x | 9x | 14x | 11x |
| binary32 | normal | as written | 3,772 | 3,613 | 3,282 | 4,797 | 4,505 | 4,401 |
| binary32 | normal | kernel path | 119 | 118 | 82 | 98 | 90 | 140 |
| binary32 | normal | ratio | 32x | 31x | 40x | 49x | 50x | 31x |
| binary32 | subnormal | as written | 3,406 | 3,249 | 3,122 | 4,400 | 4,705 | 4,265 |
| binary32 | subnormal | kernel path | 106 | 117 | 138 | 122 | 111 | 143 |
| binary32 | subnormal | ratio | 32x | 28x | 23x | 36x | 42x | 30x |
| binary32 | special | as written | 2,056 | 1,910 | 1,647 | 1,804 | 1,832 | 2,490 |
| binary32 | special | kernel path | 296 | 268 | 260 | 246 | 162 | 280 |
| binary32 | special | ratio | 7x | 7x | 6x | 7x | 11x | 9x |
| binary64 | normal | as written | 3,077 | 3,061 | 2,600 | 12,473 | 8,010 | 5,045 |
| binary64 | normal | kernel path | 111 | 124 | 84 | 102 | 94 | 164 |
| binary64 | normal | ratio | 28x | 25x | 31x | 122x | 85x | 31x |
| binary64 | subnormal | as written | 6,686 | 6,961 | 3,041 | 8,878 | 7,979 | 4,315 |
| binary64 | subnormal | kernel path | 110 | 119 | 161 | 123 | 120 | 169 |
| binary64 | subnormal | ratio | 61x | 58x | 19x | 72x | 66x | 26x |
| binary64 | special | as written | 3,543 | 2,908 | 2,811 | 3,155 | 3,265 | 4,222 |
| binary64 | special | kernel path | 304 | 281 | 266 | 246 | 170 | 310 |
| binary64 | special | ratio | 12x | 10x | 11x | 13x | 19x | 14x |
| binary128 | normal | as written | 4,143 | 4,015 | 5,835 | 18,777 | 111,607 | 11,037 |
| binary128 | normal | kernel path | 119 | 132 | 88 | 106 | 103 | 216 |
| binary128 | normal | ratio | 35x | 30x | 66x | 177x | 1,084x | 51x |
| binary128 | subnormal | as written | 8,393 | 8,198 | 3,864 | 5,109 | 11,969 | 30,071 |
| binary128 | subnormal | kernel path | 111 | 122 | 179 | 131 | 131 | 212 |
| binary128 | subnormal | ratio | 76x | 67x | 22x | 39x | 91x | 142x |
| binary128 | special | as written | 4,470 | 3,361 | 4,062 | 4,425 | 29,630 | 7,996 |
| binary128 | special | kernel path | 455 | 394 | 384 | 353 | 276 | 513 |
| binary128 | special | ratio | 10x | 9x | 11x | 13x | 107x | 16x |
| e4m3 | normal | as written | 2,579 | 2,618 | 2,234 | 2,437 | 3,719 | 3,335 |
| e4m3 | normal | kernel path | 118 | 125 | 80 | 97 | 90 | 152 |
| e4m3 | normal | ratio | 22x | 21x | 28x | 25x | 41x | 22x |
| e4m3 | subnormal | as written | 1,879 | 2,039 | 1,927 | 2,186 | 3,392 | 3,191 |
| e4m3 | subnormal | kernel path | 133 | 113 | 124 | 115 | 111 | 172 |
| e4m3 | subnormal | ratio | 14x | 18x | 16x | 19x | 31x | 19x |
| e4m3 | special | as written | 1,202 | 1,277 | 874 | 921 | 1,533 | 1,220 |
| e4m3 | special | kernel path | 156 | 161 | 163 | 220 | 108 | 196 |
| e4m3 | special | ratio | 8x | 8x | 5x | 4x | 14x | 6x |
| e5m2 | normal | as written | 3,337 | 3,308 | 2,919 | 2,178 | 3,775 | 4,197 |
| e5m2 | normal | kernel path | 120 | 128 | 77 | 94 | 87 | 149 |
| e5m2 | normal | ratio | 28x | 26x | 38x | 23x | 43x | 28x |
| e5m2 | subnormal | as written | 2,928 | 2,982 | 2,847 | 2,035 | 2,745 | 4,062 |
| e5m2 | subnormal | kernel path | 137 | 157 | 145 | 114 | 90 | 151 |
| e5m2 | subnormal | ratio | 21x | 19x | 20x | 18x | 30x | 27x |
| e5m2 | special | as written | 1,781 | 1,770 | 1,219 | 1,083 | 1,736 | 1,749 |
| e5m2 | special | kernel path | 288 | 261 | 253 | 241 | 158 | 271 |
| e5m2 | special | ratio | 6x | 7x | 5x | 4x | 11x | 6x |

## Sixty-four triples per cell, the same conversions on both sides

Both sides read and store encodings with `KernelPath.ofNat` and `KernelPath.toNat` (`KERNEL_BENCH_CONVERSIONS=kernel`), so a cell is the operation alone, and one-time work is spread over 64 operations: `run.sh public 64 2` (at `e58d3251`, 2026-11-18, Lean v4.36.0), `spec 64 2 e4m3 e5m2` and `kernel 64 5` (at `e58d3251`, 2026-11-18, Lean v4.36.0). The special class is left out: it has nine distinct triples, and the kernel remembers a repeated computation. The subnormal rows of E5M2 are too low on both sides for the same reason (three subnormal fractions).

| format | operands | | add | sub | mul | div | sqrt | fma |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| binary16 | normal | as written | 4,862 | 4,634 | 3,681 | 7,855 | 5,739 | 5,410 |
| binary16 | normal | kernel path | 77 | 84 | 53 | 70 | 62 | 104 |
| binary16 | normal | ratio | 63x | 55x | 69x | 112x | 93x | 52x |
| binary16 | subnormal | as written | 4,003 | 4,177 | 2,312 | 2,963 | 5,460 | 5,667 |
| binary16 | subnormal | kernel path | 77 | 85 | 103 | 88 | 82 | 103 |
| binary16 | subnormal | ratio | 52x | 49x | 22x | 34x | 67x | 55x |
| bfloat16 | normal | as written | 4,151 | 4,099 | 3,749 | 5,369 | 4,738 | 5,054 |
| bfloat16 | normal | kernel path | 74 | 85 | 53 | 69 | 63 | 90 |
| bfloat16 | normal | ratio | 56x | 48x | 71x | 78x | 75x | 56x |
| bfloat16 | subnormal | as written | 3,326 | 3,468 | 2,329 | 2,761 | 4,763 | 5,564 |
| bfloat16 | subnormal | kernel path | 77 | 91 | 103 | 101 | 81 | 218 |
| bfloat16 | subnormal | ratio | 43x | 38x | 23x | 27x | 59x | 26x |
| binary32 | normal | as written | 4,048 | 4,318 | 3,929 | 6,061 | 5,631 | 4,965 |
| binary32 | normal | kernel path | 83 | 83 | 53 | 70 | 62 | 108 |
| binary32 | normal | ratio | 49x | 52x | 74x | 87x | 91x | 46x |
| binary32 | subnormal | as written | 4,167 | 3,970 | 3,512 | 5,224 | 5,937 | 5,127 |
| binary32 | subnormal | kernel path | 79 | 85 | 103 | 183 | 83 | 83 |
| binary32 | subnormal | ratio | 53x | 47x | 34x | 29x | 72x | 62x |
| binary64 | normal | as written | 3,896 | 3,798 | 3,453 | 20,657 | 11,383 | 6,444 |
| binary64 | normal | kernel path | 72 | 81 | 55 | 73 | 67 | 131 |
| binary64 | normal | ratio | 54x | 47x | 63x | 283x | 170x | 49x |
| binary64 | subnormal | as written | 9,544 | 9,967 | 3,982 | 12,194 | 11,836 | 5,284 |
| binary64 | subnormal | kernel path | 81 | 92 | 128 | 92 | 92 | 127 |
| binary64 | subnormal | ratio | 118x | 108x | 31x | 133x | 129x | 42x |
| binary128 | normal | as written | 5,230 | 5,399 | 7,491 | 22,914 | 124,380 | 13,795 |
| binary128 | normal | kernel path | 81 | 91 | 61 | 78 | 79 | 188 |
| binary128 | normal | ratio | 65x | 59x | 123x | 294x | 1,574x | 73x |
| binary128 | subnormal | as written | 10,695 | 9,792 | 4,380 | 4,781 | 14,609 | 33,411 |
| binary128 | subnormal | kernel path | 84 | 93 | 154 | 104 | 104 | 183 |
| binary128 | subnormal | ratio | 127x | 105x | 28x | 46x | 140x | 183x |
| e4m3 | normal | as written | 2,905 | 2,956 | 2,612 | 3,246 | 4,590 | 4,707 |
| e4m3 | normal | kernel path | 75 | 81 | 50 | 78 | 61 | 111 |
| e4m3 | normal | ratio | 39x | 36x | 52x | 42x | 75x | 42x |
| e4m3 | subnormal | as written | 2,125 | 2,140 | 1,589 | 1,757 | 3,856 | 2,641 |
| e4m3 | subnormal | kernel path | 78 | 83 | 83 | 67 | 71 | 84 |
| e4m3 | subnormal | ratio | 27x | 26x | 19x | 26x | 54x | 31x |
| e5m2 | normal | as written | 4,074 | 4,099 | 3,583 | 2,500 | 4,898 | 5,201 |
| e5m2 | normal | kernel path | 80 | 81 | 51 | 67 | 61 | 102 |
| e5m2 | normal | ratio | 51x | 51x | 70x | 37x | 80x | 51x |
| e5m2 | subnormal | as written | 552 | 571 | 1,084 | 792 | 360 | 1,615 |
| e5m2 | subnormal | kernel path | 25 | 26 | 46 | 35 | 11 | 48 |
| e5m2 | subnormal | ratio | 22x | 22x | 24x | 23x | 33x | 34x |

## Wide and custom formats

The kernel path in two custom layouts (`e8f15`, 24 bits, and `e15f64`, 80 bits) and in the IEEE interchange formats of 256 to 4,096 bits (19, 23, 27 and 35 exponent bits), eight triples per cell, the fastest of three runs. The public operations are not measured at these widths.

| format | operands | add | sub | mul | div | sqrt | fma |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| e8f15 | normal | 134 | 124 | 81 | 98 | 100 | 143 |
| e8f15 | subnormal | 106 | 115 | 140 | 124 | 117 | 140 |
| e8f15 | special | 303 | 263 | 264 | 247 | 162 | 284 |
| e15f64 | normal | 117 | 132 | 88 | 105 | 106 | 183 |
| e15f64 | subnormal | 109 | 120 | 170 | 132 | 127 | 176 |
| e15f64 | special | 332 | 308 | 307 | 293 | 205 | 390 |
| binary256 | normal | 127 | 139 | 89 | 106 | 103 | 228 |
| binary256 | subnormal | 117 | 129 | 224 | 139 | 135 | 226 |
| binary256 | special | 486 | 432 | 444 | 361 | 283 | 534 |
| binary512 | normal | 142 | 150 | 89 | 106 | 178 | 241 |
| binary512 | subnormal | 141 | 149 | 230 | 183 | 211 | 237 |
| binary512 | special | 493 | 455 | 453 | 406 | 327 | 551 |
| binary1024 | normal | 146 | 153 | 91 | 107 | 225 | 252 |
| binary1024 | subnormal | 146 | 156 | 240 | 189 | 292 | 247 |
| binary1024 | special | 505 | 469 | 465 | 419 | 345 | 565 |
| binary4096 | normal | 160 | 161 | 94 | 116 | 295 | 287 |
| binary4096 | subnormal | 154 | 169 | 274 | 218 | 410 | 275 |
| binary4096 | special | 534 | 514 | 495 | 458 | 388 | 588 |

The cost grows slowly with the width: the short paths of addition and multiplication do not look at the width, a normal significand has its bit length after one comparison, the general rounding finds a bit length beyond 384 bits by a search down to a window of 128 bits, and the square root takes sixteen Newton steps when eight do not pass its check. No sum, no rounding and no quotient builds a power of two of the size of an exponent difference, so a sum with a zero, a product far below the subnormal range and a quotient of operands at the two ends of the range cost the same at every exponent width (`KernelPath.divCore_def` for the quotient). The operations with status flags still put the exact result on a grid of absolute exponents; they are meant for formats up to binary256.

## Outcomes with status flags, comparisons, conversions and literals

`benchmarks/kernel/extras.sh 64 5` (at `e58d3251`, 2026-11-18, Lean v4.36.0) reduces one term per row twice: as written, through the public operations, and after the rewrite that `float_decide` applies. Microseconds per operation on normal operands, 64 operand triples or literals per cell, the fastest of five runs. A row with `status := true` evaluates the delivered value, the comparison of the flags with a record and the comparison of the ternary value with a constant, as a statement about an outcome does. The cast rows are the reference cast `Model.cast` of a decoded value, stored in the destination format; the public conversion `x.cast (target := T)` is not rewritten. The rational numbers are `mkRat (2 * i + 1) (3 * i + 7)`, and the time the kernel needs to build them is subtracted on both sides. `n/a` is a cell whose difference came out at zero or below, which happens to the cheapest terms on a busy machine.

| term | binary32 as written | binary32 rewritten | ratio | binary64 as written | binary64 rewritten | ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `ExecFloat.Binary.add x y (status := true)` | 11,892 | 377 | 32x | 12,691 | 382 | 33x |
| `ExecFloat.Binary.sub x y (status := true)` | 11,637 | 387 | 30x | 12,922 | 386 | 33x |
| `ExecFloat.Binary.mul x y (status := true)` | 11,609 | 339 | 34x | 12,401 | 322 | 39x |
| `ExecFloat.Binary.div x y (status := true)` | 9,772 | 349 | 28x | 12,557 | 351 | 36x |
| `ExecFloat.Binary.sqrt x (status := true)` | 10,570 | 210 | 50x | 17,497 | 208 | 84x |
| `ExecFloat.Binary.fma x y z (status := true)` | 15,323 | 438 | 35x | 19,094 | 420 | 45x |
| `ExecFloat.Binary.roundToIntegral x .nearest (status := true)` | 7,274 | 317 | 23x | 8,550 | 307 | 28x |
| `x < y` | 2,089 | 72 | 29x | 2,238 | 73 | 31x |
| `x == y` | 2,076 | 59 | 35x | 2,253 | 58 | 39x |
| `ExecFloat.Binary.totalOrder x y` | 1,720 | 64 | 27x | 2,027 | 63 | 32x |
| `ExecFloat.Binary.isNaN x` | 117 | 31 | 4x | 101 | 30 | 3x |
| `ExecFloat.Binary.roundToIntegral x .nearest` | 4,587 | 79 | 58x | 5,289 | 78 | 68x |
| `x.toInt? (mode := .nearest)` | 828 | 78 | 11x | 714 | 72 | 10x |
| `ExecFloat.Binary.toRat? x` | 596 | 114 | 5x | 569 | 113 | 5x |
| `Model.cast` into the next narrower format, between a decode and a store | 4,801 | 73 | 66x | 5,768 | 71 | 81x |
| the same cast with `status := true` | 9,980 | 306 | 33x | 11,748 | 296 | 40x |
| a decimal literal `(2 * i + 1) / 1000` | 1,982 | 90 | 22x | 1,989 | 88 | 23x |
| `ExecFloat.Binary.ofRat q (mode := .up)` | 2,198 | 275 | 8x | 1,990 | 295 | 7x |
| `ExecFloat.Binary.ofRat q (mode := .up) (status := true)` | 5,841 | 573 | 10x | 6,687 | 545 | 12x |

## Three theorems about loops of 1,000 steps

`benchmarks/kernel/loops.sh 3` (at `e58d3251`, 2026-11-18, Lean v4.36.0) type-checks each theorem of `Loops.lean` three times by `decide +kernel` on the public operations and by `float_decide`, and prints the `type checking` time of Lean's profiler; the table has the fastest run. `FlocqConversion.v` states the same three results for Coq 8.20.1 with Flocq 4.2.2; its two columns are the `Time Qed` lines recorded on 2026-11-15 in the container `leanfloat-flocq-bench:4.2.2` (8 GB, 2 CPUs).

| theorem | `decide +kernel`, public operations | `float_decide` | Coq, kernel conversion (recorded) | Coq, bytecode VM (recorded) |
| --- | ---: | ---: | ---: | ---: |
| 1,000 binary32 additions of 0.1 | 4.24 s | 0.053 s | 0.381 s | 0.058 s |
| sum of 1,000 binary64 values | 4.70 s | 0.108 s | 4.56 s | 0.327 s |
| dot product of 1,000 binary64 pairs | 8.79 s | 0.159 s | 9.35 s | 0.73 s |

The `float_decide` column is the kernel's check of the loop. Each proof has two more lemmas, the rewrite of the goal and the statement itself, which the kernel checks in milliseconds. Each Lean theorem depends on `propext`, `Classical.choice` and `Quot.sound` only (the `axioms` column of `loops.csv`). The Coq file computes the binary64 operands once with `vm_compute` and stores them as lists, so that its conversions contain floating-point operations only; Lean computes the operands inside the kernel.

## Statements about all 65,536 pairs of encodings

Seconds of kernel time to check one statement about all pairs (at `e58d3251`, 2026-11-18, Lean v4.36.0): the loop of `float_decide` over the pairs (`benchmarks/kernel/Exhaustive.lean`: addition and multiplication of E4M3 commute on all pairs of encodings that are not both NaN), and one run of each side on rows of 65,536 lanes (`lane_decide`, `benchmarks/suite/Lanes.lean`), where the time is the sum over the lane widths that were tried.

| statement | method | seconds | lane widths tried |
| --- | --- | ---: | ---: |
| e4m3 add-commutes | float_decide loop | 19.00 |  |
| e4m3 mul-commutes | float_decide loop | 23.10 |  |
| e4m3 add-commutes | lane_decide | 2.46 | 2 |
| e4m3 mul-commutes | lane_decide | 0.75 | 1 |
| e5m2 add-commutes | lane_decide | 2.13 | 2 |
| e5m2 mul-commutes | lane_decide | 1.52 | 2 |
| binary16-slice add-commutes | lane_decide | 3.61 | 3 |
| binary16-slice mul-commutes | lane_decide | 1.59 | 2 |
| e4m3 add-table | lane_decide | 2.86 | 2 |

<!-- figures: this section is written by benchmarks/plots/figures.py draw -->

## Figures

The captions, alt texts, notes and CSV columns of these figures are in [FIGURES.md](../FIGURES.md).

![Six panels, one per arithmetic operation: kernel time against format width, with open markers for the public operation as written up to 128 bits and a line for the kernel path up to 4,096 bits.](../figures/kernel-binary.png "Kernel time of one binary operation of FloatLib from 8 to 4,096 bits, as written and on the kernel path. A point is the time Lean's kernel takes for one operation on normal operands, rounded to nearest even, as the median over the formats of that width; as written is the public operation, and the kernel path is the term that float_decide checks. Both axes are logarithmic, lower is faster, and the public operations were not measured above 128 bits. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).")

**Figure 1.** Kernel time of one binary operation of FloatLib from 8 to 4,096 bits, as written and on the kernel path. A point is the time Lean's kernel takes for one operation on normal operands, rounded to nearest even, as the median over the formats of that width; as written is the public operation, and the kernel path is the term that float_decide checks. Both axes are logarithmic, lower is faster, and the public operations were not measured above 128 bits. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).

![Six panels of lines, one per arithmetic operation: kernel time against format width for normal operands, subnormal operands and special values, all on the kernel path.](../figures/kernel-operands.png "Kernel time of one operation of FloatLib by operand class: normal operands, subnormal operands and special values. A point is the time Lean's kernel takes for one operation on the kernel path, as the median over the formats of that width. The width axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).")

**Figure 2.** Kernel time of one operation of FloatLib by operand class: normal operands, subnormal operands and special values. A point is the time Lean's kernel takes for one operation on the kernel path, as the median over the formats of that width. The width axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).

![Two panels, binary32 and binary64, with one row per term: an open circle for the kernel time of the term as written and a filled circle for the term with the kernel rules, joined by a bar, on a logarithmic time axis.](../figures/kernel-extras.png "Kernel time of the terms beyond the six operations (status flags, comparisons, conversions, casts and literals), as written and with FloatLib's kernel rules. A mark is the time Lean's kernel takes for one evaluation on normal operands; as written goes through the public operation, and the other mark is the term after the rewrite of float_decide. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).")

**Figure 3.** Kernel time of the terms beyond the six operations (status flags, comparisons, conversions, casts and literals), as written and with FloatLib's kernel rules. A mark is the time Lean's kernel takes for one evaluation on normal operands; as written goes through the public operation, and the other mark is the term after the rewrite of float_decide. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).

![Three rows, one per theorem, on a logarithmic time axis: an open circle for decide +kernel and a filled circle for float_decide in Lean, joined by a bar, and a triangle and a square for the same result in Coq by conversion and by vm_compute.](../figures/kernel-loops.png "Time to check a theorem about a loop of 1,000 floating-point operations: FloatLib by decide +kernel and by float_decide, and Flocq 4.2.2 in Coq 8.20.1. A mark is the time the proof checker spends on a theorem that states the encoding of the loop's result. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.")

**Figure 4.** Time to check a theorem about a loop of 1,000 floating-point operations: FloatLib by decide +kernel and by float_decide, and Flocq 4.2.2 in Coq 8.20.1. A mark is the time the proof checker spends on a theorem that states the encoding of the loop's result. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.

![5 panels of horizontal bars, one panel per family of proofs and one bar per checker, each bar ending in its time in seconds; a hatched grey bar is a run that ended without a verdict.](../figures/kernel-checkers.png "Time the independent checkers of Lean proofs take on the kernel proofs of FloatLib, by family of proofs. A bar is the time of one check of a family with everything it imports, and a hatched bar is a run that ended without a verdict, at the time it stopped. The checkers ran once, and the timing mode does not run them again.")

**Figure 5.** Time the independent checkers of Lean proofs take on the kernel proofs of FloatLib, by family of proofs. A bar is the time of one check of a family with everything it imports, and a hatched bar is a run that ended without a verdict, at the time it stopped. The checkers ran once, and the timing mode does not run them again.

<!-- end of figures -->
