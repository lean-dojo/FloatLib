# Benchmark suite: kernel and compiled code

This directory records the suite sections of one timing run of `benchmarks/plots/figures.py`, which starts `benchmarks/suite/run.sh` section by section: commit `e58d3251`, Lean v4.36.0, Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18. Other jobs were running, so read the tables as ratios. `../figures/measured.json` has the exit code and the time of every section.

The timing mode does not run Coq. The two Coq columns of the matched loops are the ones recorded on 2026-11-15 with Coq 8.20.1 and Flocq 4.2.2 in the image `leanfloat-flocq-bench:4.2.2`, one container at a time with 8 GB and two CPUs (`../figures/recorded/coq-flocq.csv`); in that run Coq printed the value that Lean computed in every row.

The figures of these tables are in `../figures/` and are described in [`../FIGURES.md`](../FIGURES.md): `kernel-binary`, `kernel-operands`, `kernel-vs-coq`, `kernel-families`, `kernel-all-pairs` and `compiled-precision`.

Every number is a time measured on one shared machine. The CSV files next to this file hold the same numbers.

## Kernel time per operation, binary formats

Microseconds of kernel time for one operation as `float_decide` rewrites it, nearest
even, eight operand triples per cell, the fastest of three runs
(`benchmarks/kernel/run.sh kernel 8 3`). `e8f15` is a custom layout of 24 bits and
`e15f64` one of 80 bits.

| format | bits | operands | commit | add | sub | mul | div | sqrt | fma |
| --- | ---: | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| e4m3 | 8 | normal | now | 118 | 125 | 80 | 97 | 90 | 152 |
| e4m3 | 8 | subnormal | now | 133 | 113 | 124 | 115 | 111 | 172 |
| e4m3 | 8 | special | now | 156 | 161 | 163 | 220 | 108 | 196 |
| e5m2 | 8 | normal | now | 120 | 128 | 77 | 94 | 87 | 149 |
| e5m2 | 8 | subnormal | now | 137 | 157 | 145 | 114 | 90 | 151 |
| e5m2 | 8 | special | now | 288 | 261 | 253 | 241 | 158 | 271 |
| binary16 | 16 | normal | now | 161 | 120 | 82 | 98 | 91 | 139 |
| binary16 | 16 | subnormal | now | 106 | 115 | 146 | 121 | 114 | 135 |
| binary16 | 16 | special | now | 294 | 265 | 262 | 250 | 163 | 275 |
| bfloat16 | 16 | normal | now | 103 | 119 | 82 | 112 | 90 | 140 |
| bfloat16 | 16 | subnormal | now | 105 | 116 | 154 | 122 | 112 | 136 |
| bfloat16 | 16 | special | now | 291 | 264 | 264 | 247 | 163 | 278 |
| e8f15 | 24 | normal | now | 134 | 124 | 81 | 98 | 100 | 143 |
| e8f15 | 24 | subnormal | now | 106 | 115 | 140 | 124 | 117 | 140 |
| e8f15 | 24 | special | now | 303 | 263 | 264 | 247 | 162 | 284 |
| binary32 | 32 | normal | now | 119 | 118 | 82 | 98 | 90 | 140 |
| binary32 | 32 | subnormal | now | 106 | 117 | 138 | 122 | 111 | 143 |
| binary32 | 32 | special | now | 296 | 268 | 260 | 246 | 162 | 280 |
| binary64 | 64 | normal | now | 111 | 124 | 84 | 102 | 94 | 164 |
| binary64 | 64 | subnormal | now | 110 | 119 | 161 | 123 | 120 | 169 |
| binary64 | 64 | special | now | 304 | 281 | 266 | 246 | 170 | 310 |
| e15f64 | 80 | normal | now | 117 | 132 | 88 | 105 | 106 | 183 |
| e15f64 | 80 | subnormal | now | 109 | 120 | 170 | 132 | 127 | 176 |
| e15f64 | 80 | special | now | 332 | 308 | 307 | 293 | 205 | 390 |
| binary128 | 128 | normal | now | 119 | 132 | 88 | 106 | 103 | 216 |
| binary128 | 128 | subnormal | now | 111 | 122 | 179 | 131 | 131 | 212 |
| binary128 | 128 | special | now | 455 | 394 | 384 | 353 | 276 | 513 |
| binary256 | 256 | normal | now | 127 | 139 | 89 | 106 | 103 | 228 |
| binary256 | 256 | subnormal | now | 117 | 129 | 224 | 139 | 135 | 226 |
| binary256 | 256 | special | now | 486 | 432 | 444 | 361 | 283 | 534 |
| binary512 | 512 | normal | now | 142 | 150 | 89 | 106 | 178 | 241 |
| binary512 | 512 | subnormal | now | 141 | 149 | 230 | 183 | 211 | 237 |
| binary512 | 512 | special | now | 493 | 455 | 453 | 406 | 327 | 551 |
| binary1024 | 1024 | normal | now | 146 | 153 | 91 | 107 | 225 | 252 |
| binary1024 | 1024 | subnormal | now | 146 | 156 | 240 | 189 | 292 | 247 |
| binary1024 | 1024 | special | now | 505 | 469 | 465 | 419 | 345 | 565 |
| binary4096 | 4096 | normal | now | 160 | 161 | 94 | 116 | 295 | 287 |
| binary4096 | 4096 | subnormal | now | 154 | 169 | 274 | 218 | 410 | 275 |
| binary4096 | 4096 | special | now | 534 | 514 | 495 | 458 | 388 | 588 |

## The same loops in Lean's kernel and in Coq with Flocq

Microseconds per operation in a loop of 100 operations (10 from 512 bits on), on the
same operands: Lean's kernel on the rewritten term (`#kernel_cost rewritten`), and Coq
8.20.1 with Flocq 4.2.2 (`BinarySingleNaN`, `mode_NE`) under `vm_compute` and under
`lazy`, in a container with 8 GB and two CPUs. `no result` means that the evaluation
did not finish within 300 seconds or ran out of the 8 GB. `values` says whether Coq
printed the value that Lean computed.

| format | operation | Lean kernel (µs) | Flocq `vm_compute` (µs) | Flocq `lazy` (µs) | values |
| --- | --- | ---: | ---: | ---: | --- |
| binary32 | add | 52 | 100 | 1,450 | same when Coq ran |
| binary32 | mul | 54 | 110 | 430 | same when Coq ran |
| binary32 | div | 60 | 190 | 1,280 | same when Coq ran |
| binary32 | sqrt | 67 | 250 | 1,820 | same when Coq ran |
| binary32 | fma | 93 | 120 | 930 | same when Coq ran |
| binary64 | add | 41 | 280 | 1,580 | same when Coq ran |
| binary64 | mul | 46 | 380 | 1,310 | same when Coq ran |
| binary64 | div | 59 | 670 | 7,180 | same when Coq ran |
| binary64 | sqrt | 69 | 1,460 | 2,730 | same when Coq ran |
| binary64 | fma | 116 | 260 | 3,360 | same when Coq ran |
| binary128 | add | 46 | 3,310 | 2,070 | same when Coq ran |
| binary128 | mul | 51 | 3,350 | 6,580 | same when Coq ran |
| binary128 | div | 64 | 3,630 | 23,200 | same when Coq ran |
| binary128 | sqrt | 78 | 1,720 | 8,800 | same when Coq ran |
| binary128 | fma | 151 | 3,950 | 9,460 | same when Coq ran |
| binary256 | add | 46 | 45,380 | 2,690 | same when Coq ran |
| binary256 | mul | 54 | 84,320 | 23,250 | same when Coq ran |
| binary256 | div | 64 | 97,710 | 85,210 | same when Coq ran |
| binary256 | sqrt | 77 | 6,600 | 34,220 | same when Coq ran |
| binary256 | fma | 163 | 56,800 | 50,770 | same when Coq ran |
| binary512 | add | 77 | 1,673,800 | 16,000 | same when Coq ran |
| binary512 | mul | 81 | 2,213,400 | 122,700 | same when Coq ran |
| binary512 | div | 95 | no result | 410,500 | same when Coq ran |
| binary512 | sqrt | 117 | no result | 160,000 | same when Coq ran |
| binary512 | fma | 214 | no result | 175,400 | same when Coq ran |
| binary1024 | add | 79 | no result | 21,600 | same when Coq ran |
| binary1024 | mul | 82 | no result | 531,000 | same when Coq ran |
| binary1024 | div | 96 | no result | 1,550,100 | same when Coq ran |
| binary1024 | sqrt | 143 | no result | 671,900 | same when Coq ran |
| binary1024 | fma | 223 | no result | 788,900 | same when Coq ran |
| binary4096 | add | 82 | no result | 72,600 | same when Coq ran |
| binary4096 | mul | 97 | no result | 10,535,200 | same when Coq ran |
| binary4096 | div | 100 | no result | 26,733,500 | same when Coq ran |
| binary4096 | sqrt | 290 | no result | 11,169,200 | same when Coq ran |
| binary4096 | fma | 252 | no result | 14,328,800 | same when Coq ran |

## Kernel time of one operation, other families

Median microseconds of one kernel evaluation of the public operation on stored codes,
as written and after the rewrite with the tagged kernel rules (`#kernel_cost`,
`benchmarks/suite/Families.lean`). A single evaluation includes about 100 microseconds
of fixed work that a loop pays once. `no rule` means that no tagged rule applies, so
`float_decide` evaluates the operation as written. A row that compares a rational
result with a constant includes about 800 microseconds for that comparison.

| operation | as written (µs) | with the tagged rules (µs) |
| --- | ---: | ---: |
| fixed-point(2,8) add | 937 | 272 |
| fixed-point(2,8) sub | 952 | 277 |
| logarithmic(10) mul | 1,268 | 607 |
| p3109-binary8p4se add | 5,235 | 372 |
| p3109-binary8p4se mul | 5,386 | 404 |
| p3109-binary8p4se div | 5,750 | 407 |
| posit8 add | 9,072 | 290 |
| posit8 mul | 9,098 | 251 |
| posit8 div | 13,728 | 272 |
| posit16 add | 9,511 | 302 |
| posit16 mul | 9,390 | 315 |
| posit32 add | 10,499 | 298 |
| posit32 mul | 9,195 | 261 |
| posit32 div | 27,791 | 280 |
| posit64 add | 9,593 | 307 |
| posit64 mul | 10,000 | 298 |
| posit16 quire 3 + 3 * 5, rounded | 32,080 | 432 |
| posit32 literal 0.1 | 62,272 | 195 |
| posit16 literals 1.5 + 2.25 | 79,266 | 589 |
| decimal32 add | 7,001 | 264 |
| decimal64 add | 7,683 | 314 |
| decimal64 mul | 8,510 | 338 |
| decimal64 add-rounded | 6,690 | 420 |
| decimal128 add | 9,214 | 266 |
| mx-e2m1 quantize | 37,323 | 1,332 |
| mx-e2m3 quantize | 163,197 | 1,412 |
| mx-e4m3 quantize | 721,138 | 1,481 |
| mx-e5m2 quantize | 709,388 | 1,490 |
| mx-int8 quantize | 588,828 | 1,200 |
| mx-e4m3 block of 4, one element | 823,184 | 7,969 |
| mx-e4m3 block of 32, one element | 797,545 | 24,605 |
| mx-e4m3 dequantize (value of a word, compared with 9/4) | 2,529 | 575 |
| mx-e4m3 block of 4, scale (compared with 1/32) | 16,038 | 5,814 |

## Statements about all 65,536 pairs of encodings

Seconds of kernel time to check one statement about all pairs: the loop of
`float_decide` over the pairs (`benchmarks/kernel/Exhaustive.lean`) and one run of each
side on rows of 65,536 lanes (`lane_decide`, `benchmarks/suite/Lanes.lean`). The lane
time is the sum over the lane widths that were tried (`attempts`): a run that does not
fit lanes of 16 bits is repeated with 32 and then 64. The binary16 rows cover a slice
of 65,536 pairs of encodings. `add-table` is the kernel check of one packed table.

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

## Compiled code

### FloatLib, six operations at 17 significand precisions

Nanoseconds per compiled public operation (`execFloatSweep all`, one run, loop
time divided by the iteration count). The precision is the number of
significand bits: 24 is binary32, 53 binary64, 113 binary128. `compiled-sweep.csv`
also records the backend that the planner selected for each cell.

| significand bits | add | sub | mul | div | sqrt | fma |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 122 | 120 | 262 | 121 | 23 | 127 |
| 3 | 121 | 121 | 265 | 125 | 23 | 125 |
| 4 | 120 | 175 | 263 | 121 | 23 | 124 |
| 5 | 121 | 122 | 122 | 188 | 23 | 1,224 |
| 6 | 16 | 15 | 11 | 75 | 23 | 35 |
| 7 | 16 | 14 | 13 | 79 | 23 | 36 |
| 8 | 17 | 16 | 13 | 78 | 23 | 26 |
| 11 | 18 | 15 | 12 | 75 | 26 | 32 |
| 24 | 25 | 25 | 18 | 70 | 18 | 31 |
| 53 | 17 | 17 | 11 | 81 | 92 | 114 |
| 113 | 69 | 62 | 38 | 244 | 210 | 128 |
| 161 | 1,838 | 1,916 | 1,856 | 2,689 | 5,685 | 2,339 |
| 237 | 1,993 | 1,798 | 1,705 | 2,330 | 4,472 | 2,290 |
| 493 | 2,287 | 1,850 | 1,800 | 2,012 | 5,358 | 2,436 |
| 1024 | 1,957 | 2,314 | 2,113 | 2,632 | 6,470 | 2,709 |
| 2048 | 2,075 | 4,065 | 2,611 | 3,693 | 8,602 | 3,363 |
| 4096 | 2,391 | 4,742 | 4,252 | 5,917 | 17,384 | 5,076 |

### FP8 formats

Nanoseconds per compiled operation (`execFloatFP8Bench`, one run): the nominal
type of the format, whose capability is static, and the same layout given as a
descriptor at run time.

| format | type | add | sub | mul | div | sqrt | fma |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| OCP E4M3 | nominal | 18 | 23 | 18 | 18 | 18 | 1,087 |
| OCP E4M3 | descriptor | 633 | 626 | 695 | 606 | 612 | 4,747 |
| ONNX E4M3FNUZ | nominal | 18 | 18 | 18 | 18 | 18 | 684 |
| ONNX E4M3FNUZ | descriptor | 613 | 618 | 606 | 608 | 612 | 3,457 |
| OCP E5M2 | nominal | 18 | 18 | 18 | 18 | 18 | 612 |
| OCP E5M2 | descriptor | 766 | 763 | 760 | 784 | 772 | 1,765 |
| ONNX E5M2FNUZ | nominal | 18 | 18 | 18 | 18 | 18 | 727 |
| ONNX E5M2FNUZ | descriptor | 656 | 607 | 618 | 614 | 614 | 3,401 |

### Posits

Median nanoseconds per compiled posit operation over nine trials
(`benchmarks/scripts/posit.sh`), by the total width of the posit.

| bits | add | sub | mul | div | sqrt | fma |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 20 | 20 | 20 | 20 | 21 | 80 |
| 3 | 20 | 20 | 20 | 20 | 21 | 94 |
| 4 | 20 | 20 | 20 | 20 | 21 | 99 |
| 5 | 20 | 20 | 20 | 20 | 21 | 105 |
| 6 | 20 | 20 | 20 | 20 | 21 | 109 |
| 7 | 20 | 20 | 20 | 20 | 21 | 113 |
| 8 | 94 | 97 | 75 | 203 | 21 | 115 |
| 16 | 107 | 110 | 83 | 239 | 202 | 130 |
| 32 | 109 | 110 | 84 | 267 | 245 | 131 |
| 64 | 110 | 107 | 161 | 339 | 519 | 234 |
| 128 | 967 | 964 | 964 | 4,976 | 6,519 | 4,903 |
| 256 | 4,986 | 4,472 | 4,548 | 5,513 | 7,511 | 5,997 |
| 512 | 4,933 | 4,632 | 4,761 | 5,700 | 9,348 | 6,171 |
| 1024 | 5,841 | 5,545 | 5,611 | 6,633 | 13,198 | 6,929 |
| 2048 | 5,735 | 5,315 | 6,149 | 7,613 | 25,855 | 7,476 |
| 4096 | 6,155 | 5,626 | 8,000 | 12,132 | 72,160 | 9,706 |

### FloatLib next to MPFR, Berkeley SoftFloat and the native FPU

Nanoseconds per operation in the scalar dependency chain of
`benchmarks/scripts/format-comparison.sh` (one development trial, calibrated loops of
about 200 ms). MPFR runs at the precision, exponent range and rounding of the binary
format of that width. SoftFloat and the native FPU exist for binary32 and binary64.
The posit column is FloatLib's posit of the same storage width.

| bits | operation | FloatLib | MPFR | SoftFloat | native FPU | FloatLib posit |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 2 | add |  |  |  |  | 21 |
| 2 | sub |  |  |  |  | 21 |
| 2 | mul |  |  |  |  | 21 |
| 2 | div |  |  |  |  | 21 |
| 2 | sqrt |  |  |  |  | 21 |
| 2 | fma |  |  |  |  | 82 |
| 3 | add |  |  |  |  | 21 |
| 3 | sub |  |  |  |  | 21 |
| 3 | mul |  |  |  |  | 21 |
| 3 | div |  |  |  |  | 21 |
| 3 | sqrt |  |  |  |  | 21 |
| 3 | fma |  |  |  |  | 94 |
| 4 | add | 171 | 34 |  |  | 21 |
| 4 | sub | 170 | 32 |  |  | 21 |
| 4 | mul | 171 | 30 |  |  | 21 |
| 4 | div | 202 | 34 |  |  | 21 |
| 4 | sqrt | 82 | 40 |  |  | 21 |
| 4 | fma | 151 | 73 |  |  | 106 |
| 5 | add | 191 | 41 |  |  | 23 |
| 5 | sub | 195 | 39 |  |  | 21 |
| 5 | mul | 204 | 42 |  |  | 21 |
| 5 | div | 199 | 58 |  |  | 26 |
| 5 | sqrt | 81 | 52 |  |  | 22 |
| 5 | fma | 190 | 93 |  |  | 117 |
| 6 | add | 227 | 35 |  |  | 22 |
| 6 | sub | 214 | 34 |  |  | 21 |
| 6 | mul | 204 | 37 |  |  | 21 |
| 6 | div | 221 | 37 |  |  | 21 |
| 6 | sqrt | 83 | 39 |  |  | 22 |
| 6 | fma | 222 | 59 |  |  | 117 |
| 7 | add | 242 | 36 |  |  | 21 |
| 7 | sub | 235 | 37 |  |  | 21 |
| 7 | mul | 216 | 39 |  |  | 21 |
| 7 | div | 225 | 36 |  |  | 21 |
| 7 | sqrt | 80 | 41 |  |  | 21 |
| 7 | fma | 219 | 59 |  |  | 118 |
| 8 | add | 236 | 36 |  |  | 21 |
| 8 | sub | 248 | 36 |  |  | 21 |
| 8 | mul | 210 | 35 |  |  | 22 |
| 8 | div | 219 | 37 |  |  | 21 |
| 8 | sqrt | 79 | 50 |  |  | 21 |
| 8 | fma | 1,569 | 56 |  |  | 123 |
| 16 | add | 150 | 36 |  |  | 127 |
| 16 | sub | 128 | 35 |  |  | 172 |
| 16 | mul | 89 | 33 |  |  | 92 |
| 16 | div | 157 | 36 |  |  | 240 |
| 16 | sqrt | 90 | 40 |  |  | 204 |
| 16 | fma | 137 | 58 |  |  | 135 |
| 32 | add | 161 | 34 | 23 | 8.4 | 120 |
| 32 | sub | 143 | 35 | 23 | 8.4 | 122 |
| 32 | mul | 96 | 33 | 18 | 8.4 | 92 |
| 32 | div | 148 | 36 | 25 | 10 | 257 |
| 32 | sqrt | 82 | 41 | 26 | 11 | 247 |
| 32 | fma | 145 | 55 | 27 | 8.7 | 140 |
| 64 | add | 377 | 38 | 22 | 8.3 | 125 |
| 64 | sub | 350 | 36 | 21 | 8.3 | 122 |
| 64 | mul | 408 | 34 | 18 | 8.3 | 163 |
| 64 | div | 416 | 35 | 34 | 11 | 310 |
| 64 | sqrt | 161 | 44 | 27 | 12 | 522 |
| 64 | fma | 495 | 61 | 27 | 8.6 | 238 |
| 128 | add | 74 | 38 |  |  | 942 |
| 128 | sub | 73 | 38 |  |  | 941 |
| 128 | mul | 45 | 37 |  |  | 997 |
| 128 | div | 191 | 45 |  |  | 4,947 |
| 128 | sqrt | 267 | 54 |  |  | 6,419 |
| 128 | fma | 132 | 92 |  |  | 5,057 |
| 256 | add | 1,829 | 52 |  |  | 4,752 |
| 256 | sub | 1,781 | 51 |  |  | 4,468 |
| 256 | mul | 1,700 | 58 |  |  | 4,795 |
| 256 | div | 1,884 | 132 |  |  | 6,386 |
| 256 | sqrt | 4,732 | 172 |  |  | 7,379 |
| 256 | fma | 2,300 | 101 |  |  | 6,187 |
| 512 | add | 1,941 | 57 |  |  | 4,944 |
| 512 | sub | 1,884 | 56 |  |  | 4,546 |
| 512 | mul | 1,789 | 94 |  |  | 4,717 |
| 512 | div | 2,130 | 195 |  |  | 6,108 |
| 512 | sqrt | 5,378 | 334 |  |  | 9,002 |
| 512 | fma | 2,404 | 141 |  |  | 6,092 |
| 1024 | add | 1,988 | 66 |  |  | 5,120 |
| 1024 | sub | 1,950 | 61 |  |  | 4,781 |
| 1024 | mul | 1,973 | 173 |  |  | 5,312 |
| 1024 | div | 2,223 | 351 |  |  | 8,737 |
| 1024 | sqrt | 6,778 | 521 |  |  | 13,396 |
| 1024 | fma | 2,743 | 278 |  |  | 6,766 |
| 2048 | add | 2,086 | 84 |  |  | 5,456 |
| 2048 | sub | 2,100 | 114 |  |  | 5,162 |
| 2048 | mul | 2,563 | 440 |  |  | 6,216 |
| 2048 | div | 2,851 | 794 |  |  | 8,065 |
| 2048 | sqrt | 9,120 | 1,268 |  |  | 27,423 |
| 2048 | fma | 3,315 | 722 |  |  | 7,561 |
| 4096 | add | 2,386 | 125 |  |  | 6,211 |
| 4096 | sub | 2,354 | 125 |  |  | 5,662 |
| 4096 | mul | 4,304 | 1,315 |  |  | 8,291 |
| 4096 | div | 4,570 | 2,384 |  |  | 12,019 |
| 4096 | sqrt | 14,060 | 1,872 |  |  | 71,724 |
| 4096 | fma | 5,064 | 1,874 |  |  | 10,677 |

<!-- figures: this section is written by benchmarks/plots/figures.py draw -->

## Figures

The captions, alt texts, notes and CSV columns of these figures are in [FIGURES.md](../FIGURES.md).

![5 panels of lines, one per operation: time per operation against format width for FloatLib in Lean's kernel and for Flocq in Coq under vm_compute and under lazy, with crosses along the top edge at the widths where Coq gave no result.](../figures/kernel-vs-coq.png "Time of one floating-point operation inside the proof checker: FloatLib in Lean's kernel against Flocq 4.2.2 in Coq 8.20.1 under vm_compute and under lazy. A point is the time per operation in a loop of 100 operations (10 from 512 bits on) on the same operands; a cross at the top marks a width where Coq gave no result within 8 GB and 300 seconds. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.")

**Figure 1.** Time of one floating-point operation inside the proof checker: FloatLib in Lean's kernel against Flocq 4.2.2 in Coq 8.20.1 under vm_compute and under lazy. A point is the time per operation in a loop of 100 operations (10 from 512 bits on) on the same operands; a cross at the top marks a width where Coq gave no result within 8 GB and 300 seconds. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.

![53 rows, one per operation of a format family, on a logarithmic time axis: an open circle for the kernel time of the operation as written and a filled circle for the operation with the kernel rules, joined by a bar; the last 12 rows, the block formats, have a filled circle only.](../figures/kernel-families.png "Kernel time of one operation outside the binary interchange formats, as written and with the kernel rules of FloatLib: fixed point, logarithmic, P3109, posits and the quire, OCP MX elements and blocks, decimal, OCP FP8 and NVFP4 blocks. A mark is the time Lean's kernel takes for one evaluation; a row with one mark times the rewritten term alone. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).")

**Figure 2.** Kernel time of one operation outside the binary interchange formats, as written and with the kernel rules of FloatLib: fixed point, logarithmic, P3109, posits and the quire, OCP MX elements and blocks, decimal, OCP FP8 and NVFP4 blocks. A mark is the time Lean's kernel takes for one evaluation; a row with one mark times the rewritten term alone. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).

![7 rows, one per statement, on a logarithmic time axis: an open circle for the loop of float_decide and a filled circle for lane_decide, joined by a bar where both were run.](../figures/kernel-all-pairs.png "Kernel time to decide one statement about all 65,536 pairs of encodings, by the loop of float_decide and by lane_decide in FloatLib. A mark is the time Lean's kernel takes for a statement about all pairs of an 8-bit format, or about a slice of 65,536 pairs of binary16. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).")

**Figure 3.** Kernel time to decide one statement about all 65,536 pairs of encodings, by the loop of float_decide and by lane_decide in FloatLib. A mark is the time Lean's kernel takes for a statement about all pairs of an 8-bit format, or about a slice of 65,536 pairs of binary16. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).

![Six panels of lines, one per arithmetic operation: compiled time per operation against format width for FloatLib and MPFR up to 4,096 bits, with SoftFloat and the host processor as short series at 32 and 64 bits.](../figures/compiled-precision.png "Compiled time of one arithmetic operation at every precision: FloatLib against MPFR, Berkeley SoftFloat and the host processor. A point is the time per operation in a scalar dependency chain, with MPFR at the precision, exponent range and rounding of the binary format of that width; SoftFloat and the host exist for binary32 and binary64 only. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).")

**Figure 4.** Compiled time of one arithmetic operation at every precision: FloatLib against MPFR, Berkeley SoftFloat and the host processor. A point is the time per operation in a scalar dependency chain, with MPFR at the precision, exponent range and rounding of the binary format of that width; SoftFloat and the host exist for binary32 and binary64 only. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-18).

<!-- end of figures -->
