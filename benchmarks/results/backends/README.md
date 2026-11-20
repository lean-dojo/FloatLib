# Benchmark suite: kernel and compiled code

This directory records the suite sections of the timing mode of `benchmarks/plots/figures.py`, which starts `benchmarks/suite/run.sh` section by section: Lean v4.36.0, Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20. Other jobs were running, so read the tables as ratios. `../figures/measured.json` has the exit code and the time of every section.

The timing mode does not run Coq. The two Coq columns of the matched loops are the ones recorded on 2026-11-15 with Coq 8.20.1 and Flocq 4.2.2 in the image `leanfloat-flocq-bench:4.2.2`, one container at a time with 8 GB and two CPUs (`../figures/recorded/coq-flocq.csv`); in that run Coq printed the value that Lean computed in every row.

The figures of these tables are in `../figures/` and are described in [`../FIGURES.md`](../FIGURES.md): `kernel-binary`, `kernel-operands`, `kernel-vs-coq`, `kernel-families`, `kernel-all-pairs` and `compiled-precision`.

Every number is a time measured on one shared machine. The CSV files next to this file hold the same numbers.

## Kernel time per operation, binary formats

Microseconds of kernel time for one operation as `float_decide` rewrites it, nearest
even, eight operand triples per cell, the fastest of three runs
(`benchmarks/kernel/run.sh kernel 8 3`). `e8f15` is a custom layout of 24 bits and
`e15f64` one of 80 bits.

| format | bits | operands | add | sub | mul | div | sqrt | fma |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| e4m3 | 8 | normal | 113 | 123 | 66 | 80 | 75 | 119 |
| e4m3 | 8 | subnormal | 126 | 114 | 109 | 99 | 95 | 122 |
| e4m3 | 8 | special | 141 | 138 | 115 | 120 | 77 | 131 |
| e5m2 | 8 | normal | 118 | 127 | 66 | 81 | 75 | 119 |
| e5m2 | 8 | subnormal | 121 | 144 | 129 | 100 | 75 | 120 |
| e5m2 | 8 | special | 244 | 225 | 174 | 157 | 112 | 197 |
| binary16 | 16 | normal | 132 | 120 | 70 | 83 | 80 | 122 |
| binary16 | 16 | subnormal | 107 | 115 | 127 | 109 | 100 | 118 |
| binary16 | 16 | special | 250 | 230 | 179 | 161 | 114 | 207 |
| bfloat16 | 16 | normal | 115 | 131 | 70 | 83 | 78 | 118 |
| bfloat16 | 16 | subnormal | 117 | 116 | 139 | 105 | 100 | 119 |
| bfloat16 | 16 | special | 244 | 232 | 182 | 162 | 115 | 204 |
| e8f15 | 24 | normal | 123 | 125 | 69 | 84 | 68 | 135 |
| e8f15 | 24 | subnormal | 106 | 119 | 121 | 107 | 100 | 120 |
| e8f15 | 24 | special | 248 | 235 | 184 | 161 | 114 | 209 |
| binary32 | 32 | normal | 120 | 121 | 67 | 81 | 78 | 121 |
| binary32 | 32 | subnormal | 108 | 116 | 122 | 106 | 99 | 122 |
| binary32 | 32 | special | 248 | 234 | 182 | 159 | 116 | 209 |
| binary64 | 64 | normal | 111 | 121 | 72 | 86 | 83 | 141 |
| binary64 | 64 | subnormal | 109 | 117 | 143 | 107 | 104 | 141 |
| binary64 | 64 | special | 262 | 244 | 187 | 163 | 122 | 236 |
| e15f64 | 80 | normal | 117 | 131 | 76 | 90 | 89 | 164 |
| e15f64 | 80 | subnormal | 110 | 121 | 152 | 111 | 113 | 157 |
| e15f64 | 80 | special | 299 | 277 | 233 | 208 | 154 | 311 |
| binary128 | 128 | normal | 119 | 129 | 76 | 90 | 90 | 196 |
| binary128 | 128 | subnormal | 115 | 123 | 163 | 116 | 118 | 193 |
| binary128 | 128 | special | 414 | 367 | 312 | 268 | 223 | 439 |
| binary256 | 256 | normal | 126 | 141 | 76 | 92 | 91 | 212 |
| binary256 | 256 | subnormal | 127 | 129 | 208 | 127 | 125 | 201 |
| binary256 | 256 | special | 448 | 403 | 396 | 270 | 224 | 451 |
| binary512 | 512 | normal | 141 | 149 | 76 | 91 | 162 | 223 |
| binary512 | 512 | subnormal | 140 | 151 | 217 | 177 | 199 | 217 |
| binary512 | 512 | special | 452 | 423 | 365 | 312 | 278 | 473 |
| binary1024 | 1024 | normal | 145 | 152 | 77 | 93 | 207 | 229 |
| binary1024 | 1024 | subnormal | 145 | 157 | 244 | 176 | 278 | 237 |
| binary1024 | 1024 | special | 472 | 453 | 374 | 328 | 304 | 488 |
| binary4096 | 4096 | normal | 156 | 158 | 82 | 104 | 283 | 258 |
| binary4096 | 4096 | subnormal | 159 | 169 | 252 | 199 | 390 | 252 |
| binary4096 | 4096 | special | 485 | 463 | 402 | 350 | 334 | 523 |

## The same loops in Lean's kernel and in Coq with Flocq

Microseconds per operation in a loop of 100 operations (10 from 512 bits on), on the
same operands: Lean's kernel on the rewritten term (`#kernel_cost rewritten`), and Coq
8.20.1 with Flocq 4.2.2 (`BinarySingleNaN`, `mode_NE`) under `vm_compute` and under
`lazy`, in a container with 8 GB and two CPUs. `no result` means that the evaluation
did not finish within 300 seconds or ran out of the 8 GB. `values` says whether Coq
printed the value that Lean computed.

| format | operation | Lean kernel (µs) | Flocq `vm_compute` (µs) | Flocq `lazy` (µs) | values |
| --- | --- | ---: | ---: | ---: | --- |
| binary32 | add | 39 | 100 | 1,450 | same when Coq ran |
| binary32 | mul | 45 | 110 | 430 | same when Coq ran |
| binary32 | div | 57 | 190 | 1,280 | same when Coq ran |
| binary32 | sqrt | 64 | 250 | 1,820 | same when Coq ran |
| binary32 | fma | 87 | 120 | 930 | same when Coq ran |
| binary64 | add | 40 | 280 | 1,580 | same when Coq ran |
| binary64 | mul | 47 | 380 | 1,310 | same when Coq ran |
| binary64 | div | 58 | 670 | 7,180 | same when Coq ran |
| binary64 | sqrt | 71 | 1,460 | 2,730 | same when Coq ran |
| binary64 | fma | 108 | 260 | 3,360 | same when Coq ran |
| binary128 | add | 44 | 3,310 | 2,070 | same when Coq ran |
| binary128 | mul | 51 | 3,350 | 6,580 | same when Coq ran |
| binary128 | div | 67 | 3,630 | 23,200 | same when Coq ran |
| binary128 | sqrt | 79 | 1,720 | 8,800 | same when Coq ran |
| binary128 | fma | 150 | 3,950 | 9,460 | same when Coq ran |
| binary256 | add | 45 | 45,380 | 2,690 | same when Coq ran |
| binary256 | mul | 53 | 84,320 | 23,250 | same when Coq ran |
| binary256 | div | 64 | 97,710 | 85,210 | same when Coq ran |
| binary256 | sqrt | 89 | 6,600 | 34,220 | same when Coq ran |
| binary256 | fma | 187 | 56,800 | 50,770 | same when Coq ran |
| binary512 | add | 62 | 1,673,800 | 16,000 | same when Coq ran |
| binary512 | mul | 71 | 2,213,400 | 122,700 | same when Coq ran |
| binary512 | div | 83 | no result | 410,500 | same when Coq ran |
| binary512 | sqrt | 106 | no result | 160,000 | same when Coq ran |
| binary512 | fma | 204 | no result | 175,400 | same when Coq ran |
| binary1024 | add | 63 | no result | 21,600 | same when Coq ran |
| binary1024 | mul | 71 | no result | 531,000 | same when Coq ran |
| binary1024 | div | 84 | no result | 1,550,100 | same when Coq ran |
| binary1024 | sqrt | 130 | no result | 671,900 | same when Coq ran |
| binary1024 | fma | 209 | no result | 788,900 | same when Coq ran |
| binary4096 | add | 65 | no result | 72,600 | same when Coq ran |
| binary4096 | mul | 75 | no result | 10,535,200 | same when Coq ran |
| binary4096 | div | 89 | no result | 26,733,500 | same when Coq ran |
| binary4096 | sqrt | 275 | no result | 11,169,200 | same when Coq ran |
| binary4096 | fma | 249 | no result | 14,328,800 | same when Coq ran |

## Kernel time of one operation, other families

Median microseconds of one kernel evaluation of the public operation on stored codes,
as written and after the rewrite with the tagged kernel rules (`#kernel_cost`,
`benchmarks/suite/Families.lean`). A single evaluation includes about 100 microseconds
of fixed work that a loop pays once. `no rule` means that no tagged rule applies, so
`float_decide` evaluates the operation as written. A row that compares a rational
result with a constant includes about 800 microseconds for that comparison.

| operation | as written (µs) | with the tagged rules (µs) |
| --- | ---: | ---: |
| fixed-point(2,8) add | 938 | 24 |
| fixed-point(2,8) sub | 956 | 22 |
| logarithmic(10) mul | 1,263 | 98 |
| p3109-binary8p4se add | 5,377 | 273 |
| p3109-binary8p4se mul | 5,427 | 274 |
| p3109-binary8p4se div | 6,147 | 271 |
| posit8 add | 9,741 | 235 |
| posit8 mul | 9,434 | 183 |
| posit8 div | 15,187 | 203 |
| posit16 add | 12,209 | 244 |
| posit16 mul | 9,009 | 192 |
| posit32 add | 11,542 | 247 |
| posit32 mul | 9,099 | 192 |
| posit32 div | 28,454 | 210 |
| posit64 add | 10,994 | 253 |
| posit64 mul | 10,103 | 205 |
| posit16 quire 3 + 3 * 5, rounded | 33,781 | 353 |
| posit32 literal 0.1 | 86,866 | 134 |
| posit16 literals 1.5 + 2.25 | 101,472 | 465 |
| decimal32 add | 6,994 | 164 |
| decimal64 add | 8,338 | 168 |
| decimal64 mul | 7,253 | 165 |
| decimal64 add-rounded | 6,196 | 229 |
| decimal128 add | 9,022 | 168 |
| mx-e2m1 quantize | 40,316 | 336 |
| mx-e2m3 quantize | 185,122 | 346 |
| mx-e4m3 quantize | 806,602 | 351 |
| mx-e5m2 quantize | 855,409 | 340 |
| mx-int8 quantize | 610,411 | 261 |
| mx-e4m3 block of 4, one element | 752,144 | 7,249 |
| mx-e4m3 block of 32, one element | 789,866 | 23,884 |
| mx-e4m3 dequantize (value of a word, compared with 9/4) | 2,532 | 506 |
| mx-e4m3 block of 4, scale (compared with 1/32) | 11,674 | 5,834 |

## Statements about all 65,536 pairs of encodings

Seconds of kernel time to check one statement about all pairs: the loop of
`float_decide` over the pairs (`benchmarks/kernel/Exhaustive.lean`) and one run of each
side on rows of 65,536 lanes (`lane_decide`, `benchmarks/suite/Lanes.lean`). The lane
time is the sum over the lane widths that were tried (`attempts`): a run that does not
fit lanes of 16 bits is repeated with 32 and then 64. The binary16 rows cover a slice
of 65,536 pairs of encodings. `add-table` is the kernel check of one packed table.

| statement | method | seconds | lane widths tried |
| --- | --- | ---: | ---: |
| e4m3 add-commutes | float_decide loop | 18.60 |  |
| e4m3 mul-commutes | float_decide loop | 23.40 |  |
| e4m3 add-commutes | lane_decide | 2.40 | 2 |
| e4m3 mul-commutes | lane_decide | 0.76 | 1 |
| e5m2 add-commutes | lane_decide | 1.92 | 2 |
| e5m2 mul-commutes | lane_decide | 1.59 | 2 |
| binary16-slice add-commutes | lane_decide | 3.57 | 3 |
| binary16-slice mul-commutes | lane_decide | 1.54 | 2 |
| e4m3 add-table | lane_decide | 3.11 | 2 |

## Compiled code

### FloatLib, six operations at 17 significand precisions

Nanoseconds per compiled public operation (`execFloatSweep all`, one run, loop
time divided by the iteration count). The precision is the number of
significand bits: 24 is binary32, 53 binary64, 113 binary128. `compiled-sweep.csv`
also records the backend that the planner selected for each cell.

| significand bits | add | sub | mul | div | sqrt | fma |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 121 | 118 | 118 | 120 | 23 | 122 |
| 3 | 119 | 120 | 120 | 166 | 23 | 122 |
| 4 | 122 | 120 | 120 | 124 | 23 | 123 |
| 5 | 121 | 120 | 128 | 125 | 23 | 1,219 |
| 6 | 16 | 14 | 13 | 55 | 23 | 35 |
| 7 | 16 | 16 | 13 | 55 | 25 | 37 |
| 8 | 18 | 17 | 13 | 53 | 23 | 24 |
| 11 | 19 | 15 | 11 | 55 | 23 | 29 |
| 24 | 26 | 25 | 20 | 51 | 17 | 30 |
| 53 | 17 | 16 | 11 | 58 | 91 | 115 |
| 113 | 69 | 70 | 38 | 186 | 210 | 129 |
| 161 | 1,883 | 1,902 | 2,184 | 1,974 | 4,505 | 2,347 |
| 237 | 1,805 | 1,796 | 1,720 | 2,032 | 4,526 | 2,294 |
| 493 | 1,859 | 1,956 | 1,795 | 2,652 | 5,479 | 7,479 |
| 1024 | 1,944 | 2,193 | 2,124 | 2,232 | 6,674 | 2,716 |
| 2048 | 2,125 | 2,842 | 2,655 | 2,791 | 10,039 | 3,402 |
| 4096 | 2,373 | 3,118 | 8,274 | 4,537 | 14,058 | 10,124 |

### FP8 formats

Nanoseconds per compiled operation (`execFloatFP8Bench`, one run): the nominal
type of the format, whose capability is static, and the same layout given as a
descriptor at run time.

| format | type | add | sub | mul | div | sqrt | fma |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| OCP E4M3 | nominal | 18 | 18 | 18 | 18 | 18 | 1,119 |
| OCP E4M3 | descriptor | 669 | 669 | 643 | 717 | 669 | 5,007 |
| ONNX E4M3FNUZ | nominal | 18 | 18 | 18 | 18 | 44 | 735 |
| ONNX E4M3FNUZ | descriptor | 650 | 668 | 640 | 709 | 650 | 3,705 |
| OCP E5M2 | nominal | 18 | 18 | 18 | 18 | 19 | 650 |
| OCP E5M2 | descriptor | 818 | 799 | 802 | 948 | 830 | 1,866 |
| ONNX E5M2FNUZ | nominal | 18 | 18 | 18 | 18 | 18 | 738 |
| ONNX E5M2FNUZ | descriptor | 642 | 647 | 640 | 729 | 645 | 3,604 |

### Posits

Median nanoseconds per compiled posit operation over nine trials
(`benchmarks/scripts/posit.sh`), by the total width of the posit.

| bits | add | sub | mul | div | sqrt | fma |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 20 | 20 | 20 | 20 | 21 | 77 |
| 3 | 20 | 20 | 20 | 20 | 21 | 91 |
| 4 | 20 | 20 | 20 | 20 | 21 | 96 |
| 5 | 20 | 20 | 20 | 20 | 21 | 102 |
| 6 | 20 | 20 | 20 | 20 | 21 | 108 |
| 7 | 20 | 20 | 20 | 20 | 21 | 111 |
| 8 | 95 | 95 | 73 | 207 | 21 | 112 |
| 16 | 109 | 105 | 83 | 242 | 200 | 129 |
| 32 | 105 | 104 | 83 | 270 | 245 | 129 |
| 64 | 105 | 108 | 162 | 344 | 533 | 236 |
| 128 | 957 | 960 | 995 | 5,002 | 6,498 | 4,865 |
| 256 | 4,839 | 4,517 | 4,625 | 5,561 | 7,477 | 6,067 |
| 512 | 4,918 | 4,630 | 4,783 | 5,728 | 9,249 | 6,279 |
| 1024 | 5,424 | 5,105 | 5,315 | 6,487 | 13,211 | 6,653 |
| 2048 | 5,565 | 5,227 | 5,913 | 7,837 | 25,964 | 7,539 |
| 4096 | 6,374 | 5,889 | 8,090 | 12,188 | 72,427 | 10,008 |

### FloatLib next to MPFR, Berkeley SoftFloat and the native FPU

Nanoseconds per operation in the scalar dependency chain of
`benchmarks/scripts/format-comparison.sh` (one development trial, calibrated loops of
about 200 ms). MPFR runs at the precision, exponent range and rounding of the binary
format of that width. SoftFloat and the native FPU exist for binary32 and binary64.
The posit column is FloatLib's posit of the same storage width.

| bits | operation | FloatLib | MPFR | SoftFloat | native FPU | FloatLib posit |
| ---: | --- | ---: | ---: | ---: | ---: | ---: |
| 2 | add |  |  |  |  | 21 |
| 2 | sub |  |  |  |  | 22 |
| 2 | mul |  |  |  |  | 21 |
| 2 | div |  |  |  |  | 21 |
| 2 | sqrt |  |  |  |  | 21 |
| 2 | fma |  |  |  |  | 78 |
| 3 | add |  |  |  |  | 22 |
| 3 | sub |  |  |  |  | 21 |
| 3 | mul |  |  |  |  | 21 |
| 3 | div |  |  |  |  | 21 |
| 3 | sqrt |  |  |  |  | 21 |
| 3 | fma |  |  |  |  | 96 |
| 4 | add | 170 | 33 |  |  | 21 |
| 4 | sub | 168 | 32 |  |  | 21 |
| 4 | mul | 169 | 30 |  |  | 21 |
| 4 | div | 180 | 34 |  |  | 21 |
| 4 | sqrt | 84 | 39 |  |  | 21 |
| 4 | fma | 151 | 73 |  |  | 107 |
| 5 | add | 189 | 41 |  |  | 21 |
| 5 | sub | 193 | 38 |  |  | 21 |
| 5 | mul | 188 | 42 |  |  | 21 |
| 5 | div | 201 | 59 |  |  | 21 |
| 5 | sqrt | 83 | 51 |  |  | 21 |
| 5 | fma | 190 | 93 |  |  | 133 |
| 6 | add | 217 | 35 |  |  | 21 |
| 6 | sub | 215 | 34 |  |  | 21 |
| 6 | mul | 204 | 39 |  |  | 21 |
| 6 | div | 223 | 40 |  |  | 21 |
| 6 | sqrt | 81 | 41 |  |  | 21 |
| 6 | fma | 220 | 58 |  |  | 120 |
| 7 | add | 244 | 36 |  |  | 21 |
| 7 | sub | 235 | 35 |  |  | 22 |
| 7 | mul | 206 | 40 |  |  | 22 |
| 7 | div | 223 | 36 |  |  | 21 |
| 7 | sqrt | 79 | 39 |  |  | 21 |
| 7 | fma | 219 | 56 |  |  | 115 |
| 8 | add | 238 | 37 |  |  | 21 |
| 8 | sub | 236 | 36 |  |  | 24 |
| 8 | mul | 203 | 35 |  |  | 21 |
| 8 | div | 220 | 37 |  |  | 21 |
| 8 | sqrt | 81 | 40 |  |  | 21 |
| 8 | fma | 1,312 | 55 |  |  | 121 |
| 16 | add | 150 | 38 |  |  | 124 |
| 16 | sub | 134 | 35 |  |  | 120 |
| 16 | mul | 101 | 34 |  |  | 91 |
| 16 | div | 156 | 36 |  |  | 243 |
| 16 | sqrt | 91 | 40 |  |  | 201 |
| 16 | fma | 138 | 56 |  |  | 137 |
| 32 | add | 164 | 37 | 23 | 8.4 | 120 |
| 32 | sub | 143 | 35 | 23 | 8.6 | 127 |
| 32 | mul | 97 | 33 | 18 | 8.4 | 92 |
| 32 | div | 157 | 40 | 26 | 11 | 307 |
| 32 | sqrt | 83 | 41 | 26 | 11 | 252 |
| 32 | fma | 151 | 58 | 30 | 8.9 | 138 |
| 64 | add | 394 | 36 | 22 | 8.4 | 122 |
| 64 | sub | 355 | 38 | 21 | 8.3 | 120 |
| 64 | mul | 322 | 32 | 18 | 8.3 | 163 |
| 64 | div | 398 | 35 | 33 | 11 | 312 |
| 64 | sqrt | 163 | 44 | 28 | 13 | 522 |
| 64 | fma | 490 | 59 | 27 | 9.2 | 241 |
| 128 | add | 74 | 39 |  |  | 956 |
| 128 | sub | 73 | 38 |  |  | 958 |
| 128 | mul | 45 | 37 |  |  | 997 |
| 128 | div | 190 | 47 |  |  | 5,270 |
| 128 | sqrt | 214 | 56 |  |  | 6,383 |
| 128 | fma | 133 | 88 |  |  | 5,001 |
| 256 | add | 1,860 | 53 |  |  | 4,895 |
| 256 | sub | 1,813 | 52 |  |  | 4,403 |
| 256 | mul | 1,757 | 61 |  |  | 4,522 |
| 256 | div | 1,894 | 135 |  |  | 5,437 |
| 256 | sqrt | 4,578 | 172 |  |  | 7,334 |
| 256 | fma | 2,306 | 102 |  |  | 6,015 |
| 512 | add | 1,879 | 58 |  |  | 5,085 |
| 512 | sub | 1,867 | 55 |  |  | 4,678 |
| 512 | mul | 1,832 | 98 |  |  | 4,717 |
| 512 | div | 2,050 | 190 |  |  | 5,594 |
| 512 | sqrt | 5,460 | 324 |  |  | 9,052 |
| 512 | fma | 2,507 | 146 |  |  | 6,147 |
| 1024 | add | 1,941 | 66 |  |  | 5,127 |
| 1024 | sub | 1,935 | 61 |  |  | 4,885 |
| 1024 | mul | 2,018 | 174 |  |  | 5,345 |
| 1024 | div | 2,298 | 329 |  |  | 6,379 |
| 1024 | sqrt | 6,762 | 523 |  |  | 13,256 |
| 1024 | fma | 2,799 | 283 |  |  | 7,163 |
| 2048 | add | 2,083 | 86 |  |  | 5,460 |
| 2048 | sub | 2,115 | 78 |  |  | 5,197 |
| 2048 | mul | 2,793 | 439 |  |  | 5,967 |
| 2048 | div | 2,879 | 739 |  |  | 7,620 |
| 2048 | sqrt | 8,743 | 909 |  |  | 26,007 |
| 2048 | fma | 3,448 | 711 |  |  | 7,724 |
| 4096 | add | 2,512 | 121 |  |  | 6,286 |
| 4096 | sub | 2,548 | 109 |  |  | 6,271 |
| 4096 | mul | 4,282 | 1,322 |  |  | 8,079 |
| 4096 | div | 4,455 | 2,111 |  |  | 12,026 |
| 4096 | sqrt | 14,399 | 1,870 |  |  | 83,493 |
| 4096 | fma | 4,990 | 1,801 |  |  | 9,925 |

<!-- figures: this section is written by benchmarks/plots/figures.py draw -->

## Figures

The captions, alt texts, notes and CSV columns of these figures are in [FIGURES.md](../FIGURES.md).

![5 panels of lines, one per operation: time per operation against format width for FloatLib in Lean's kernel and for Flocq in Coq under vm_compute and under lazy, with crosses along the top edge at the widths where Coq gave no result.](../figures/kernel-vs-coq.png "Time of one floating-point operation inside the proof checker: FloatLib in Lean's kernel against Flocq 4.2.2 in Coq 8.20.1 under vm_compute and under lazy. A point is the time per operation in a loop of 100 operations (10 from 512 bits on) on the same operands; a cross at the top marks a width where Coq gave no result within 8 GB and 300 seconds. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.")

**Figure 1.** Time of one floating-point operation inside the proof checker: FloatLib in Lean's kernel against Flocq 4.2.2 in Coq 8.20.1 under vm_compute and under lazy. A point is the time per operation in a loop of 100 operations (10 from 512 bits on) on the same operands; a cross at the top marks a width where Coq gave no result within 8 GB and 300 seconds. Both axes are logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20); the Coq times were recorded on 2026-11-15 in a container with 8 GB and two CPUs.

![53 rows, one per operation of a format family, on a logarithmic time axis: an open circle for the kernel time of the operation as written and a filled circle for the operation with the kernel rules, joined by a bar; the last 12 rows, the block formats, have a filled circle only.](../figures/kernel-families.png "Kernel time of one operation outside the binary interchange formats, as written and with the kernel rules of FloatLib: fixed point, logarithmic, P3109, posits and the quire, OCP MX elements and blocks, decimal, OCP FP8 and NVFP4 blocks. A mark is the time Lean's kernel takes for one evaluation; a row with one mark times the rewritten term alone. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

**Figure 2.** Kernel time of one operation outside the binary interchange formats, as written and with the kernel rules of FloatLib: fixed point, logarithmic, P3109, posits and the quire, OCP MX elements and blocks, decimal, OCP FP8 and NVFP4 blocks. A mark is the time Lean's kernel takes for one evaluation; a row with one mark times the rewritten term alone. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).

![7 rows, one per statement, on a logarithmic time axis: an open circle for the loop of float_decide and a filled circle for lane_decide, joined by a bar where both were run.](../figures/kernel-all-pairs.png "Kernel time to decide one statement about all 65,536 pairs of encodings, by the loop of float_decide and by lane_decide in FloatLib. A mark is the time Lean's kernel takes for a statement about all pairs of an 8-bit format, or about a slice of 65,536 pairs of binary16. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

**Figure 3.** Kernel time to decide one statement about all 65,536 pairs of encodings, by the loop of float_decide and by lane_decide in FloatLib. A mark is the time Lean's kernel takes for a statement about all pairs of an 8-bit format, or about a slice of 65,536 pairs of binary16. The time axis is logarithmic, and lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).

![Six panels of lines, one per arithmetic operation: compiled time per operation against format width for FloatLib and MPFR up to 4,096 bits, with SoftFloat, the host processor and FloatLib's public calls as short series at 32 and 64 bits, where the public calls lie below the FloatLib line in every panel.](../figures/compiled-precision.png "Time per operation against format width, both on logarithmic scales. In the comparison with MPFR, SoftFloat and the host processor, each result selects the next input. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20). The open circles show public FloatLib calls at 32 and 64 bits, timed on a fixed cycle of inputs (median of nine trials on one pinned core, Lean 4.35.0, 2026-10-31).")

**Figure 4.** Time per operation against format width, both on logarithmic scales. In the comparison with MPFR, SoftFloat and the host processor, each result selects the next input. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20). The open circles show public FloatLib calls at 32 and 64 bits, timed on a fixed cycle of inputs (median of nine trials on one pinned core, Lean 4.35.0, 2026-10-31).

<!-- end of figures -->
