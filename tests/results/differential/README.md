# Differential campaigns

Summaries of the differential comparisons. The drivers and references are in `tests/oracles/`,
and `tests/EXTERNAL.md` describes each comparison.

| File | Contents |
| --- | --- |
| `exhaustive16-floatlib.csv` | Every binary16 and bfloat16 addition, subtraction, multiplication, and division pair and every binary32 square root, per direction: cases and value, flag, kernel, or reference disagreements. 154,618,822,656 cases, none disagreeing. |
| `certified-expm1-log1p-binary32.csv` | Certified `expMinus1` and `logPlus1` on all 2^32 binary32 inputs against MPFR. |
| `certified-expm1-log1p-other.csv` | The same functions on every finite binary16 and bfloat16 input and on the distinct entries of CORE-MATH's binary64 `expm1.wc` and `log1p.wc` lists. |
| `ieee2019.csv` | The IEEE 754-2019 operations (`tests/oracles/ieee2019.sh 20000 20261116` with `mpmath`, one row per group): the clause 9.4 to 9.7 operations on every pair of encodings of a six-bit format against brute force, and 199,720 generated cases against Python's `decimal`, exact rational arithmetic and glibc, 225,320 cases. Also: the formatOf operations of clause 5.4.1 with the square root (1,232,256 cases on small formats), the functions of clause 9.2 on binary formats against `mpmath` in the five rounding directions (461,520 cases, value and flags: the small formats exhaustively in each direction, 20 operands per function in each of binary16, binary32 and binary64 in a pseudo-random direction), the decimal reductions (20,000 cases), the decimal scaled products (20,000) and the ordered decimal reductions (20,000) against Python's `decimal`, the total decimal functions of clause 9.2 (13,500 cases) and the certified ones against `mpmath` (1,676 results of 28 functions in decimal32, decimal64 and decimal128; 4 further cases returned no result). 1,994,276 cases in 145 groups, none failing. |
| `mpfx-sampled.csv` | MPFX against FloatLib on six formats, six operations, four directions, and three operand sets of 200,000 cases, per container and engine. |
| `mpfx-sampled-classes.csv` | Differences grouped by sign/flag behavior or EFT engine by `tests/oracles/mpfx/classify.py`. |
| `mpfx-exhaustive16.csv` | MPFX against FloatLib on every binary16 and bfloat16 pair and every binary32 square root of the exhaustive campaign. |

A row of `none_overflow_or_undefined` counts calls that returned nothing because the real result
overflows or is undefined; `none_nonfinite_input` counts NaN and infinite inputs. MPFX was tested
at commit `b2d27a2`; its differences are reported as
[bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36).
