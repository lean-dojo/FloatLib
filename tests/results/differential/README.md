# Differential campaigns

Summaries of three comparisons that complement the sealed release campaign in `../main/`. The
drivers and references are in `tests/oracles/`; `tests/EXTERNAL.md` describes each comparison.

| File | Contents |
| --- | --- |
| `exhaustive16-floatlib.csv` | Every binary16 and bfloat16 addition, subtraction, multiplication, and division pair and every binary32 square root, per direction: cases and value, flag, kernel, or reference disagreements. 154,618,822,656 cases, none disagreeing. |
| `certified-expm1-log1p-binary32.csv` | Certified `expMinus1` and `logPlus1` on all 2^32 binary32 inputs against MPFR. |
| `certified-expm1-log1p-other.csv` | The same functions on every finite binary16 and bfloat16 input and on the distinct entries of CORE-MATH's binary64 `expm1.wc` and `log1p.wc` lists. |
| `mpfx-sampled.csv` | MPFX against FloatLib on six formats, six operations, four directions, and three operand sets of 200,000 cases, per container and engine. |
| `mpfx-sampled-classes.csv` | Differences grouped by sign/flag behavior or EFT engine by `tests/oracles/mpfx/classify.py`. |
| `mpfx-exhaustive16.csv` | MPFX against FloatLib on every binary16 and bfloat16 pair and every binary32 square root of the exhaustive campaign. |

A row of `none_overflow_or_undefined` counts calls that returned nothing because the real result
overflows or is undefined; `none_nonfinite_input` counts NaN and infinite inputs. MPFX was tested
at commit `b2d27a2`; its differences are reported as
[bksaiki/mpfx#36](https://github.com/bksaiki/mpfx/issues/36).
