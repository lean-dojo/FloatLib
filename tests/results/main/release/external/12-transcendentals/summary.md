# Bounded transcendental comparison

Status: **observational comparison complete; this is not a conformance pass**.

Input: `mpfr.tsv`
Optional external providers: CORE-MATH, OpenLibm, RLIBM

MPFR is the correctly rounded nearest-even reference. FloatLib's current transcendental kernels are deterministic approximations: differences below are measurements, not conformance failures.

`Value exact` treats any NaN result as a NaN match because MPFR does not preserve IEEE NaN payloads. `Bit exact` is literal encoding equality. ULP columns include only pairs where both outputs are finite; signed zero has distance zero. `Nonfinite mismatch` counts differing infinities, NaNs, or finite/nonfinite pairs.

| Candidate | Format | Operation | Cases | Value exact | Bit exact | Finite | Nonfinite mismatch | 0 ULP | 1 ULP | 2–3 | 4–15 | 16–255 | ≥256 | Max | P50 | P90 | P99 |
| --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| FloatLib | binary32 | exp | 293 | 293 (100.00%) | 293 (100.00%) | 241 | 0 | 241 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| FloatLib | binary32 | log | 293 | 292 (99.66%) | 292 (99.66%) | 151 | 0 | 150 | 0 | 0 | 0 | 0 | 1 | 142384 | 0 | 0 | 0 |
| FloatLib | binary32 | sin | 293 | 293 (100.00%) | 293 (100.00%) | 290 | 0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| FloatLib | binary32 | cos | 293 | 293 (100.00%) | 293 (100.00%) | 290 | 0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| FloatLib | binary32 | sinh | 293 | 282 (96.25%) | 282 (96.25%) | 185 | 1 | 175 | 10 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| FloatLib | binary32 | cosh | 293 | 264 (90.10%) | 264 (90.10%) | 185 | 1 | 157 | 28 | 0 | 0 | 0 | 0 | 1 | 0 | 1 | 1 |
| FloatLib | binary32 | tanh | 293 | 291 (99.32%) | 291 (99.32%) | 292 | 0 | 290 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 0 |
| FloatLib | binary64 | exp | 294 | 294 (100.00%) | 294 (100.00%) | 246 | 0 | 246 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| FloatLib | binary64 | log | 294 | 292 (99.32%) | 292 (99.32%) | 147 | 0 | 145 | 1 | 0 | 0 | 0 | 1 | 4194304 | 0 | 0 | 1 |
| FloatLib | binary64 | sin | 294 | 294 (100.00%) | 294 (100.00%) | 291 | 0 | 291 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| FloatLib | binary64 | cos | 294 | 294 (100.00%) | 294 (100.00%) | 291 | 0 | 291 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| FloatLib | binary64 | sinh | 294 | 282 (95.92%) | 282 (95.92%) | 203 | 0 | 191 | 12 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| FloatLib | binary64 | cosh | 294 | 273 (92.86%) | 273 (92.86%) | 203 | 0 | 182 | 21 | 0 | 0 | 0 | 0 | 1 | 0 | 1 | 1 |
| FloatLib | binary64 | tanh | 294 | 288 (97.96%) | 288 (97.96%) | 293 | 0 | 287 | 6 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| CORE-MATH | binary32 | exp | 293 | 293 (100.00%) | 293 (100.00%) | 241 | 0 | 241 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary32 | log | 293 | 293 (100.00%) | 155 (52.90%) | 151 | 0 | 151 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary32 | sin | 293 | 293 (100.00%) | 291 (99.32%) | 290 | 0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary32 | cos | 293 | 293 (100.00%) | 291 (99.32%) | 290 | 0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary32 | sinh | 293 | 293 (100.00%) | 293 (100.00%) | 186 | 0 | 186 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary32 | cosh | 293 | 293 (100.00%) | 293 (100.00%) | 186 | 0 | 186 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary32 | tanh | 293 | 293 (100.00%) | 293 (100.00%) | 292 | 0 | 292 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | exp | 294 | 294 (100.00%) | 294 (100.00%) | 246 | 0 | 246 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | log | 294 | 294 (100.00%) | 151 (51.36%) | 147 | 0 | 147 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | sin | 294 | 294 (100.00%) | 292 (99.32%) | 291 | 0 | 291 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | cos | 294 | 294 (100.00%) | 292 (99.32%) | 291 | 0 | 291 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | sinh | 294 | 294 (100.00%) | 294 (100.00%) | 203 | 0 | 203 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | cosh | 294 | 294 (100.00%) | 294 (100.00%) | 203 | 0 | 203 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| CORE-MATH | binary64 | tanh | 294 | 294 (100.00%) | 294 (100.00%) | 293 | 0 | 293 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| OpenLibm | binary32 | exp | 293 | 285 (97.27%) | 285 (97.27%) | 241 | 0 | 233 | 8 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary32 | log | 293 | 289 (98.63%) | 151 (51.54%) | 151 | 0 | 147 | 4 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary32 | sin | 293 | 293 (100.00%) | 291 (99.32%) | 290 | 0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| OpenLibm | binary32 | cos | 293 | 293 (100.00%) | 291 (99.32%) | 290 | 0 | 290 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| OpenLibm | binary32 | sinh | 293 | 265 (90.44%) | 265 (90.44%) | 186 | 0 | 158 | 28 | 0 | 0 | 0 | 0 | 1 | 0 | 1 | 1 |
| OpenLibm | binary32 | cosh | 293 | 279 (95.22%) | 279 (95.22%) | 186 | 0 | 172 | 14 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary32 | tanh | 293 | 270 (92.15%) | 270 (92.15%) | 292 | 0 | 269 | 23 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary64 | exp | 294 | 284 (96.60%) | 284 (96.60%) | 246 | 0 | 236 | 10 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary64 | log | 294 | 292 (99.32%) | 149 (50.68%) | 147 | 0 | 145 | 2 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary64 | sin | 294 | 285 (96.94%) | 283 (96.26%) | 291 | 0 | 282 | 9 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary64 | cos | 294 | 289 (98.30%) | 287 (97.62%) | 291 | 0 | 286 | 5 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary64 | sinh | 294 | 270 (91.84%) | 270 (91.84%) | 203 | 0 | 179 | 24 | 0 | 0 | 0 | 0 | 1 | 0 | 1 | 1 |
| OpenLibm | binary64 | cosh | 294 | 282 (95.92%) | 282 (95.92%) | 203 | 0 | 191 | 12 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| OpenLibm | binary64 | tanh | 294 | 262 (89.12%) | 262 (89.12%) | 293 | 0 | 261 | 31 | 1 | 0 | 0 | 0 | 2 | 0 | 1 | 1 |
| RLIBM | binary32 | exp | 293 | 293 (100.00%) | 292 (99.66%) | 241 | 0 | 241 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| RLIBM | binary32 | log | 293 | 293 (100.00%) | 155 (52.90%) | 151 | 0 | 151 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| RLIBM | binary32 | sinh | 293 | 293 (100.00%) | 292 (99.66%) | 186 | 0 | 186 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| RLIBM | binary32 | cosh | 293 | 293 (100.00%) | 292 (99.66%) | 186 | 0 | 186 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
