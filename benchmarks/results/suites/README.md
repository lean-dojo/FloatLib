# Standard suites: results

Written by `benchmarks/suites/summarize.py` from the results of `benchmarks/suites/run.sh`. Each section gives the time of its run: a suite can be run again alone, and the others keep their results. The CSV files next to this file have one short row per case; `counts.csv` has every number of the tables below; `provenance.json` has the toolchain and the size and SHA-256 of each full result file, which is not in the repository. The suite READMEs say what each outcome means.

FPBench and the inequalities ran on 2026-11-20, the hard-to-round inputs, TestFloat and the external FPBench tools on 2026-11-17 (Lean v4.36.0): eight Lean processes at a time, three threads each, on a shared 96-thread Xeon Platinum 8275CL. Limits per process: FPBench 60 seconds and 4 GB (`lean -M 4096`) for a conditional and for a numerical proof; inequalities 20 seconds and 4 GB, one goal per process; TestFloat 900 seconds per campaign. Hard-to-round inputs: 16,384 sampled CORE-MATH cases per function, and the binary32 screens.

## FPBench with `roundoff`

Measured 2026-11-20T11:24:20Z to 2026-11-20T11:32:47Z with Lean 4.36.0.

| theorem | proved | refused | over the time limit | out of memory | not attempted | not translated |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| forward, conditional theorem | 184 | 4 | 0 | 0 | 0 | 84 |
| forward, numerical bound | 33 | 71 | 0 | 0 | 4 | 164 |
| closed, conditional theorem | 180 | 8 | 0 | 0 | 0 | 84 |
| closed, numerical bound | 18 | 82 | 2 | 0 | 6 | 164 |
| backward, conditional theorem | 22 | 166 | 0 | 0 | 0 | 84 |

`out of memory` is a Lean process that stopped at its 4 GB limit (`lean -M 4096`); `not attempted` is a numerical bound whose conditional theorem was not proved.

Of these, proved within 20 seconds of process time: forward, conditional theorem 184, forward, numerical bound 33, closed, conditional theorem 174, closed, numerical bound 18, backward, conditional theorem 22.

| external tool, run on the same exported program | bounded | export_refusal | exported | loaded_no_bound | no_bound | timeout | tool_refusal | tool_unavailable |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| daisy | 117 | 54 | 0 | 0 | 58 | 0 | 43 | 0 |
| fptaylor | 106 | 118 | 0 | 0 | 42 | 6 | 0 | 0 |
| gappa | 96 | 142 | 0 | 0 | 0 | 0 | 34 | 0 |
| satire | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 272 |
| smtlib | 0 | 130 | 142 | 0 | 0 | 0 | 0 | 0 |
| sollya | 0 | 10 | 0 | 262 | 0 | 0 | 0 | 0 |

Programs and default precisions with a numerical bound from both sides: 41; from another tool only: 88; from FloatLib only: 0; from neither: 143.

| FloatLib's bound over the bound of | ratios | smallest | median | largest |
| --- | ---: | ---: | ---: | ---: |
| fptaylor | 23 | 2.133 | 3.2 | 6.984e+05 |
| gappa | 14 | 1.039 | 1.542 | 1.939 |

## Real inequalities with `interval`

Measured 2026-11-20T11:44:50Z to 2026-11-20T12:03:31Z with Lean 4.36.0.

| suite and route | proved | refused | timeout | translation refusal |
| --- | ---: | ---: | ---: | ---: |
| flyspeck, constraint | 6 | 11 | 3 | 144 |
| flyspeck, interval | 3 | 17 | 0 | 144 |
| metitarski, constraint | 340 | 394 | 64 | 150 |
| metitarski, interval | 124 | 674 | 0 | 150 |

| goals | proved by at least one route | by neither |
| --- | ---: | ---: |
| flyspeck, either route | 6 | 158 |
| metitarski, either route | 340 | 608 |

## Hard-to-round inputs

Measured 2026-11-17T22:27:50Z to 2026-11-17T22:32:07Z with Lean 4.36.0.

| domain | matched | not representable | excluded |
| --- | ---: | ---: | ---: |
| real | 107,199 | 16 | 0 |
| complex | 214,396 | 32 | 2 |

A complex input `z = x + i x` counts once per part of its result. `correct-rounding.csv` has the counts and the median times per source, format and function.

## Berkeley TestFloat

Measured 2026-11-17T22:34:02Z to 2026-11-17T22:38:34Z with Lean 4.36.0.

| operations | campaigns that match | vectors | campaigns that do not |
| --- | ---: | ---: | ---: |
| arithmetic, comparisons and the rest | 148 | 5,045,232 | 0 |
| conversions between formats | 42 | 31,512 | 0 |
| fused multiply-add | 20 | 122,664,960 | 0 |

All: 210 campaigns, 127,741,704 vectors, 0 value mismatches, 0 flag mismatches.

<!-- figures: this section is written by benchmarks/plots/figures.py draw -->

## Figures

The captions, alt texts, notes and CSV columns of these figures are in [FIGURES.md](../FIGURES.md).

![Two panels. Left: five stacked horizontal bars, one per kind of theorem, split into programs proved, not proved and not translated. Right: three rows of dots on a logarithmic axis, one dot per program for the ratio of FloatLib's bound to another tool's, with a tick at the median of a row that has three ratios or more, and a vertical line at ratio one.](../figures/suites-fpbench.png "FPBench: what FloatLib's roundoff tactic proves, and its proved bounds against FPTaylor and Gappa. Panel (a) counts the 136 programs of twelve FPBench suite files, each in binary32 and in binary64, by outcome for each kind of theorem; panel (b) is FloatLib's proved numerical bound divided by the other tool's bound on the same program, on a logarithmic axis where 1 is equal and above 1 is looser. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

**Figure 1.** FPBench: what FloatLib's roundoff tactic proves, and its proved bounds against FPTaylor and Gappa. Panel (a) counts the 136 programs of twelve FPBench suite files, each in binary32 and in binary64, by outcome for each kind of theorem; panel (b) is FloatLib's proved numerical bound divided by the other tool's bound on the same program, on a logarithmic axis where 1 is equal and above 1 is looser. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).

![Two panels with the same four rows, MetiTarski and Flyspeck each with interval alone and with the constraint engine. Left: stacked horizontal bars of goals proved, not proved and not translated. Right: one dot per proved goal on a logarithmic time axis, with a tick at the median of a row that has three goals or more.](../figures/suites-inequalities.png "MetiTarski and Flyspeck inequalities given to FloatLib's interval tactic, alone and with the constraint engine. Panel (a) counts the goals by outcome (948 MetiTarski goals and 164 Flyspeck records, one tactic call each); panel (b) is the time Lean took to elaborate each proved goal, without the imports of its file, on a logarithmic axis where lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).")

**Figure 2.** MetiTarski and Flyspeck inequalities given to FloatLib's interval tactic, alone and with the constraint engine. Panel (a) counts the goals by outcome (948 MetiTarski goals and 164 Flyspeck records, one tactic call each); panel (b) is the time Lean took to elaborate each proved goal, without the imports of its file, on a logarithmic axis where lower is faster. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-20).

![Two panels with the same 24 rows, one per function, format and source of inputs. Left: horizontal bars of the number of inputs whose result equals the reference. Right: the median time per call on a logarithmic axis, a filled circle for FloatLib, a diamond for MPFR and a grey cross for CORE-MATH; the complex rows have the FloatLib mark only.](../figures/suites-hard-cases.png "Hard-to-round inputs of exp, expm1, log and log1p: the results of FloatLib against MPFR, CORE-MATH and GNU MPC, and the time per call. Panel (a) counts the inputs whose result word from FloatLib equals the reference (107,199 real results and 214,396 parts of complex results, a complex input counting once per part); panel (b) is the median time of one compiled call, on a logarithmic axis where lower is faster. These are tests on listed inputs, not proofs. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-17).")

**Figure 3.** Hard-to-round inputs of exp, expm1, log and log1p: the results of FloatLib against MPFR, CORE-MATH and GNU MPC, and the time per call. Panel (a) counts the inputs whose result word from FloatLib equals the reference (107,199 real results and 214,396 parts of complex results, a complex input counting once per part); panel (b) is the median time of one compiled call, on a logarithmic axis where lower is faster. These are tests on listed inputs, not proofs. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-17).

![Two panels of horizontal bars with one row per format (binary16, binary32, binary64, binary128, bfloat16). Left: the number of TestFloat campaigns, all in the colour of a campaign in which every vector matches. Right: the number of vectors checked, in millions.](../figures/suites-testfloat.png "Berkeley TestFloat, level 1: the campaigns FloatLib matches and the vectors they check, by format. Panel (a) counts the 210 campaigns, one per operation and rounding direction in each format, of which 210 match on every vector in value and in status flags; panel (b) is the number of vectors of those campaigns, 127,741,704 in all with 0 mismatches. A finite campaign is not a proof. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-17).")

**Figure 4.** Berkeley TestFloat, level 1: the campaigns FloatLib matches and the vectors they check, by format. Panel (a) counts the 210 campaigns, one per operation and rounding direction in each format, of which 210 match on every vector in value and in status flags; panel (b) is the number of vectors of those campaigns, 127,741,704 in all with 0 mismatches. A finite campaign is not a proof. Measured with Lean v4.36.0 (Intel Xeon Platinum 8275CL @ 3.00GHz, 96 threads, shared with other jobs, 2026-11-17).

<!-- end of figures -->
