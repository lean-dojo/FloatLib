# External conformance campaign

We ran these comparisons before releasing FloatLib. This directory contains
the results, raw output, commands, source and environment information, and a plot
of the time spent running each suite.

The binary and IEEE-facing suites passed. The transcendental comparison is
observational because the binary kernels tested here are approximations without
general correct-rounding proofs. SoftPosit is marked `external-limitation`: its pX2 implementation
reported 7,562 differences, while FloatLib's executable and exact
specification agreed on every disputed output. We work through those differences
in [`11-softposit/ADJUDICATION.md`](11-softposit/ADJUDICATION.md).

The campaign's final exit code remains nonzero. One part comes from the original
SoftPosit report; the other comes from a `cp -a` ownership error on EFS after the
files had been written. `provenance/archive-recovery.txt` explains the
recovery procedure.
