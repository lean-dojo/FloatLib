# CORE-MATH qualification

This directory keeps the completed upstream CORE-MATH qualification run used
by the ecosystem report. The campaign checked out CORE-MATH at
`68b034fbe9512781352d28f2dc9795c1686fe8e9` and ran its own `check.sh`
driver over every function found in the binary16, bfloat16, binary32, and
binary64 source families.

`functions.tsv` is the deduplicated result table. It has 169 function rows:
166 passed, while the three compound functions exited with status 2. Those
three checks could not link because the Ubuntu MPFR package did not provide
`mpfr_compound`. We therefore record this as a qualified pass. The failure
happened before those three functions reached a numerical comparison.

The work ran in three waves because several exhaustive checks outlived the
first workers. The later workers resumed from the rows already written instead
of rerunning completed functions. `attempts/` preserves the logs and
environment records from all 18 selected workers. The aggregate `run.log`
summarizes how those files were combined.

This is an upstream qualification result. It records what the pinned
CORE-MATH checkout did in its own test harness. FloatLib is not part of this
execution path.
