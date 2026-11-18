# Reproducing capability and resource refusals

These probes record failures at a named checkout. They do not modify the library.
Run them through `benchmarks/suites/run.sh capabilities` under the same resource
policy as the main suites. `results.csv` records each actual diagnostic and the
hash of its JSON command plan.

The constraint probe asks `interval` for its constraint route. Four complex probes
check the tested `ExecComplex.exp`, `expm1`, `log` and `log1p` names. The determinant
probe is generated from FPBench's first determinant program through the same
translator as the full suite; it uses the same one-process, sampled 8 GiB and
45-second limits. A resource failure is evidence about that budget, not a
mathematical impossibility or a claim that larger budgets cannot succeed.
