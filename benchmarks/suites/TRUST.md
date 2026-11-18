# Trust and evidence

The reading order is [PROOF.md](PROOF.md), this file, then the suite READMEs.
These benchmarks add no library axioms or analytic soundness theorems.

| Item | Role and reason |
| --- | --- |
| Lean kernel and imported FloatLib/mathlib declarations | Check the elaborated FPBench and inequality theorems. Each successful row audits the transitive axiom set, allowing only `propext`, `Classical.choice` and `Quot.sound`. |
| Python source translators | Determine which mathematical statement is submitted to Lean. Kernel checking establishes that statement, so source fidelity remains a separate audit obligation. Unsupported constructs are explicit refusals; source hashes and generated plans support inspection. |
| Exact JSON plans and downloaded sources | Carry inputs, source formulas and proposed bounds. Their bytes and dependencies are hashed. Reading them does not establish a theorem; every admitted bound must be proved from its translated source hypotheses. |
| Native Lean compiler, runtime and selected numerical implementation | Execute correct-rounding and TestFloat checks. These are finite observations, not kernel proofs or exhaustive claims beyond the recorded vectors. |
| MPFR, CORE-MATH and TestFloat references | Supply independent executable comparison results under the documented format, rounding and NaN conventions. Reference disagreements suppress a correctness verdict. |
| FPBench exporter and external analyzers | Produce independent comparison artifacts. Input-contract audits control which numerical bound ratios are admitted; successful exports or procedure loads alone do not count as bounds. |
| Operating system, clocks and resource monitors | Supply elapsed time, process status and memory evidence. Sampled RSS may miss a short-lived peak; `/usr/bin/time -v` supplies additional job-level measurements. |

Capability probes test specific syntax or declaration names under the benchmark
imports. A failed probe does not establish that every alternative interface is
absent. A successful name lookup does not establish numerical correctness.
Constraint probes enable corresponding proof attempts; available complex names
still require a validated reference and encoding adapter before execution.

Neither raw published numbers nor numerical reference outputs become Lean
axioms. Published comparisons retain their source, version and contract
limitations. A conditional roundoff theorem does not become a source-domain
numerical bound merely because an external tool reported a number.
