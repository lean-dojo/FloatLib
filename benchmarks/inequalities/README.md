# Real inequalities

This suite translates formulas from the standard MetiTarski problem set and
Flyspeck's nonlinear inequality records. It asks FloatLib's `interval` tactic
to prove each translated goal under its source hypotheses. No sampled real
evaluation is counted as a proof.

Sources:

- [MetiTarski](https://bitbucket.org/lcpaulson/metitarski-git/), commit
  `5a63f3ecb8c8edf721f0051431db3e0f689d5c17`, MIT.
- [Flyspeck](https://github.com/flyspeck/flyspeck), commit
  `32948714cdf06d700af2c993c9a92b7b551d7af5`, MIT.

The two source manifests pin selected files and their checksums. The TPTP
translator interprets supported arithmetic and transcendental symbols over
the reals. It proves conjectures directly rather than adding the prover's
analytic axiom files as unchecked Lean axioms. Clause sets without a conjecture,
unknown symbols and unsupported logical forms are explicit refusals.

The Flyspeck reader extracts quoted inequality records and unfolds supported
definitions with capture-avoiding substitution. It retains source record
status. It does not execute OCaml generators, choose a value for a Hilbert
choice expression, or silently replace an unimplemented geometric definition.
Natural-to-real coercions admit literal natural numbers only: natural
subtraction and division cannot be interpreted as real operations.

```sh
FLOATLIB_SUITE_OFFSET=0 FLOATLIB_SUITE_LIMIT=24 \
  FLOATLIB_SUITE_BATCH=1 FLOATLIB_SUITE_TIMEOUT=45 \
  bash benchmarks/suites/run.sh inequalities
```

`inventory.json` contains every source record and both requested routes.
`results.csv` distinguishes translation refusal, tactic refusal, resource
failure, proof and unselected rows. Every checkout probes
`interval (constraint := true)` before selecting the constraint route; a
successful probe enables those attempts. A refusal records the tested
syntax and compiler diagnostics, without claiming that no differently
named interface exists. Probe caches are tied to the commit and source hashes.

Lean elaboration time, wall time and proof status are separate fields.
Published MetiTarski, HOL Light and dReal results require a matching source
problem and formulation. A whole-project Flyspeck verification total cannot
be used as a per-goal timing for this extracted subset.

`dreal-published.json` transcribes Table 1 and Examples 2.1 and 2.2 of Gao, Kong
and Clarke, *dReal: An SMT Solver for Nonlinear Theories over the Reals*
(CADE 2013), with the author PDF and extracted-text checksums. Its aggregate
828/916 UNSAT result concerns the paper's SMT translation. Its named
6096597438b example replaces π with 3.14159265; the HOL source uses π.
The corresponding CSV row therefore carries a related-formula candidate,
with no exact-formula match or speedup. The fifteen numerical artifact IDs
in Table 1 remain unmapped to the current extraction.

## Results on Lean v4.36.0

The suite ran on 2026-11-20, eight Lean
processes at a time with three threads each, one goal per process, 20 seconds and 4 GB per process.
[`../results/suites/README.md`](../results/suites/README.md) has the tables and
[`inequalities.csv`](../results/suites/inequalities.csv) one row per goal and route.

The second route is not an option of the tactic: it is the same call of `interval`
with `FloatLib.Tactic.Interval.Constraints` imported as well, which is `interval` as `import FloatLib`
provides it. The first route imports `FloatLib.Tactic.Interval` alone.

| Route | Proved | Tactic refusals | Timeouts | Out of memory | Translation refusals |
|---|---:|---:|---:|---:|---:|
| MetiTarski, `interval` alone | 124 | 674 | 0 | 0 | 150 |
| MetiTarski, with the constraint engine | 340 | 394 | 64 | 0 | 150 |
| Flyspeck, `interval` alone | 3 | 17 | 0 | 0 | 144 |
| Flyspeck, with the constraint engine | 6 | 11 | 3 | 0 | 144 |

At least one route proves 340 of the 948 MetiTarski goals and
6 of the 164 Flyspeck records, and the second route proves every goal that the first one
proves. An out-of-memory row would be a Lean process that stopped at its 4 GB limit
(`lean -M 4096`): the largest process took 3.8 GB. Of the eight problems named after π, the
first route proves three and the second six.
