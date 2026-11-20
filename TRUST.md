# What FloatLib trusts

A theorem of the library is checked by Lean's kernel. This file lists everything else that a
claim about FloatLib rests on, with the reason each item is trusted and the check that watches
it. `tests/checks/trust-surface.sh` holds the exact per-file counts of the source-level items
and fails when one is added, and `tests/FloatLibTests/Conformance/Trust/Axioms.lean` audits the
compiled declarations.

## Proofs

| Item | Reason | Check |
| --- | --- | --- |
| Lean's kernel, with its native arithmetic on natural-number literals | Every proof, and every proof by evaluation (`decide +kernel`, `float_decide`, `lane_decide`), is a term this kernel accepts. | `FLOATLIB_RUN_INDEPENDENT_CHECKER=1 bash tests/verify.sh` gives every compiled declaration of the library to the kernel once more, one module per process, and fails on a constant that is an axiom (`tests/checks/kernel-replay.sh`). `benchmarks/kernel/checkers.sh` gives five families of proofs by evaluation to the proof checkers that ship with Lean: `leanchecker`, `leanchecker-paranoid` and `con-ron`, which is written independently of Lean's kernel, accept all five. `nanoda_bin`, also independent, accepts four and gave no verdict on the fifth within the limits of the run (`benchmarks/kernel/checkers.csv`, one run with Lean v4.36.0) |
| The axioms `propext`, `Classical.choice`, `Quot.sound` | Mathlib's real analysis uses them. No other axiom is accepted. | `Trust/Axioms.lean` fails on any other axiom in the loaded library declarations, and its imports reach every library module but the unchecked host-FPU one; `trust-surface.sh` checks that reach, rejects `sorry` and `axiom` in every source, and fails if the kernel holds a constant of the library as an axiom, private ones included |
| Hypotheses of theorems | Finiteness, range, IEEE-descriptor and fresh-randomness conditions are premises of the statements, never axioms. | the statements |

## Compiled code

A refinement theorem equates Lean definitions. What runs is the code that Lean's compiler and
the C compiler produce from them, and no theorem covers those compilers or the hardware.

| Item | Reason | Check |
| --- | --- | --- |
| `@[csimp]` replacements | Each is a proved equation between the two definitions, for all arguments. | the axiom audit traverses every `@[csimp]` theorem |
| `@[implemented_by]` on the posit decoder `Posit.Model.toDyadic?` | The one-pass decoder is proved equal to the transparent one (`Internal.toDyadic?_eq`), registered with `@[replacement_proof]`. | the audit checks that the theorem equates exactly the attribute's two endpoints on all arguments; `trust-surface.sh` allows this one site in the library |
| Backends registered with `@[compiler_optimize]` | A candidate carries the proof `run = spec`. The `reference` form uses the shared `Certified.reference` at the operation's full type; registration checks both the operation and constructor. Registration refuses an unproved candidate and a candidate whose code reaches an `@[implemented_by]` or `@[extern]` replacement outside Lean's own library without a registered proof, other than Lean's generated constructor-index tag read of the next row. | `Util/Provenance.lean`; the check reads the definition bodies that the registering module can see, so a replacement behind an unexported body is covered by the audit of the library only |
| Lean's generated `T.ctorIdx._impl` | Since Lean 4.36, compiled code finds out which constructor a value was built with by reading a tag that Lean generates for every inductive type with several constructors, in place of running the definition `T.ctorIdx`. That read is unsafe code, so nothing can be proved about it, and we trust it as we trust the rest of Lean's code generation. | `Provenance.isGeneratedCtorIdx` recognizes exactly that pair by its names, its type and both bodies; `@[compiler_optimize]` and the audit accept no other unproved replacement, and the audit reports the count |
| `Configured.NativeFPU.Unchecked` | Host binary32 and binary64 operations, for callers who ask for them by name. No refinement theorem mentions them and no planner candidate uses them. | the import is allowed in three files; `check native` compares them with the software path |
| Arithmetic of `Native.Half` and `Native.BFloat16` | Computed in host binary32 and rounded once more, which is correct when the host is IEEE binary32 (Figueroa's double-rounding condition holds for both formats). Narrowing, widening and NaN normalization are proved; the arithmetic is not. | `check native` compares add, sub, mul, div, sqrt, negation and comparisons with the software models, including the bfloat16 subnormal range |
| Elementary functions of the native carriers and of Lean's `Float` | Host library calls. They carry no rounding guarantee. | none |
| `roundoff` theorems about programs on `Float32` and `Float` | The laws that move the imports `ExecFloat.Binary.ofFloat32` and `ofFloat` through `+`, `-`, `*`, `/`, the square root, negation and natural-number literals are theorems about Lean's logical model of the native types. That the compiled program and the processor compute what that model says is the trust of this section. `roundoff` refuses `Float32.exp` and the other host library functions, and says so. | `tests/FloatLibTests/Tactic/Roundoff/Native.lean` pins the statements and the refusal; `check native` compares native execution with the software path |

## Proof automation and tooling

| Item | Reason | Check |
| --- | --- | --- |
| `native_decide` in 47 test sites | Finite checks of execution boundaries, faster by compiled evaluation. They trust the compiler for that check. The library's proofs use none. | `trust-surface.sh` checks the per-file counts. The axiom audit rejects the extra axioms generated by native evaluation in library proofs. |
| `unsafe` evaluation in `Tactic/FloatInfo/Inspection.lean`, `Tactic/Roundoff/Extension.lean`, `Tactic/Roundoff/Check.lean` and `site/tooling/ExportNodes.lean` | Each evaluates a declaration at elaboration time to display a plan, read a registered extension, run a program at inputs for the report of `#roundoff_check`, or export the site. None produces a proof term the kernel does not check. | counted per file by `trust-surface.sh` |
| The report of `#roundoff_check` | It runs the compiled program in Lean's interpreter and evaluates the reference and the bound of a generated theorem with its own rational enclosures, taking the premises as given. It is a report at the inputs it names. It proves nothing and no theorem depends on it. | `tests/FloatLibTests/Tactic/Roundoff/Check.lean` pins its reports |
| The reference that `roundoff` states a bound against | The kernel checks the generated theorem. That its reference is the intended exact computation rests on the conditions listed under "Trust assumptions" in `Tactic/Roundoff.lean`. | the statement is printed for the reader |
| `kernel_twin` and `cover%` | Elaboration computes a candidate program or finite cover; the kernel checks its equality proof or coverage proof. Neither command supplies an axiom. | `KernelTwin.lean`, `KernelComplex.lean`, and the audit of all their declarations |
| Cost estimates of the planner and declared kernel costs | They choose among proved candidates. A wrong estimate costs speed. | `AutomaticDispatch.lean` pins the selections |

## Evidence that is not proof

Comparisons with MPFR, GNU MPC, CPython's `cmath`, SoftFloat, SoftPosit, Flocq, Arb and other
libraries, the native regression suites, and every timing are tests and measurements. They can
show a disagreement; they prove nothing. The stochastic-rounding theorems assume fresh,
independent entropy at every rounding; no theorem covers a random-number generator.
