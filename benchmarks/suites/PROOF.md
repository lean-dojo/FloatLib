# What a successful benchmark row establishes

This directory contains an experiment harness, not a new numerical theorem. Read this file
before the suite READMEs. Each original problem is identified by a pinned source path, source
hash, and index. Exact input values live in source files or JSON plans; generated Lean commands
carry the program or goal, not a hand-transcribed coefficient table.

For an FPBench program, the input variables are stored floating-point values. A translation
preserves the source operation order, lexical bindings, explicit precision annotations, and
rounding attributes for the supported scalar fragment. It specializes the default precision to
binary32 or binary64. An unsupported construct is a refusal, not an approximation.

The forward, closed, and backward commands generate their own propositions. The experiment
records the complete proposition, including every finiteness, range, domain, or perturbation
premise. A successful elaboration proves that proposition for all its quantified arguments
under exactly those premises. It does **not** by itself prove that an FPBench precondition
implies those premises, nor yield a uniform numeric bound over that precondition. In particular,
the reference inputs are the decoded stored values; external results that include real-input
rounding cannot be silently compared to that different statement.

An optional numeric closure is a separate theorem. Its inputs are finite stored
values satisfying the exact real interpretation of the source precondition; its
conclusion bounds the absolute difference from the exact real source expression
by a rational candidate. Python may propose this candidate, but only Lean's proof
of the entire implication admits a numeric result. The forward route specializes
the generated mixed theorem; the closed route specializes the generated closed
theorem and proves its finiteness premise. Every remaining premise must close
from the source hypotheses. Branch-sensitive references and unsupported domains
remain explicit refusals. A backward perturbation theorem is recorded in its own
form and is not silently converted into an absolute-error ratio.

For a real inequality, success means that the translated goal, with its source hypotheses and
quantifiers, was closed by the specified tactic. Neither the Python translator nor a floating
point evaluation supplies proof evidence. A proof is admitted as a successful row only when its
declaration exists as a Lean theorem and its transitive axiom set is contained in
`{propext, Classical.choice, Quot.sound}`. This check rejects a theorem containing a placeholder
even if Lean's elaborator recovered from an earlier error.

The argument for isolation is the same for every case: save the imported command environment,
elaborate the commands, inspect the resulting theorem and its axioms, record the outcome, and
restore the saved environment. A failed case cannot contribute a theorem to a later case.
An operating-system timeout or infrastructure error is a separate status and never a proof.

Correctly rounded function and TestFloat rows are executable differential checks over their
listed finite vector sets. They compare encodings and, where available, exception flags. Their
argument is finite enumeration by a compiled Lean implementation against an independently
identified reference. They are not kernel proofs or statements about all inputs. The reusable
analytic soundness theorems remain the existing FloatLib library theorems; no imported expected
output is treated as a theorem.

Dependencies: the pinned Lean and mathlib versions, FloatLib's existing `roundoff` and `interval`
tactics, the chosen runtime interfaces, the original input corpora, and the published or
independent executable references named in each suite. Source translation itself is outside the
trusted kernel and must be audited against those inputs. The unit checks cover parsing,
lexical scope, numeric exactness, rounding annotations, and failure accounting.

CORE-MATH supplies an exhaustive binary32 input space for its unary functions, rather than a
binary32 worst-case file. The optional binary32 screening pass enumerates an explicitly recorded
range of those encodings. It ranks normal-output candidates by the distance of the correctly
rounded binary64 result from a binary32 rounding midpoint. MPFR at 256 and 512 bits then measures
the retained candidates' distance independently. This is a way to select difficult tests, not a
proof that the selected inputs are globally hardest: the screening value itself is rounded, and
subnormal outputs are excluded from this ranking. Input encodings and enumeration limits are
exact JSON integers; measured difficulty and reference timings are experimental quantities.

## Applicable Gappa bounds on integer polynomials

The contract audit accepts scalar `+`, `-`, `*`, and parallel `let` at one
binary32 or binary64 precision, with one supported rounding mode. Every body
literal and every closed-box endpoint is an integer of magnitude at most
2^24. Other operations, annotations and legacy input precision are refused.
This is an expression family, not a list of named benchmarks.

The pinned exporter emits those integers exactly. Its real expression retains
the source operation tree and lexical bindings. In the rounded expression,
Gappa's `name float<...,mode>= expression` syntax rounds every arithmetic
operation; a variable-only assignment introduces no new rounding. Input
variables and literals are rounded separately.

The audit checks a coarse magnitude invariant. Associate each input interval
with M = 2 max(1, |lo|, |hi|), and each literal k with max(1, |k|). Negation
preserves M. For addition/subtraction use the pre-rounding bound M1 + M2;
for multiplication use M1 M2. Reject a pre-rounding bound greater than
2^(emax-1), where emax is 127 or 1023. Otherwise assign twice that bound to
the result. Every bound is at least one. If |z| <= M, supported IEEE rounding
has magnitude at most 2M: adjacent representable powers of two enclose its
magnitude, including the region below one. The rejection threshold keeps
those powers finite. Induction excludes overflow at every operation; the
small integer input and literal bounds also lie within the finite range.

For a finite stored input satisfying the source box, use its decoded value
as Gappa's real input. Rounding it again gives the same value. Induction on
the source tree identifies the rounded real-valued computations; signed zero
has no observable effect in this polynomial subset. The exact references
also agree. A uniform Gappa error bound therefore applies to these stored
inputs. It can cover additional real inputs, so the ratio compares applicable
upper bounds, not identical optimization domains.

Dependencies: the pinned FPBench `src/core2gappa.rkt` and
`src/fpcore-extra.rkt`; Gappa 1.8.3 `doc/formalizing.rst` (Definitions) and
`doc/examples.rst` (implicit rounding and absence of overflow). This Python
contract audit is not a Lean proof of the exporter or external analyzer.
