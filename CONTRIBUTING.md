# Contributing to FloatLib

Thanks for your interest in FloatLib! We welcome new mathematics, faster algorithms,
clearer explanations, and useful examples. A simpler proof, or a good explanation of how
something rounds, can help as much as a new format does. And if something is confusing,
we'd like to hear about that too.

## Getting started

Use the Lean version in [lean-toolchain](lean-toolchain) and the pinned dependencies in
[lake-manifest.json](lake-manifest.json). From the repository root:

```bash
source tests/lib/lake.sh
floatlib_lake exe cache get
floatlib_lake build
```

To build a single module, add its name to the last command. The helper keeps build
products outside the checkout, in a directory you can choose with `FLOATLIB_BUILD_DIR`. For
examples to start from, see the
[first guide chapter](site/content/chapters/01-using-the-library.md), and the
[source map](README.md#source-files) shows which directory each kind of code belongs in.

## Code and proofs

FloatLib builds on mathlib and follows its
[style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html), and
[documentation conventions](https://leanprover-community.github.io/contribute/doc.html).
Before adding a definition or lemma, look for an existing one. Keep related results
together, explain the mathematical idea, and state the hypotheses a caller needs. Each
public operation has one name, and its variants are options of that name, such as
`Model.sqrt x (mode := .up) (status := true)`, so you won't find suffixed copies. A choice
that decides whether a result can be missing, or which algorithm runs and what it guarantees,
is different and gets its own name: a `?` name for a partial variant, or the same short name
in a namespace that states the contract, such as `ExecFloat.Mixed.mul` or
`ExecFloat.Binary.Certified.exp`. We don't keep aliases or deprecated names, so when you
rename a declaration, update every use along with it. Finished proofs should have no
`sorry`, `admit`, or new project-local axioms.

The kernel number types under `FloatLib/Numerics/Kernel`, the packed rows, the core kernel
paths of posits and P3109 and a few tactic modules import nothing beyond Lean itself, so a
file that checks a certificate with them loads in a fraction of a second. Please keep Mathlib
out of their imports (`python3 tests/checks/core-only.py` prints these modules), and put a
proof that needs Mathlib in a module beside them, as `FracProof` is to `Frac`.

An optimized backend needs a proof that it agrees with the reference specification,
rounding and exceptional values included, and the
[backend guide](FloatLib/Floats/ExecFloat/Backends/README.md) explains how to connect such
a kernel to execution. If your change is a speedup, include measurements of the public
calls it affects (the [benchmark guide](benchmarks/README.md) has the commands).

### Linters

We build FloatLib with Mathlib's standard set of linters and the options of `linterOptions`,
and a change is ready when none of them has anything to say. Beyond the standard set, the
options ask for: a docstring on every definition, constructor and structure field, no name that
nothing refers to (also inside tactic proofs), no redundant `private` or `public`, no `omit`
(declare a `variable` where the theorems that need it begin), no `admit`, no file over 1,500
lines, and Lean's extra linters. The list is `linterOptions` in [lakefile.lean](lakefile.lean).
The tests use the same list without the four linters a test module cannot meet, as
[tests/lakefile.lean](tests/lakefile.lean) explains. To check your change, run

```bash
bash tests/checks/linters.sh
```

It builds the library and the tests and fails on any warning, then runs `lake lint`, which
applies the Batteries environment linters to every module and checks that every theorem has a
docstring. `bash tests/verify.sh` runs it too. If a linter is wrong about a declaration, switch
it off for that declaration only (`set_option linter.… false in`, `@[nolint …]`) and say why in
a comment on the line above.

## Sending a change

Keep the change focused. Tell us the problem, what you changed, and which checks you ran, and
for an arithmetic bug, include an input that shows it. If the public API changes, update the
examples and docs, and remove temporary checks and generated files before you send it.

```bash
bash tests/verify.sh     # library checks
bash site/build.sh       # guide and its Lean examples
```

The [testing guide](tests/README.md) and [website tooling guide](site/tooling/README.md)
cover the details. If a proof or a design needs discussion, open an issue with the
statement or example in question, and we can work through it together.
