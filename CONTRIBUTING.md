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
products outside the checkout, and `FLOATLIB_BUILD_DIR` sets where they go. The
[first guide chapter](site/content/chapters/01-using-the-library.md) has examples to start
from, and the [source map](README.md#source-files) shows which directory each kind of code
belongs in.

## Code and proofs

We build on mathlib and follow its
[style](https://leanprover-community.github.io/contribute/style.html),
[naming](https://leanprover-community.github.io/contribute/naming.html), and
[documentation conventions](https://leanprover-community.github.io/contribute/doc.html).
Before adding a definition or lemma, look for an existing one. Keep related results
together, explain the mathematical idea, and state the hypotheses a caller needs. Each
public operation has one name. Its variants are options of that name, such as
`Model.sqrt x (mode := .up) (status := true)`, so there are no suffixed copies. When you
rename a declaration, update every use along with it, because we don't keep aliases or
deprecated names. Finished proofs should have no `sorry`, `admit`, or new project-local
axioms.

An optimized backend needs a proof that it agrees with the reference specification,
rounding and exceptional values included, and the
[backend guide](FloatLib/Floats/ExecFloat/Backends/README.md) explains how to connect such
a kernel to execution. If your change is a speedup, include measurements of the public
calls it affects (the [benchmark guide](benchmarks/README.md) has the commands).

## Sending a change

Keep the change focused. Tell us the problem, what you changed, and which checks you ran,
and for an arithmetic bug, include an input that shows it. If the public API changes,
update the examples and docs, and remove temporary checks and generated files before you
send it.

```bash
bash tests/verify.sh     # library checks
bash site/build.sh       # guide and its Lean examples
```

The [testing guide](tests/README.md) and [website tooling guide](site/tooling/README.md)
cover the details. If a proof or a design needs discussion, open an issue with the
statement or example in question, and we can work through it together.
